//! Tree-walking reducer — continuation-passing.
//!
//! The activation stack is the only recursion that grows with program
//! depth: `step()` does one small transition per call (either rewriting
//! the top frame in place or pushing a child), and `deliver()` loops over
//! cascades without calling back into `step()`. Host Rust call depth stays
//! O(1) for any program depth, so runaway recursion surfaces as
//! `EvalError::DepthExceeded` rather than as a native stack overflow.

use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::node_occurrence::{Expr, MatchBranch, NodeKind, NodeOccurrence};
use crate::kb::term::{HandleKind, Literal, Term, TermId};
use crate::kb::KnowledgeBase;

use super::closure::Closure;
use super::error::EvalError;
use super::frame::{AwaitState, Frame};
use super::pattern::{constructor_pattern_name, match_pattern};
use super::value::Value;
use super::Interpreter;

pub enum StepOutcome {
    /// The stack emptied and the top-level computation produced a value.
    Done(Value),
    /// Advance the driver: `step()` either pushed a child, transitioned a
    /// wait-state, or rewrote the top frame's expr in place.
    Continue,
}

impl Interpreter {
    /// Drive the activation stack until it empties. Single loop, no native
    /// recursion. Enforces `EvalConfig::step_cap` per iteration so
    /// TCO'd infinite tail loops surface as `StepsExhausted` rather than
    /// hanging the host.
    pub fn run(&mut self) -> Result<Value, EvalError> {
        loop {
            if let Some(cap) = self.config.step_cap {
                if self.step_count >= cap {
                    return Err(EvalError::StepsExhausted { cap });
                }
            }
            self.step_count = self.step_count.saturating_add(1);
            match self.step()? {
                StepOutcome::Done(v) => return Ok(v),
                StepOutcome::Continue => {}
            }
        }
    }

    /// Do one evaluation step. Invariants:
    /// - `self.stack.top().awaiting` is always `None` here (waiting frames
    ///   have a child above them, so they can never be the top during step).
    /// - After `step()` returns `Continue` the stack's top is either fresh
    ///   (ready for the next `step()`) or empty (`Done`).
    pub fn step(&mut self) -> Result<StepOutcome, EvalError> {
        let occ = {
            let top = self.stack.top()
                .ok_or_else(|| EvalError::Internal("step() on empty stack".into()))?;
            debug_assert!(top.awaiting.is_none(), "top frame should be fresh");
            top.expr.clone()
        };
        self.reduce_node(&occ)
    }

    fn reduce_node(&mut self, occ: &Rc<NodeOccurrence>) -> Result<StepOutcome, EvalError> {
        let expr = match &occ.kind {
            NodeKind::Expr { expr, .. } => expr,
            NodeKind::RuleHead { .. } => {
                return Err(EvalError::Internal(
                    "unexpected RuleHead occurrence in expression position".into(),
                ));
            }
        };
        match expr {
            Expr::Const(lit) => {
                let v = self.literal_to_value(lit.clone())?;
                self.deliver(v)
            }
            Expr::Ref(sym) | Expr::Ident(sym) => self.reduce_var(*sym),
            Expr::VarRef { name } => self.reduce_var(*name),
            Expr::If { condition, then_branch, else_branch } => {
                self.start_if(condition, then_branch, else_branch)
            }
            Expr::Let { pattern, value, body, .. } => {
                self.start_let(*pattern, value, body)
            }
            Expr::Match { scrutinee, branches } => {
                self.start_match(scrutinee, branches)
            }
            Expr::Lambda { param, body } => self.reduce_lambda(*param, body.clone()),
            Expr::Apply { functor, pos_args, named_args } => {
                // WI-218: the typer may have classified this apply for
                // spec-op rewrite. PinNow redirects the call to the
                // impl op; ConcreteApplyWithin similarly redirects (the
                // requirements channel is empty for the bare-apply
                // form). Read the classification off the NodeOccurrence's
                // RefCell — written by `kb/typing.rs::classify` during
                // type-checking.
                let target = classified_apply_target(occ).unwrap_or(*functor);
                self.start_apply(target, pos_args, named_args)
            }
            Expr::ApplyWithin { functor, args, named_args, requirements } => {
                self.start_apply_within(*functor, args, named_args, requirements)
            }
            Expr::Constructor { name, pos_args, named_args } => {
                self.start_constructor(*name, pos_args, named_args)
            }
            Expr::RequirementAtSort { chain, slot } => {
                self.reduce_requirement_at_sort_node(chain, *slot)
            }
            Expr::ConstructRequirement { impl_functor, requirements } => {
                self.reduce_construct_requirement_node(*impl_functor, requirements)
            }
            Expr::HoApply { .. }
            | Expr::HoApplyWithin { .. }
            | Expr::ConstructorWithin { .. }
            | Expr::LambdaWithin { .. }
            | Expr::Instantiation { .. }
            | Expr::ListLit(_)
            | Expr::SetLit(_)
            | Expr::TupleLit { .. } => Err(EvalError::Internal(format!(
                "unhandled Expr variant in eval: {:?}",
                std::mem::discriminant(expr),
            ))),
            Expr::Var(_) => Err(EvalError::Internal(
                "unexpected unopened DeBruijn variable in expression body".into(),
            )),
            Expr::Bottom => Err(EvalError::Internal(
                "unexpected Expr::Bottom in expression body".into(),
            )),
        }
    }

    fn reduce_var(&mut self, sym: Symbol) -> Result<StepOutcome, EvalError> {
        let target_name = self.kb.resolve_sym(sym).to_string();
        // Local binding first, then a frame requirement (a body reading
        // a `__req_*` param by name — WI-237 names model), then dispatch.
        let bound = {
            let top = self.stack.top()
                .ok_or_else(|| EvalError::Internal("reduce_var on empty stack".into()))?;
            find_local(&self.kb, &top.locals, &target_name)
                .cloned()
                .or_else(|| {
                    find_requirement(&top.requirements, sym)
                        .map(|h| Value::Requirement(h.clone()))
                })
        };
        if let Some(v) = bound {
            return self.deliver(v);
        }
        self.dispatch_call(sym, Vec::new())
    }

    fn reduce_lambda(
        &mut self,
        param: TermId,
        body: Rc<NodeOccurrence>,
    ) -> Result<StepOutcome, EvalError> {
        // Any pattern is legal as a lambda param; match_pattern unpacks it
        // at call time. `lambda (a, b) -> body` is a tuple pattern against
        // a single tuple arg; `lambda _` ignores the arg; `lambda x` is
        // the common identifier case.
        let env = self.stack.top()
            .map(|f| f.locals.clone())
            .unwrap_or_default();
        // WI-223: snapshot the enclosing frame's requirements so the
        // closure restores them on invocation (lexical scope at lambda
        // creation, not invocation site). Frame-side SmallVec is sized 2,
        // closure-side is sized 1 (most lambdas hold 0–1 reqs); collect
        // across the size boundary.
        let requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 1]> = self.stack.top()
            .map(|f| f.requirements.iter().cloned().collect())
            .unwrap_or_default();
        let handle = self.closures.alloc(Closure {
            param_pattern: param,
            body,
            env,
            requirements,
        });
        self.deliver(Value::Closure(handle))
    }

    // ── Requirement-typed value reductions (WI-223) ────────────────
    //
    // The grammar in `docs/design/operation-call-model.md` §"Two
    // primitives" restricts these to chains rooted at `var_ref` (a
    // named frame-requirement read), so reduction is direct (no
    // AwaitState dance — the chain is statically resolvable to arena
    // handles).

    fn reduce_requirement_at_sort_node(
        &mut self,
        chain: &Rc<NodeOccurrence>,
        slot: i64,
    ) -> Result<StepOutcome, EvalError> {
        let parent = self.eval_requirement_chain_node(chain)?;
        let projected = parent.project(slot as usize);
        self.deliver(Value::Requirement(projected))
    }

    fn reduce_construct_requirement_node(
        &mut self,
        impl_functor: Symbol,
        requirements: &[Rc<NodeOccurrence>],
    ) -> Result<StepOutcome, EvalError> {
        let mut handles: SmallVec<[super::value::RequirementHandle; 1]> = SmallVec::new();
        for occ in requirements.iter() {
            handles.push(self.eval_requirement_chain_node(occ)?);
        }
        let new_handle = self.requirements.alloc(impl_functor, handles);
        self.deliver(Value::Requirement(new_handle))
    }

    /// Synchronously reduce a requirement-typed NodeOccurrence to a
    /// `RequirementHandle`. Walks the chain per the design grammar:
    /// bottoms out at `var_ref(name)`; intermediate nodes are
    /// `RequirementAtSort` (projection) or `ConstructRequirement`
    /// (allocation). No AwaitState — the grammar is closed under direct
    /// recursion.
    fn eval_requirement_chain_node(
        &self,
        occ: &Rc<NodeOccurrence>,
    ) -> Result<super::value::RequirementHandle, EvalError> {
        let expr = match &occ.kind {
            NodeKind::Expr { expr, .. } => expr,
            _ => return Err(EvalError::Internal(
                "requirement chain must be an Expr-kind occurrence".into(),
            )),
        };
        match expr {
            Expr::RequirementAtSort { chain, slot } => {
                let parent = self.eval_requirement_chain_node(chain)?;
                Ok(parent.project(*slot as usize))
            }
            Expr::ConstructRequirement { impl_functor, requirements } => {
                let mut handles: SmallVec<[super::value::RequirementHandle; 1]> = SmallVec::new();
                for r in requirements.iter() {
                    handles.push(self.eval_requirement_chain_node(r)?);
                }
                Ok(self.requirements.alloc(*impl_functor, handles))
            }
            Expr::VarRef { name } => {
                let top = self.stack.top().ok_or_else(|| {
                    EvalError::Internal("requirement chain var_ref on empty stack".into())
                })?;
                find_requirement(&top.requirements, *name).cloned().ok_or_else(|| {
                    EvalError::Internal(format!(
                        "var_ref({}) unbound in requirement position",
                        self.kb.resolve_sym(*name)
                    ))
                })
            }
            other => Err(EvalError::Internal(format!(
                "expected requirement-chain Expr, got {:?}",
                std::mem::discriminant(other),
            ))),
        }
    }

    /// Spec-op dispatch via the dispatching dictionary's functor.
    /// Conceptually a vtable / sort-ops-table lookup; materialized as a
    /// qualified-name resolution `<dict.functor_qn>.<op_short>`. Falls
    /// back to `fn_sym` when the impl has no override — supports
    /// spec-op default-body invocation (e.g., `Eq.neq`'s default when
    /// the impl doesn't override `neq`).
    fn dispatch_via_sort_ops_table(
        &self,
        fn_sym: Symbol,
        dispatching_dict: &super::value::RequirementHandle,
    ) -> Symbol {
        let fn_qn = self.kb.qualified_name_of(fn_sym);
        let Some((_, op_short)) = fn_qn.rsplit_once('.') else {
            return fn_sym;
        };
        let impl_qn = self.kb.qualified_name_of(dispatching_dict.functor());
        let target_qn = format!("{impl_qn}.{op_short}");
        self.kb.try_resolve_symbol(&target_qn).unwrap_or(fn_sym)
    }

    // ── Binder starts: update top.awaiting, push child frame. ──────

    fn start_if(
        &mut self,
        condition: &Rc<NodeOccurrence>,
        then_branch: &Rc<NodeOccurrence>,
        else_branch: &Rc<NodeOccurrence>,
    ) -> Result<StepOutcome, EvalError> {
        self.suspend_and_push(
            AwaitState::ChooseBranch {
                then_branch: then_branch.clone(),
                else_branch: else_branch.clone(),
            },
            condition.clone(),
        )
    }

    fn start_let(
        &mut self,
        pattern: TermId,
        value: &Rc<NodeOccurrence>,
        body: &Rc<NodeOccurrence>,
    ) -> Result<StepOutcome, EvalError> {
        self.suspend_and_push(
            AwaitState::LetBind {
                pattern,
                body: body.clone(),
            },
            value.clone(),
        )
    }

    fn start_match(
        &mut self,
        scrutinee: &Rc<NodeOccurrence>,
        branches: &[MatchBranch],
    ) -> Result<StepOutcome, EvalError> {
        let branches_cloned: Vec<MatchBranch> = branches
            .iter()
            .map(|b| MatchBranch {
                pattern: b.pattern,
                guard: b.guard.clone(),
                body: b.body.clone(),
                span: b.span,
            })
            .collect();
        self.suspend_and_push(
            AwaitState::MatchDispatch { branches: branches_cloned },
            scrutinee.clone(),
        )
    }

    fn start_apply(
        &mut self,
        functor: Symbol,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
    ) -> Result<StepOutcome, EvalError> {
        // WI-218: if this apply's functor has a typer-recorded dispatch
        // rewrite via the legacy term-keyed map, redirect to the impl op.
        // The rewrite map is populated by `kb/typing.rs::record_apply_*`
        // during requirement-insertion; while the post-WI-247 substrate
        // keeps the same map, the eval looks up by the apply's functor
        // for now via `dispatch_call`'s callee resolution path.
        let target = functor;

        if pos_args.is_empty() && named_args.is_empty() {
            return self.dispatch_call(target, Vec::new());
        }

        // Build the per-arg occurrence stream. Positional args come
        // first (matching legacy source-order behavior), then named
        // args. The eval currently evaluates all args by position; the
        // typer is responsible for ordering named args to align with
        // the callee's params.
        let mut remaining: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(
            pos_args.len() + named_args.len(),
        );
        for arg in pos_args.iter() { remaining.push(arg.clone()); }
        for (_, arg) in named_args.iter() { remaining.push(arg.clone()); }
        let first = remaining.remove(0);
        self.suspend_and_push(
            AwaitState::ApplyArgs {
                target,
                buffered: Vec::new(),
                remaining,
            },
            first,
        )
    }

    /// WI-223 / WI-234 (Model 1): reduce `apply_within(fn, args,
    /// requirements)`. The requirements channel has at most one entry —
    /// the dispatching dictionary; when present, its functor selects
    /// the impl op for a spec-op `fn`, and its sub-tree is expanded
    /// into the callee's `frame.requirements` at frame push.
    fn start_apply_within(
        &mut self,
        functor: Symbol,
        args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
        requirements_occ: &[Rc<NodeOccurrence>],
    ) -> Result<StepOutcome, EvalError> {
        if requirements_occ.len() > 1 {
            return Err(EvalError::Internal(format!(
                "apply_within requirements channel has {} entries; v0 Model 1 \
                 expects 0 or 1",
                requirements_occ.len(),
            )));
        }
        let dispatching_dict: Option<super::value::RequirementHandle> =
            if let Some(first) = requirements_occ.first() {
                Some(self.eval_requirement_chain_node(first)?)
            } else {
                None
            };

        let target = match &dispatching_dict {
            Some(dict) => self.dispatch_via_sort_ops_table(functor, dict),
            None => functor,
        };

        // Names model (WI-237): expand the dispatching dict into
        // name-keyed frame requirements — `__req_self` → the dict, and
        // `__req_<spec>` → each positional sub-instance, named by
        // `synth_req_names` against the callee's impl parent sort. The
        // same name synthesis runs in the typer's IR emitter, so a
        // generic body's `var_ref(__req_*)` reads resolve against this.
        let requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 2]> =
            match dispatching_dict {
                Some(dict) => {
                    let names = match crate::kb::typing::impl_parent_of_op(&self.kb, target) {
                        Some(p) => Some(crate::kb::typing::synth_req_names(&mut self.kb, p)),
                        None => None,
                    };
                    let arity = dict.arity();
                    let name_count = names.as_ref().map_or(0, |n| n.len());
                    if arity != name_count {
                        return Err(EvalError::Internal(format!(
                            "apply_within frame-push: dispatching dict for {} has \
                             arity {arity} but its requires chain has {name_count} entries",
                            self.kb.qualified_name_of(target),
                        )));
                    }
                    let mut reqs: SmallVec<[(Symbol, super::value::RequirementHandle); 2]> =
                        SmallVec::with_capacity(arity + 1);
                    reqs.push((self.fields.req_self, dict.clone()));
                    if let Some(names) = names {
                        for (k, name) in names.iter().enumerate() {
                            reqs.push((*name, dict.project(k)));
                        }
                    }
                    reqs
                }
                None => SmallVec::new(),
            };

        let total_args = args.len() + named_args.len();
        if total_args == 0 {
            return self.dispatch_call_with_requirements(target, Vec::new(), requirements);
        }

        let mut remaining: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(total_args);
        for a in args.iter() { remaining.push(a.clone()); }
        for (_, a) in named_args.iter() { remaining.push(a.clone()); }
        let first = remaining.remove(0);
        self.suspend_and_push(
            AwaitState::ApplyWithinArgs {
                target,
                buffered: Vec::new(),
                remaining,
                requirements,
            },
            first,
        )
    }

    fn start_constructor(
        &mut self,
        name: Symbol,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
    ) -> Result<StepOutcome, EvalError> {
        let is_tuple_literal = Some(name) == self.reflect.tuple_literal;
        let mut remaining: Vec<(Option<Symbol>, Rc<NodeOccurrence>)> =
            Vec::with_capacity(pos_args.len() + named_args.len());
        for a in pos_args.iter() {
            remaining.push((None, a.clone()));
        }
        for (n, a) in named_args.iter() {
            remaining.push((Some(*n), a.clone()));
        }

        if remaining.is_empty() {
            return self.finish_constructor(name, is_tuple_literal, Vec::new(), Vec::new());
        }

        let (first_name, first_expr) = remaining.remove(0);
        let placeholder = first_expr.clone();
        let top = self.stack.top_mut().ok_or_else(
            || EvalError::Internal("start_constructor with no parent".into()),
        )?;
        top.awaiting = Some(AwaitState::ConstructorArgs {
            ctor_sym: name,
            is_tuple_literal,
            buffered_pos: Vec::new(),
            buffered_named: Vec::new(),
            // Prepend the currently-in-flight name so the delivery logic
            // knows which slot to place the next value into.
            remaining: std::iter::once((first_name, placeholder))
                .chain(remaining.into_iter())
                .collect(),
        });
        let (op, locals, requirements) = {
            let top = self.stack.top().unwrap();
            (top.op, top.locals.clone(), top.requirements.clone())
        };
        self.stack.push(Frame {
            op,
            expr: first_expr,
            locals,
            requirements,
            awaiting: None,
        })?;
        Ok(StepOutcome::Continue)
    }

    /// Suspend the top frame with the given await state and push a child
    /// frame for the sub-expression.
    fn suspend_and_push(
        &mut self,
        state: AwaitState,
        child_expr: Rc<NodeOccurrence>,
    ) -> Result<StepOutcome, EvalError> {
        let top = self.stack.top_mut()
            .ok_or_else(|| EvalError::Internal("suspend_and_push with no parent".into()))?;
        top.awaiting = Some(state);
        let (op, locals, requirements) = {
            let top = self.stack.top().unwrap();
            (top.op, top.locals.clone(), top.requirements.clone())
        };
        self.stack.push(Frame {
            op,
            expr: child_expr,
            locals,
            requirements,
            awaiting: None,
        })?;
        Ok(StepOutcome::Continue)
    }

    // ── Dispatch and delivery ──────────────────────────────────

    fn dispatch_call(
        &mut self,
        target: Symbol,
        arg_values: Vec<Value>,
    ) -> Result<StepOutcome, EvalError> {
        self.dispatch_call_with_requirements(target, arg_values, SmallVec::new())
    }

    fn dispatch_call_with_requirements(
        &mut self,
        target: Symbol,
        arg_values: Vec<Value>,
        requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        // 1. Local closure bound to target?
        let target_name = self.kb.resolve_sym(target).to_string();
        let local_closure = {
            let top = self.stack.top()
                .ok_or_else(|| EvalError::Internal("dispatch_call with no parent".into()))?;
            find_local(&self.kb, &top.locals, &target_name)
                .and_then(|v| match v {
                    Value::Closure(h) => Some(h.clone()),
                    _ => None,
                })
        };
        if let Some(handle) = local_closure {
            // Closures override apply.requirements with their own
            // (the HO-call exception). The caller's `requirements`
            // here are discarded — see closure invocation in the design.
            drop(requirements);
            return self.enter_closure(handle, arg_values);
        }

        // 2. Registered Rust builtin?
        if let Some(builtin) = self.builtins.get(&target).cloned() {
            let result = (builtin)(self, &arg_values)?;
            return self.deliver(result);
        }

        // 3. Anthill-defined operation body.
        let (body_node, params) = lookup_operation_body(&self.kb, target)
            .ok_or_else(|| EvalError::UnknownOperation { name: target_name })?;
        self.enter_operation(target, body_node, &params, arg_values, requirements)
    }

    fn enter_operation(
        &mut self,
        target: Symbol,
        body_node: Rc<NodeOccurrence>,
        params: &[(Symbol, TermId)],
        arg_values: Vec<Value>,
        requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        if arg_values.len() != params.len() {
            return Err(EvalError::ArityMismatch {
                op: "operation call",
                expected: params.len(),
                got: arg_values.len(),
            });
        }
        let mut locals: SmallVec<[(Symbol, Value); 4]> = SmallVec::new();
        for (i, (pname, _ptype)) in params.iter().enumerate() {
            locals.push((*pname, arg_values[i].clone()));
        }
        // TCO: the current frame has nothing left to do — its expr has
        // already been fully consumed (either it WAS the apply node whose
        // args are now collected, or a var_ref that resolved to this op).
        // Replace the frame in-place instead of pushing + waiting on
        // OperationResult. This is the standard CEK-machine TCO: drop the
        // trivial continuation frame. Preserves constant activation-stack
        // depth for tail-recursive programs.
        let top = self.stack.top_mut()
            .ok_or_else(|| EvalError::Internal("enter_operation with no parent".into()))?;
        // WI-223 / WI-237: callee's frame.requirements come from
        // apply_within's expanded requirements channel. Plain `apply`
        // calls install an empty channel — a generic body's
        // `var_ref(__req_*)` read then surfaces a clear "unbound in
        // requirement position" error rather than being silently wrong.
        *top = Frame {
            op: target,
            expr: body_node,
            locals,
            requirements,
            awaiting: None,
        };
        Ok(StepOutcome::Continue)
    }

    fn enter_closure(
        &mut self,
        handle: super::value::ClosureHandle,
        args: Vec<Value>,
    ) -> Result<StepOutcome, EvalError> {
        if args.len() != 1 {
            return Err(EvalError::ArityMismatch {
                op: "closure",
                expected: 1,
                got: args.len(),
            });
        }
        let arg = args.into_iter().next().unwrap();
        let (param_pattern, body) = self.closures.with(&handle, |c| {
            (c.param_pattern, c.body.clone())
        });
        let bindings = match_pattern(self, param_pattern, &arg).ok_or_else(|| {
            EvalError::MatchFailed { scrutinee: arg.type_name().to_string() }
        })?;
        let mut locals: SmallVec<[(Symbol, Value); 4]> = self.closures.clone_env(&handle);
        for (sym, v) in bindings {
            locals.push((sym, v));
        }
        // WI-223: closure invocation overrides the uniform
        // `frame.requirements = apply_within.requirements` rule with the
        // requirements snapshotted at lambda construction. Preserves
        // lexical scope of the lambda's creation site. See
        // `docs/design/operation-call-model.md` §"Closure invocation:
        // the one runtime exception". The closure-side SmallVec has inline
        // size 1 (most lambdas need 0–1 reqs), the frame-side has 2;
        // collect across the size boundary.
        let requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 2]> =
            self.closures.with(&handle, |c| c.requirements.iter().cloned().collect());
        // TCO: same rationale as enter_operation. A closure call in any
        // position is a tail call relative to its own apply frame. The
        // closure inherits its caller's `op` for error-reporting purposes.
        let top = self.stack.top_mut()
            .ok_or_else(|| EvalError::Internal("enter_closure with no parent".into()))?;
        let op = top.op;
        *top = Frame {
            op,
            expr: body,
            locals,
            requirements,
            awaiting: None,
        };
        Ok(StepOutcome::Continue)
    }

    /// Deliver a computed value to the frame beneath `top` (or finish the
    /// computation if the stack empties). Loops internally to cascade
    /// through `OperationResult` pass-throughs and through builtin
    /// dispatches that themselves produce values.
    fn deliver(&mut self, v: Value) -> Result<StepOutcome, EvalError> {
        loop {
            self.stack.pop();
            let Some(top) = self.stack.top_mut() else {
                return Ok(StepOutcome::Done(v));
            };
            let state = top.awaiting.take().ok_or_else(|| {
                EvalError::Internal(
                    "deliver: parent frame had no awaiting state".into(),
                )
            })?;
            match state {
                AwaitState::ChooseBranch { then_branch, else_branch } => {
                    let chosen = match v.as_bool() {
                        Some(true) => then_branch,
                        Some(false) => else_branch,
                        None => return Err(EvalError::TypeMismatch {
                            expected: "Bool",
                            got: v.type_name().to_string(),
                        }),
                    };
                    top.expr = chosen;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::LetBind { pattern, body } => {
                    // Hoist the pattern-match result out of the borrow so we
                    // don't hold a `&self` while we mutate `top.locals`.
                    let bindings = match_pattern(self, pattern, &v).ok_or_else(|| {
                        EvalError::MatchFailed { scrutinee: v.type_name().to_string() }
                    })?;
                    let top = self.stack.top_mut().unwrap();
                    for (sym, val) in bindings {
                        top.locals.push((sym, val));
                    }
                    top.expr = body;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::MatchDispatch { branches } => {
                    let scrutinee_functor = value_functor(&self.kb, &v);
                    let mut picked: Option<(Rc<NodeOccurrence>, super::pattern::Bindings)> = None;
                    for branch in &branches {
                        let pat_tid = branch.pattern;
                        // Cheap pre-filter: constructor-pattern functor
                        // mismatch can skip the full match attempt.
                        if let (Some(pat_name), Some(scr_name)) =
                            (constructor_pattern_name(self, pat_tid), scrutinee_functor)
                        {
                            if pat_name != scr_name { continue; }
                        }
                        if let Some(bindings) = match_pattern(self, pat_tid, &v) {
                            picked = Some((branch.body.clone(), bindings));
                            break;
                        }
                    }
                    let (body, bindings) = picked.ok_or_else(|| {
                        EvalError::MatchFailed { scrutinee: v.type_name().to_string() }
                    })?;
                    let top = self.stack.top_mut().unwrap();
                    for (sym, val) in bindings {
                        top.locals.push((sym, val));
                    }
                    top.expr = body;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::ApplyArgs { target, mut buffered, mut remaining } => {
                    buffered.push(v);
                    if remaining.is_empty() {
                        return self.dispatch_call(target, buffered);
                    }
                    let next_expr = remaining.remove(0);
                    let top = self.stack.top_mut().unwrap();
                    top.awaiting = Some(AwaitState::ApplyArgs {
                        target, buffered, remaining,
                    });
                    let (op, locals, requirements) =
                        (top.op, top.locals.clone(), top.requirements.clone());
                    self.stack.push(Frame {
                        op,
                        expr: next_expr,
                        locals,
                        requirements,
                        awaiting: None,
                    })?;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::ApplyWithinArgs {
                    target,
                    mut buffered,
                    mut remaining,
                    requirements,
                } => {
                    buffered.push(v);
                    if remaining.is_empty() {
                        return self.dispatch_call_with_requirements(
                            target,
                            buffered,
                            requirements,
                        );
                    }
                    let next_expr = remaining.remove(0);
                    let top = self.stack.top_mut().unwrap();
                    top.awaiting = Some(AwaitState::ApplyWithinArgs {
                        target,
                        buffered,
                        remaining,
                        requirements,
                    });
                    let (op, locals, frame_requirements) =
                        (top.op, top.locals.clone(), top.requirements.clone());
                    self.stack.push(Frame {
                        op,
                        expr: next_expr,
                        locals,
                        requirements: frame_requirements,
                        awaiting: None,
                    })?;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::ConstructorArgs {
                    ctor_sym,
                    is_tuple_literal,
                    mut buffered_pos,
                    mut buffered_named,
                    mut remaining,
                } => {
                    // First entry in `remaining` names the arg we just evaluated.
                    let (current_name, _placeholder_occ) = remaining.remove(0);
                    classify_ctor_arg(
                        &self.kb,
                        ctor_sym,
                        is_tuple_literal,
                        &self.reflect,
                        current_name,
                        v,
                        &mut buffered_pos,
                        &mut buffered_named,
                    );
                    if remaining.is_empty() {
                        return self.finish_constructor(
                            ctor_sym,
                            is_tuple_literal,
                            buffered_pos,
                            buffered_named,
                        );
                    }
                    let (next_name, next_expr) = remaining[0].clone();
                    // The currently-in-flight entry's placeholder is the
                    // occurrence we're about to push. The name flows with
                    // the value when it comes back.
                    let pushed_expr = next_expr.clone();
                    remaining[0] = (next_name, next_expr);
                    let top = self.stack.top_mut().unwrap();
                    top.awaiting = Some(AwaitState::ConstructorArgs {
                        ctor_sym,
                        is_tuple_literal,
                        buffered_pos,
                        buffered_named,
                        remaining,
                    });
                    let (op, locals, requirements) =
                        (top.op, top.locals.clone(), top.requirements.clone());
                    self.stack.push(Frame {
                        op,
                        expr: pushed_expr,
                        locals,
                        requirements,
                        awaiting: None,
                    })?;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::OperationResult => {
                    // Body produced a value — that's this apply's result.
                    // Cascade: loop again to pop this frame and deliver `v`
                    // further.
                    continue;
                }
            }
        }
    }

    fn finish_constructor(
        &mut self,
        ctor_sym: Symbol,
        is_tuple_literal: bool,
        pos: Vec<Value>,
        mut named: Vec<(Symbol, Value)>,
    ) -> Result<StepOutcome, EvalError> {
        sort_named_canonical(&self.kb, ctor_sym, &mut named);
        let value = if Some(ctor_sym) == self.reflect.list_literal {
            self.build_list_value(pos, &named)?
        } else if is_tuple_literal {
            Value::Tuple { pos, named }
        } else if Some(ctor_sym) == self.reflect.set_literal {
            // SetLiteral has set semantics: dedup via `structural_eq` so
            // nested tuples/entities compare by shape, not identity. Opaque
            // handles (Closure/Stream/Lazy) still compare as distinct.
            let mut deduped: Vec<Value> = Vec::with_capacity(pos.len());
            for v in pos {
                if !deduped.iter().any(|existing| existing.structural_eq(&v)) {
                    deduped.push(v);
                }
            }
            Value::Entity { functor: ctor_sym, pos: deduped, named }
        } else {
            Value::Entity { functor: ctor_sym, pos, named }
        };
        self.deliver(value)
    }

    /// Build a `cons(head, tail)` chain ending in `nil()`. A `tail` named
    /// arg overrides the default `nil` terminator.
    pub fn build_list_value(
        &self,
        elements: Vec<Value>,
        named: &[(Symbol, Value)],
    ) -> Result<Value, EvalError> {
        let cons_sym = self.reflect.cons.ok_or_else(|| EvalError::Internal(
            "cons not loaded — stdlib missing anthill.prelude.List.cons".into()
        ))?;
        let nil_sym = self.reflect.nil.ok_or_else(|| EvalError::Internal(
            "nil not loaded — stdlib missing anthill.prelude.List.nil".into()
        ))?;
        let tail_seed = named.iter()
            .find(|(s, _)| *s == self.fields.tail)
            .map(|(_, v)| v.clone())
            .unwrap_or(Value::Entity { functor: nil_sym, pos: Vec::new(), named: Vec::new() });

        let mut acc = tail_seed;
        for elem in elements.into_iter().rev() {
            acc = Value::Entity {
                functor: cons_sym,
                pos: Vec::new(),
                named: vec![(self.fields.head, elem), (self.fields.tail, acc)],
            };
        }
        Ok(acc)
    }

    fn literal_to_value(&self, lit: Literal) -> Result<Value, EvalError> {
        Ok(match lit {
            Literal::Int(n) => Value::Int(n),
            Literal::Float(f) => Value::Float(f.into_inner()),
            Literal::Bool(b) => Value::Bool(b),
            Literal::String(s) => Value::Str(s),
            Literal::BigInt(n) => Value::BigInt(n),
            Literal::Handle(HandleKind::Occurrence, raw) => {
                // Occurrence handle in expression position: unwrap to the
                // underlying term and evaluate it. This would normally be
                // resolved by `resolve_handle` earlier, but some paths pass
                // the raw handle through.
                let tid = self.kb.occurrences.term(
                    crate::kb::occurrence::OccurrenceId::from_raw(raw)
                );
                return Err(EvalError::Internal(format!(
                    "unexpected occurrence handle as direct value; resolve first (got tid {:?})",
                    tid,
                )));
            }
            Literal::Handle(_, _) => {
                return Err(EvalError::Internal("non-occurrence Handle in expression".into()));
            }
        })
    }
}

// ── helpers ─────────────────────────────────────────────────────

/// WI-218 — read the typer's `CallClass` off the Apply occurrence's
/// RefCell and return the impl-op symbol to dispatch to. PinNow tags
/// the call for direct redirection to `impl_op_sym`; the bare-apply
/// `ConcreteApplyWithin` form (empty requirements channel) redirects
/// to `fn_target_sym`. DeferToRequirement leaves the target as the
/// spec op — the dispatch happens at runtime via the requirements
/// channel, not at the apply.
fn classified_apply_target(occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    use crate::kb::typing::CallClass;
    let classification = match &occ.kind {
        NodeKind::Expr { classification, .. } => classification.borrow(),
        _ => return None,
    };
    match classification.as_deref() {
        Some(CallClass::PinNow { impl_op_sym, .. }) => Some(*impl_op_sym),
        Some(CallClass::ConcreteApplyWithin { fn_target_sym, .. }) => {
            Some(*fn_target_sym)
        }
        _ => None,
    }
}

/// Short-name-aware local lookup. See the note in reduce_var for why we
/// compare by name rather than by interned `Symbol`.
fn find_local<'a>(
    kb: &KnowledgeBase,
    locals: &'a SmallVec<[(Symbol, Value); 4]>,
    target_name: &str,
) -> Option<&'a Value> {
    for (bound, val) in locals.iter().rev() {
        if kb.resolve_sym(*bound) == target_name {
            return Some(val);
        }
    }
    None
}

/// Find a frame-level requirement by its synthesized `__req_*` name.
/// Synth names are interned once (see `kb::typing::synth_req_names`), so
/// Symbol equality suffices — unlike `find_local`, which must compare
/// resolved short names. Reverse order: last binding wins (shadowing).
fn find_requirement<'a>(
    reqs: &'a SmallVec<[(Symbol, super::value::RequirementHandle); 2]>,
    name: Symbol,
) -> Option<&'a super::value::RequirementHandle> {
    reqs.iter().rev().find(|(s, _)| *s == name).map(|(_, h)| h)
}

/// Head functor of a value, when one is recoverable.
fn value_functor(kb: &KnowledgeBase, value: &Value) -> Option<Symbol> {
    match value {
        Value::Entity { functor, .. } => Some(*functor),
        Value::Term(tid) => match kb.get_term(*tid) {
            Term::Fn { functor, .. } => Some(*functor),
            _ => None,
        },
        _ => None,
    }
}

/// Decide whether a constructor arg with optional auto-name goes into the
/// positional or named slot of the emerging value. Tuple literals' `_N`
/// auto-names are unwrapped back to positional; everything else goes named
/// iff it has a name.
fn classify_ctor_arg(
    kb: &KnowledgeBase,
    _ctor_sym: Symbol,
    is_tuple_literal: bool,
    _reflect: &super::ReflectSymbols,
    name: Option<Symbol>,
    value: Value,
    pos: &mut Vec<Value>,
    named: &mut Vec<(Symbol, Value)>,
) {
    match name {
        Some(sym) if is_tuple_literal && kb.resolve_sym(sym).starts_with('_') => {
            pos.push(value);
        }
        Some(sym) => named.push((sym, value)),
        None => pos.push(value),
    }
}

/// Sort named args by the entity's declared field order when the functor
/// is registered, falling back to `Symbol::index()` for anonymous shapes.
/// Mirrors `alloc_from_value` in `kb/execute.rs` so Value and Term share
/// the same canonical form.
fn sort_named_canonical(kb: &KnowledgeBase, functor: Symbol, named: &mut Vec<(Symbol, Value)>) {
    if named.len() < 2 {
        return;
    }
    match kb.entity_field_names(functor) {
        Some(order) => named.sort_by_key(|(s, _)|
            order.iter().position(|f| f == s).unwrap_or(usize::MAX)),
        None => named.sort_by_key(|(s, _)| s.index()),
    }
}

/// Walk OperationInfo facts for a functor, return (body node, params).
/// Thin wrapper over `kb::op_info::lookup_operation_info`. Returns
/// `None` for body-less ops (specs) and for ops whose `op_body_node`
/// the loader didn't populate.
pub fn lookup_operation_body(
    kb: &KnowledgeBase,
    functor: Symbol,
) -> Option<(std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>, Vec<(Symbol, TermId)>)> {
    let rec = crate::kb::op_info::lookup_operation_info(kb, functor)?;
    let body = rec.body_node?;
    Some((body, rec.params))
}
