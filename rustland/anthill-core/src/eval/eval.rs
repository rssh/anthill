//! Tree-walking reducer — continuation-passing.
//!
//! The activation stack is the only recursion that grows with program
//! depth: `step()` does one small transition per call (either rewriting
//! the top frame in place or pushing a child), and `deliver()` loops over
//! cascades without calling back into `step()`. Host Rust call depth stays
//! O(1) for any program depth, so runaway recursion surfaces as
//! `EvalError::DepthExceeded` rather than as a native stack overflow.

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::term::{HandleKind, Literal, Term, TermId};
use crate::kb::typing::{get_named_arg, resolve_handle, unwrap_option};
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
        let tid = {
            let top = self.stack.top()
                .ok_or_else(|| EvalError::Internal("step() on empty stack".into()))?;
            debug_assert!(top.awaiting.is_none(), "top frame should be fresh");
            top.expr
        };
        self.reduce_expr(tid)
    }

    fn reduce_expr(&mut self, tid: TermId) -> Result<StepOutcome, EvalError> {
        // WI-218: if this term is a spec-op apply that the typer rewrote
        // to point at the impl op, evaluate the rewritten apply instead.
        // The rewrite map is populated by `kb/typing.rs::check_apply` at
        // type-checking time; the original term's `fn` symbol points at
        // the spec op (no body), the rewritten term's points at the
        // impl op (has body). dispatch_origin preserves the original
        // spec op symbol for reflection / debug; runtime uses only the
        // term-substitution map.
        let tid = self.kb.dispatch_rewrites.get(&tid).copied().unwrap_or(tid);
        let term = self.kb.get_term(tid).clone();
        match term {
            Term::Const(lit) => {
                let v = self.literal_to_value(lit)?;
                self.deliver(v)
            }
            Term::Ref(sym) | Term::Ident(sym) => self.reduce_var(sym),
            Term::Fn { functor, pos_args, named_args } => {
                self.reduce_fn(functor, &pos_args, &named_args)
            }
            Term::Var(_) => Err(EvalError::Internal(
                "unexpected unopened DeBruijn variable in expression body".into(),
            )),
            Term::Bottom => Err(EvalError::Internal(
                "unexpected Term::Bottom in expression body".into(),
            )),
        }
    }

    fn reduce_fn(
        &mut self,
        functor: Symbol,
        pos_args: &SmallVec<[TermId; 4]>,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        let sx = &self.reflect;

        if Some(functor) == sx.int_lit
            || Some(functor) == sx.float_lit
            || Some(functor) == sx.string_lit
            || Some(functor) == sx.bool_lit
            || Some(functor) == sx.bigint_lit
        {
            let value_tid = named_arg(named_args, self.fields.value)
                .ok_or_else(|| EvalError::Internal("literal entity missing 'value' arg".into()))?;
            return match self.kb.get_term(value_tid).clone() {
                Term::Const(lit) => {
                    let v = self.literal_to_value(lit)?;
                    self.deliver(v)
                }
                other => Err(EvalError::Internal(format!("literal 'value' is not Const: {other:?}"))),
            };
        }

        if Some(functor) == sx.var_ref {
            let name_tid = named_arg(named_args, self.fields.name)
                .ok_or_else(|| EvalError::Internal("var_ref missing 'name'".into()))?;
            let sym = term_as_symbol(&self.kb, name_tid)
                .ok_or_else(|| EvalError::Internal("var_ref name not a symbol".into()))?;
            return self.reduce_var(sym);
        }

        if Some(functor) == sx.if_expr {
            return self.start_if(named_args);
        }
        if Some(functor) == sx.let_expr {
            return self.start_let(named_args);
        }
        if Some(functor) == sx.match_expr {
            return self.start_match(named_args);
        }
        if Some(functor) == sx.lambda {
            return self.reduce_lambda(named_args);
        }
        if Some(functor) == sx.apply {
            return self.start_apply(named_args);
        }
        if Some(functor) == sx.constructor {
            return self.start_constructor(named_args);
        }

        // A bare reference to a nullary operation: functor is the operation's
        // name and both arg lists are empty. Dispatch through the same path.
        if pos_args.is_empty() && named_args.is_empty() {
            return self.dispatch_call(functor, Vec::new());
        }

        Err(EvalError::Internal(format!(
            "unhandled expression functor: {}",
            self.kb.resolve_sym(functor)
        )))
    }

    fn reduce_var(&mut self, sym: Symbol) -> Result<StepOutcome, EvalError> {
        let target_name = self.kb.resolve_sym(sym).to_string();
        let local = {
            let top = self.stack.top()
                .ok_or_else(|| EvalError::Internal("reduce_var on empty stack".into()))?;
            find_local(&self.kb, &top.locals, &target_name).cloned()
        };
        if let Some(v) = local {
            return self.deliver(v);
        }
        self.dispatch_call(sym, Vec::new())
    }

    fn reduce_lambda(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        let param_tid = named_arg(named_args, self.fields.param)
            .ok_or_else(|| EvalError::Internal("lambda missing 'param'".into()))?;
        let body_tid = named_arg(named_args, self.fields.body)
            .ok_or_else(|| EvalError::Internal("lambda missing 'body'".into()))?;
        let body_term = resolve_handle(&self.kb, body_tid);

        // Any pattern is legal as a lambda param; match_pattern unpacks it
        // at call time. `lambda (a, b) -> body` is a tuple pattern against
        // a single tuple arg; `lambda _` ignores the arg; `lambda x` is
        // the common identifier case.
        let env = self.stack.top()
            .map(|f| f.locals.clone())
            .unwrap_or_default();
        let handle = self.closures.alloc(Closure {
            param_pattern: param_tid,
            body: body_term,
            env,
        });
        self.deliver(Value::Closure(handle))
    }

    // ── Binder starts: update top.awaiting, push child frame. ──────

    fn start_if(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        let cond_tid = named_arg(named_args, self.fields.cond)
            .ok_or_else(|| EvalError::Internal("if_expr missing 'cond'".into()))?;
        let then_tid = named_arg(named_args, self.fields.then_branch)
            .ok_or_else(|| EvalError::Internal("if_expr missing 'then_branch'".into()))?;
        let else_tid = named_arg(named_args, self.fields.else_branch)
            .ok_or_else(|| EvalError::Internal("if_expr missing 'else_branch'".into()))?;
        self.suspend_and_push(
            AwaitState::ChooseBranch {
                then_branch: resolve_handle(&self.kb, then_tid),
                else_branch: resolve_handle(&self.kb, else_tid),
            },
            resolve_handle(&self.kb, cond_tid),
        )
    }

    fn start_let(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        let pat_tid = named_arg(named_args, self.fields.pattern)
            .ok_or_else(|| EvalError::Internal("let_expr missing 'pattern'".into()))?;
        let value_tid = named_arg(named_args, self.fields.value)
            .ok_or_else(|| EvalError::Internal("let_expr missing 'value'".into()))?;
        let body_tid = named_arg(named_args, self.fields.body)
            .ok_or_else(|| EvalError::Internal("let_expr missing 'body'".into()))?;
        self.suspend_and_push(
            AwaitState::LetBind {
                pattern: pat_tid,
                body: resolve_handle(&self.kb, body_tid),
            },
            resolve_handle(&self.kb, value_tid),
        )
    }

    fn start_match(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        let scrutinee_tid = named_arg(named_args, self.fields.scrutinee)
            .ok_or_else(|| EvalError::Internal("match_expr missing 'scrutinee'".into()))?;
        let branches_tid = named_arg(named_args, self.fields.branches)
            .ok_or_else(|| EvalError::Internal("match_expr missing 'branches'".into()))?;
        let branches = crate::kb::typing::list_to_vec(&self.kb, branches_tid);
        self.suspend_and_push(
            AwaitState::MatchDispatch { branches },
            resolve_handle(&self.kb, scrutinee_tid),
        )
    }

    fn start_apply(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        let fn_tid = named_arg(named_args, self.fields.fn_)
            .ok_or_else(|| EvalError::Internal("apply missing 'fn'".into()))?;
        let target = term_as_symbol(&self.kb, fn_tid)
            .ok_or_else(|| EvalError::Internal("apply 'fn' is not a symbol".into()))?;

        let args_tid = named_arg(named_args, self.fields.args)
            .ok_or_else(|| EvalError::Internal("apply missing 'args'".into()))?;
        let arg_terms = crate::kb::typing::list_to_vec(&self.kb, args_tid);

        if arg_terms.is_empty() {
            return self.dispatch_call(target, Vec::new());
        }

        let mut remaining: Vec<TermId> = Vec::with_capacity(arg_terms.len());
        for arg_tid in arg_terms {
            let (_name, value_inner) = decode_apply_arg(&self.kb, arg_tid, &self.fields)?;
            remaining.push(value_inner);
        }
        let first = remaining.remove(0);
        self.suspend_and_push(
            AwaitState::ApplyArgs {
                target,
                buffered: Vec::new(),
                remaining,
            },
            resolve_handle(&self.kb, first),
        )
    }

    fn start_constructor(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        let name_tid = named_arg(named_args, self.fields.name)
            .ok_or_else(|| EvalError::Internal("constructor missing 'name'".into()))?;
        let ctor_sym = term_as_symbol(&self.kb, name_tid)
            .ok_or_else(|| EvalError::Internal("constructor name not a symbol".into()))?;
        let args_tid = named_arg(named_args, self.fields.args)
            .ok_or_else(|| EvalError::Internal("constructor missing 'args'".into()))?;
        let arg_terms = crate::kb::typing::list_to_vec(&self.kb, args_tid);

        let is_tuple_literal = Some(ctor_sym) == self.reflect.tuple_literal;
        let mut remaining: Vec<(Option<Symbol>, TermId)> = Vec::with_capacity(arg_terms.len());
        for arg_tid in arg_terms {
            let (name_opt, value_inner) = decode_apply_arg(&self.kb, arg_tid, &self.fields)?;
            remaining.push((name_opt, value_inner));
        }

        if remaining.is_empty() {
            // No-arg constructor — produce Value::Entity immediately.
            return self.finish_constructor(ctor_sym, is_tuple_literal, Vec::new(), Vec::new());
        }

        let (first_name, first_expr) = remaining.remove(0);
        let _ = first_name; // name handled when the value is delivered (in ConstructorArgs transition we need it — see note).
        // We actually need to know the NAME of the arg currently being
        // evaluated, because when it returns we have to decide pos vs named.
        // The AwaitState::ConstructorArgs structure holds `remaining` which
        // includes names for upcoming args, but *not* for the arg currently
        // in flight. Stash that name in an extra slot.
        let expr = resolve_handle(&self.kb, first_expr);
        let current_name = first_name;
        let top = self.stack.top_mut().ok_or_else(
            || EvalError::Internal("start_constructor with no parent".into()),
        )?;
        top.awaiting = Some(AwaitState::ConstructorArgs {
            ctor_sym,
            is_tuple_literal,
            buffered_pos: Vec::new(),
            buffered_named: Vec::new(),
            // Prepend the currently-in-flight name so the delivery logic
            // knows which slot to place the next value into.
            remaining: std::iter::once((current_name, TermId::from_raw(u32::MAX)))
                .chain(remaining.into_iter())
                .collect(),
        });
        let (op, locals) = {
            let top = self.stack.top().unwrap();
            (top.op, top.locals.clone())
        };
        self.stack.push(Frame {
            op,
            expr,
            locals,
            awaiting: None,
        })?;
        Ok(StepOutcome::Continue)
    }

    /// Suspend the top frame with the given await state and push a child
    /// frame for the sub-expression.
    fn suspend_and_push(
        &mut self,
        state: AwaitState,
        child_expr: TermId,
    ) -> Result<StepOutcome, EvalError> {
        let top = self.stack.top_mut()
            .ok_or_else(|| EvalError::Internal("suspend_and_push with no parent".into()))?;
        top.awaiting = Some(state);
        let (op, locals) = {
            let top = self.stack.top().unwrap();
            (top.op, top.locals.clone())
        };
        self.stack.push(Frame {
            op,
            expr: child_expr,
            locals,
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
            return self.enter_closure(handle, arg_values);
        }

        // 2. Registered Rust builtin?
        if let Some(builtin) = self.builtins.get(&target).cloned() {
            let result = (builtin)(self, &arg_values)?;
            return self.deliver(result);
        }

        // 3. Anthill-defined operation body.
        let (body_term, params) = lookup_operation_body(&self.kb, target)
            .ok_or_else(|| EvalError::UnknownOperation { name: target_name })?;
        self.enter_operation(target, body_term, &params, arg_values)
    }

    fn enter_operation(
        &mut self,
        target: Symbol,
        body_term: TermId,
        params: &[(Symbol, TermId)],
        arg_values: Vec<Value>,
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
        *top = Frame {
            op: target,
            expr: body_term,
            locals,
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
        let (param_pattern, body) = self.closures.with(&handle, |c| (c.param_pattern, c.body));
        let bindings = match_pattern(self, param_pattern, &arg).ok_or_else(|| {
            EvalError::MatchFailed { scrutinee: arg.type_name().to_string() }
        })?;
        let mut locals: SmallVec<[(Symbol, Value); 4]> = self.closures.clone_env(&handle);
        for (sym, v) in bindings {
            locals.push((sym, v));
        }
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
                    let mut picked: Option<(TermId, super::pattern::Bindings)> = None;
                    for branch_tid in &branches {
                        let (pat_tid, body_tid) = match self.kb.get_term(*branch_tid) {
                            Term::Fn { named_args: br, .. } => {
                                let p = named_arg(br, self.fields.pattern);
                                let b = named_arg(br, self.fields.body);
                                match (p, b) {
                                    (Some(p), Some(b)) => (p, b),
                                    _ => continue,
                                }
                            }
                            _ => continue,
                        };
                        // Cheap pre-filter: constructor-pattern functor
                        // mismatch can skip the full match attempt.
                        if let (Some(pat_name), Some(scr_name)) =
                            (constructor_pattern_name(self, pat_tid), scrutinee_functor)
                        {
                            if pat_name != scr_name { continue; }
                        }
                        if let Some(bindings) = match_pattern(self, pat_tid, &v) {
                            picked = Some((resolve_handle(&self.kb, body_tid), bindings));
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
                    let (op, locals) = (top.op, top.locals.clone());
                    self.stack.push(Frame {
                        op,
                        expr: resolve_handle(&self.kb, next_expr),
                        locals,
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
                    let (current_name, _placeholder_tid) = remaining.remove(0);
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
                    // Leave `remaining[0]` as the "current" entry with the
                    // placeholder term; we only need the name during delivery.
                    remaining[0] = (next_name, TermId::from_raw(u32::MAX));
                    let top = self.stack.top_mut().unwrap();
                    top.awaiting = Some(AwaitState::ConstructorArgs {
                        ctor_sym,
                        is_tuple_literal,
                        buffered_pos,
                        buffered_named,
                        remaining,
                    });
                    let (op, locals) = (top.op, top.locals.clone());
                    self.stack.push(Frame {
                        op,
                        expr: resolve_handle(&self.kb, next_expr),
                        locals,
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

/// Symbol-keyed named-arg lookup — compare pre-interned `Symbol`s rather
/// than walking the key string through `resolve_sym`.
fn named_arg(
    args: &SmallVec<[(Symbol, TermId); 2]>,
    key: Symbol,
) -> Option<TermId> {
    args.iter().find(|(s, _)| *s == key).map(|(_, v)| *v)
}

fn term_as_symbol(kb: &KnowledgeBase, tid: TermId) -> Option<Symbol> {
    match kb.get_term(tid) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

fn decode_apply_arg(
    kb: &KnowledgeBase,
    arg_tid: TermId,
    fields: &super::FieldSymbols,
) -> Result<(Option<Symbol>, TermId), EvalError> {
    let named_args = match kb.get_term(arg_tid) {
        Term::Fn { named_args, .. } => named_args,
        _ => return Err(EvalError::Internal("ApplyArg not a Fn term".into())),
    };
    let value = named_arg(named_args, fields.value)
        .ok_or_else(|| EvalError::Internal("ApplyArg missing 'value'".into()))?;
    let name = named_arg(named_args, fields.name)
        .and_then(|n| unwrap_option(kb, n))
        .and_then(|inner| term_as_symbol(kb, inner));
    Ok((name, value))
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

/// Walk OperationInfo facts for a functor, return (body term, params).
/// Mirrors `kb::typing::check_operation_bodies` but yields the body
/// expression `TermId` directly via `resolve_handle`.
///
/// WI-053 / WI-054 track a cache + shared-helper refactor so per-call
/// lookup becomes O(1) instead of linear in OperationInfo fact count.
pub(crate) fn lookup_operation_body(
    kb: &KnowledgeBase,
    functor: Symbol,
) -> Option<(TermId, Vec<(Symbol, TermId)>)> {
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo")?;
    for rid in kb.by_functor(op_info_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
        let head = kb.rule_head(rid);
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };

        let name_sym = get_named_arg(kb, named_args, "name")
            .and_then(|v| term_as_symbol(kb, v));
        if name_sym != Some(functor) { continue; }

        let body_opt = get_named_arg(kb, named_args, "body")?;
        let body_handle = unwrap_option(kb, body_opt)?;
        let body_term = resolve_handle(kb, body_handle);

        let mut params = Vec::new();
        if let Some(params_tid) = get_named_arg(kb, named_args, "params") {
            for param_tid in &crate::kb::typing::list_to_vec(kb, params_tid) {
                if let Term::Fn { named_args: pargs, .. } = kb.get_term(*param_tid) {
                    let pname = get_named_arg(kb, pargs, "name")
                        .and_then(|v| term_as_symbol(kb, v));
                    let ptype = get_named_arg(kb, pargs, "type_name");
                    if let (Some(n), Some(t)) = (pname, ptype) {
                        params.push((n, t));
                    }
                }
            }
        }

        return Some((body_term, params));
    }
    None
}
