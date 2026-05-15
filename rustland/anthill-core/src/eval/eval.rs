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
use crate::kb::typing::{resolve_handle, unwrap_option};
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
        if Some(functor) == sx.apply_within {
            return self.start_apply_within(named_args);
        }
        if Some(functor) == sx.constructor {
            return self.start_constructor(named_args);
        }
        // WI-223 / WI-237 — requirement-typed value forms. Each yields a
        // `Value::Requirement(handle)`. A body reads its own frame
        // requirements by name via `var_ref` (handled in `reduce_var`),
        // not positionally. See `docs/design/operation-call-model.md`
        // §"Two primitives".
        if Some(functor) == sx.requirement_at_sort {
            return self.reduce_requirement_at_sort(named_args);
        }
        if Some(functor) == sx.construct_requirement {
            return self.reduce_construct_requirement(named_args);
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
        // WI-223: snapshot the enclosing frame's requirements so the
        // closure restores them on invocation (lexical scope at lambda
        // creation, not invocation site). Frame-side SmallVec is sized 2,
        // closure-side is sized 1 (most lambdas hold 0–1 reqs); collect
        // across the size boundary.
        let requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 1]> = self.stack.top()
            .map(|f| f.requirements.iter().cloned().collect())
            .unwrap_or_default();
        let handle = self.closures.alloc(Closure {
            param_pattern: param_tid,
            body: body_term,
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

    fn reduce_requirement_at_sort(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        let chain_tid = named_arg(named_args, self.fields.chain)
            .ok_or_else(|| EvalError::Internal(
                "requirement_at_sort missing 'chain'".into(),
            ))?;
        let slot_tid = named_arg(named_args, self.fields.slot)
            .ok_or_else(|| EvalError::Internal(
                "requirement_at_sort missing 'slot'".into(),
            ))?;
        let slot = extract_static_int(&self.kb, slot_tid, &self.fields)
            .ok_or_else(|| EvalError::Internal(
                "requirement_at_sort 'slot' is not a static Int".into(),
            ))? as usize;
        let parent = self.eval_requirement_chain(resolve_handle(&self.kb, chain_tid))?;
        let projected = parent.project(slot);
        self.deliver(Value::Requirement(projected))
    }

    fn reduce_construct_requirement(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        let impl_tid = named_arg(named_args, self.fields.impl_functor)
            .ok_or_else(|| EvalError::Internal(
                "construct_requirement missing 'impl_functor'".into(),
            ))?;
        let functor_sym = term_as_symbol(&self.kb, impl_tid)
            .ok_or_else(|| EvalError::Internal(
                "construct_requirement 'impl_functor' is not a Symbol".into(),
            ))?;
        let reqs_tid = named_arg(named_args, self.fields.requirements)
            .ok_or_else(|| EvalError::Internal(
                "construct_requirement missing 'requirements'".into(),
            ))?;
        let req_terms = list_terms(&self.kb, reqs_tid, self.fields.head, self.fields.tail);
        let mut handles: SmallVec<[super::value::RequirementHandle; 1]> = SmallVec::new();
        for tid in req_terms {
            let h = self.eval_requirement_chain(resolve_handle(&self.kb, tid))?;
            handles.push(h);
        }
        let new_handle = self.requirements.alloc(functor_sym, handles);
        self.deliver(Value::Requirement(new_handle))
    }

    /// Synchronously reduce a requirement-typed term to a
    /// `RequirementHandle`. Walks the chain per the design grammar:
    /// bottoms out at `requirement_at_current`; intermediate nodes are
    /// `requirement_at_sort` (projection) or `construct_requirement`
    /// (allocation). No AwaitState — the grammar is closed under direct
    /// recursion.
    fn eval_requirement_chain(
        &self,
        tid: TermId,
    ) -> Result<super::value::RequirementHandle, EvalError> {
        let term = self.kb.get_term(tid).clone();
        let sx = &self.reflect;
        let (functor, named_args) = match term {
            Term::Fn { functor, named_args, .. } => (functor, named_args),
            _ => return Err(EvalError::Internal(
                "requirement chain must be a Term::Fn".into(),
            )),
        };

        if Some(functor) == sx.requirement_at_sort {
            let chain_tid = named_arg(&named_args, self.fields.chain)
                .ok_or_else(|| EvalError::Internal(
                    "requirement_at_sort missing 'chain'".into(),
                ))?;
            let slot_tid = named_arg(&named_args, self.fields.slot)
                .ok_or_else(|| EvalError::Internal(
                    "requirement_at_sort missing 'slot'".into(),
                ))?;
            let slot = extract_static_int(&self.kb, slot_tid, &self.fields)
                .ok_or_else(|| EvalError::Internal(
                    "requirement_at_sort 'slot' is not a static Int".into(),
                ))? as usize;
            let parent = self.eval_requirement_chain(resolve_handle(&self.kb, chain_tid))?;
            Ok(parent.project(slot))
        } else if Some(functor) == sx.construct_requirement {
            let impl_tid = named_arg(&named_args, self.fields.impl_functor)
                .ok_or_else(|| EvalError::Internal(
                    "construct_requirement missing 'impl_functor'".into(),
                ))?;
            let functor_sym = term_as_symbol(&self.kb, impl_tid)
                .ok_or_else(|| EvalError::Internal(
                    "construct_requirement 'impl_functor' is not a Symbol".into(),
                ))?;
            let reqs_tid = named_arg(&named_args, self.fields.requirements)
                .ok_or_else(|| EvalError::Internal(
                    "construct_requirement missing 'requirements'".into(),
                ))?;
            let req_terms = list_terms(&self.kb, reqs_tid, self.fields.head, self.fields.tail);
            let mut handles: SmallVec<[super::value::RequirementHandle; 1]> = SmallVec::new();
            for t in req_terms {
                handles.push(self.eval_requirement_chain(resolve_handle(&self.kb, t))?);
            }
            Ok(self.requirements.alloc(functor_sym, handles))
        } else if Some(functor) == sx.var_ref {
            // WI-237 (names model): a body reads a requirement by its
            // synthesized `__req_*` name. Synth names are interned once,
            // so Symbol equality suffices (no short-name aliasing).
            let name_tid = named_arg(&named_args, self.fields.name)
                .ok_or_else(|| EvalError::Internal("var_ref missing 'name'".into()))?;
            let name_sym = term_as_symbol(&self.kb, name_tid).ok_or_else(|| {
                EvalError::Internal("var_ref 'name' is not a Symbol".into())
            })?;
            let top = self.stack.top().ok_or_else(|| {
                EvalError::Internal("requirement chain var_ref on empty stack".into())
            })?;
            find_requirement(&top.requirements, name_sym).cloned().ok_or_else(|| {
                EvalError::Internal(format!(
                    "var_ref({}) unbound in requirement position",
                    self.kb.resolve_sym(name_sym)
                ))
            })
        } else {
            Err(EvalError::Internal(format!(
                "expected requirement-chain term, got functor {}",
                self.kb.resolve_sym(functor)
            )))
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

    /// WI-223 / WI-234 (Model 1): reduce `apply_within(fn, args,
    /// requirements)`. The requirements channel has at most one entry —
    /// the dispatching dictionary; when present, its functor selects
    /// the impl op for a spec-op `fn`, and its sub-tree is expanded
    /// into the callee's `frame.requirements` at frame push.
    fn start_apply_within(
        &mut self,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> Result<StepOutcome, EvalError> {
        let fn_tid = named_arg(named_args, self.fields.fn_)
            .ok_or_else(|| EvalError::Internal("apply_within missing 'fn'".into()))?;
        let fn_sym = term_as_symbol(&self.kb, fn_tid).ok_or_else(|| {
            EvalError::Internal(format!(
                "apply_within 'fn' must be a Symbol; got {:?}",
                self.kb.get_term(fn_tid)
            ))
        })?;

        let reqs_tid = named_arg(named_args, self.fields.requirements)
            .ok_or_else(|| {
                EvalError::Internal("apply_within missing 'requirements'".into())
            })?;
        let req_terms = list_terms(&self.kb, reqs_tid, self.fields.head, self.fields.tail);
        if req_terms.len() > 1 {
            return Err(EvalError::Internal(format!(
                "apply_within requirements channel has {} entries; v0 Model 1 \
                 expects 0 or 1",
                req_terms.len(),
            )));
        }
        let dispatching_dict: Option<super::value::RequirementHandle> =
            if let Some(first) = req_terms.first() {
                Some(self.eval_requirement_chain(resolve_handle(&self.kb, *first))?)
            } else {
                None
            };

        let target = match &dispatching_dict {
            Some(dict) => self.dispatch_via_sort_ops_table(fn_sym, dict),
            None => fn_sym,
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

        let args_tid = named_arg(named_args, self.fields.args)
            .ok_or_else(|| EvalError::Internal("apply_within missing 'args'".into()))?;
        let arg_terms = crate::kb::typing::list_to_vec(&self.kb, args_tid);

        if arg_terms.is_empty() {
            return self.dispatch_call_with_requirements(target, Vec::new(), requirements);
        }

        let mut remaining: Vec<TermId> = Vec::with_capacity(arg_terms.len());
        for arg_tid in arg_terms {
            let (_name, value_inner) = decode_apply_arg(&self.kb, arg_tid, &self.fields)?;
            remaining.push(value_inner);
        }
        let first = remaining.remove(0);
        self.suspend_and_push(
            AwaitState::ApplyWithinArgs {
                target,
                buffered: Vec::new(),
                remaining,
                requirements,
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
        let (op, locals, requirements) = {
            let top = self.stack.top().unwrap();
            (top.op, top.locals.clone(), top.requirements.clone())
        };
        self.stack.push(Frame {
            op,
            expr,
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
        child_expr: TermId,
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
        let (body_term, params) = lookup_operation_body(&self.kb, target)
            .ok_or_else(|| EvalError::UnknownOperation { name: target_name })?;
        self.enter_operation(target, body_term, &params, arg_values, requirements)
    }

    fn enter_operation(
        &mut self,
        target: Symbol,
        body_term: TermId,
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
            expr: body_term,
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
        let (param_pattern, body) = self.closures.with(&handle, |c| (c.param_pattern, c.body));
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
                    let (op, locals, requirements) =
                        (top.op, top.locals.clone(), top.requirements.clone());
                    self.stack.push(Frame {
                        op,
                        expr: resolve_handle(&self.kb, next_expr),
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
                        expr: resolve_handle(&self.kb, next_expr),
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
                    let (op, locals, requirements) =
                        (top.op, top.locals.clone(), top.requirements.clone());
                    self.stack.push(Frame {
                        op,
                        expr: resolve_handle(&self.kb, next_expr),
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

/// Pull a static `i64` out of a slot/index field of a requirement IR
/// node. Accepts either a bare `Term::Const(Int)` (what the rewrite pass
/// emits for compile-time-known indices) or an `int_lit(value: ...)`
/// reflect-entity wrapper (what user code might construct). Returns
/// `None` for any other shape.
fn extract_static_int(
    kb: &KnowledgeBase,
    tid: TermId,
    fields: &super::FieldSymbols,
) -> Option<i64> {
    match kb.get_term(tid) {
        Term::Const(Literal::Int(n)) => Some(*n),
        Term::Fn { named_args, .. } => {
            let value_tid = named_arg(named_args, fields.value)?;
            match kb.get_term(value_tid) {
                Term::Const(Literal::Int(n)) => Some(*n),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Walk a `cons`/`nil` cons-list, returning each element's `head` term.
/// Non-list shapes fall through as an empty vec — diagnostics fire from
/// the requirement-IR reductions if a missing `requirements` slot causes
/// downstream lookup failures.
fn list_terms(
    kb: &KnowledgeBase,
    list_tid: TermId,
    head_field: Symbol,
    tail_field: Symbol,
) -> Vec<TermId> {
    let mut out = Vec::new();
    let mut cur = list_tid;
    loop {
        match kb.get_term(cur) {
            Term::Fn { named_args, .. } => {
                let head = named_arg(named_args, head_field);
                let tail = named_arg(named_args, tail_field);
                match (head, tail) {
                    (Some(h), Some(t)) => {
                        out.push(h);
                        cur = t;
                    }
                    _ => break,
                }
            }
            _ => break,
        }
    }
    out
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

/// Walk OperationInfo facts for a functor, return (body term, params).
/// Thin wrapper over `kb::op_info::lookup_operation_info`. Returns
/// `None` for body-less ops (specs).
pub fn lookup_operation_body(
    kb: &KnowledgeBase,
    functor: Symbol,
) -> Option<(TermId, Vec<(Symbol, TermId)>)> {
    let rec = crate::kb::op_info::lookup_operation_info(kb, functor)?;
    let body = rec.body?;
    Some((body, rec.params))
}
