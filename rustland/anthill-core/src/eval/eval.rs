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
use crate::kb::term::{Literal, Term, TermId};
use crate::kb::KnowledgeBase;

use super::closure::{Closure, ClosureTypeArgs};
use super::error::EvalError;
use super::frame::{AwaitState, ChildFrameContext, Frame, FrameTypeArgs};
use super::pattern::{constructor_pattern_name, match_pattern};
use super::value::Value;
use super::Interpreter;

pub enum StepOutcome {
    /// The stack emptied and the top-level computation produced a value.
    Done(Value),
    /// Advance the driver: `step()` either pushed a child, transitioned a
    /// wait-state, or rewrote the top frame's expr in place.
    Continue,
    /// A value was produced and must be delivered to the parent frame. The
    /// `run()` trampoline picks it up and calls `deliver` on the next
    /// iteration. Returning this — rather than calling `self.deliver(v)`
    /// inline — is what keeps the value-cascade (`dispatch → deliver →
    /// dispatch`) on the heap activation stack instead of the native Rust
    /// stack, so host call depth stays O(1) for any program depth.
    Deliver(Value),
}

// Interpreter profiler, enabled by the `ANTHILL_PROFILE` env var. Exact
// (not sampled — a deterministic reducer can attribute every reduction
// precisely):
//  - OP_PROF:      op Symbol -> (calls, self-reductions). A reduction is
//    attributed to the op whose body the top frame is executing.
//  - BUILTIN_PROF: builtin Symbol -> (calls, wall nanos).
// Counters are dumped (top operations + builtins) and reset by
// `invoke_op_with_requirements` after each top-level call. When the env
// var is unset the only cost is one `var_os` check per `run()` plus a
// branch-predicted `if prof` per step — no measurable overhead.
thread_local! {
    pub(crate) static OP_PROF: std::cell::RefCell<std::collections::HashMap<Symbol, (u64, u64)>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
    pub(crate) static BUILTIN_PROF: std::cell::RefCell<std::collections::HashMap<Symbol, (u64, u128)>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

/// A resolved operation body: its body node plus its params. Params are
/// `Rc<[…]>` (not `Vec`) so a `op_body_cache` hit is a pair of refcount
/// bumps rather than a per-call heap allocation.
pub(crate) type OpBody = (Rc<NodeOccurrence>, Rc<[(Symbol, Value)]>);

impl Interpreter {
    /// Drive the activation stack until it empties. Single loop, no native
    /// recursion. Enforces `EvalConfig::step_cap` per iteration so
    /// TCO'd infinite tail loops surface as `StepsExhausted` rather than
    /// hanging the host.
    pub fn run(&mut self) -> Result<Value, EvalError> {
        let prof = self.profiling;
        // `pending` carries a produced value awaiting delivery to its parent
        // frame. The trampoline alternates between reducing the top frame
        // (`step`) and delivering a value (`deliver`); both return their next
        // action as a `StepOutcome` rather than calling each other natively, so
        // the value-cascade stays on the heap stack. `step_cap` is the single
        // runaway guard: EVERY iteration — a reduction OR a delivery — is one
        // tick, so a no-reduction dispatch/deliver cascade (a self-redispatching
        // spec op) is bounded too, not just `step()`-driven loops.
        let mut pending: Option<Value> = None;
        loop {
            if let Some(cap) = self.config.step_cap {
                if self.step_count >= cap {
                    return Err(EvalError::StepsExhausted {
                        cap,
                        chain: self.recent_dispatch_chain(),
                    });
                }
            }
            self.step_count = self.step_count.saturating_add(1);
            let outcome = match pending.take() {
                Some(v) => self.deliver(v)?,
                None => {
                    // Profiling attributes a reduction to the executing op —
                    // only `step()` iterations are reductions, deliveries aren't.
                    if prof {
                        if let Some(op) = self.stack.top().map(|f| f.op) {
                            OP_PROF.with(|p| p.borrow_mut().entry(op).or_insert((0, 0)).1 += 1);
                        }
                    }
                    self.step()?
                }
            };
            match outcome {
                StepOutcome::Done(v) => return Ok(v),
                StepOutcome::Continue => {}
                StepOutcome::Deliver(v) => pending = Some(v),
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
            NodeKind::Pattern(_) => {
                // Patterns are consumed by `match_pattern` at let/lambda/
                // match dispatch — they should never reach `reduce_node`
                // as a top-level expression target (WI-318).
                return Err(EvalError::Internal(
                    "unexpected Pattern occurrence in expression position".into(),
                ));
            }
            NodeKind::Type(_) | NodeKind::EffectExpr(_) => {
                // WI-342: Type/EffectExpr occurrences are type-level data,
                // never an evaluation target.
                return Err(EvalError::Internal(
                    "unexpected Type/EffectExpr occurrence in expression position".into(),
                ));
            }
        };
        match expr {
            Expr::Const(lit) => {
                let v = self.literal_to_value(lit.clone())?;
                Ok(StepOutcome::Deliver(v))
            }
            // WI-714: a macro-spliced pre-built value evaluates to itself verbatim.
            Expr::Spliced(v) => Ok(StepOutcome::Deliver(v.clone())),
            Expr::Ref(sym) | Expr::Ident(sym) => self.reduce_var(*sym, occ),
            Expr::VarRef { name } => self.reduce_var(*name, occ),
            Expr::If { condition, then_branch, else_branch } => {
                self.start_if(condition, then_branch, else_branch)
            }
            Expr::Let { pattern, value, body, .. } => {
                self.start_let(Rc::clone(pattern), value, body)
            }
            Expr::Match { scrutinee, branches } => {
                self.start_match(scrutinee, branches)
            }
            Expr::Lambda { param, body } => self.reduce_lambda(Rc::clone(param), body.clone()),
            Expr::Proof { body, .. } => {
                // WI-538: an in-body proof is a static (type-level)
                // construct — it discharges an obligation at type-check
                // time and has no runtime effect. Continue evaluating
                // the continuation in place (no new frame).
                let body = body.clone();
                let top = self
                    .stack
                    .top_mut()
                    .ok_or_else(|| EvalError::Internal("proof: empty stack".into()))?;
                top.expr = body;
                Ok(StepOutcome::Continue)
            }
            Expr::Apply { functor, pos_args, named_args, .. } => {
                // WI-707: a SORT-headed application is a parameterized TYPE VALUE,
                // not a call — `Cell[V = Int64]` in `is_modifiable(Cell[V = Int64])`.
                // The eval twin of the typer's sort-application arm, and the
                // application peer of `reduce_var`'s bare-sort arm (WI-206).
                // Unconditional on the functor's kind, as there: the typer has
                // already settled the reading (it admits a sort-headed apply only
                // where a `Type` is expected), and a sort names no operation, so
                // such a node could only ever have died in dispatch as
                // `UnknownOperation`. Sits ahead of the classification match — the
                // typer classifies operation calls, never type applications.
                if self.kb.kind_of(*functor) == Some(crate::intern::SymbolKind::Sort) {
                    return self.start_sort_type(*functor, pos_args, named_args);
                }
                // WI-714 (proposal 052): a RULE-headed application (`queens(board)`,
                // `queryTwoParams(x: 3)`) is an APPLIED rule reference — a
                // `Relation[T]` value whose supplied arguments BIND head parameters
                // (subtracted from the free columns). The applied peer of
                // `reduce_var`'s bare rule arm, and — like the sort arm above —
                // re-derived from `kind_of(functor)` with no `CallClass` mark: the
                // typer has settled the reading (a rule name applied to args), and a
                // rule names no operation, so this could only ever have died in
                // dispatch as `UnknownOperation`.
                if matches!(
                    self.kb.kind_of(*functor),
                    Some(crate::intern::SymbolKind::Goal | crate::intern::SymbolKind::Rule)
                ) {
                    return self.start_relation_apply(*functor, pos_args, named_args);
                }
                // WI-218: the typer may have classified this apply for
                // spec-op rewrite. PinNow redirects the call to the
                // impl op; ConcreteApplyWithin similarly redirects (the
                // requirements channel is empty for the bare-apply
                // form). Read the classification off the NodeOccurrence's
                // RefCell — written by `kb/typing.rs::classify` during
                // type-checking.
                // WI-204 phase B1: DeferToRequirement classifications
                // resolve at runtime — pull the dispatching dict from
                // the caller's frame via the synthesized `__req_<spec>`
                // name, then dispatch the impl op with the dict's
                // sub-instances threaded into the callee's frame.
                let class = match &occ.kind {
                    NodeKind::Expr { classification, .. } => classification.borrow().clone(),
                    _ => None,
                };
                // The typer writes the resolved operation type-arg
                // values (positional, declaration order) into the
                // apply occurrence's `resolved_type_args` RefCell
                // after seeding + unification + unconstrained checks.
                // Eval reads them here so every dispatch path (plain,
                // deferred, same-sort, pin-now) installs the same
                // type-arg channel on the callee's frame (WI-272).
                let type_args = collect_resolved_type_args(occ);
                use crate::kb::typing::CallClass;
                match class.as_deref() {
                    Some(CallClass::DeferToRequirement {
                        spec_op_sym, slot, proj_path, enclosing_sort, ..
                    }) => self.start_apply_deferred(
                        *spec_op_sym, *slot, proj_path, *enclosing_sort,
                        pos_args, named_args, type_args,
                    ),
                    Some(CallClass::ConcreteApplyWithin {
                        fn_target_sym, enclosing_sort, dispatch_dict, ..
                    }) => self.start_apply_same_sort(
                        *fn_target_sym, *enclosing_sort, *dispatch_dict,
                        pos_args, named_args, type_args,
                    ),
                    _ => {
                        let target = classified_apply_target(occ).unwrap_or(*functor);
                        self.start_apply(target, pos_args, named_args, type_args)
                    }
                }
            }
            Expr::ApplyWithin { functor, args, named_args, requirements, .. } => {
                let type_args = collect_resolved_type_args(occ);
                self.start_apply_within(
                    *functor, args, named_args, requirements, type_args,
                )
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
            // `DotApply` is a pre-dispatch form: the `[simp]` dot rules must
            // have rewritten it to `Apply`/field-access before eval (WI-278).
            // Reaching here means it survived unresolved.
            Expr::HoApply { .. }
            | Expr::HoApplyWithin { .. }
            | Expr::ConstructorWithin { .. }
            | Expr::LambdaWithin { .. }
            | Expr::Instantiation { .. }
            | Expr::DotApply { .. }
            | Expr::ListLit(_)
            | Expr::SetLit(_)
            | Expr::TupleLit { .. } => Err(EvalError::Internal(format!(
                "unhandled Expr variant in eval: {:?}",
                std::mem::discriminant(expr),
            ))),
            // A `Global` var carries a name (WI-279: a value-receiver `?x` in a
            // dot form reaches eval as `Expr::Var(Global)` — the only op-body
            // var that isn't already a `Ref`/`VarRef`). Resolve it by name like
            // the other reference forms. `DeBruijn` (unopened param — frame setup
            // substitutes those away) and `Rigid` (a skolemized type-param,
            // type-level only) are never runnable values: a loud error.
            Expr::Var(crate::kb::term::Var::Global(vid)) => self.reduce_var(vid.name(), occ),
            Expr::Var(_) => Err(EvalError::Internal(
                "unexpected unopened / type-level variable in expression body".into(),
            )),
            Expr::Bottom => Err(EvalError::Internal(
                "unexpected Expr::Bottom in expression body".into(),
            )),
        }
    }

    fn reduce_var(&mut self, sym: Symbol, occ: &Rc<NodeOccurrence>) -> Result<StepOutcome, EvalError> {
        let target_name = self.kb.resolve_sym(sym).to_string();
        // Local binding first, then a frame requirement (a body reading
        // a `__req_*` param by name — WI-237 names model), then a
        // frame type-arg (a body reading a declared `T` from
        // `operation foo[T](...)` per WI-272), then dispatch.
        let bound = {
            let top = self.stack.top()
                .ok_or_else(|| EvalError::Internal("reduce_var on empty stack".into()))?;
            find_local(&self.kb, &top.locals, &target_name)
                .cloned()
                .or_else(|| {
                    find_requirement(&top.requirements, sym)
                        .map(|h| Value::Requirement(h.clone()))
                })
                .or_else(|| {
                    find_type_arg(&top.type_args, sym).map(Value::term)
                })
        };
        if let Some(v) = bound {
            return Ok(StepOutcome::Deliver(v));
        }
        // Proposal 039 / WI-084: a bare reference to a term-level constant
        // materializes its memoized value, folding the (pure, carrier-independent)
        // body on FIRST demand and caching it. A const is nullary by construction,
        // so there is no dispatch — just force + deliver. Sits before the
        // entity/constructor/operation arms; a `Const` symbol is none of those, so
        // ordering is moot, but resolving the value here keeps the const path self
        // contained.
        if self.kb.kind_of(sym) == Some(crate::intern::SymbolKind::Const) {
            let v = self.force_const(sym)?;
            return Ok(StepOutcome::Deliver(v));
        }
        // A bare reference to a free-standing entity (e.g. `WorkItem` in
        // `facts_of(kb(), WorkItem)`) is the entity as a type value, not a call.
        if self.kb.is_free_standing_entity(sym) {
            let tid = self.kb.alloc(crate::kb::term::Term::Ref(sym));
            return Ok(StepOutcome::Deliver(Value::term(tid)));
        }
        // WI-206: likewise a bare reference to a SORT (e.g. `Cell` in
        // `is_modifiable(Cell)`) is the sort as a type value — the eval twin of
        // `check_bare_ref`'s `Type`-slot arm. Unconditional here because the typer
        // has already settled the reading: it admits a bare sort name ONLY where a
        // `Type` is expected, so one in any other value position never reaches eval.
        if self.kb.kind_of(sym) == Some(crate::intern::SymbolKind::Sort) {
            let tid = self.kb.alloc(crate::kb::term::Term::Ref(sym));
            return Ok(StepOutcome::Deliver(Value::term(tid)));
        }
        // WI-365: a bare reference to a NULLARY constructor — an enum variant
        // with no fields, e.g. `none` in `Option`'s `case nil() -> none` (and
        // `nil` itself) — is the *constructed value*, not an operation call.
        // Such a name reaches here as an `Expr::Ref` or, when it came through
        // the loader's `var_ref` form, an `Expr::VarRef` — both routed through
        // `reduce_var`, so this is the single reference→value resolution point
        // (the loader keeps the bare name as a reference; whether it denotes a
        // value or a call is settled here, exactly as the free-standing-entity
        // case above is). `is_free_standing_entity` covers only a top-level
        // `entity`; an enum variant like `Option.none` is a *constructor*
        // symbol, so without this it fell through to `dispatch_call` and failed
        // as `UnknownOperation { name: "none" }`. Latent until now: consuming a
        // `List` as a `Stream` is the first eval to reach `List.splitFirst`'s
        // empty case, which returns a bare `none`. The constructor registry is
        // fully populated by eval time (unlike mid-load), so the kind test is
        // reliable here. Constructors WITH fields are never referenced bare in
        // value position (the typer requires the application form), so gate on
        // nullary.
        if self.kb.is_constructor_symbol(sym)
            && self.kb.entity_field_names(sym).map_or(true, |f| f.is_empty())
        {
            return self.start_constructor(sym, &[], &[]);
        }
        // WI-275: a bare reference to an operation of arity ≥ 1 in value position
        // is that operation as a first-class function value (eta), not a call —
        // the runtime counterpart of the typer's `operation_as_function_value`.
        // The `Function`-typed parameter it flows into applies it later via the
        // closure-dispatch path.
        //
        // WI-700: a NULLARY op is AMBIGUOUS — a bare `poke` can mean "call it now"
        // (→ its return value) or "eta" (→ a `() -> ret` thunk), and arity cannot
        // decide. The typer resolves it: it eta-lifts only in a function-typed slot
        // and MARKS that occurrence `CallClass::EtaOpRef`. So mint the `OpRef` when
        // the op has arity ≥ 1 (unambiguously a function value) OR the occurrence
        // carries the eta marker (the nullary case); otherwise fall through to the
        // zero-arg call. `spread_eta_args`/`enter_operation` handle the arity-0
        // apply (`f()`) with no indexing.
        if let Some((_, params)) = self.cached_operation_body(sym) {
            if !params.is_empty() || Self::occ_is_eta_marked(occ) {
                // WI-420: if the typer attached a dispatching dict to this eta
                // occurrence, evaluate it IN THE CURRENT (eta-site) FRAME — so
                // an abstract requirement reads the enclosing `__req_*` and a
                // concrete one builds from its `fact` — and capture it on the
                // OpRef for the apply path to install into the callee frame.
                let dict = self.eta_dispatch_dict(occ)?;
                return Ok(StepOutcome::Deliver(Value::OpRef { op: sym, dict }));
            }
        }
        // WI-714 (proposal 052): a bare reference to a RULE — its head functor
        // (`SymbolKind::Goal`, an unlabeled rule) or a rule label
        // (`SymbolKind::Rule`) — is a first-class `Relation` VALUE, not a call. This
        // is the eval twin of the typer's `check_bare_ref` `Relation[T]` arm
        // (parallel kind detection, like the free-standing-entity / sort arms
        // above). A rule head functor is neither an entity, sort, constructor, nor
        // operation, so it reaches here; without this it fell to `dispatch_call` →
        // `UnknownOperation`.
        if matches!(
            self.kb.kind_of(sym),
            Some(crate::intern::SymbolKind::Goal | crate::intern::SymbolKind::Rule)
        ) {
            return Ok(StepOutcome::Deliver(self.build_relation_value(sym, &[], &[])?));
        }
        self.dispatch_call(sym, Vec::new(), SmallVec::new())
    }

    /// WI-714 (proposal 052) — build the `Relation` VALUE a rule reference denotes.
    /// Resolves `ref_sym` (a rule label or head functor) to the rule's clauses and
    /// opens the (shared) head into a `pattern_query(head(…))` goal atom, packaged as
    /// `Value::Relation { query, columns }`. Consuming it runs the query
    /// (`Relation.splitFirst`) and materializes each answer onto `columns`.
    ///
    /// A head VARIABLE slot NOT bound by a supplied argument opens to a FRESH global —
    /// a free COLUMN, named by the head parameter. The APPLIED citation position
    /// (`supplied_pos` / `supplied_named` non-empty) BINDS some COLUMNS instead: the
    /// supplied value is spliced verbatim into every slot of that column (a filter, not
    /// a column). Binding is over the relation's dedup'd COLUMN names — the SAME
    /// [`rule_head_var_slots`] enumeration + [`resolve_relation_arg_columns`] plan the
    /// typer used — so a nonlinear head column binds as ONE parameter (all its slots
    /// spliced) and the runtime columns match the typed schema exactly.
    ///
    /// All clauses of a multi-clause relation share one head interface, so the
    /// first clause's head fixes the columns; the column TYPE lub across clauses is
    /// a typing concern (C3), not a runtime one.
    fn build_relation_value(
        &mut self,
        ref_sym: Symbol,
        supplied_pos: &[Value],
        supplied_named: &[(Symbol, Value)],
    ) -> Result<Value, EvalError> {
        use crate::kb::term::{Var, VarId};
        use crate::kb::typing::{resolve_relation_arg_columns, rule_head_var_slots, SlotKey};
        let qn = self.kb.qualified_name_of(ref_sym).to_string();
        let rids = self.kb.rule_ids_by_qn(&qn);
        let rid = *rids.first().ok_or_else(|| {
            EvalError::Internal(format!("WI-714: no rule clause for reference `{qn}`"))
        })?;
        let head_tid = match self.kb.rule_head_value(rid) {
            Value::Term { id, .. } => *id,
            other => {
                return Err(EvalError::Internal(format!(
                    "WI-714: rule `{qn}` has a non-term head carrier ({})",
                    other.type_name()
                )))
            }
        };
        let (functor, pos_args, named_args) = match self.kb.get_term(head_tid) {
            Term::Fn { functor, pos_args, named_args } => {
                (*functor, pos_args.clone(), named_args.clone())
            }
            // A nullary head (`Ref(f)`) — a 0-column membership relation.
            Term::Ref(f) | Term::Ident(f) => (*f, SmallVec::new(), SmallVec::new()),
            other => {
                return Err(EvalError::Internal(format!(
                    "WI-714: rule `{qn}` head is not an atom: {other:?}"
                )))
            }
        };

        // The head's free-variable slots (the SAME enumeration the typer's schema
        // used) and the ordered dedup'd column names binding operates on.
        let var_slots = rule_head_var_slots(&self.kb, rid);
        let mut seen: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
        let column_names: Vec<Symbol> =
            var_slots.iter().map(|(_, n, _)| *n).filter(|n| seen.insert(*n)).collect();
        let named_keys: Vec<Symbol> = supplied_named.iter().map(|(k, _)| *k).collect();
        let bound = resolve_relation_arg_columns(&column_names, supplied_pos.len(), &named_keys)
            .map_err(|e| EvalError::Internal(format!("WI-714: {}", e.message(&self.kb))))?;
        // `bound[i]` is the column NAME the i-th supplied argument (positionals first,
        // then named) binds — resolve a column name to its supplied value.
        let bound_value = |name: Symbol| -> Option<Value> {
            bound.iter().position(|n| *n == name).map(|i| {
                if i < supplied_pos.len() {
                    supplied_pos[i].clone()
                } else {
                    supplied_named[i - supplied_pos.len()].1.clone()
                }
            })
        };
        // A head slot's column name if it is a free variable (looked up in the shared
        // enumeration), so var-ness and naming match the typer exactly.
        let slot_name = |slot: SlotKey| -> Option<Symbol> {
            var_slots.iter().find(|(s, _, _)| *s == slot).map(|(_, n, _)| *n)
        };

        let mut pos: Vec<Value> = Vec::with_capacity(pos_args.len());
        let mut named: Vec<(Symbol, Value)> = Vec::with_capacity(named_args.len());
        let mut columns: Vec<(Symbol, VarId)> = Vec::new();
        // Fill one head slot: a bound column splices its supplied value (a filter); a
        // free column opens a fresh global (a materialized column); a ground slot rides
        // verbatim; a compound slot mentioning a variable is rejected loudly (its raw
        // DeBruijn would unify reflexively-only → silent 0 solutions — the typer
        // rejects this at LOAD, this guards a programmatically-built reference).
        let fill = |me: &mut Self,
                    slot: SlotKey,
                    arg: TermId,
                    columns: &mut Vec<(Symbol, VarId)>|
         -> Result<Value, EvalError> {
            match slot_name(slot) {
                Some(name) => match bound_value(name) {
                    Some(v) => Ok(v),
                    None => {
                        let fresh = me.kb.fresh_var(name);
                        columns.push((name, fresh));
                        Ok(Value::term(me.kb.alloc(Term::Var(Var::Global(fresh)))))
                    }
                },
                None => {
                    if me.kb.term_mentions_debruijn(arg) {
                        return Err(EvalError::Internal(
                            "WI-714: a relation reference with a compound head argument \
                             (e.g. `some(?x)`) is not yet supported"
                                .into(),
                        ));
                    }
                    Ok(Value::term(arg))
                }
            }
        };
        for (i, arg) in pos_args.into_iter().enumerate() {
            let v = fill(self, SlotKey::Pos(i), arg, &mut columns)?;
            pos.push(v);
        }
        for (key, arg) in named_args {
            let v = fill(self, SlotKey::Named(key), arg, &mut columns)?;
            named.push((key, v));
        }
        // Dedup columns by NAME (a nonlinear head variable `twin(?n, ?n)` fills two
        // slots but is ONE logical column) so the materialized row matches the typer
        // schema's collapsed column set. The goal atom keeps both slots (distinct
        // fresh vars unified by the rule head), so the resolver still enforces the
        // equality; only the projection targets dedup.
        {
            let mut seen: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
            columns.retain(|(name, _)| seen.insert(*name));
        }

        let goal_atom = Value::Entity { functor, pos: pos.into(), named: named.into() };
        // Wrap as `pattern_query(term: <goal atom>)` — the arbitrary-goal-atom
        // LogicalQuery constructor `execute_logical_query` lowers to one goal.
        let query = self.build_logical_query_value("pattern_query", vec![("term", goal_atom)])?;
        Ok(Value::Relation { query: Rc::new(query), columns: columns.into() })
    }

    /// Build a `LogicalQuery` constructor VALUE (WI-714 / proposal 052). This is the
    /// single query-builder shared by BOTH `build_relation_value` (the `pattern_query`
    /// leaf, above) and the relational-algebra ops (`negation` / `disjunction` /
    /// `conjunction` / `guarded` / … each wrapping operand queries — `Relation.negate`
    /// etc. in `builtins.rs`), so the two cannot drift. `ctor` is the short
    /// constructor name (resolved to `anthill.reflect.LogicalQuery.<ctor>`); `fields`
    /// its named args. Every algebra op COMBINES QUERIES this way — the result stays a
    /// `LogicalQuery`, so a `Relation` stays composable and never collapses to a
    /// materialized stream. Fields are stored in canonical (field-name) order per the
    /// repo convention; the resolver reads them by name (`lower_query_with`) so order
    /// never affects resolution, and reification (`alloc_from_value`) re-canonicalizes.
    pub(crate) fn build_logical_query_value(
        &mut self,
        ctor: &str,
        fields: Vec<(&str, Value)>,
    ) -> Result<Value, EvalError> {
        let functor = self
            .kb
            .try_resolve_symbol(&format!("anthill.reflect.LogicalQuery.{}", ctor))
            .ok_or_else(|| {
                EvalError::Internal(format!("WI-714: LogicalQuery.{} unresolved", ctor))
            })?;
        let mut fields = fields;
        fields.sort_by(|a, b| a.0.cmp(b.0));
        let mut named = Vec::with_capacity(fields.len());
        for (key, value) in fields {
            let key = self.kb.intern(key);
            named.push((key, value));
        }
        Ok(Value::Entity { functor, pos: Vec::new().into(), named: named.into() })
    }

    /// WI-714 (proposal 052) — begin an APPLIED rule reference `ref_sym(args…)`
    /// (`queens(board)`, `queryTwoParams(x: 3)`). Mirrors
    /// [`Interpreter::start_sort_type`]'s one-argument-at-a-time evaluation pump (see
    /// [`AwaitState::RelationArgs`]); when the last argument arrives,
    /// [`Interpreter::build_relation_value`] assembles the `Value::Relation` with the
    /// supplied values bound into the query's goal atom. An argument-less `queens()`
    /// is exactly the bare reference (no bound slots).
    fn start_relation_apply(
        &mut self,
        ref_sym: Symbol,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
    ) -> Result<StepOutcome, EvalError> {
        let mut remaining: Vec<(Option<Symbol>, Rc<NodeOccurrence>)> =
            Vec::with_capacity(pos_args.len() + named_args.len());
        for a in pos_args.iter() {
            remaining.push((None, a.clone()));
        }
        for (n, a) in named_args.iter() {
            remaining.push((Some(*n), a.clone()));
        }

        if remaining.is_empty() {
            return Ok(StepOutcome::Deliver(
                self.build_relation_value(ref_sym, &[], &[])?,
            ));
        }

        let (first_name, first_expr) = remaining.remove(0);
        let placeholder = first_expr.clone();
        let top = self
            .stack
            .top_mut()
            .ok_or_else(|| EvalError::Internal("start_relation_apply with no parent".into()))?;
        top.awaiting = Some(AwaitState::RelationArgs {
            ref_sym,
            buffered_pos: Vec::new(),
            buffered_named: Vec::new(),
            remaining: std::iter::once((first_name, placeholder))
                .chain(remaining.into_iter())
                .collect(),
        });
        let ctx = self.stack.top().unwrap().child_context();
        self.stack.push(child_frame(ctx, first_expr))?;
        Ok(StepOutcome::Continue)
    }

    /// Proposal 039 / WI-084 — produce a term-level constant's value, memoized.
    /// First demand folds the anthill body (or fetches the host value via a
    /// registered reflect builtin) and caches it; every later demand returns the
    /// cache. The `Forcing` sentinel makes a dependency cycle (`const A = B + 1;
    /// const B = A + 1`) a loud `ConstCycle` error rather than an infinite fold.
    fn force_const(&mut self, sym: Symbol) -> Result<Value, EvalError> {
        match self.const_cache.get(&sym) {
            Some(super::ConstCacheEntry::Cached(v)) => return Ok(v.clone()),
            Some(super::ConstCacheEntry::Forcing) => {
                return Err(EvalError::ConstCycle {
                    name: self.kb.qualified_name_of(sym).to_string(),
                });
            }
            None => {}
        }
        // Host-supplied value source: a registered nullary reflect builtin. Takes
        // precedence — a host const is constant by construction, so caching its
        // first fetch is trivially safe.
        if let Some(builtin) = self.builtins.get(&sym).cloned() {
            self.const_cache.insert(sym, super::ConstCacheEntry::Forcing);
            let v = (builtin)(self, &[])?;
            self.const_cache.insert(sym, super::ConstCacheEntry::Cached(v.clone()));
            return Ok(v);
        }
        // Anthill-bodied: fold the stored body lazily, under the shared step_cap.
        // Bodyless with no registered builtin → the value is unavailable in this
        // build (it still type-checked: the declared type is known).
        let body = match self.kb.const_body_node(sym) {
            Some(node) => Rc::clone(node),
            None => {
                return Err(EvalError::ConstValueUnavailable {
                    name: self.kb.qualified_name_of(sym).to_string(),
                });
            }
        };
        self.const_cache.insert(sym, super::ConstCacheEntry::Forcing);
        // On a fold error, drop the Forcing entry so the const isn't poisoned —
        // a later demand re-attempts (and re-reports) rather than masquerading as
        // an in-progress cycle.
        match self.eval_node_isolated(sym, &body) {
            Ok(v) => {
                self.const_cache.insert(sym, super::ConstCacheEntry::Cached(v.clone()));
                Ok(v)
            }
            Err(e) => {
                self.const_cache.remove(&sym);
                Err(e)
            }
        }
    }

    /// Proposal 039 / WI-084 — evaluate a node to a value on a FRESH activation
    /// stack, leaving the in-flight stack untouched. A const reference is reduced
    /// mid-evaluation (the parent's frames are live), so a nested `run()` on the
    /// shared stack would wrongly drain those parents; swapping in a fresh stack
    /// confines `run()` to just this body. The shared `step_count` / `step_cap`
    /// still bound the work, so a non-terminating const body surfaces as
    /// `StepsExhausted`. The depth cap is carried over from the live config.
    fn eval_node_isolated(
        &mut self,
        op: Symbol,
        node: &Rc<NodeOccurrence>,
    ) -> Result<Value, EvalError> {
        let fresh = match self.config.depth_cap {
            Some(cap) => super::frame::ActivationStack::with_cap(cap),
            None => super::frame::ActivationStack::with_cap(usize::MAX),
        };
        let saved = std::mem::replace(&mut self.stack, fresh);
        let pushed = self.stack.push(Frame {
            op,
            expr: Rc::clone(node),
            locals: SmallVec::new(),
            requirements: SmallVec::new(),
            type_args: SmallVec::new(),
            awaiting: None,
        });
        let result = match pushed {
            Ok(()) => self.run(),
            Err(e) => Err(e),
        };
        // Restore the caller's stack whether the fold succeeded or errored.
        self.stack = saved;
        result
    }

    /// WI-700: the eta marker on an occurrence, if any. `Some(dict)` when the typer
    /// classified it `CallClass::EtaOpRef` — the inner `dict` is `None` at a
    /// requires-free / nullary eta site (marker-only, forward the caller's reqs) and
    /// `Some(tid)` for a requires-carrying one. `None` (outer) when unclassified.
    /// Shared by `occ_is_eta_marked` (`.is_some()`) and `eta_dispatch_dict`
    /// (`.flatten()`), so the classification read lives in one place.
    fn eta_marker(occ: &Rc<NodeOccurrence>) -> Option<Option<TermId>> {
        match &occ.kind {
            NodeKind::Expr { classification, .. } => match classification.borrow().as_deref() {
                Some(crate::kb::typing::CallClass::EtaOpRef { dict }) => Some(*dict),
                _ => None,
            },
            _ => None,
        }
    }

    /// WI-700: true iff the typer marked this occurrence as an eta-lift. `reduce_var`
    /// uses it to mint an `OpRef` for a NULLARY op — which arity alone cannot
    /// distinguish from a zero-arg call. An arity-≥1 bare ref does not consult this
    /// (it is unambiguously a function value).
    fn occ_is_eta_marked(occ: &Rc<NodeOccurrence>) -> bool {
        Self::eta_marker(occ).is_some()
    }

    /// WI-420: read the `CallClass::EtaOpRef` dict the typer attached to an eta
    /// occurrence (if any) and evaluate it to a `RequirementHandle` in the
    /// CURRENT frame (so an abstract requirement reads the enclosing `__req_*`).
    /// `None` when the occ carries no such classification — a requires-free or
    /// same-sort eta, for which the apply path forwards the caller's reqs.
    fn eta_dispatch_dict(
        &self,
        occ: &Rc<NodeOccurrence>,
    ) -> Result<Option<super::value::RequirementHandle>, EvalError> {
        // WI-700: `.flatten()` collapses "not eta" and "eta with no dict" — both mean
        // "no dispatch dict, forward the caller's reqs".
        let dict_tid = Self::eta_marker(occ).flatten();
        match dict_tid {
            Some(tid) => {
                let dict_occ = crate::kb::node_occurrence::materialize_from_handle(&self.kb, tid);
                Ok(Some(self.eval_requirement_chain_node(&dict_occ)?))
            }
            None => Ok(None),
        }
    }

    fn reduce_lambda(
        &mut self,
        param: Rc<NodeOccurrence>,
        body: Rc<NodeOccurrence>,
    ) -> Result<StepOutcome, EvalError> {
        // WI-511: `param` is a Pattern-kind Rc<NodeOccurrence>, stored
        // directly on the closure and read by `match_pattern` on the Pattern
        // enum — no `pattern_to_term` bridge.
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
        // Snapshot the enclosing frame's type_args alongside (WI-272)
        // — same lexical-capture rule. Both channels share the
        // "lambda inherits its creation scope" convention from
        // §"Closures" of operation-call-model.md.
        let type_args: ClosureTypeArgs = self.stack.top()
            .map(|f| f.type_args.iter().cloned().collect())
            .unwrap_or_default();
        let handle = self.closures.alloc(Closure {
            param_pattern: param,
            body,
            env,
            requirements,
            type_args,
        });
        Ok(StepOutcome::Deliver(Value::Closure(handle)))
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
        Ok(StepOutcome::Deliver(Value::Requirement(projected)))
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
        Ok(StepOutcome::Deliver(Value::Requirement(new_handle)))
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

    /// Spec-op dispatch via the dispatching dictionary's sort. Reads the
    /// load-time `sort_ops_table[dict.sort][op_short]` (WI-240) — a real
    /// override (`S.<op>`), a retroactive instance-fact binding, or `fn_sym`
    /// itself (a spec rewrite-rule / builtin default, or a Pin-now / Direct
    /// caller's already-concrete `fn_sym` the dict carries no row for). The
    /// resolution lives in [`crate::kb::typing::resolve_op_target`], shared with
    /// the reflect `Dictionary.resolveOp` / `ops` faces so they cannot drift.
    fn dispatch_via_sort_ops_table(
        &self,
        fn_sym: Symbol,
        dispatching_dict: &super::value::RequirementHandle,
    ) -> Symbol {
        crate::kb::typing::resolve_op_target(&self.kb, dispatching_dict.functor(), fn_sym)
    }

    /// WI-350 — value-directed dispatch for a body-less spec op the typer
    /// left un-rewritten. That happens for an *abstract-receiver* call: the
    /// receiver's static type was the spec sort itself (`s : Stream[T]`), so
    /// no concrete impl was pinnable at type-check and the call types through
    /// the spec op's interface. At runtime the receiver is a concrete value
    /// that names its own carrier — resolve the impl from it: the self-
    /// receiver argument's entity functor → its parent sort → that sort's
    /// operation for this spec op's short name (the same `(impl_sort,
    /// op_short)` table the requirement-dict path uses). Mirrors the typer's
    /// `receiver_carrier`: the self-receiver parameter is the one declared
    /// with the spec sort itself. Returns `None` when the op has no self-
    /// receiver parameter, the receiver carries no sort, or that sort
    /// provides no impl — the caller then reports `UnknownOperation`.
    fn resolve_spec_op_target_by_value(
        &self,
        spec_op: Symbol,
        arg_values: &[Value],
    ) -> Option<Symbol> {
        use crate::kb::typing::{instance_fact_op_binding, witness_op_for_carrier};
        let (spec_sort, carrier) = self.spec_call_runtime_carrier(spec_op, arg_values)?;
        let op_qn = self.kb.qualified_name_of(spec_op);
        let op_short = op_qn.rsplit('.').next().unwrap_or(op_qn);
        let op_short_sym = self.kb.lookup_symbol(op_short)?;
        // A carrier that OWNS the op (its own override) wins. `sort_ops_lookup`
        // returns the body-less spec op itself when the carrier merely inherits
        // it (no real impl) — filter that placeholder out so it doesn't mask the
        // instance fact below.
        let own = self
            .kb
            .sort_ops_lookup(carrier, op_short_sym)
            .filter(|&op| op != spec_op);
        // WI-431: a RETROACTIVE INSTANCE FACT binds the op in the provision
        // (`fact Combiner[T = Tag, combine = tagCombine]`) instead of on the
        // carrier — the op-valued binding IS the dictionary entry. Fall back to
        // it so a spec-op call on an instance-fact carrier dispatches to the
        // bound op instead of dying `UnknownOperation`.
        // WI-450: a WITNESS SORT (`sort TagCombiner provides Combiner[T = Tag]`
        // with a member `combine`) provides the spec for `carrier` without binding
        // the op in the provision and without being the carrier itself — the
        // carrier-keyed `instance_fact_op_binding` misses it. Resolve it
        // param-agnostically by the provision's application.
        own.or_else(|| instance_fact_op_binding(&self.kb, carrier, spec_sort, op_short))
            .or_else(|| witness_op_for_carrier(&self.kb, spec_sort, carrier, op_short_sym))
    }

    /// WI-444 — the GENUINE carrier override of a (possibly defaulted) spec op,
    /// resolved from a runtime receiver value. Returns the carrier sort's OWN
    /// member backing `spec_op` (declared IN the carrier), or `None` when the
    /// carrier merely inherits the spec default (`carrier_override_op` rejects
    /// both the spec op itself and a DIFFERENT spec's same-short-name default
    /// the carrier also inherits). Stricter than [`Self::resolve_spec_op_target_by_value`]
    /// — it never dispatches to another spec's default body — so the eval step-3
    /// override path runs the genuine override or the spec's OWN default,
    /// nothing in between.
    fn resolve_carrier_override_by_value(
        &self,
        spec_op: Symbol,
        arg_values: &[Value],
    ) -> Option<Symbol> {
        let (_spec_sort, carrier) = self.spec_call_runtime_carrier(spec_op, arg_values)?;
        let op_qn = self.kb.qualified_name_of(spec_op);
        let op_short = op_qn.rsplit('.').next().unwrap_or(op_qn);
        let op_short_sym = self.kb.lookup_symbol(op_short)?;
        crate::kb::typing::carrier_override_op(&self.kb, carrier, spec_op, op_short_sym)
    }

    /// WI-350/WI-444 — the `(spec_sort, carrier_sort)` a spec-op call names at
    /// runtime: the spec op's parent sort (body-agnostic — WI-444 admits a
    /// DEFAULTED op so its carrier can still override), and the receiver
    /// argument value's own carrier sort. Mirrors the typer's `receiver_carrier`
    /// / `carrier_param_receiver` classification so the static and dynamic paths
    /// never disagree about which argument names the carrier.
    fn spec_call_runtime_carrier(
        &self,
        spec_op: Symbol,
        arg_values: &[Value],
    ) -> Option<(Symbol, Symbol)> {
        use crate::kb::typing::{
            carrier_param_receiver_for_values, self_receiver_param_index, spec_op_parent_sort,
        };
        let spec_sort = spec_op_parent_sort(&self.kb, spec_op)?;
        let rec = crate::kb::op_info::lookup_operation_info(&self.kb, spec_op)?;
        // The carrier sort a runtime argument value names. Entity/Term values
        // derive it from their constructor's parent sort; HANDLE / SCALAR values
        // (a stream cursor, a `Map`, a `Cell`, a closure, a boxed scalar) carry no
        // constructor functor, so they map to a FIXED prelude sort. Since WI-385
        // widened consumer params from concrete handle types to the SPEC (e.g.
        // `LogicalStream` → `Stream`), the typer no longer statically rewrites those
        // calls, so THIS dynamic path must classify the handle's carrier or every
        // spec op consuming one dies `UnknownOperation` — the regression that
        // silently broke `next` on a stream, and `isEmpty`/`find` on a `Map`
        // (WI-435 generalized the WI-009 `Value::Stream` special-case into
        // `runtime_carrier_sort`). Classifying handle receivers also closes the
        // WI-424 "non-receiver slot steals dispatch" gap: a receiver that returned
        // `None` here was skipped, so a later carrier-typed arg won the first-passing
        // `carrier_param_receiver_for_values` loop; now the receiver classifies and
        // wins, matching the typer's `carrier_param_receiver` index.
        let carrier_of =
            |i: usize| -> Option<Symbol> { runtime_carrier_sort(&self.kb, arg_values.get(i)?) };
        // Same self-receiver classification the typer's `receiver_carrier`
        // uses, so the two never disagree about which argument names the
        // carrier. `arg_values` is in callee-parameter order here (the typer
        // reorders named args), so the declaration index reads the receiver.
        // WI-424: a spec may name its carrier through its own type-param
        // (`Iterable.iterator(c: C)`) instead of the spec sort — fall back to
        // the carrier-param receiver, gated on the SAME provision check the
        // typer's classification applies (the value's sort must provide the
        // spec with that param bound to the carrier), so an element-typed
        // param never dispatches (`iterator` on a `List` value → `List.iterator`).
        let carrier = match self_receiver_param_index(&self.kb, &rec.params, spec_sort) {
            Some(idx) => carrier_of(idx)?,
            None => {
                carrier_param_receiver_for_values(&self.kb, &rec.params, spec_sort, &carrier_of)?.1
            }
        };
        Some((spec_sort, carrier))
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
        pattern: Rc<NodeOccurrence>,
        value: &Rc<NodeOccurrence>,
        body: &Rc<NodeOccurrence>,
    ) -> Result<StepOutcome, EvalError> {
        // WI-511: pattern is a Pattern-kind occurrence, stored directly on the
        // LetBind AwaitState and read by `match_pattern` — no bridge.
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
                pattern: Rc::clone(&b.pattern),
                guard: b.guard.clone(),
                body: b.body.clone(),
                span: b.span,
            })
            .collect();
        self.suspend_and_push(
            AwaitState::MatchDispatch {
                branches: branches_cloned,
                scrutinee_occ: scrutinee.clone(),
            },
            scrutinee.clone(),
        )
    }

    fn start_apply(
        &mut self,
        functor: Symbol,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
        type_args: FrameTypeArgs,
    ) -> Result<StepOutcome, EvalError> {
        // WI-218: if this apply's functor has a typer-recorded dispatch
        // rewrite via the legacy term-keyed map, redirect to the impl op.
        // The rewrite map is populated by `kb/typing.rs::record_apply_*`
        // during requirement-insertion; while the post-WI-247 substrate
        // keeps the same map, the eval looks up by the apply's functor
        // for now via `dispatch_call`'s callee resolution path.
        let target = functor;

        if pos_args.is_empty() && named_args.is_empty() {
            return self.dispatch_call(target, Vec::new(), type_args);
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
                type_args,
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
        type_args: FrameTypeArgs,
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
        // name-keyed frame requirements (`__req_self` → the dict,
        // `__req_<spec>` → each positional sub-instance). Same name
        // synthesis as the typer's IR emitter, so the callee body's
        // `var_ref(__req_*)` reads resolve against this frame.
        let requirements = match dispatching_dict {
            Some(dict) => self.expand_dispatching_dict(target, &dict)?,
            None => SmallVec::new(),
        };
        self.dispatch_apply_with_requirements(
            target, requirements, type_args, args, named_args,
        )
    }

    /// Dispatch a `CallClass::ConcreteApplyWithin` into a sort with
    /// non-empty `requires`, supplying the callee's frame requirements one
    /// of three ways:
    ///
    /// 1. **Same-sort inherit** — when the callee's parent sort matches the
    ///    caller's enclosing sort, the callee inherits the caller's
    ///    `frame.requirements` as-is (same chain shape, same names). The
    ///    common case for multi-op bundles like anthill-todo's `Main`.
    /// 2. **WI-415 compile-built dict** — a cross-sort / no-enclosing-sort
    ///    call (`member(2, [1,2,3])` from a plain namespace) cannot inherit;
    ///    when the typer pinned the callee parent's type params concretely it
    ///    built the parent-bundle dispatching dict at compile stage. Install
    ///    it via the SAME path an explicit `apply_within` dict takes
    ///    (materialize → reduce to a handle → expand into named `__req_*`
    ///    slots). No requirement is resolved here — the dict is pre-built.
    /// 3. **Plain apply** — no dict (an abstract call with no covering
    ///    requirement); fall through with no requirements channel.
    fn start_apply_same_sort(
        &mut self,
        target: Symbol,
        enclosing_sort: Option<Symbol>,
        dispatch_dict: Option<TermId>,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
        type_args: FrameTypeArgs,
    ) -> Result<StepOutcome, EvalError> {
        let callee_parent = crate::kb::typing::impl_parent_of_op(&self.kb, target);
        let inherit = matches!(
            (callee_parent, enclosing_sort),
            (Some(c), Some(e)) if c == e,
        );
        if inherit {
            let caller_reqs = self.stack.top()
                .ok_or_else(|| EvalError::Internal(
                    "start_apply_same_sort with no current frame".into()))?
                .requirements.clone();
            return self.dispatch_apply_with_requirements(
                target, caller_reqs, type_args, pos_args, named_args,
            );
        }
        // WI-415: cross-sort / no-enclosing-sort call — install the
        // compile-stage-built dispatching dict (if any) through the existing
        // apply_within machinery.
        if let Some(dict_tid) = dispatch_dict {
            let dict_occ =
                crate::kb::node_occurrence::materialize_from_handle(&self.kb, dict_tid);
            return self.start_apply_within(
                target, pos_args, named_args, std::slice::from_ref(&dict_occ), type_args,
            );
        }
        self.start_apply(target, pos_args, named_args, type_args)
    }

    /// Runtime path for `CallClass::DeferToRequirement`: resolve the
    /// dispatching dict from the caller frame's `__req_<spec>` slot,
    /// optionally descend a `proj_path` into its bundled sub-requirements
    /// (WI-239 nested case), then dispatch the impl op with the dict's
    /// sub-instances expanded into the callee's frame requirements.
    /// Equivalent to evaluating `apply_within(fn = spec_op_sym, args = …,
    /// requirements = [requirement_at_sort(…var_ref(__req_<spec>)…)])`
    /// directly against the original `Apply` NodeOccurrence (no IR
    /// rewrite). `proj_path` is empty for a direct require (read the slot
    /// as-is), non-empty when the spec is nested inside a direct
    /// requirement's tree-shaped value.
    fn start_apply_deferred(
        &mut self,
        spec_op_sym: Symbol,
        slot: usize,
        proj_path: &[usize],
        enclosing_sort: Option<Symbol>,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
        type_args: FrameTypeArgs,
    ) -> Result<StepOutcome, EvalError> {
        let encl = enclosing_sort.ok_or_else(|| EvalError::Internal(
            "DeferToRequirement classification missing enclosing_sort".into()))?;
        let caller_names = crate::kb::typing::synth_req_names(&mut self.kb, encl);
        let name_sym = *caller_names.get(slot).ok_or_else(|| EvalError::Internal(format!(
            "DeferToRequirement slot {slot} out of range for {} (chain len {})",
            self.kb.resolve_sym(encl), caller_names.len())))?;
        let mut dispatching_dict = {
            let top = self.stack.top().ok_or_else(|| EvalError::Internal(
                "start_apply_deferred without a current frame".into()))?;
            find_requirement(&top.requirements, name_sym)
                .ok_or_else(|| EvalError::Internal(format!(
                    "DeferToRequirement: requirement param `{}` not bound in caller frame",
                    self.kb.resolve_sym(name_sym))))?
                .clone()
        };
        // WI-239: descend into the direct requirement's bundled value for
        // a nested spec (`requirement_at_sort` semantics). A bounds check
        // before each projection keeps a producer/consumer mismatch a
        // clean `EvalError` rather than the arena's `project` panic.
        for &k in proj_path {
            let arity = dispatching_dict.arity();
            if k >= arity {
                return Err(EvalError::Internal(format!(
                    "DeferToRequirement: projection index {k} out of range \
                     (requirement `{}` bundles {arity} sub-requirement(s))",
                    self.kb.resolve_sym(name_sym),
                )));
            }
            dispatching_dict = dispatching_dict.project(k);
        }
        let target = self.dispatch_via_sort_ops_table(spec_op_sym, &dispatching_dict);
        let requirements = self.expand_dispatching_dict(target, &dispatching_dict)?;
        self.dispatch_apply_with_requirements(
            target, requirements, type_args, pos_args, named_args,
        )
    }

    /// Build the callee's `frame.requirements` from a resolved dispatching
    /// dict: `__req_self` plus one entry per sub-instance, keyed by the
    /// impl parent sort's synthesized `__req_<spec>` chain names.
    /// Mirrors `start_apply_within`'s names-model expansion.
    fn expand_dispatching_dict(
        &mut self,
        target: Symbol,
        dict: &super::value::RequirementHandle,
    ) -> Result<SmallVec<[(Symbol, super::value::RequirementHandle); 2]>, EvalError> {
        let names = match crate::kb::typing::impl_parent_of_op(&self.kb, target) {
            Some(p) => Some(crate::kb::typing::synth_req_names(&mut self.kb, p)),
            None => None,
        };
        let arity = dict.arity();
        let name_count = names.as_ref().map_or(0, |n| n.len());
        if arity != name_count {
            return Err(EvalError::Internal(format!(
                "deferred dispatch frame-push: dispatching dict for {} has \
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
        Ok(reqs)
    }

    /// Suspend the current frame with `ApplyWithinArgs` (or dispatch
    /// immediately when there are no args) given a pre-built requirements
    /// channel. Shared tail of every code path that needs the
    /// requirements-passing variant of `start_apply`.
    fn dispatch_apply_with_requirements(
        &mut self,
        target: Symbol,
        requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 2]>,
        type_args: FrameTypeArgs,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
    ) -> Result<StepOutcome, EvalError> {
        let total_args = pos_args.len() + named_args.len();
        if total_args == 0 {
            return self.dispatch_call_with_requirements(
                target, Vec::new(), requirements, type_args,
            );
        }
        let mut remaining: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(total_args);
        for a in pos_args.iter() { remaining.push(a.clone()); }
        for (_, a) in named_args.iter() { remaining.push(a.clone()); }
        let first = remaining.remove(0);
        self.suspend_and_push(
            AwaitState::ApplyWithinArgs {
                target,
                buffered: Vec::new(),
                remaining,
                requirements,
                type_args,
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
            buffered_pos: Vec::new().into(),
            buffered_named: Vec::new().into(),
            // Prepend the currently-in-flight name so the delivery logic
            // knows which slot to place the next value into.
            remaining: std::iter::once((first_name, placeholder))
                .chain(remaining.into_iter())
                .collect(),
        });
        let ctx = self.stack.top().unwrap().child_context();
        self.stack.push(child_frame(ctx, first_expr))?;
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
        let ctx = self.stack.top().unwrap().child_context();
        self.stack.push(child_frame(ctx, child_expr))?;
        Ok(StepOutcome::Continue)
    }

    // ── Dispatch and delivery ──────────────────────────────────

    fn dispatch_call(
        &mut self,
        target: Symbol,
        arg_values: Vec<Value>,
        type_args: FrameTypeArgs,
    ) -> Result<StepOutcome, EvalError> {
        self.dispatch_call_with_requirements(
            target, arg_values, SmallVec::new(), type_args,
        )
    }

    /// Records each dispatch into the recent-dispatch ring (for the
    /// `StepsExhausted` diagnostic) before delegating to the inner dispatch.
    /// The runaway guard itself is `step_cap`, enforced by the `run()`
    /// trampoline — the dispatch value-cascade is iterative, so a
    /// self-redispatching op ticks `step_cap` like any other loop; this
    /// wrapper only feeds the ring that names the looping ops on exhaustion.
    fn dispatch_call_with_requirements(
        &mut self,
        target: Symbol,
        arg_values: Vec<Value>,
        requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 2]>,
        type_args: FrameTypeArgs,
    ) -> Result<StepOutcome, EvalError> {
        self.note_dispatch(target);
        self.dispatch_call_with_requirements_inner(
            target, arg_values, requirements, type_args,
        )
    }

    /// Push `target` onto the bounded recent-dispatch ring (newest at the
    /// back). Skipped entirely when no `step_cap` is set — the ring's only
    /// reader is `StepsExhausted`, which cannot fire without a cap, so the
    /// per-dispatch bookkeeping would be pure waste on the uncapped hot path.
    fn note_dispatch(&mut self, target: Symbol) {
        if self.config.step_cap.is_none() {
            return;
        }
        const RING: usize = 32;
        if self.recent_dispatches.len() == RING {
            self.recent_dispatches.pop_front();
        }
        self.recent_dispatches.push_back(target);
    }

    /// The recent-dispatch ring as qualified operation names, oldest-first —
    /// surfaced in `StepsExhausted` so the looping source is easy to locate
    /// (a loop repeats its operations, so they fill the ring).
    fn recent_dispatch_chain(&self) -> Vec<String> {
        self.recent_dispatches
            .iter()
            .map(|s| self.kb.qualified_name_of(*s).to_string())
            .collect()
    }

    /// Dispatch a call whose `target` is a source-level NAME — so a local holding
    /// a callable (a lambda; a WI-275 eta'd operation reference) may shadow the
    /// operation of that name, and wins. That shadowing is the whole point here,
    /// and it is why this entry is distinct from `dispatch_resolved_operation`:
    /// a *name* is subject to scope, an already-resolved operation Symbol is not
    /// (WI-455).
    fn dispatch_call_with_requirements_inner(
        &mut self,
        target: Symbol,
        arg_values: Vec<Value>,
        requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 2]>,
        type_args: FrameTypeArgs,
    ) -> Result<StepOutcome, EvalError> {
        // 1. Local binding to target — a closure, or (WI-275) an eta'd
        //    operation reference. Clone out the callable value (a handle/Symbol
        //    copy) so the `self.stack` borrow is released before dispatch.
        let target_name = self.kb.resolve_sym(target).to_string();
        let local_callable = {
            let top = self.stack.top()
                .ok_or_else(|| EvalError::Internal("dispatch_call with no parent".into()))?;
            find_local(&self.kb, &top.locals, &target_name)
                .and_then(|v| match v {
                    Value::Closure(_) | Value::OpRef { .. } => Some(v.clone()),
                    _ => None,
                })
        };
        match local_callable {
            Some(Value::Closure(handle)) => {
                // Closures override apply.requirements with their own
                // (the HO-call exception). The caller's `requirements`
                // here are discarded — see closure invocation in the design.
                // Type-args from the apply site are likewise dropped:
                // closure invocation restores the lambda's captured
                // type_args, not the caller's. See
                // `docs/design/operation-call-model.md` §"Closures".
                drop(requirements);
                drop(type_args);
                return self.enter_closure(handle, arg_values);
            }
            Some(Value::OpRef { op, dict }) => {
                // WI-275: applying an eta'd operation reference dispatches to the
                // operation itself, spreading a single tuple argument across its
                // parameters (`cmp((x, y))` ⇒ `op(x, y)`) — the runtime mirror of
                // the typer's `Function[(A, B), R]` ⇒ `op(a, b)` eta convention.
                let spread = self.spread_eta_args(op, arg_values)?;
                // WI-420: a `requires`-carrying op captured its dispatching dict
                // at mint (evaluated in the eta-site frame). Install THAT into
                // the callee frame — not the caller's (empty / wrong-scope)
                // requirements. A dict-less OpRef (requires-free, or a same-sort
                // eta that inherits) forwards the caller's requirements.
                let requirements = match dict {
                    Some(d) => {
                        drop(requirements);
                        self.expand_dispatching_dict(op, &d)?
                    }
                    None => requirements,
                };
                // WI-455: an `OpRef` DENOTES the operation `op`. It is an already-
                // resolved reference, not a name to be looked up again — so go
                // straight to resolved dispatch, bypassing the shadowing lookup
                // above. Re-entering that lookup would re-resolve `op`'s SHORT NAME
                // against the caller's locals (this frame is still on top — an
                // OpRef hop pushes nothing), letting a caller-local that merely
                // SHARES `op`'s name hijack the call: `apply_it(f, double)` called
                // as `apply_it(double, triple)` ran `triple`, a silent wrong answer.
                // Two such locals pointing at each other made it worse — an
                // unbounded redispatch chain that grew on the host Rust stack,
                // where no `step_cap` could see it, until the process aborted.
                // Resolving here settles both: one hop, and no chain to grow.
                //
                // Note `op` explicitly: going straight to resolved dispatch skips
                // the `dispatch_call_with_requirements` wrapper, and with it the
                // ring that names the ops in `StepsExhausted`. Without this, an op
                // reached through an OpRef (i.e. every HOF call) would be invisible
                // to the one diagnostic that locates a runaway loop. The `_inner`
                // tail needs no such call — the wrapper already noted its target.
                self.note_dispatch(op);
                return self.dispatch_resolved_operation(op, spread, requirements, type_args);
            }
            _ => {}
        }

        self.dispatch_resolved_operation(target, arg_values, requirements, type_args)
    }

    /// Dispatch to an operation Symbol that is already RESOLVED — one no local
    /// may shadow. Two callers: the tail of `dispatch_call_with_requirements_inner`
    /// (a source-level name that no local shadowed) and its `OpRef` arm (a
    /// first-class reference that denotes its operation outright).
    ///
    /// INVARIANT (WI-455): this must never re-enter `dispatch_call*`. Every arm
    /// either delivers a value (builtin, eq-bridge) or enters a frame
    /// (`enter_operation`), so one dispatch costs O(1) host stack and cannot chain.
    /// Keep it so. A redispatch added here would grow the NATIVE stack — the one
    /// place `step_cap` cannot see, because ticking it requires returning to
    /// `run()` — and a cycle would abort the process rather than raise.
    fn dispatch_resolved_operation(
        &mut self,
        target: Symbol,
        arg_values: Vec<Value>,
        requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 2]>,
        type_args: FrameTypeArgs,
    ) -> Result<StepOutcome, EvalError> {
        // 2. Registered Rust builtin?
        if let Some(builtin) = self.builtins.get(&target).cloned() {
            let result = if self.profiling {
                let t0 = std::time::Instant::now();
                let r = (builtin)(self, &arg_values)?;
                let dt = t0.elapsed().as_nanos();
                BUILTIN_PROF.with(|p| {
                    let mut m = p.borrow_mut();
                    let e = m.entry(target).or_insert((0, 0));
                    e.0 += 1;
                    e.1 += dt;
                });
                r
            } else {
                (builtin)(self, &arg_values)?
            };
            return Ok(StepOutcome::Deliver(result));
        }

        // 3. Anthill-defined operation body.
        if let Some((body_node, params)) = self.cached_operation_body(target) {
            // WI-444: a DEFAULTED spec op must not SHADOW a carrier's own member
            // (typeclass default-method semantics — defaults fill GAPS, they do
            // not shadow). When `target` is a spec op and the receiver value's
            // runtime sort declares its OWN impl of it, dispatch to that override
            // instead of running the spec's default body. This is the dynamic
            // dual of the typer's static PinNow: it fires for an abstract-receiver
            // call the typer could not pin (the concrete-carrier call is already
            // rewritten to the impl op, whose `target` is not a spec op so this
            // resolves `None`). The STRICT resolver returns only a GENUINE carrier
            // override (a member declared in the carrier sort itself), never
            // another spec's same-short-name default — so a carrier that merely
            // inherits the default runs it, unchanged; a normal (non-spec) op
            // resolves `None` and runs its body directly.
            if let Some(impl_target) = self.resolve_carrier_override_by_value(target, &arg_values) {
                if impl_target != target {
                    // WI-455: name the op we actually RUN. The ring was fed with
                    // `target` (the spec op) by the dispatch wrapper; the override
                    // below is a different op, so without this a runaway loop
                    // through a carrier override would name only the spec op and
                    // never the impl doing the looping. Noted at each dispatch
                    // point rather than up front: an `impl_target` with neither a
                    // builtin nor a body falls through to the spec's own body, and
                    // must not leave a ring entry for a call that never happened.
                    if let Some(builtin) = self.builtins.get(&impl_target).cloned() {
                        self.note_dispatch(impl_target);
                        let result = (builtin)(self, &arg_values)?;
                        return Ok(StepOutcome::Deliver(result));
                    }
                    if let Some((impl_body, impl_params)) = self.cached_operation_body(impl_target) {
                        self.note_dispatch(impl_target);
                        return self.enter_operation(
                            impl_target, impl_body, &impl_params, arg_values, requirements, type_args,
                        );
                    }
                }
            }
            return self.enter_operation(
                target, body_node, &params, arg_values, requirements, type_args,
            );
        }

        // 3b. WI-350 — a body-less spec op left un-rewritten by the typer
        // (abstract-receiver call). Resolve the impl from the receiver
        // value's own runtime sort and dispatch to it. Purely additive: it
        // only fires where step 3 found no body, turning what would be an
        // `UnknownOperation` on a spec op into a concrete impl call.
        //
        // The resolved impl is entered with the spec call's own
        // `requirements`/`type_args` channel (empty for the plain abstract
        // call that reaches here via `start_apply`). This covers leaf impls
        // whose bodies are self-contained; an impl whose parent sort itself
        // declares a `requires` chain would need that chain threaded (the
        // rewrite path's `construct_requirement` machinery) — surfaced as a
        // requirement-read error rather than silently mis-dispatched.
        //
        // Resolves an impl the *operation interpreter* can run: a carrier-
        // defined body, or a builtin-backed declaration (e.g. the body-less
        // `LogicalStream.splitFirst`, registered as a builtin). A spec op whose
        // only definition is equational rules (`Stream.head`, given by `rule
        // head(?s) = … :- splitFirst(?s) = …`) is evaluated by the SLD resolver,
        // not here — the interpreter has no equational-rewrite fallback. Such an
        // op has no own `sort_ops` entry, so the inherited entry points back at
        // the body-less spec op (`impl_target == target`); the guard below skips
        // it and it falls through to `UnknownOperation`, exactly as before this
        // change.
        if let Some(impl_target) = self.resolve_spec_op_target_by_value(target, &arg_values) {
            if impl_target != target {
                // WI-455: same as the carrier-override arm above — the ring must
                // name the impl that runs, not just the body-less spec op the call
                // was written against.
                if let Some(builtin) = self.builtins.get(&impl_target).cloned() {
                    self.note_dispatch(impl_target);
                    let result = (builtin)(self, &arg_values)?;
                    return Ok(StepOutcome::Deliver(result));
                }
                if let Some((body_node, params)) = self.cached_operation_body(impl_target) {
                    self.note_dispatch(impl_target);
                    return self.enter_operation(
                        impl_target, body_node, &params, arg_values, requirements, type_args,
                    );
                }
            }
        }

        // WI-625 (the eval→SLD bridge): a body-less carrier `eq` op invoked
        // directly (a typer PinNow-pinned `Set.eq`/`Map.eq`, WI-210/WI-350 gap 6;
        // or a dictionary-resolved `Set.eq`, gap 4) has no host body for the
        // interpreter to run — but the SLD resolver CAN prove it. Prove the goal
        // in a closed bounded sub-resolution and deliver the Bool verdict, the
        // exact evaluator the resolver's semantic `eq` dispatches through, so
        // eval and SLD agree.
        if let Some(pred) = self.eq_bridge_target(target, &arg_values) {
            return self.prove_rule_predicate_value(pred, &arg_values).map(StepOutcome::Deliver);
        }

        Err(EvalError::UnknownOperation {
            name: self.kb.resolve_sym(target).to_string(),
        })
    }

    /// WI-275: adapt the arguments of an eta'd operation reference (a
    /// `Value::OpRef`) applied as a function value to the operation's own
    /// parameter arity. An arity-matched call passes through unchanged
    /// (`inc(n)`); a single tuple argument — the `Function[(A, B), R]` ⇒
    /// `op(a, b)` convention, e.g. `cmp((x, y))` — is spread across a
    /// multi-parameter operation. Anything else is a genuine arity error.
    fn spread_eta_args(
        &mut self,
        op: Symbol,
        arg_values: Vec<Value>,
    ) -> Result<Vec<Value>, EvalError> {
        // Eta-expansion (`reduce_var`) mints an `OpRef` for a body-having op, so
        // its arity comes from the body. WI-577's reflect `Dictionary.resolveOp`
        // / `ops` additionally mint an OpRef for a native-builtin-backed op (no
        // anthill body, e.g. `PartialEq.eq`), which must stay callable — so fall back to
        // the arity declared in the op's SIGNATURE (`OperationInfo.params`) when
        // there is no body. The apply path's builtin-dispatch step (step 2) then
        // runs the builtin. `UnknownOperation` only when the op has no signature
        // at all — genuinely unknown, surfaced loudly rather than mis-applied.
        let arity = match self.cached_operation_body(op) {
            Some((_, params)) => params.len(),
            None => match crate::kb::op_info::lookup_operation_info(&self.kb, op) {
                Some(info) => info.params.len(),
                None => return Err(EvalError::UnknownOperation {
                    name: self.kb.resolve_sym(op).to_string(),
                }),
            },
        };
        if arg_values.len() == arity {
            return Ok(arg_values);
        }
        if arity != 1 && arg_values.len() == 1 {
            if let Value::Tuple { pos, .. } = &arg_values[0] {
                if pos.len() == arity {
                    return Ok(pos.iter().cloned().collect());
                }
            }
        }
        Err(EvalError::ArityMismatch {
            op: "function-value application",
            expected: arity,
            got: arg_values.len(),
        })
    }

    /// Operation-body lookup, memoized. `lookup_operation_body` linear-scans
    /// every `OperationInfo` fact, so calling it per dispatch makes every
    /// operation call O(num_operations) — the dominant cost in interpreted
    /// programs that make many calls. `OperationInfo` facts are static across
    /// a run (only data facts get persisted/retracted), so caching by op
    /// `Symbol` is sound. See `Interpreter::op_body_cache`.
    pub(crate) fn cached_operation_body(&mut self, target: Symbol) -> Option<OpBody> {
        if let Some(cached) = self.op_body_cache.get(&target) {
            return Some(cached.clone());
        }
        let (node, params) = lookup_operation_body(&self.kb, target)?;
        let entry: OpBody = (node, params.into());
        self.op_body_cache.insert(target, entry.clone());
        Some(entry)
    }

    /// WI-625 — is `op` a body-less operation, backed by relational rule clauses,
    /// declared to return `Bool` (i.e. a PREDICATE the SLD resolver can prove)?
    /// The eval→SLD bridge (`dispatch_call_with_requirements_inner`) runs such an
    /// op via [`KnowledgeBase::prove_rule_predicate`]. Excludes host-bodied ops
    /// (the interpreter runs those) and functional rule-backed ops (a non-`Bool`
    /// equational law such as `Stream.head`), which carry no predicate goal to
    /// prove and stay a loud `UnknownOperation`.
    /// WI-625 — the eval→SLD bridge's Site-B gate: if `target` is a body-less
    /// carrier `eq` op invoked DIRECTLY over two GROUND operands that dispatch
    /// their semantic equality to `target`, return the eq-dispatch INDEX symbol
    /// (`dispatched`) as the resolvable predicate. This is the `Set.eq`/`Map.eq`
    /// shape a typer PinNow leaves when it pins a concrete-receiver `eq(...)`
    /// (WI-210/WI-350, gap 6), and the op a dictionary `resolveOp` yields for an
    /// `Eq[Set]` witness (gap 4). The interpreter has no equational-rewrite
    /// engine; the resolver evaluates the rule clauses.
    ///
    /// Returns the INDEX symbol, not the caller's `target`: the resolver keys its
    /// rule clauses off the index value (as `semantic_equal` does), and a caller
    /// may hold a non-canonical interning of the op whose goal would match no
    /// clause. Ground-gated because `=` is a test that must not bind (a sub-proof
    /// over a non-ground operand could enumerate bindings — the resolver Delays
    /// there). A body-less op that is NOT these operands' carrier eq, or a
    /// non-ground pair, is not bridged — a loud `UnknownOperation` /
    /// `OperationBodyMissing`.
    pub(crate) fn eq_bridge_target(&self, target: Symbol, args: &[Value]) -> Option<Symbol> {
        if args.len() != 2 || self.kb.op_body_node(target).is_some() {
            return None;
        }
        let dispatched = self
            .kb
            .sem_eq_dispatch_target(&args[0])
            .or_else(|| self.kb.sem_eq_dispatch_target(&args[1]))?;
        if self.kb.canonical_sym(dispatched) != self.kb.canonical_sym(target) {
            return None;
        }
        let empty = crate::kb::subst::Substitution::new();
        if !self.kb.value_deep_ground(&args[0], &empty) || !self.kb.value_deep_ground(&args[1], &empty) {
            return None;
        }
        Some(dispatched)
    }

    /// WI-625 — prove a rule-backed Bool predicate `pred(args)` via the eval→SLD
    /// bridge ([`KnowledgeBase::prove_rule_predicate`]) and deliver its Bool
    /// verdict. Callers gate on [`Self::eq_bridge_target`] first. An UNDECIDED
    /// proof (truncation / flounder — not reachable for the ground operands eval
    /// always has) surfaces loudly rather than guessing.
    pub(crate) fn prove_rule_predicate_value(
        &mut self,
        pred: Symbol,
        args: &[Value],
    ) -> Result<Value, EvalError> {
        match self.kb.prove_rule_predicate(pred, args.to_vec()) {
            crate::kb::resolve::PredicateProof::Proved => Ok(Value::Bool(true)),
            crate::kb::resolve::PredicateProof::Refuted => Ok(Value::Bool(false)),
            crate::kb::resolve::PredicateProof::Undecided { .. } => Err(EvalError::Internal(format!(
                "rule-backed predicate `{}` could not be decided at eval \
                 (proof truncated or floundered)",
                self.kb.resolve_sym(pred)
            ))),
        }
    }

    fn enter_operation(
        &mut self,
        target: Symbol,
        body_node: Rc<NodeOccurrence>,
        params: &[(Symbol, Value)],
        arg_values: Vec<Value>,
        requirements: SmallVec<[(Symbol, super::value::RequirementHandle); 2]>,
        type_args: FrameTypeArgs,
    ) -> Result<StepOutcome, EvalError> {
        if arg_values.len() != params.len() {
            return Err(EvalError::ArityMismatch {
                op: "operation call",
                expected: params.len(),
                got: arg_values.len(),
            });
        }
        if self.profiling {
            OP_PROF.with(|p| p.borrow_mut().entry(target).or_insert((0, 0)).0 += 1);
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
        // type_args sequence after the sort-level requirements per
        // `operation-call-model.md` §"Operation type arguments"
        // (WI-272).
        *top = Frame {
            op: target,
            expr: body_node,
            locals,
            requirements,
            type_args,
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
        // WI-223: closure invocation overrides the uniform
        // `frame.requirements = apply_within.requirements` rule with the
        // requirements snapshotted at lambda construction. Preserves
        // lexical scope of the lambda's creation site. See
        // `docs/design/operation-call-model.md` §"Closure invocation:
        // the one runtime exception". The closure-side SmallVecs have
        // inline size 1 (most lambdas need 0–1 reqs/type-args), the
        // frame-side has 2; collect across the size boundary. Single
        // arena borrow grabs param/body/both channels at once.
        let (param_pattern, body, requirements, type_args) = self.closures.with(&handle, |c| {
            let reqs: SmallVec<[(Symbol, super::value::RequirementHandle); 2]> =
                c.requirements.iter().cloned().collect();
            let ta: FrameTypeArgs =
                c.type_args.iter().cloned().collect();
            (c.param_pattern.clone(), c.body.clone(), reqs, ta)
        });
        let bindings = match match_pattern(self, &param_pattern, &arg) {
            Some(b) => b,
            // WI-610: route the match failure through the Error handler so an
            // installed `Error[MatchFailed]` handler catches it; occurrence is
            // the closure's parameter pattern, scrutinee the argument value.
            None => return Err(self.raise_match_failed(param_pattern.clone(), arg.clone())),
        };
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
            requirements,
            type_args,
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
                    // WI-610: a `let` pattern that doesn't match routes through
                    // the Error handler (occurrence = the let pattern).
                    let bindings = match match_pattern(self, &pattern, &v) {
                        Some(b) => b,
                        None => return Err(self.raise_match_failed(pattern.clone(), v.clone())),
                    };
                    let top = self.stack.top_mut().unwrap();
                    for (sym, val) in bindings {
                        top.locals.push((sym, val));
                    }
                    top.expr = body;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::MatchDispatch { branches, scrutinee_occ } => {
                    let scrutinee_functor = value_functor(&self.kb, &v);
                    let mut picked: Option<(Rc<NodeOccurrence>, super::pattern::Bindings)> = None;
                    for branch in &branches {
                        // WI-511: branch.pattern is a Pattern-kind occurrence,
                        // read directly by `match_pattern` / `constructor_
                        // pattern_name` — no `pattern_to_term` bridge.
                        // Cheap pre-filter: constructor-pattern functor
                        // mismatch can skip the full match attempt.
                        // `functor_matches` collapses short vs. qualified
                        // — `wis(_, _)` patterns compare equal to host-
                        // built `…FileBasedWorkitemStore.wis` values.
                        if let (Some(pat_name), Some(scr_name)) =
                            (constructor_pattern_name(&branch.pattern), scrutinee_functor)
                        {
                            if !super::pattern::functor_matches(
                                &self.kb, pat_name, scr_name,
                            ) {
                                continue;
                            }
                        }
                        if let Some(bindings) = match_pattern(self, &branch.pattern, &v) {
                            picked = Some((branch.body.clone(), bindings));
                            break;
                        }
                    }
                    // WI-610: no arm matched — route through the Error handler
                    // with the scrutinee occurrence and the failing value.
                    let (body, bindings) = match picked {
                        Some(x) => x,
                        None => return Err(self.raise_match_failed(scrutinee_occ, v.clone())),
                    };
                    let top = self.stack.top_mut().unwrap();
                    for (sym, val) in bindings {
                        top.locals.push((sym, val));
                    }
                    top.expr = body;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::ApplyArgs { target, mut buffered, mut remaining, type_args } => {
                    buffered.push(v);
                    if remaining.is_empty() {
                        return self.dispatch_call(target, buffered, type_args);
                    }
                    let next_expr = remaining.remove(0);
                    let top = self.stack.top_mut().unwrap();
                    top.awaiting = Some(AwaitState::ApplyArgs {
                        target, buffered, remaining, type_args,
                    });
                    let ctx = self.stack.top().unwrap().child_context();
                    self.stack.push(child_frame(ctx, next_expr))?;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::ApplyWithinArgs {
                    target,
                    mut buffered,
                    mut remaining,
                    requirements,
                    type_args,
                } => {
                    buffered.push(v);
                    if remaining.is_empty() {
                        return self.dispatch_call_with_requirements(
                            target,
                            buffered,
                            requirements,
                            type_args,
                        );
                    }
                    let next_expr = remaining.remove(0);
                    let top = self.stack.top_mut().unwrap();
                    top.awaiting = Some(AwaitState::ApplyWithinArgs {
                        target,
                        buffered,
                        remaining,
                        requirements,
                        type_args,
                    });
                    let ctx = self.stack.top().unwrap().child_context();
                    self.stack.push(child_frame(ctx, next_expr))?;
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
                    let ctx = self.stack.top().unwrap().child_context();
                    self.stack.push(child_frame(ctx, pushed_expr))?;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::SortTypeArgs {
                    sort_sym,
                    mut buffered_pos,
                    mut buffered_named,
                    mut remaining,
                } => {
                    // WI-707: same one-at-a-time pump as `ConstructorArgs` — the
                    // first entry of `remaining` names the argument just evaluated.
                    // No `classify_ctor_arg`: a type argument is placed by its own
                    // name/position, with no declared-field lookup to reconcile
                    // against (a sort's type params are not entity fields).
                    let (current_name, _placeholder_occ) = remaining.remove(0);
                    match current_name {
                        Some(n) => buffered_named.push((n, v)),
                        None => buffered_pos.push(v),
                    }
                    if remaining.is_empty() {
                        return self.finish_sort_type(sort_sym, buffered_pos, buffered_named);
                    }
                    let (next_name, next_expr) = remaining[0].clone();
                    let pushed_expr = next_expr.clone();
                    remaining[0] = (next_name, next_expr);
                    let top = self.stack.top_mut().unwrap();
                    top.awaiting = Some(AwaitState::SortTypeArgs {
                        sort_sym,
                        buffered_pos,
                        buffered_named,
                        remaining,
                    });
                    let ctx = self.stack.top().unwrap().child_context();
                    self.stack.push(child_frame(ctx, pushed_expr))?;
                    return Ok(StepOutcome::Continue);
                }
                AwaitState::RelationArgs {
                    ref_sym,
                    mut buffered_pos,
                    mut buffered_named,
                    mut remaining,
                } => {
                    // WI-714: same one-at-a-time pump as `SortTypeArgs` — the first
                    // entry of `remaining` names the argument just evaluated.
                    let (current_name, _placeholder_occ) = remaining.remove(0);
                    match current_name {
                        Some(n) => buffered_named.push((n, v)),
                        None => buffered_pos.push(v),
                    }
                    if remaining.is_empty() {
                        return Ok(StepOutcome::Deliver(self.build_relation_value(
                            ref_sym,
                            &buffered_pos,
                            &buffered_named,
                        )?));
                    }
                    let (next_name, next_expr) = remaining[0].clone();
                    let pushed_expr = next_expr.clone();
                    remaining[0] = (next_name, next_expr);
                    let top = self.stack.top_mut().unwrap();
                    top.awaiting = Some(AwaitState::RelationArgs {
                        ref_sym,
                        buffered_pos,
                        buffered_named,
                        remaining,
                    });
                    let ctx = self.stack.top().unwrap().child_context();
                    self.stack.push(child_frame(ctx, pushed_expr))?;
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

    /// WI-707: begin evaluating a SORT-headed application's type arguments —
    /// `Cell[V = Int64]`, `Map[K = String, V = Cell]`. Mirrors
    /// [`Interpreter::start_constructor`]'s one-arg-at-a-time pump (see
    /// [`AwaitState::SortTypeArgs`] for why the arguments are evaluated rather than
    /// read off the syntax); [`Interpreter::finish_sort_type`] assembles the result.
    ///
    /// A bare sort carrying no arguments never reaches here — `reduce_var`'s WI-206
    /// arm already delivers it — but an argument-less application (`Cell[]`) finishes
    /// straight away, and `make_parameterized_type` maps it to the bare `Ref(Cell)`,
    /// so `Cell[]` and `Cell` are the same type term.
    fn start_sort_type(
        &mut self,
        sort_sym: Symbol,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
    ) -> Result<StepOutcome, EvalError> {
        let mut remaining: Vec<(Option<Symbol>, Rc<NodeOccurrence>)> =
            Vec::with_capacity(pos_args.len() + named_args.len());
        for a in pos_args.iter() {
            remaining.push((None, a.clone()));
        }
        for (n, a) in named_args.iter() {
            remaining.push((Some(*n), a.clone()));
        }

        if remaining.is_empty() {
            return self.finish_sort_type(sort_sym, Vec::new(), Vec::new());
        }

        let (first_name, first_expr) = remaining.remove(0);
        let placeholder = first_expr.clone();
        let top = self
            .stack
            .top_mut()
            .ok_or_else(|| EvalError::Internal("start_sort_type with no parent".into()))?;
        top.awaiting = Some(AwaitState::SortTypeArgs {
            sort_sym,
            buffered_pos: Vec::new(),
            buffered_named: Vec::new(),
            remaining: std::iter::once((first_name, placeholder))
                .chain(remaining.into_iter())
                .collect(),
        });
        let ctx = self.stack.top().unwrap().child_context();
        self.stack.push(child_frame(ctx, first_expr))?;
        Ok(StepOutcome::Continue)
    }

    /// WI-707: assemble the parameterized type value from its evaluated type
    /// arguments — `Cell` + `{V: Int64}` ⇒ the type term for `Cell[V = Int64]`.
    ///
    /// Built through `make_parameterized_type`, the SAME canonical builder the loader
    /// lowers a written type with (`load.rs`'s `TypeExpr::Parameterized` arm), so an
    /// evaluated type and a written one hash-cons to ONE term and every type reader
    /// (`extract_type`, the discrimination tree, unification) sees them as equal.
    /// Hand-rolling the `Term::Fn` here would silently diverge from it three ways:
    /// the builder canonicalizes named-arg ORDER (`canonicalize_record_named_args` —
    /// declared-field order, not the spelling order), and it maps EMPTY bindings to a
    /// bare `Ref(S)` rather than a degenerate no-arg `Fn{S}`, which `type_head`
    /// classifies as `Error` (losing the base sort entirely).
    ///
    /// POSITIONAL type arguments bind the sort's declared type params in order
    /// (`Cell[Int64]` ≡ `Cell[V = Int64]`), again mirroring the loader — otherwise the
    /// two spellings of one type would build structurally different terms, and the
    /// positional binding would be invisible to `extract_type_param`.
    ///
    /// Every argument must itself be a TYPE value, and a positional must have a
    /// declared param to bind: both are loud errors rather than silent drops, per
    /// CLAUDE.md's loud-over-silent rule — a type term quietly carrying a scalar, or
    /// quietly missing an argument, would resurface far away as an unmatchable type.
    ///
    /// WI-709: the type ARGUMENTS are checked against the sort's declared params by the
    /// shared [`KnowledgeBase::check_sort_type_args`] — the same rule the typer applies
    /// to this call at load, and the loader to the same type written in TYPE position, so
    /// the written and the evaluated spelling admit the SAME arguments (without which
    /// they would build different terms for one source text, defeating WI-707's
    /// hash-consing identity). This replaced a LOCAL over-application guard that stated
    /// the rule a second, weaker way (it never saw an undeclared NAME).
    ///
    /// For loaded source the typer now rejects the same call first, so this is a backstop
    /// — for a synthesized occurrence, which never went through the typer. (A rule-body
    /// occurrence does NOT reach here at all: `convert_term` builds it as a plain term at
    /// load, a third lowering path this check does not cover — WI-710.)
    fn finish_sort_type(
        &mut self,
        sort_sym: Symbol,
        pos: Vec<Value>,
        named: Vec<(Symbol, Value)>,
    ) -> Result<StepOutcome, EvalError> {
        // WI-709: the arguments must FIT the sort's declared params — the SAME rule the
        // typer applies to this call at load and the loader applies to the type written
        // in TYPE position, so one written type is admissible in one set of spellings
        // wherever it appears. Kept here (rather than deleted as "the typer already
        // checked") because not every occurrence reaches the typer: a RULE BODY is not
        // type-checked, so eval is where its type arguments are heard — loud, not a
        // silently-built term carrying a parameter the sort never declared.
        let declared = self.kb.type_params_of_sort(sort_sym);
        let named_keys: Vec<Symbol> = named.iter().map(|(s, _)| *s).collect();
        if let Err(problem) =
            self.kb.check_sort_type_args(sort_sym, &declared, &named_keys, pos.len())
        {
            return Err(EvalError::TypeMismatch {
                expected: "type arguments matching the sort's declared type parameters",
                got: problem.describe(&self.kb, sort_sym),
            });
        }

        let mut bindings: Vec<(Symbol, TermId)> = Vec::with_capacity(pos.len() + named.len());
        for (n, v) in &named {
            bindings.push((*n, self.expect_type_arg(sort_sym, v)?));
        }

        let mut next_param = 0usize;
        for v in &pos {
            let term = self.expect_type_arg(sort_sym, v)?;
            // Bind the next declared param not already given by name — the loader's
            // rule, so `Cell[V = Int64]` and `Cell[Int64]` agree. The check above admitted
            // this many positionals, so a free param is guaranteed to be there.
            let param = loop {
                let Some(name) = declared.get(next_param) else {
                    return Err(EvalError::Internal(format!(
                        "finish_sort_type: `{}` ran out of declared type params for a \
                         positional that `check_sort_type_args` admitted",
                        self.kb.qualified_name_of(sort_sym),
                    )));
                };
                next_param += 1;
                let sym = self.kb.intern(name);
                if !bindings.iter().any(|(s, _)| *s == sym) {
                    break sym;
                }
            };
            bindings.push((param, term));
        }

        let base = self.kb.make_sort_ref(sort_sym);
        let tid = self.kb.make_parameterized_type(base, &bindings);
        Ok(StepOutcome::Deliver(Value::term(tid)))
    }

    /// WI-707: a type argument must denote a TYPE — a `Term`-carried type value.
    /// Loud (never a silent drop) so a `Cell[V = <not a type>]` cannot quietly build
    /// a malformed type term.
    fn expect_type_arg(&self, sort_sym: Symbol, v: &Value) -> Result<TermId, EvalError> {
        match v {
            Value::Term { id, .. } => Ok(*id),
            other => Err(EvalError::TypeMismatch {
                expected: "Type (a type argument)",
                got: format!(
                    "{} (in a type argument of `{}[…]`)",
                    other.type_name(),
                    self.kb.qualified_name_of(sort_sym),
                ),
            }),
        }
    }

    fn finish_constructor(
        &mut self,
        ctor_sym: Symbol,
        is_tuple_literal: bool,
        pos: Vec<Value>,
        mut named: Vec<(Symbol, Value)>,
    ) -> Result<StepOutcome, EvalError> {
        // Shared with the Term-side builders (WI-299): `KnowledgeBase::canonicalize_record_named_args`
        // is generic over the arg value type, so Value- and Term-carried entities
        // canonicalize to the SAME declared-field order (else they'd hash-cons /
        // discrim-match as distinct shapes).
        self.kb.canonicalize_record_named_args(ctor_sym, &mut named);
        let value = if Some(ctor_sym) == self.reflect.list_literal {
            self.build_list_value(pos, &named)?
        } else if is_tuple_literal {
            Value::Tuple { pos: pos.into(), named: named.into() }
        } else if Some(ctor_sym) == self.reflect.set_literal {
            // SetLiteral has set semantics: dedup by structural equality so
            // nested tuples/entities compare by shape, not identity. Opaque
            // handles (Closure/Stream) still compare as distinct.
            // WI-511: carrier-aware via `views_structurally_equal` so a 0-ary
            // constructor dedups across carriers (`Entity{c}` vs `Term(Ref(c))`),
            // matching the `eq`/`neq` builtins.
            let kb: &KnowledgeBase = &self.kb;
            let mut deduped: Vec<Value> = Vec::with_capacity(pos.len());
            for v in pos {
                if !deduped.iter().any(|existing| {
                    crate::kb::term_view::views_structurally_equal(kb, existing, &v)
                }) {
                    deduped.push(v);
                }
            }
            Value::Entity { functor: ctor_sym, pos: deduped.into(), named: named.into() }
        } else {
            Value::Entity { functor: ctor_sym, pos: pos.into(), named: named.into() }
        };
        Ok(StepOutcome::Deliver(value))
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
            .unwrap_or(Value::Entity { functor: nil_sym, pos: Vec::new().into(), named: Vec::new().into() });

        let mut acc = tail_seed;
        for elem in elements.into_iter().rev() {
            acc = Value::Entity {
                functor: cons_sym,
                pos: Vec::new().into(),
                named: vec![(self.fields.head, elem), (self.fields.tail, acc)].into(),
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
            Literal::Handle(_, _) => {
                return Err(EvalError::Internal(
                    "Handle literal in expression value position — \
                     unexpected after WI-251 NodeOccurrence cleanup".into(),
                ));
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

/// Find a frame-level operation type-argument value by its declared
/// param name (e.g. `T` from `operation foo[T](...)`). Same lookup
/// contract as `find_requirement` but on the type-arg channel
/// (WI-272). Reverse order so an inner scope's `T` shadows an outer
/// one if closure capture ever bridges nested definitions with
/// same-named type params.
fn find_type_arg(
    type_args: &FrameTypeArgs,
    name: Symbol,
) -> Option<crate::kb::term::TermId> {
    type_args.iter().rev().find(|(s, _)| *s == name).map(|(_, t)| *t)
}

/// Assemble a fresh child frame from a snapshotted parent context
/// plus the sub-expression to reduce. Centralises the otherwise-
/// fivefold expansion in `start_constructor` / `suspend_and_push` /
/// the `AwaitState::*Args` delivery branches.
fn child_frame(ctx: ChildFrameContext, expr: Rc<NodeOccurrence>) -> Frame {
    Frame {
        op: ctx.op,
        expr,
        locals: ctx.locals,
        requirements: ctx.requirements,
        type_args: ctx.type_args,
        awaiting: None,
    }
}

/// Read the typer-resolved operation type arguments off an
/// apply/apply_within occurrence's RefCell into the eval's frame-channel
/// shape (WI-272). Skips the SmallVec allocation when the occurrence
/// has no entries — the common case (ops without `[T, ...]`).
fn collect_resolved_type_args(occ: &Rc<NodeOccurrence>) -> FrameTypeArgs {
    occ.with_resolved_type_args(|entries| {
        if entries.is_empty() {
            FrameTypeArgs::new()
        } else {
            entries.iter().copied().collect()
        }
    })
}

/// Head functor of a value, when one is recoverable: an entity, a `Fn` term,
/// or a bare `Ref` (a nullary reference, e.g. a free-standing entity used as a
/// type value). `pub` (re-exported as `anthill_core::eval::value_functor`) so
/// the reflect host bridge (`anthill-stl`) reads an entity reference's functor
/// through the SAME single source the interpreter uses (WI-551), instead of a
/// hand-maintained twin.
pub fn value_functor(kb: &KnowledgeBase, value: &Value) -> Option<Symbol> {
    match value {
        Value::Entity { functor, .. } => Some(*functor),
        Value::Term { id: tid, .. } => match kb.get_term(*tid) {
            Term::Fn { functor, .. } => Some(*functor),
            Term::Ref(sym) => Some(*sym),
            _ => None,
        },
        _ => None,
    }
}

/// The prelude carrier sort a runtime VALUE names, for dynamic spec-op
/// dispatch — the runtime twin of the typer's `carrier_sort_of_value` (which
/// keys on a TYPE). `Entity` / `Term` values derive the carrier from their
/// constructor's parent sort; HANDLE and SCALAR values carry no constructor
/// functor, so each maps to a FIXED prelude sort (a stream cursor → `LogicalStream`,
/// a `Map` → `Map`, a `Cell` → `Cell`, a closure / op-ref → `Function`, a boxed
/// scalar → its primitive sort).
///
/// The match is EXHAUSTIVE over `Value` (mirrors [`Value::type_name`], no `_`
/// arm) so a new variant must declare its carrier here rather than silently
/// fall through to `None` and dispatch as `UnknownOperation` — the exact
/// WI-385-widening regression class WI-435 closes (the WI-009 `Value::Stream →
/// LogicalStream` patch generalized to every handle). A value that never names a
/// spec receiver (unit, tuple, lazy thunk, substitution, raw node, logic var)
/// maps to `None`.
pub(crate) fn runtime_carrier_sort(kb: &KnowledgeBase, value: &Value) -> Option<Symbol> {
    // Handle / scalar values: a FIXED prelude carrier sort per variant.
    let qualified: Option<&str> = match value {
        Value::Stream(_) => Some("anthill.prelude.LogicalStream"),
        Value::Map(_) => Some("anthill.prelude.Map"),
        Value::Cell(_) => Some("anthill.prelude.Cell"),
        // WI-577 — a runtime requirement dictionary names the `Dictionary` view
        // sort (the anthill face of `Value::Requirement`). `OpRef` stays
        // `Function` below so an eta'd op-ref remains callable. This is the
        // value→carrier map for uniform typing; it is NOT a live dynamic-dispatch
        // path — `Dictionary` provides no spec, so the typer never binds a
        // `Value::Requirement` into a spec-op receiver slot, and the
        // `spec_call_runtime_carrier` route (whose `resolve_spec_op_target_by_value`
        // matches by short name) is unreachable for it. If `Dictionary` ever
        // provides a spec, that route would need `carrier_override_op`'s
        // runnable-body gate to avoid a short-name collision (`sub` ↔ `Numeric.sub`).
        Value::Requirement(_) => Some("anthill.realization.runtime.Dictionary"),
        Value::Closure(_) | Value::OpRef { .. } => Some("anthill.prelude.Function"),
        Value::Int(_) => Some("anthill.prelude.Int64"),
        Value::BigInt(_) => Some("anthill.prelude.BigInt"),
        Value::Float(_) => Some("anthill.prelude.Float"),
        Value::Str(_) => Some("anthill.prelude.String"),
        Value::Bool(_) => Some("anthill.prelude.Bool"),
        // Structured values: the carrier is the constructor's parent sort (below).
        Value::Entity { .. } | Value::Term { .. } => None,
        // WI-714 (proposal 052): a `Relation` value's carrier IS the `Relation`
        // sort — so `splitFirst`/`head`/`map`/… dispatch to `Relation.splitFirst`
        // (the query-running host builtin) and, via `provides LogicalStream`, the
        // inherited Stream API. Without this it would fall to `None` and dispatch
        // as `UnknownOperation` (the WI-435 widening class this exhaustive match
        // closes).
        Value::Relation { .. } => Some("anthill.prelude.Relation"),
        // Values that never name a spec receiver — no carrier sort. Listed
        // explicitly (no `_` arm) so a new `Value` variant forces a decision.
        Value::Unit
        | Value::Tuple { .. }
        | Value::Substitution(_)
        | Value::Node(_)
        | Value::Var(_) => return None,
    };
    if let Some(qn) = qualified {
        return kb.try_resolve_symbol(qn);
    }
    // Entity / Term: the carrier is the constructor's parent-sort base symbol.
    let functor = value_functor(kb, value)?;
    let parent_tid = kb.constructor_parent_sort(functor)?;
    match kb.get_term(parent_tid) {
        Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => Some(*functor),
        _ => None,
    }
}

/// Is `label` the parser's synthetic positional name for source index `index`?
///
/// Mirrors `intern_positional_label` (parse/convert.rs), which emits exactly
/// `_{index + 1}` — so `_01` is a USER label, not a synthetic one, and stays
/// named.
fn is_synthetic_positional_label(label: &str, index: usize) -> bool {
    match label.strip_prefix('_') {
        Some(digits) if !digits.starts_with('0') => {
            matches!(digits.parse::<usize>(), Ok(n) if n == index + 1)
        }
        _ => false,
    }
}

/// Decide whether a constructor arg with optional auto-name goes into the
/// positional or named slot of the emerging value. Tuple literals' `_N`
/// auto-names are unwrapped back to positional; everything else goes named
/// iff it has a name.
///
/// WI-786: the tuple-literal unwrap is narrow on purpose, and both conditions
/// are load-bearing.
///
///  * The label must be EXACTLY the synthetic name for this component's source
///    index — not merely `_`-prefixed. Identifiers may begin with `_`, so a
///    plain prefix test also caught user labels like `_id`; those were re-slotted
///    into `pos`, which carries no labels, DISCARDING the name and scrambling
///    source order.
///  * Nothing may have gone to `named` yet, so `pos` stays a source-order
///    PREFIX. The reachable case is an all-named literal whose LATER label is
///    the synthetic name for `pos.len()`: in `(a: 3, _1: 10)`, `a` goes to
///    `named`, and without this condition `_1` would match index `pos.len() ==
///    0` and hoist into `pos`, so `pos ++ named` would read `[10, 3]`.
///    (`(a: 1, 2)` cannot reach here at all — the parser rejects mixing
///    positional and named in a tuple literal.)
///
/// Together they give every consumer the invariant that **`pos ++ named` is
/// source order** — making a named tuple an ordered product in its runtime
/// carrier, not just in its type. `match_tuple_pattern` (eval/pattern.rs) relies
/// on it to bind a destructuring binder list; `validate_projection_labels`
/// (parse/convert.rs) previously had to defend WI-639 projections against the
/// old behaviour at the producer instead.
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
        // `named.is_empty()` makes `pos.len()` this component's source index.
        Some(sym)
            if is_tuple_literal
                && named.is_empty()
                && is_synthetic_positional_label(kb.resolve_sym(sym), pos.len()) =>
        {
            pos.push(value);
        }
        Some(sym) => named.push((sym, value)),
        None => pos.push(value),
    }
}

/// Walk OperationInfo facts for a functor, return (body node, params).
/// Thin wrapper over `kb::op_info::lookup_operation_info`. Returns
/// `None` for body-less ops (specs) and for ops whose `op_body_node`
/// the loader didn't populate.
pub fn lookup_operation_body(
    kb: &KnowledgeBase,
    functor: Symbol,
) -> Option<(std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>, Vec<(Symbol, Value)>)> {
    let rec = crate::kb::op_info::lookup_operation_info(kb, functor)?;
    let body = rec.body_node?;
    Some((body, rec.params))
}
