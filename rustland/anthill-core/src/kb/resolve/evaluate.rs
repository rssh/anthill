//! WI-20260926-K4JGC — proposal 068 §1.1's ONE evaluation strategy
//! (`docs/design/068-implementation.md` §5).
//!
//! An operation application written in a rule body denotes its VALUE, at any depth —
//! under an entity constructor, a tuple, a collection literal, or as a goal's argument.
//! Every consumer that reads an operand (`<=>`, `=` / `neq`, `===`, the comparisons, the
//! arithmetic relations, and a goal's arguments before its head is matched) reads it
//! through [`KnowledgeBase::evaluate_value`] or [`KnowledgeBase::evaluate_with_holes`]:
//! evaluate, strictly and arguments first, until what is left is a variable or a STUCK
//! call, then work structurally.
//!
//! Before this each consumer reduced to its own depth — `reduce_operand` the top of an
//! operand, `<=>` the node its walk was at (a bind stored the rest unvisited), head
//! matching nothing — so one call answered true, false or nothing by where it was
//! written, and a stuck call was bound as DATA and reported as a definite answer.
//!
//! The walk reads every carrier through [`TermView`] and rebuilds a spine it changed as
//! a transient `Value::Entity` / `Value::Tuple`. The one occurrence-specific step is the
//! CALL itself: an `Expr::Apply` whose argument changed is rebuilt with
//! [`NodeOccurrence::rebuilt_expr`], because the typer's dispatch stamps ride on that
//! node and `reduce_op_value` decides the callee from them (WI-1026).

use super::*;

/// Why a call was left in a value unevaluated.
///
/// Ordered by precedence: a value holding stuck calls in two states takes the greater
/// ([`Stuck::join`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Stuck {
    /// It has an implementation and did not run, and no binding in this derivation can
    /// change that: an argument is a RIGID variable (design D7 — an eigenvariable, so the
    /// call is the most precise name its value has), or the evaluator declined a ground
    /// call it can run in general (an effect row, the fold's depth cap, a fault). Kept as a
    /// symbolic term where a value is built, and compared as today where one is tested:
    /// the test delays.
    Symbolic,
    /// It cannot run YET: an argument it needs is an unbound variable (068 §2's
    /// SUSPENDED). Design D1: its blockers are the free variables of its arguments,
    /// which the goal carrying it mentions, so ordinary rotation re-asks it.
    Suspended,
    /// It can never run: no implementation is reachable (068 §2's UNREDUCED) — the
    /// operation has none of any kind, or it is a body-less spec operation whose ground
    /// carrier no provider supplies. Undecided, never false.
    Unreduced,
    /// It RAN and has no value: an arithmetic builtin over numbers that has no answer
    /// (`div(1, 0)`, `mod(5, 0)`). Its relation `div(1, 0, ?r)` FAILS, so a goal reading
    /// the call wherever it is written fails with it — one call, one answer (068 §1). It is
    /// never a hole: there is no value for a pending equation to wait for.
    Absent,
}

impl Stuck {
    /// The state of a value holding stuck calls in two states. ABSENT wins — the value
    /// does not exist, whatever the others turn out to be; then UNREDUCED — no binding can
    /// make the value decidable (068 §2.2); a SUSPENDED call may still run, so it wins over
    /// a SYMBOLIC one.
    pub(super) fn join(self, other: Stuck) -> Stuck {
        self.max(other)
    }

    /// The verdict of a goal over an operand holding a stuck call: UNREDUCED is the third
    /// truth value, ABSENT a failure, everything else waits.
    pub(super) fn verdict(self) -> BuiltinResult {
        match self {
            Stuck::Absent => BuiltinResult::Failure,
            Stuck::Unreduced => BuiltinResult::Unknown {
                cause: UnknownCause::Unreduced,
            },
            Stuck::Suspended | Stuck::Symbolic => BuiltinResult::delay(),
        }
    }
}

/// A stuck call replaced by a fresh variable (068 §1.2): the value keeps `var` where the
/// call stood, and the call becomes the pending equation `unify(var, call)`.
pub(super) struct Hole {
    pub(super) var: VarId,
    pub(super) call: Value,
    pub(super) state: Stuck,
}

/// The holes minted by one evaluation — ONE per distinct stuck call, so two identical
/// stuck calls share a variable and unify by reflexivity (068 §1.1: a pure operation
/// applied to the same arguments has the same value, whatever it is).
#[derive(Default)]
pub(super) struct Holes {
    pub(super) entries: Vec<Hole>,
}

impl Holes {
    /// The hole `v` is, if it is one of these holes' variables.
    pub(super) fn hole_of(&self, kb: &KnowledgeBase, v: &Value) -> Option<&Hole> {
        let vid = kb.value_global_var(v)?;
        self.entries.iter().find(|h| h.var == vid)
    }
}

/// The walk's state: where a stuck call goes, and whether anything was replaced.
struct EvalCtx<'h> {
    /// `Some` — a stuck SUSPENDED / UNREDUCED call becomes a hole and the walk goes on (an
    /// ABSENT one still fails the value: it has nothing to wait for); `None` — any stuck
    /// call makes the whole value stuck.
    holes: Option<&'h mut Holes>,
    /// Set when a call was replaced — by its value or by a hole. A spine none of whose
    /// children was replaced is handed back as it came, not rebuilt.
    replaced: bool,
}

/// How many times a call's value may itself be a call to evaluate before the walk gives up
/// on it (as SYMBOLIC — kept, never data). A value the bridge returns is a value; this
/// bounds a FOLD whose result is again a call. It counts those re-evaluations only — never
/// the depth of DATA, which is as deep as the value is (a 1000-element list is walked).
const EVAL_DEPTH_CAP: usize = 64;

impl KnowledgeBase {
    /// Evaluate `v` under `subst`: every operation application in it that can run is
    /// replaced by its value. `Err` is the state of the stuck call(s) it still holds
    /// ([`Stuck::join`] over all of them) — the reading a TEST needs (`=`, the
    /// comparisons, the arithmetic relations), since none of them may compare a call as
    /// data.
    pub(super) fn evaluate_value(
        &mut self,
        v: Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
    ) -> Result<Value, Stuck> {
        let mut ctx = EvalCtx {
            holes: None,
            replaced: false,
        };
        self.evaluate_at(v, subst, faults, &mut ctx, 0)
    }

    /// [`Self::evaluate_value`] for a comparison's OPERAND: a qualified NAME written with
    /// dots at its top (`Box.zero`, `ns.inner.rel` — [`Self::is_qualified_name`]) is first
    /// read as an operand reads it — a dotted NULLARY operation is its call, anything
    /// else the name it spells (`reduce_dot_value`, WI-20260901-719FJ / 4NEKZ). Inside a
    /// value the same chain is data and stays the chain.
    pub(super) fn evaluate_operand(
        &mut self,
        v: Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
    ) -> Result<Value, Stuck> {
        let v = self.read_operand_name(v, subst);
        self.evaluate_value(v, subst, faults)
    }

    /// [`Self::evaluate_with_holes`] for `<=>`'s operand — see [`Self::evaluate_operand`].
    pub(super) fn evaluate_operand_with_holes(
        &mut self,
        v: Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
        holes: &mut Holes,
    ) -> Result<Value, Stuck> {
        let v = self.read_operand_name(v, subst);
        self.evaluate_with_holes(v, subst, faults, holes).map(|(v, _)| v)
    }

    fn read_operand_name(&mut self, v: Value, subst: &Substitution) -> Value {
        let v = self.chase_value(v, subst);
        if self.is_qualified_name(&v) {
            self.reduce_dot_value(v, subst)
        } else {
            v
        }
    }

    /// Is `v` a qualified NAME written with dots — a `field_access` chain whose innermost
    /// receiver names a scope (a namespace, a sort, a relation), as `Box.zero` or
    /// `ns.inner.rel` — rather than a PROJECTION of a value (`?p.x`)? A projection is a
    /// computation; a name is §5.4's bare-name question (design D3: "a bare nullary name
    /// is left alone"), read by an operand and kept as the term it spells in a data slot,
    /// where `fact holds(ns.rel)` and the goal `holds(ns.rel)` must build ONE term.
    pub(super) fn is_qualified_name(&self, v: &Value) -> bool {
        let ViewHead::Functor {
            functor: Some(f),
            pos_arity: 2,
            named_arity: 0,
        } = v.head(self)
        else {
            return false;
        };
        if self.builtins.get(&f).copied() != Some(BuiltinTag::FieldAccess) {
            return false;
        }
        let Some(receiver) = v.pos_arg(self, 0).map(|r| r.to_value()) else {
            return false;
        };
        self.is_qualified_name(&receiver) || self.names_a_scope(&receiver)
    }

    /// Does `v` spell a scope's name — a namespace, a sort, a relation — rather than a value?
    fn names_a_scope(&self, v: &Value) -> bool {
        use crate::intern::SymbolKind;
        match v.head(self) {
            ViewHead::Ident(_) => true,
            ViewHead::Functor {
                functor: Some(f),
                pos_arity: 0,
                named_arity: 0,
            } => {
                let def = self.symbols.get(f);
                [SymbolKind::Namespace, SymbolKind::Sort, SymbolKind::Rule, SymbolKind::Fact]
                    .into_iter()
                    .any(|k| def.has_kind(k))
            }
            _ => false,
        }
    }

    /// Evaluate `v` under `subst`, replacing each SUSPENDED / UNREDUCED call by a hole
    /// ([`Holes`]) — the reading a value that is BUILT needs (`<=>`'s operands, a goal's
    /// arguments), since no binding may hold an unevaluated call (068 §1.2). A SYMBOLIC
    /// call stays in place (design D7). The second component says whether anything was
    /// replaced. `Err` is [`Stuck::Absent`] alone: a call with no value fails the value.
    pub(super) fn evaluate_with_holes(
        &mut self,
        v: Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
        holes: &mut Holes,
    ) -> Result<(Value, bool), Stuck> {
        let mut ctx = EvalCtx {
            holes: Some(holes),
            replaced: false,
        };
        let out = self.evaluate_at(v, subst, faults, &mut ctx, 0)?;
        Ok((out, ctx.replaced))
    }

    fn evaluate_at(
        &mut self,
        v: Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
        ctx: &mut EvalCtx<'_>,
        depth: usize,
    ) -> Result<Value, Stuck> {
        if depth > EVAL_DEPTH_CAP {
            return Err(Stuck::Symbolic);
        }
        let v = self.chase_value(v, subst);
        if self.value_global_var(&v).is_some() {
            return Ok(v);
        }
        if self.is_written_call(&v) {
            let evaluated = self.evaluate_call(v.clone(), subst, faults, depth);
            return match evaluated {
                Ok(value) => {
                    ctx.replaced = true;
                    Ok(value)
                }
                Err(Stuck::Symbolic) if ctx.holes.is_some() => Ok(v),
                Err(Stuck::Absent) => Err(Stuck::Absent),
                Err(state) => match ctx.holes.as_deref_mut() {
                    Some(holes) => {
                        ctx.replaced = true;
                        Ok(self.hole_for(v, state, holes))
                    }
                    None => Err(state),
                },
            };
        }
        if !self.evaluation_descends(&v) {
            return Ok(v);
        }
        let ViewHead::Functor {
            functor, pos_arity, ..
        } = v.head(self)
        else {
            return Ok(v);
        };
        let mut stuck: Option<Stuck> = None;
        let mut spine_changed = false;
        let mut pos: Vec<Value> = Vec::with_capacity(pos_arity);
        for i in 0..pos_arity {
            let child = v
                .pos_arg(self, i)
                .expect("a view reports every positional child its head counts")
                .to_value();
            match self.evaluate_child(child, subst, faults, ctx, depth) {
                Ok((c, changed)) => {
                    spine_changed |= changed;
                    pos.push(c);
                }
                Err(s) => stuck = Some(stuck.map_or(s, |t| t.join(s))),
            }
        }
        let keys = v.named_keys(self);
        let mut named: Vec<(Symbol, Value)> = Vec::with_capacity(keys.len());
        for key in keys {
            let child = v
                .named_arg(self, key)
                .expect("a view reports a child for every key it lists")
                .to_value();
            match self.evaluate_child(child, subst, faults, ctx, depth) {
                Ok((c, changed)) => {
                    spine_changed |= changed;
                    named.push((key, c));
                }
                Err(s) => stuck = Some(stuck.map_or(s, |t| t.join(s))),
            }
        }
        if let Some(state) = stuck {
            return Err(state);
        }
        if !spine_changed {
            return Ok(v);
        }
        Ok(match functor {
            Some(functor) => Value::Entity {
                functor,
                pos: Rc::from(pos),
                named: Rc::from(named),
            },
            None => Value::Tuple {
                pos: Rc::from(pos),
                named: Rc::from(named),
            },
        })
    }

    /// One child of a spine: its evaluated value when a call in it was replaced, else the
    /// child as it came (so an unchanged spine is not rebuilt).
    fn evaluate_child(
        &mut self,
        child: Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
        ctx: &mut EvalCtx<'_>,
        depth: usize,
    ) -> Result<(Value, bool), Stuck> {
        let before = std::mem::replace(&mut ctx.replaced, false);
        // `depth` counts FOLD steps, not data: a list of any length is walked, and only a
        // call whose value is again a call (`evaluate_call`'s re-evaluation) goes deeper.
        let out = self.evaluate_at(child.clone(), subst, faults, ctx, depth);
        let changed = ctx.replaced;
        ctx.replaced |= before;
        out.map(|c| if changed { (c, true) } else { (child, false) })
    }

    /// Does some ARGUMENT of the goal `goal` hold a written call (design D3)? The goal's
    /// own functor is not asked — a goal is not an operand.
    pub(super) fn goal_args_hold_call(&self, goal: &Value) -> bool {
        let ViewHead::Functor { pos_arity, .. } = goal.head(self) else {
            return false;
        };
        (0..pos_arity).any(|i| {
            goal.pos_arg(self, i)
                .is_some_and(|c| self.value_holds_call(&c.to_value()))
        }) || goal.named_keys(self).into_iter().any(|k| {
            goal.named_arg(self, k)
                .is_some_and(|c| self.value_holds_call(&c.to_value()))
        })
    }

    /// Design D3 — the goal `goal` with every call written in its arguments EVALUATED,
    /// each stuck one a hole ([`Self::evaluate_with_holes`]), so candidate selection —
    /// which matches clause heads structurally — meets `p(C.tag(red()))` as `p(1)`. The
    /// goal's own functor stays. `Ok(None)` when nothing was replaced; `Err` when an
    /// argument holds a call with no value ([`Stuck::Absent`]) — the goal fails. An
    /// occurrence goal is rebuilt on its own node, so the typer's stamps stay with it;
    /// any other carrier as a transient spine.
    pub(super) fn evaluate_goal_args(
        &mut self,
        goal: &Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
        holes: &mut Holes,
    ) -> Result<Option<Value>, Stuck> {
        if let Value::Node(occ) = goal {
            if let Some(Expr::Apply {
                functor,
                pos_args,
                named_args,
                type_args,
                recv_type,
            }) = occ.as_expr()
            {
                let mut changed = false;
                let mut new_pos = Vec::with_capacity(pos_args.len());
                for a in pos_args {
                    let (c, ch) =
                        self.evaluate_with_holes(Value::Node(Rc::clone(a)), subst, faults, holes)?;
                    changed |= ch;
                    new_pos.push(if ch { self.child_occurrence(&c, a) } else { Rc::clone(a) });
                }
                let mut new_named = Vec::with_capacity(named_args.len());
                for (k, a) in named_args {
                    let (c, ch) =
                        self.evaluate_with_holes(Value::Node(Rc::clone(a)), subst, faults, holes)?;
                    changed |= ch;
                    let a = if ch { self.child_occurrence(&c, a) } else { Rc::clone(a) };
                    new_named.push((*k, a));
                }
                return Ok(changed.then(|| {
                    Value::Node(occ.rebuilt_expr(Expr::Apply {
                        functor: *functor,
                        pos_args: new_pos,
                        named_args: new_named,
                        type_args: type_args.clone(),
                        recv_type: recv_type.clone(),
                    }))
                }));
            }
        }
        let ViewHead::Functor {
            functor: Some(functor),
            pos_arity,
            ..
        } = goal.head(self)
        else {
            return Ok(None);
        };
        let mut changed = false;
        let mut pos = Vec::with_capacity(pos_arity);
        for i in 0..pos_arity {
            let child = goal
                .pos_arg(self, i)
                .expect("a view reports every positional child its head counts")
                .to_value();
            let (c, ch) = self.evaluate_with_holes(child.clone(), subst, faults, holes)?;
            changed |= ch;
            pos.push(if ch { c } else { child });
        }
        let keys = goal.named_keys(self);
        let mut named = Vec::with_capacity(keys.len());
        for key in keys {
            let child = goal
                .named_arg(self, key)
                .expect("a view reports a child for every key it lists")
                .to_value();
            let (c, ch) = self.evaluate_with_holes(child.clone(), subst, faults, holes)?;
            changed |= ch;
            named.push((key, if ch { c } else { child }));
        }
        Ok(changed.then(|| Value::Entity {
            functor,
            pos: Rc::from(pos),
            named: Rc::from(named),
        }))
    }

    /// `v` — an application — with its positional argument `i` replaced, as a transient
    /// spine: a citation's marker re-wrapped around its evaluated root goal.
    pub(super) fn with_pos_arg(&self, v: &Value, i: usize, new: Value) -> Value {
        let ViewHead::Functor {
            functor: Some(functor),
            pos_arity,
            ..
        } = v.head(self)
        else {
            panic!("with_pos_arg: `{v:?}` is not an application");
        };
        let mut new = Some(new);
        let pos: Vec<Value> = (0..pos_arity)
            .map(|j| {
                if j == i {
                    new.take().expect("one slot replaced")
                } else {
                    v.pos_arg(self, j)
                        .expect("a view reports every positional child its head counts")
                        .to_value()
                }
            })
            .collect();
        assert!(new.is_none(), "with_pos_arg: slot {i} is not among {pos_arity}");
        let named: Vec<(Symbol, Value)> = v
            .named_keys(self)
            .into_iter()
            .map(|k| {
                let c = v
                    .named_arg(self, k)
                    .expect("a view reports a child for every key it lists")
                    .to_value();
                (k, c)
            })
            .collect();
        Value::Entity {
            functor,
            pos: Rc::from(pos),
            named: Rc::from(named),
        }
    }

    /// Mint (or reuse, for an identical call) the hole standing for a stuck call.
    fn hole_for(&mut self, call: Value, state: Stuck, holes: &mut Holes) -> Value {
        if let Some(h) = holes
            .entries
            .iter()
            .find(|h| crate::kb::term_view::views_structurally_equal(self, &h.call, &call))
        {
            return Value::Var(Var::Global(h.var));
        }
        let name = self.intern("t");
        let var = self.fresh_var(name);
        holes.entries.push(Hole { var, call, state });
        Value::Var(Var::Global(var))
    }

    /// Is `v` an operation application WRITTEN as one — a node with parentheses whose
    /// functor is an operation or a builtin, not an entity constructor, a relation, a
    /// tuple, a collection literal or a variable? A bare nullary NAME (an `Expr::Ref`, or
    /// a dotted one — [`Self::is_qualified_name`]) is not: §5.4 reads it by type, and it
    /// is left alone.
    ///
    /// On a carrier with no occurrence (a query's term, a σ-rebuilt `Entity`) a nullary
    /// application and a bare name are one term (the nullary canon), so there only an
    /// application WITH arguments is a call — as `reduce_op_value` reads it.
    pub(super) fn is_written_call(&self, v: &Value) -> bool {
        if self.is_qualified_name(v) {
            return false;
        }
        if let Value::Node(o) = v {
            match o.as_expr() {
                Some(Expr::ApplyWithin { .. }) => return true,
                Some(Expr::Apply { functor, .. }) => return self.names_a_computation(*functor),
                Some(Expr::Ref(_)) => return false,
                _ => {}
            }
        }
        match v.head(self) {
            ViewHead::Functor {
                functor: Some(f),
                pos_arity,
                named_arity,
            } => pos_arity + named_arity > 0 && self.names_a_computation(f),
            _ => false,
        }
    }

    /// An operation (declared, or host-mapped under its canonical twin) or a resolver
    /// builtin — a functor whose application computes rather than builds.
    fn names_a_computation(&self, f: Symbol) -> bool {
        self.builtins.get(&f).is_some()
            || self.op_record(f).is_some()
            || self.functor_leaves_an_unreduced_op_call(f)
    }

    /// Does the walk go INTO `v` looking for calls? Through data — an entity or relation
    /// application, a tuple, a collection literal. Not into a reflected expression form
    /// (`anthill.reflect.Expr.*`: a lambda, `let`, `match`, `if`, an unresolved dot, a
    /// binder reference), whose calls run only when the form does and whose variables are
    /// bound by it; not into a type or a pattern.
    fn evaluation_descends(&self, v: &Value) -> bool {
        if let Value::Node(o) = v {
            if o.as_expr().is_none() {
                return false;
            }
        }
        match v.head(self) {
            ViewHead::Functor {
                functor: Some(f), ..
            } => !self
                .qualified_name_of(f)
                .starts_with(REFLECT_EXPR_PREFIX),
            ViewHead::Functor { functor: None, .. } => true,
            _ => false,
        }
    }

    /// Evaluate one written call: its arguments first, then the call. `Err` is why it
    /// did not run.
    fn evaluate_call(
        &mut self,
        call: Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
        depth: usize,
    ) -> Result<Value, Stuck> {
        let call = self.evaluate_call_args(call, subst, faults, depth)?;
        let functor = self.call_functor(&call);
        // The operation the TYPER pinned this site to is the callee, not the spelled one
        // (WI-1026): `PartialOrd.gt(pt(…), pt(…))` is spelled with a builtin and pinned
        // to the carrier's own bodied `gt`. `reduce_op_value` reads that pin, and hands a
        // call back at once when its callee is a builtin — which then runs here.
        let r = self.reduce_op_value(call.clone(), subst, 0, true, None, faults);
        let reduced = if !self.declined(&r, &call) {
            Some(r)
        } else {
            match functor.and_then(|f| self.builtins.get(&f).copied()) {
                // A projection reads the receiver's field — or, for a dotted NULLARY
                // operation (`Box.zero`), becomes that operation's call, which is
                // evaluated in turn below. One the occurrence path left untouched (a
                // term-carried `field_access`) goes through the builtin's result column.
                Some(BuiltinTag::FieldAccess) => {
                    let projected = self.reduce_dot_value(call.clone(), subst);
                    if self.declined(&projected, &call) {
                        self.run_builtin_for_value(BuiltinTag::FieldAccess, &call, subst, faults)
                            .into_value()?
                    } else {
                        Some(projected)
                    }
                }
                Some(tag) => self
                    .run_builtin_for_value(tag, &call, subst, faults)
                    .into_value()?,
                None => None,
            }
        };
        match reduced {
            // A value may itself hold a call (a fold's result): evaluate it in turn.
            Some(value) if self.value_holds_call(&value) => {
                self.evaluate_value_at_depth(value, subst, faults, depth + 1)
            }
            Some(value) => Ok(value),
            None => Err(self.stuck_state(&call, functor, subst)),
        }
    }

    /// Did a reduction hand `call` back rather than a value? By IDENTITY on an occurrence —
    /// `reduce_op_value` / `reduce_dot_value` return the value they were given when they
    /// decline — because a VALUE may be structurally the call: `KB.kb()`'s host function
    /// returns the term `kb()`. Another carrier has no identity to ask, and is declined when
    /// what came back is still a written call equal to it. DRIVEN by `wi_9r5hn_reflect_set_test`:
    /// with a structural test its three `KB` rows are undecided — every reader over `KB.kb()`
    /// read the handle as a call that did not run.
    fn declined(&self, r: &Value, call: &Value) -> bool {
        match (r, call) {
            (Value::Node(a), Value::Node(b)) => Rc::ptr_eq(a, b),
            _ => {
                self.is_written_call(r) && crate::kb::term_view::views_structurally_equal(self, r, call)
            }
        }
    }

    fn evaluate_value_at_depth(
        &mut self,
        v: Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
        depth: usize,
    ) -> Result<Value, Stuck> {
        let mut ctx = EvalCtx {
            holes: None,
            replaced: false,
        };
        self.evaluate_at(v, subst, faults, &mut ctx, depth)
    }

    /// Does `v` hold a written call anywhere the walk would go?
    pub(super) fn value_holds_call(&self, v: &Value) -> bool {
        if self.is_written_call(v) {
            return true;
        }
        if !self.evaluation_descends(v) {
            return false;
        }
        let ViewHead::Functor { pos_arity, .. } = v.head(self) else {
            return false;
        };
        (0..pos_arity).any(|i| {
            v.pos_arg(self, i)
                .is_some_and(|c| self.value_holds_call(&c.to_value()))
        }) || v.named_keys(self).into_iter().any(|k| {
            v.named_arg(self, k)
                .is_some_and(|c| self.value_holds_call(&c.to_value()))
        })
    }

    /// The unbound variables under `subst` of the calls written in the ARGUMENTS of the goal
    /// `goal` — the goal's own functor is not an operand, whether it is `unify`, `eq` or the
    /// functional-relation view's callee. What can still change an UNREDUCED verdict: the
    /// unreduced call itself never runs, but a SUSPENDED call beside it can run once these
    /// are bound, and turn out ABSENT — which outranks UNREDUCED ([`Stuck::join`]) and fails
    /// the goal. A variable outside every call cannot: no binding holds a call (068 §1.2).
    pub(super) fn unbound_vars_in_goal_calls(
        &self,
        goal: &Value,
        subst: &Substitution,
        out: &mut Vec<VarId>,
    ) {
        let ViewHead::Functor { pos_arity, .. } = goal.head(self) else {
            return;
        };
        for i in 0..pos_arity {
            if let Some(c) = goal.pos_arg(self, i) {
                self.unbound_vars_in_calls(&c.to_value(), subst, out);
            }
        }
        for k in goal.named_keys(self) {
            if let Some(c) = goal.named_arg(self, k) {
                self.unbound_vars_in_calls(&c.to_value(), subst, out);
            }
        }
    }

    /// The unbound variables under `subst` of every call written in `v`, arguments included.
    fn unbound_vars_in_calls(&self, v: &Value, subst: &Substitution, out: &mut Vec<VarId>) {
        let v = self.chase_value(v.clone(), subst);
        if self.is_written_call(&v) {
            self.collect_unbound_vars_value(&v, subst, out);
            return;
        }
        if !self.evaluation_descends(&v) {
            return;
        }
        let ViewHead::Functor { pos_arity, .. } = v.head(self) else {
            return;
        };
        for i in 0..pos_arity {
            if let Some(c) = v.pos_arg(self, i) {
                self.unbound_vars_in_calls(&c.to_value(), subst, out);
            }
        }
        for k in v.named_keys(self) {
            if let Some(c) = v.named_arg(self, k) {
                self.unbound_vars_in_calls(&c.to_value(), subst, out);
            }
        }
    }

    /// A call's arguments, evaluated — strictly: a stuck argument makes the call stuck.
    /// The call comes back rebuilt only if an argument changed; an occurrence is rebuilt
    /// on its own node so the typer's stamps stay with it.
    fn evaluate_call_args(
        &mut self,
        call: Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
        depth: usize,
    ) -> Result<Value, Stuck> {
        let mut ctx = EvalCtx {
            holes: None,
            replaced: false,
        };
        if let Value::Node(occ) = &call {
            let (pos_args, named_args) = match occ.as_expr() {
                Some(Expr::Apply {
                    pos_args,
                    named_args,
                    ..
                }) => (pos_args.clone(), named_args.clone()),
                Some(Expr::ApplyWithin {
                    args, named_args, ..
                }) => (args.clone(), named_args.clone()),
                _ => return Ok(call),
            };
            let mut stuck: Option<Stuck> = None;
            let mut changed = false;
            let mut new_pos = Vec::with_capacity(pos_args.len());
            for a in &pos_args {
                match self.evaluate_child(Value::Node(Rc::clone(a)), subst, faults, &mut ctx, depth)
                {
                    Ok((c, ch)) => {
                        changed |= ch;
                        new_pos.push(if ch { self.child_occurrence(&c, a) } else { Rc::clone(a) });
                    }
                    Err(s) => stuck = Some(stuck.map_or(s, |t| t.join(s))),
                }
            }
            let mut new_named = Vec::with_capacity(named_args.len());
            for (k, a) in &named_args {
                match self.evaluate_child(Value::Node(Rc::clone(a)), subst, faults, &mut ctx, depth)
                {
                    Ok((c, ch)) => {
                        changed |= ch;
                        let occ = if ch { self.child_occurrence(&c, a) } else { Rc::clone(a) };
                        new_named.push((*k, occ));
                    }
                    Err(s) => stuck = Some(stuck.map_or(s, |t| t.join(s))),
                }
            }
            if let Some(state) = stuck {
                return Err(state);
            }
            if !changed {
                return Ok(call);
            }
            let rebuilt = match occ.as_expr() {
                Some(Expr::Apply {
                    functor,
                    type_args,
                    recv_type,
                    ..
                }) => occ.rebuilt_expr(Expr::Apply {
                    functor: *functor,
                    pos_args: new_pos,
                    named_args: new_named,
                    type_args: type_args.clone(),
                    recv_type: recv_type.clone(),
                }),
                Some(Expr::ApplyWithin {
                    functor,
                    requirements,
                    type_args,
                    ..
                }) => occ.rebuilt_expr(Expr::ApplyWithin {
                    functor: *functor,
                    args: new_pos,
                    named_args: new_named,
                    requirements: requirements.clone(),
                    type_args: type_args.clone(),
                }),
                _ => unreachable!("matched as an application above"),
            };
            return Ok(Value::Node(rebuilt));
        }
        // Every other carrier: the arguments through the view, a changed call rebuilt as
        // a transient spine.
        let ViewHead::Functor {
            functor: Some(functor),
            pos_arity,
            ..
        } = call.head(self)
        else {
            return Ok(call);
        };
        let mut stuck: Option<Stuck> = None;
        let mut changed = false;
        let mut pos = Vec::with_capacity(pos_arity);
        for i in 0..pos_arity {
            let child = call
                .pos_arg(self, i)
                .expect("a view reports every positional child its head counts")
                .to_value();
            match self.evaluate_child(child, subst, faults, &mut ctx, depth) {
                Ok((c, ch)) => {
                    changed |= ch;
                    pos.push(c);
                }
                Err(s) => stuck = Some(stuck.map_or(s, |t| t.join(s))),
            }
        }
        let keys = call.named_keys(self);
        let mut named = Vec::with_capacity(keys.len());
        for key in keys {
            let child = call
                .named_arg(self, key)
                .expect("a view reports a child for every key it lists")
                .to_value();
            match self.evaluate_child(child, subst, faults, &mut ctx, depth) {
                Ok((c, ch)) => {
                    changed |= ch;
                    named.push((key, c));
                }
                Err(s) => stuck = Some(stuck.map_or(s, |t| t.join(s))),
            }
        }
        if let Some(state) = stuck {
            return Err(state);
        }
        if !changed {
            return Ok(call);
        }
        Ok(Value::Entity {
            functor,
            pos: Rc::from(pos),
            named: Rc::from(named),
        })
    }

    /// An evaluated argument as a child of the rebuilt call: a variable stays a variable
    /// leaf, anything else rides on the one materializer.
    fn child_occurrence(&mut self, v: &Value, was: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
        match v {
            Value::Var(var) => NodeOccurrence::new_expr(Expr::Var(*var), was.span, was.owner),
            _ => node_occurrence::value_as_occurrence(self, v),
        }
    }

    /// The functor a call applies — the woven call's callee for an `ApplyWithin`.
    fn call_functor(&self, call: &Value) -> Option<Symbol> {
        if let Value::Node(o) = call {
            match o.as_expr() {
                Some(Expr::Apply { functor, .. } | Expr::ApplyWithin { functor, .. }) => {
                    return Some(*functor)
                }
                _ => {}
            }
        }
        call.head(self).functor_sym()
    }

    /// A value-returning builtin run through its RESULT COLUMN: `add(a, b)` as the goal
    /// `add(a, b, ?r)`, answering `?r`'s binding.
    fn run_builtin_for_value(
        &mut self,
        tag: BuiltinTag,
        call: &Value,
        subst: &Substitution,
        faults: &mut ReduceFaults,
    ) -> BuiltinValue {
        // A GOAL-ONLY builtin (`eq`, `not`, `unify`, a reflect goal) has no result column:
        // written in a value slot it is not a value computation — a goal passed as data
        // (`prove(eq(?x, 1))`) stays the term, and a test over it waits, as WI-738 had it.
        let Some(arity) = builtin_value_arity(tag) else {
            return BuiltinValue::Stuck(Stuck::Symbolic);
        };
        let ViewHead::Functor {
            functor: Some(f),
            pos_arity,
            named_arity,
        } = call.head(self)
        else {
            return BuiltinValue::Declined;
        };
        if pos_arity != arity || named_arity != 0 {
            return BuiltinValue::Declined;
        }
        let mut args: Vec<Value> = (0..arity)
            .map(|i| {
                call.pos_arg(self, i)
                    .expect("a view reports every positional child its head counts")
                    .to_value()
            })
            .collect();
        let numeric_operands = args.iter().all(|a| self.value_num(a).is_some());
        let name = self.intern("r");
        let r = self.fresh_var(name);
        args.push(Value::Var(Var::Global(r)));
        let goal = self.make_goal_value(f, args);
        match self.execute_builtin(tag, &goal, subst, faults) {
            BuiltinResult::SuccessWithBindings(extra) => match extra.resolve_as_value(r) {
                Some(v) => BuiltinValue::Value(v.clone()),
                None => BuiltinValue::Declined,
            },
            // Over NUMBERS a failure is the relation saying there is no answer (`div(1, 0)`)
            // — the call has no value. Over anything else it is an operand the builtin
            // cannot compute over (an eigenvariable constant, an ill-typed pair): not run.
            BuiltinResult::Failure if numeric_operands => BuiltinValue::Stuck(Stuck::Absent),
            // A fault (an overflow, a comparison with no order) is RECORDED where the
            // stream reads it, never dropped: the call did not produce a value, loudly.
            BuiltinResult::Error(err) => {
                faults.fault(err.message);
                BuiltinValue::Declined
            }
            BuiltinResult::Failure
            | BuiltinResult::Success
            | BuiltinResult::SuccessSplicing { .. }
            | BuiltinResult::Delay { .. }
            | BuiltinResult::Unknown { .. } => BuiltinValue::Declined,
        }
    }

    /// Why `call` (its arguments already evaluated) did not run.
    fn stuck_state(&self, call: &Value, functor: Option<Symbol>, subst: &Substitution) -> Stuck {
        let implementation = functor.map(|f| self.implementation_of(f));
        if implementation == Some(Implementation::None) {
            return Stuck::Unreduced;
        }
        let mut flex = Vec::new();
        self.collect_unbound_vars_value(call, subst, &mut flex);
        if !flex.is_empty() {
            return Stuck::Suspended;
        }
        if self.value_has_rigid_var(call, subst) {
            return Stuck::Symbolic;
        }
        // Ground, and it did not run. A call whose only implementation is a provider's
        // was dispatched by its carrier (`dispatch_body_less`), so one that stayed is one
        // no provider supplies — or two tie (068 §2: both UNREDUCED).
        match implementation {
            Some(Implementation::ProviderOnly) => Stuck::Unreduced,
            _ => Stuck::Symbolic,
        }
    }

    /// What could run an application of `f` — 068 §2.2's first UNREDUCED case is
    /// [`Implementation::None`], decided by the operation alone.
    ///
    /// An EQUATION is not an implementation here: `@[simp]` does not fire inside this
    /// evaluation (068 §5), and an untagged one is inert (§5.3). So `Set.insert`, whose
    /// only rules are its idempotence and commutativity laws, is a provider-only spec
    /// operation like any other.
    fn implementation_of(&self, f: Symbol) -> Implementation {
        let direct = self.builtins.get(&f).is_some()
            || self.op_body_node(f).is_some()
            || self.is_interpreter_mapped_op(f)
            || self.host_op_reducible_at_a_value(f)
            || self.rules_by_functor_iter(f).any(|rid| !self.is_equation(rid));
        if direct {
            Implementation::Direct
        } else if super::super::typing::lookup_spec_op_dispatch(self, f).is_some() {
            Implementation::ProviderOnly
        } else {
            Implementation::None
        }
    }

    /// Does `v` hold a RIGID variable (an eigenvariable) under `subst`?
    fn value_has_rigid_var(&self, v: &Value, subst: &Substitution) -> bool {
        match v.index_var(self) {
            Some(Var::Global(vid)) => match self.chase_var(vid, subst) {
                Some(bound) if self.value_global_var(bound) != Some(vid) => {
                    let bound = bound.clone();
                    self.value_has_rigid_var(&bound, subst)
                }
                _ => false,
            },
            Some(Var::Rigid(_)) => true,
            Some(_) => false,
            None => match v.head(self) {
                ViewHead::Functor { pos_arity, .. } => {
                    (0..pos_arity).any(|i| {
                        v.pos_arg(self, i)
                            .is_some_and(|c| self.value_has_rigid_var(&c.to_value(), subst))
                    }) || v.named_keys(self).into_iter().any(|k| {
                        v.named_arg(self, k)
                            .is_some_and(|c| self.value_has_rigid_var(&c.to_value(), subst))
                    })
                }
                _ => false,
            },
        }
    }
}

/// What running a builtin through its result column gave ([`KnowledgeBase::run_builtin_for_value`]).
enum BuiltinValue {
    /// Its value.
    Value(Value),
    /// A state decided by the builtin itself: a goal-only builtin (SYMBOLIC), or no value
    /// over numbers (ABSENT).
    Stuck(Stuck),
    /// It did not run; why is [`KnowledgeBase::stuck_state`]'s to say.
    Declined,
}

impl BuiltinValue {
    /// `Ok(Some(value))`, `Ok(None)` for "ask `stuck_state`", or the decided state.
    fn into_value(self) -> Result<Option<Value>, Stuck> {
        match self {
            BuiltinValue::Value(v) => Ok(Some(v)),
            BuiltinValue::Declined => Ok(None),
            BuiltinValue::Stuck(s) => Err(s),
        }
    }
}

/// What could run an application of an operation ([`KnowledgeBase::implementation_of`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Implementation {
    /// A builtin, a body (a spec operation's default included), a host mapping, or
    /// relational clauses.
    Direct,
    /// Only a provider's: a body-less spec operation, run through its carrier's supplier.
    ProviderOnly,
    /// Nothing: no provider could supply it either.
    None,
}

/// The reflected expression forms' namespace — the twins a lambda, `let`, `match`, `if`,
/// an unresolved dot and a binder reference read as through [`TermView`].
const REFLECT_EXPR_PREFIX: &str = "anthill.reflect.Expr.";

/// The number of operands a value-returning builtin takes before its result column, or
/// `None` for a builtin that has no result column (a goal-only builtin: `eq`, `not`, …).
fn builtin_value_arity(tag: BuiltinTag) -> Option<usize> {
    match tag {
        BuiltinTag::Add
        | BuiltinTag::Sub
        | BuiltinTag::Mul
        | BuiltinTag::Div
        | BuiltinTag::Mod
        | BuiltinTag::Gt
        | BuiltinTag::Lt
        | BuiltinTag::Gte
        | BuiltinTag::Lte
        | BuiltinTag::FieldAccess => Some(2),
        BuiltinTag::ToBigInt | BuiltinTag::ToInt => Some(1),
        _ => None,
    }
}
