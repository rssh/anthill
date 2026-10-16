//! WI-352 — load-time `flow`-fact derivation for the `Modify` `effect_derive`
//! slice (proposal 046, `docs/design/modify-effect-derive.md` §"Derived from a
//! body"). A standalone pass (mirroring `req_insertion::run`) that walks each
//! operation body once and asserts the ground `flow(kind, from, to)` facts.
//! `provenance` is *not* derived here — it is a function of each place's
//! `SymbolKind` (the `provenance` builtin); only the body-dependent connectivity
//! lives in facts.
//!
//! The pass is signature-free: every callable in the body (`apply(F, args)`)
//! carries its ordered argument-place symbols on `F`'s own symbol
//! (`SymbolTable::arg_places`, WI-352), so `args[i]` maps to `F`'s i-th place
//! from symbol data alone — for the op (self-recursion) and callbacks alike.
//!
//! Coverage (v1): destructuring (`cons(h,_) := xs` ⇒ `element_of`), callback
//! application feeds, the self-recursive loop-carried accumulator (one unfold),
//! and return positions.
//!
//! **A drop needs evidence.** The consumer (`region::op_boundary_effects`, through
//! `feed.keep_modify`) DROPS a callback parameter's `Modify` whose origins are all
//! non-escaping, so a feed this pass did not see used to be a silent unsound drop
//! (measured: `f(first(l, d))` and `let k = f` loaded typed pure while writing an
//! element of `l`). So the pass also asserts `traced(to: p)` for a parameter `p`
//! of one of the op's callbacks, and for the op's `result`, only when it followed
//! every value that reaches `p`. No `traced` fact for: a place fed a value whose
//! source it did not follow (an ordinary call's result, a lambda's binder, a
//! constructed value); every parameter of a callback read as a VALUE — aliased by
//! a `let`, handed to another operation, returned, passed in another slot of a
//! self-call — since it is then applied where this pass does not look; and any
//! place fed from one of those. (A callback APPLIED inside a lambda body is still
//! an application this pass reads; what it is handed there is usually the
//! lambda's binder, which has no followed source.) `keep_modify` keeps a `Modify`
//! on an untraced place on every input and on the result. A construct the pass
//! does not recognise costs precision, never soundness.
//!
//! ONE ASSUMPTION IS NOT EVIDENCE-BACKED: a callback's result counts as a fresh
//! value (provenance `fresh_output`), so a place fed only callback results that do
//! not reach `result` still drops. A callback returning its own argument, or a
//! cell its closure captured, defeats it (measured: `f(g(h))` with `g = lambda x
//! -> x` loads pure while writing an element of `l`). It is the assumption the
//! typer's local masking makes of EVERY call's result (`let x = first(l, d);
//! Cell.set(x, 1)` loads pure as well), so it is not this pass's alone to lift.
//!
//! The pass walks EVERY body at every load, so a body an earlier load holds is
//! read again in the form the typer left it (`@[simp]` and dot dispatch write
//! back). The facts are a union over those readings, which is sound because each
//! reading is: `traced(p)` from one reading says its own `flow` facts cover `p`'s
//! feeds, and the other readings' facts only add origins.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::{Symbol, SymbolKind};
use crate::kb::node_occurrence::{for_each_child, Expr, NodeOccurrence, Pattern};
use crate::kb::term::{Term, TermId};
use crate::kb::ClauseKind;
use crate::kb::KnowledgeBase;

/// Feed kind — the `FlowKind` precision knob (046). v1 derives `Direct` /
/// `ElementOf`; `field_of` is deferred.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Fk {
    Direct,
    ElementOf,
}

/// Where an expression's value comes from: a feed kind + the source place.
#[derive(Clone, Copy)]
struct Origin {
    kind: Fk,
    src: Symbol,
}

/// A derived edge over places (asserted as a `flow(kind, from, to)` fact).
struct Edge {
    kind: Fk,
    from: Symbol,
    to: Symbol,
}

/// WI-352 entry point: derive + assert `flow` facts for every operation body,
/// and a `traced` fact for each place whose feeds they cover in full.
pub fn run(kb: &mut KnowledgeBase) {
    // Collect bodies first (release the `op_bodies` borrow before mutating).
    let bodies: Vec<(Symbol, Rc<NodeOccurrence>)> =
        kb.op_bodies_iter().map(|(s, b)| (s, b.clone())).collect();

    let mut edges: Vec<Edge> = Vec::new();
    let mut traced: Vec<Symbol> = Vec::new();
    for (op_sym, body) in &bodies {
        derive_op(kb, *op_sym, body, &mut edges, &mut traced);
    }
    if edges.is_empty() && traced.is_empty() {
        return;
    }

    // Resolve the `feed` vocabulary once. Absent (e.g. reflect/feed not loaded)
    // ⇒ nothing to assert against; bail. The consumer then keeps every callback
    // parameter's `Modify` (`region::keep_modify_holds`).
    // `flow` / `traced` are variants of `enum Flow`, qualified `<ns>.<Enum>.<variant>`.
    let flow_functor = match kb.try_resolve_symbol("anthill.reflect.feed.Flow.flow") {
        Some(s) => s,
        None => return,
    };
    let traced_functor = match kb.try_resolve_symbol("anthill.reflect.feed.Flow.traced") {
        Some(s) => s,
        None => return,
    };
    let direct_ctor = kb.try_resolve_symbol("anthill.reflect.feed.FlowKind.direct");
    let element_ctor = kb.try_resolve_symbol("anthill.reflect.feed.FlowKind.element_of");
    let (direct_ctor, element_ctor) = match (direct_ctor, element_ctor) {
        (Some(d), Some(e)) => (d, e),
        _ => return,
    };
    let kind_f = kb.intern("kind");
    let from_f = kb.intern("from");
    let to_f = kb.intern("to");
    let sort = ClauseKind::Flow;
    let domain = kb.global_scope().owner();

    for e in edges {
        let kind_ctor = if e.kind == Fk::Direct {
            direct_ctor
        } else {
            element_ctor
        };
        let kind_term = kb.make_name_term_from_sym(kind_ctor);
        let from_term = kb.alloc(Term::Ref(e.from));
        let to_term = kb.alloc(Term::Ref(e.to));
        // Named args must be stored in the `flow` entity's FIELD-DECLARATION
        // order (`kind, from, to`) — the canonical order the loader uses for
        // the `reaches` rule's `flow(...)` goal, so the fact unifies against it.
        let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named.push((kind_f, kind_term));
        named.push((from_f, from_term));
        named.push((to_f, to_term));
        let fact = kb.alloc(Term::Fn {
            functor: flow_functor,
            pos_args: SmallVec::new(),
            named_args: named,
        });
        // assert_fact dedups by (term, sort, domain); hash-consing makes equal
        // edges the same TermId, so re-analysed duplicates collapse here.
        kb.assert_fact(fact, sort, domain, None);
    }
    for place in traced {
        let to_term = kb.alloc(Term::Ref(place));
        let fact = kb.alloc(Term::Fn {
            functor: traced_functor,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_elem((to_f, to_term), 1),
        });
        kb.assert_fact(fact, sort, domain, None);
    }
}

fn derive_op(
    kb: &KnowledgeBase,
    op_sym: Symbol,
    body: &Rc<NodeOccurrence>,
    edges: &mut Vec<Edge>,
    traced: &mut Vec<Symbol>,
) {
    let op_places: Vec<Symbol> = kb.symbols.arg_places(op_sym).to_vec();
    // The classifier's own lookup (kind-checked), so the two agree on the target.
    let result = match super::region::resolve_op_result_sym(kb, op_sym) {
        Some(s) => s,
        // No result place: nothing of this op is traced, so nothing of it drops.
        None => return,
    };
    // Accumulator param indices: op params returned bare in a base (tail)
    // position — `nil() -> z` makes `z`'s index the loop-carried accumulator
    // (the one-unfold provenance fixpoint, 046 §1).
    let mut acc: Vec<usize> = Vec::new();
    find_accumulators(&op_places, body, &mut acc);

    let first_edge = edges.len();
    let mut d = Deriver {
        kb,
        op_sym,
        op_places: &op_places,
        result,
        acc: &acc,
        edges: &mut *edges,
        untraced: HashSet::new(),
        escaped: HashSet::new(),
    };
    let env: HashMap<Symbol, Origin> = HashMap::new();
    d.analyze(body, &env, true);

    let Deriver {
        mut untraced,
        escaped,
        ..
    } = d;
    for cb in escaped {
        untraced.extend(kb.symbols.arg_places(cb).iter().copied());
    }
    close_untraced(&mut untraced, &edges[first_edge..]);
    // Only one level: a nested callback's places (`f.g.x`) are bound inside `f`,
    // which this body cannot see, so they are never traced.
    let mut has_callback = false;
    for &p in &op_places {
        if is_callback(kb, p) {
            has_callback = true;
            traced.extend(
                kb.symbols
                    .arg_places(p)
                    .iter()
                    .copied()
                    .filter(|q| !untraced.contains(q)),
            );
        }
    }
    // `traced(result)` is read only beside a callback's place; an op with no
    // callback has no such label to classify.
    if has_callback && !untraced.contains(&result) {
        traced.push(result);
    }
}

/// Close `untraced` over one op's edges: a place fed from an untraced place holds
/// whatever that one was fed. The edges are few per op, so a plain fixpoint.
fn close_untraced(untraced: &mut HashSet<Symbol>, edges: &[Edge]) {
    loop {
        let before = untraced.len();
        for e in edges {
            if untraced.contains(&e.from) {
                untraced.insert(e.to);
            }
        }
        if untraced.len() == before {
            return;
        }
    }
}

/// A callback-typed parameter: a `Param` that is callable — a `() -> T` one too,
/// whose argument places are empty.
fn is_callback(kb: &KnowledgeBase, sym: Symbol) -> bool {
    kb.kind_of(sym) == Some(SymbolKind::Param) && kb.symbols.is_callable(sym)
}

struct Deriver<'a> {
    kb: &'a KnowledgeBase,
    op_sym: Symbol,
    op_places: &'a [Symbol],
    result: Symbol,
    acc: &'a [usize],
    edges: &'a mut Vec<Edge>,
    /// Places fed, somewhere in the body, a value whose source was not followed.
    untraced: HashSet<Symbol>,
    /// Callback parameters used as a value rather than applied (module doc).
    escaped: HashSet<Symbol>,
}

impl<'a> Deriver<'a> {
    fn emit(&mut self, kind: Fk, from: Symbol, to: Symbol) {
        // Skip self-loops (`xs -> xs`, `f -> f`): harmless for reachability and
        // not part of the declared form.
        if from != to {
            self.edges.push(Edge { kind, from, to });
        }
    }

    /// `value`, whose origin is `o`, reaches place `to`.
    fn feed(&mut self, o: Option<Origin>, value: &Rc<NodeOccurrence>, to: Symbol) {
        match o {
            Some(o) => self.emit(o.kind, o.src, to),
            None if self.holds_no_value(value) => {}
            None => {
                self.untraced.insert(to);
            }
        }
    }

    /// Walk `occ`, emitting feed / loop-carried / return edges as side effects,
    /// and return the value-origin of `occ` (if a place feeds it).
    fn analyze(
        &mut self,
        occ: &Rc<NodeOccurrence>,
        env: &HashMap<Symbol, Origin>,
        is_tail: bool,
    ) -> Option<Origin> {
        let Some(expr) = occ.as_expr() else {
            // Not an expression node: its value is not followed either.
            if is_tail {
                self.untraced.insert(self.result);
            }
            return None;
        };
        match expr {
            Expr::VarRef { name } | Expr::Ref(name) | Expr::Ident(name) => {
                self.use_as_value(*name);
                let o = self.origin_of_name(*name, env);
                if is_tail {
                    self.feed(o, occ, self.result);
                }
                o
            }
            Expr::Apply {
                functor,
                pos_args,
                named_args,
                ..
            } => self.apply(*functor, pos_args, named_args, occ, env, is_tail),
            // The same call after requirement elaboration — read alike, so a body
            // an earlier load left elaborated derives what its source form did.
            Expr::ApplyWithin {
                functor,
                args,
                named_args,
                requirements,
                ..
            } => {
                for r in requirements {
                    self.analyze(r, env, false);
                }
                self.apply(*functor, args, named_args, occ, env, is_tail)
            }
            Expr::HoApply { predicate, args } | Expr::HoApplyWithin { predicate, args, .. } => {
                if let Expr::HoApplyWithin { requirements, .. } = expr {
                    for r in requirements {
                        self.analyze(r, env, false);
                    }
                }
                match self.callback_named_by(predicate) {
                    Some(cb) => self.apply_callback(cb, args, &[], env, is_tail),
                    // A computed function applied: the predicate is walked like any
                    // child (a callback named in it escapes), its value not followed.
                    None => {
                        self.analyze(predicate, env, false);
                        for arg in args {
                            self.analyze(arg, env, false);
                        }
                        if is_tail {
                            self.untraced.insert(self.result);
                        }
                        None
                    }
                }
            }
            Expr::Match {
                scrutinee,
                branches,
            } => {
                let so = self.analyze(scrutinee, env, false);
                for br in branches {
                    let benv = self.bind(&br.pattern, so, env);
                    // A guard can carry feeds (`case … if f(h) -> …`); analyze it.
                    if let Some(g) = &br.guard {
                        self.analyze(g, &benv, false);
                    }
                    self.analyze(&br.body, &benv, is_tail);
                }
                None
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                // Both branches are tail positions when the `if` is. Its value has
                // two origins, which one `Origin` cannot hold: none, so a place it
                // feeds is untraced.
                self.analyze(condition, env, false);
                self.analyze(then_branch, env, is_tail);
                self.analyze(else_branch, env, is_tail);
                None
            }
            Expr::Let {
                pattern,
                value,
                body,
                ..
            } => {
                let vo = self.analyze(value, env, false);
                let benv = self.bind(pattern, vo, env);
                self.analyze(body, &benv, is_tail)
            }
            Expr::Proof { conclude, body, .. } => {
                // WI-538: a proof is type-transparent — its `body` is the
                // continuation and inherits the proof's tail-ness (like
                // `let`'s body), so feed/return edges in a tail-position
                // body survive. A `conclude` goal can carry feeds; analyze
                // it non-tail, as a `match` guard is.
                if let Some(c) = conclude {
                    self.analyze(c, env, false);
                }
                self.analyze(body, env, is_tail)
            }
            _ => {
                // Unrecognised: walk children for nested feeds; its own value is
                // not followed, so as a return value it leaves `result` untraced.
                self.walk_children(expr, env);
                if is_tail && !self.holds_no_value(occ) {
                    self.untraced.insert(self.result);
                }
                None
            }
        }
    }

    /// An application of `functor` — the op itself, one of its callbacks, or an
    /// ordinary call.
    fn apply(
        &mut self,
        functor: Symbol,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
        occ: &Rc<NodeOccurrence>,
        env: &HashMap<Symbol, Origin>,
        is_tail: bool,
    ) -> Option<Origin> {
        if functor == self.op_sym {
            self.apply_self(pos_args, named_args, env, is_tail);
            None
        } else if is_callback(self.kb, functor) {
            self.apply_callback(functor, pos_args, named_args, env, is_tail)
        } else {
            // Ordinary call / constructor: walk args for nested feeds. Its value
            // is not followed.
            for arg in pos_args {
                self.analyze(arg, env, false);
            }
            for (_, arg) in named_args {
                self.analyze(arg, env, false);
            }
            if is_tail && !self.holds_no_value(occ) {
                self.untraced.insert(self.result);
            }
            None
        }
    }

    /// Self-recursion: each arg feeds the op's own param (loop-carried), and —
    /// in tail position — the accumulator arg(s) flow to the op result. The
    /// call's own value is the result again, so it adds nothing to it.
    fn apply_self(
        &mut self,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
        env: &HashMap<Symbol, Origin>,
        is_tail: bool,
    ) {
        for (i, arg) in pos_args.iter().enumerate() {
            let slot = self.op_places.get(i).copied();
            self.feed_own_param(slot, arg, env);
        }
        // Named args map to the op's own places by param name.
        for (key, arg) in named_args {
            let slot = place_by_name(self.kb, self.op_places, *key);
            self.feed_own_param(slot, arg, env);
        }
        if is_tail {
            for &k in self.acc {
                if let Some(arg) = pos_args.get(k) {
                    // Re-analyse for the value-origin; duplicate feeds dedup at
                    // assert time. An untraced one already left its param
                    // untraced, and the param's base-case edge carries that on.
                    if let Some(o) = self.analyze(arg, env, false) {
                        self.emit(o.kind, o.src, self.result);
                    }
                }
            }
        }
    }

    /// `arg`, passed to the op's own parameter `slot` in a self-call.
    fn feed_own_param(
        &mut self,
        slot: Option<Symbol>,
        arg: &Rc<NodeOccurrence>,
        env: &HashMap<Symbol, Origin>,
    ) {
        match slot {
            // The callback handed back in its own slot: the recursive frame
            // applies the same callback.
            Some(p) if is_callback(self.kb, p) && self.callback_named_by(arg) == Some(p) => {}
            Some(p) if is_callback(self.kb, p) => {
                // Something else is applied as `p` in the recursive frame.
                self.analyze(arg, env, false);
                self.escaped.insert(p);
            }
            Some(p) => {
                let o = self.analyze(arg, env, false);
                self.feed(o, arg, p);
            }
            None => {
                // No parameter of the op takes it by position or name (a
                // variadic capture, or a call the typer refuses): any may.
                self.analyze(arg, env, false);
                for &p in self.op_places {
                    if is_callback(self.kb, p) {
                        self.escaped.insert(p);
                    } else {
                        self.untraced.insert(p);
                    }
                }
            }
        }
    }

    /// Callback application: arg i feeds the callback's i-th place; the value of
    /// `f(...)` is `f.result`.
    fn apply_callback(
        &mut self,
        cb: Symbol,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
        env: &HashMap<Symbol, Origin>,
        is_tail: bool,
    ) -> Option<Origin> {
        let places: Vec<Symbol> = self.kb.symbols.arg_places(cb).to_vec();
        for (i, arg) in pos_args.iter().enumerate() {
            let o = self.analyze(arg, env, false);
            match places.get(i) {
                Some(&p) => self.feed(o, arg, p),
                // More arguments than the callback has places: where they land
                // is not known.
                None => {
                    self.escaped.insert(cb);
                }
            }
        }
        // Named callback args map to the callback's places by name.
        for (key, arg) in named_args {
            let o = self.analyze(arg, env, false);
            match place_by_name(self.kb, &places, *key) {
                Some(p) => self.feed(o, arg, p),
                None => {
                    self.escaped.insert(cb);
                }
            }
        }
        let cb_qn = self.kb.qualified_name_of(cb).to_owned();
        let val = self
            .kb
            .try_resolve_symbol(&format!("{}.result", cb_qn))
            .filter(|&r| self.kb.kind_of(r) == Some(SymbolKind::CallbackResult))
            .map(|r| Origin {
                kind: Fk::Direct,
                src: r,
            });
        if is_tail {
            match val {
                Some(o) => self.emit(o.kind, o.src, self.result),
                None => {
                    self.untraced.insert(self.result);
                }
            }
        }
        val
    }

    fn walk_children(&mut self, expr: &Expr, env: &HashMap<Symbol, Origin>) {
        for_each_child(expr, |c| {
            self.analyze(c, env, false);
        });
    }

    /// A name read as a value. A callback parameter so read escapes: whoever
    /// receives it applies it where this pass does not look.
    fn use_as_value(&mut self, name: Symbol) {
        if is_callback(self.kb, name) {
            self.escaped.insert(name);
        }
    }

    /// The callback parameter `occ` names, when it is a bare name of one.
    fn callback_named_by(&self, occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
        match occ.as_expr()? {
            Expr::VarRef { name } | Expr::Ref(name) | Expr::Ident(name)
                if is_callback(self.kb, *name) =>
            {
                Some(*name)
            }
            _ => None,
        }
    }

    /// Whether `occ` holds no value this invocation was handed or made, so a
    /// place it reaches learns nothing from it: a literal, the empty tuple, a
    /// constructor applied to nothing (spelled bare, as a constructor, or as an
    /// apply). NOT a bare operation or const: in a value slot a bare nullary
    /// operation is its call (§5.4), whose result is not followed — so `f(op)`
    /// reads as `f(op())` does — and a const may hold anything.
    fn holds_no_value(&self, occ: &Rc<NodeOccurrence>) -> bool {
        let is_entity = |s: Symbol| self.kb.kind_of(s) == Some(SymbolKind::Entity);
        match occ.as_expr() {
            Some(Expr::Const(_) | Expr::Bottom) => true,
            Some(Expr::TupleLit { positional, named }) => positional.is_empty() && named.is_empty(),
            Some(Expr::Ref(s) | Expr::Ident(s)) => is_entity(*s),
            Some(Expr::Constructor {
                pos_args,
                named_args,
                ..
            }) => pos_args.is_empty() && named_args.is_empty(),
            Some(Expr::Apply {
                functor,
                pos_args,
                named_args,
                ..
            }) => is_entity(*functor) && pos_args.is_empty() && named_args.is_empty(),
            _ => false,
        }
    }

    fn origin_of_name(&self, name: Symbol, env: &HashMap<Symbol, Origin>) -> Option<Origin> {
        if let Some(o) = env.get(&name) {
            return Some(*o);
        }
        // An op parameter is its own `input` place (kind `Param`).
        if self.kb.kind_of(name) == Some(SymbolKind::Param) {
            return Some(Origin {
                kind: Fk::Direct,
                src: name,
            });
        }
        None
    }

    fn bind(
        &self,
        pat: &Rc<NodeOccurrence>,
        scrutinee: Option<Origin>,
        env: &HashMap<Symbol, Origin>,
    ) -> HashMap<Symbol, Origin> {
        let mut e = env.clone();
        bind_into(pat, scrutinee, &mut e);
        e
    }
}

/// The callable place whose param name (last dotted segment) equals the
/// named-arg key — maps a named call `f(a: x)` to the place `f.a`.
fn place_by_name(kb: &KnowledgeBase, places: &[Symbol], key: Symbol) -> Option<Symbol> {
    let kn = kb.local_name_of(key);
    places
        .iter()
        .copied()
        .find(|&p| kb.qualified_name_of(p).rsplit('.').next() == Some(kn))
}

/// Bind a pattern's variables under the scrutinee's origin. Constructor
/// destructuring yields `element_of` sub-origins; tuple/var keep the kind.
fn bind_into(pat: &Rc<NodeOccurrence>, scrutinee: Option<Origin>, e: &mut HashMap<Symbol, Origin>) {
    match pat.as_pattern() {
        Some(Pattern::Var { name, .. }) => {
            if let Some(o) = scrutinee {
                e.insert(*name, o);
            }
        }
        Some(Pattern::Constructor {
            pos_args,
            named_args,
            ..
        }) => {
            let sub = scrutinee.map(|o| Origin {
                kind: Fk::ElementOf,
                src: o.src,
            });
            for a in pos_args {
                bind_into(a, sub, e);
            }
            for (_, a) in named_args {
                bind_into(a, sub, e);
            }
        }
        // WI-803: `labels` says which component each binder takes; every binder
        // still binds from the same scrutinee, so the flow edge is unchanged.
        Some(Pattern::Tuple { positional, .. }) => {
            for a in positional {
                bind_into(a, scrutinee, e);
            }
        }
        _ => {} // Wildcard / Literal bind nothing.
    }
}

/// Collect op-param indices returned bare in a tail position (the base-case
/// accumulator) by walking tail positions only.
fn find_accumulators(op_places: &[Symbol], occ: &Rc<NodeOccurrence>, acc: &mut Vec<usize>) {
    match occ.as_expr() {
        // The same three spellings of a name read that `Deriver::analyze` takes.
        Some(Expr::VarRef { name } | Expr::Ref(name) | Expr::Ident(name)) => {
            if let Some(idx) = op_places.iter().position(|&p| p == *name) {
                if !acc.contains(&idx) {
                    acc.push(idx);
                }
            }
        }
        Some(Expr::Match { branches, .. }) => {
            for br in branches {
                find_accumulators(op_places, &br.body, acc);
            }
        }
        Some(Expr::Let { body, .. }) => find_accumulators(op_places, body, acc),
        // WI-538: a proof is type-transparent — recurse into the tail
        // continuation (its `body`).
        Some(Expr::Proof { body, .. }) => find_accumulators(op_places, body, acc),
        Some(Expr::If {
            then_branch,
            else_branch,
            ..
        }) => {
            find_accumulators(op_places, then_branch, acc);
            find_accumulators(op_places, else_branch, acc);
        }
        _ => {}
    }
}
