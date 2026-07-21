//! WI-352 — load-time `flow`-fact derivation for the `Modify` `effect_derive`
//! slice (proposal 046, `docs/design/modify-effect-derive.md` §"Derived from a
//! body"). A standalone pass (mirroring `req_insertion::run`) that walks each
//! operation body once and asserts the ground `flow(kind, from, to)` facts a
//! bodyless op would otherwise declare by hand. `provenance` is *not* derived
//! here — it is a function of each place's `SymbolKind` (the `provenance`
//! builtin); only the body-dependent connectivity lives in facts.
//!
//! The pass is signature-free: every callable in the body (`apply(F, args)`)
//! carries its ordered argument-place symbols on `F`'s own symbol
//! (`SymbolTable::arg_places`, WI-352), so `args[i]` maps to `F`'s i-th place
//! from symbol data alone — for the op (self-recursion) and callbacks alike.
//!
//! Coverage (v1): destructuring (`cons(h,_) := xs` ⇒ `element_of`), callback
//! application feeds, the self-recursive loop-carried accumulator (one unfold),
//! and return positions. Constructs it doesn't recognise emit nothing — the op
//! stays opaque/coarse downstream (046 "Source priority"), which is sound.

use std::collections::HashMap;
use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::{Symbol, SymbolKind};
use crate::kb::node_occurrence::{for_each_child, Expr, NodeOccurrence, Pattern};
use crate::kb::term::{Term, TermId};
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

/// WI-352 entry point: derive + assert `flow` facts for every operation body.
pub fn run(kb: &mut KnowledgeBase) {
    // Collect bodies first (release the `op_bodies` borrow before mutating).
    let bodies: Vec<(Symbol, Rc<NodeOccurrence>)> =
        kb.op_bodies_iter().map(|(s, b)| (s, b.clone())).collect();

    let mut edges: Vec<Edge> = Vec::new();
    for (op_sym, body) in &bodies {
        derive_op(kb, *op_sym, body, &mut edges);
    }
    if edges.is_empty() {
        return;
    }

    // Resolve the `feed` vocabulary once. Absent (e.g. reflect/feed not loaded)
    // ⇒ nothing to assert against; bail (the analysis is auxiliary).
    // `flow` is a variant of `enum Flow`, qualified `<ns>.<Enum>.<variant>`.
    let flow_functor = match kb.try_resolve_symbol("anthill.reflect.feed.Flow.flow") {
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
    let sort = kb.make_name_term("Flow");
    let domain = kb.make_name_term("_global");

    for e in edges {
        let kind_ctor = if e.kind == Fk::Direct { direct_ctor } else { element_ctor };
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
}

fn derive_op(kb: &KnowledgeBase, op_sym: Symbol, body: &Rc<NodeOccurrence>, edges: &mut Vec<Edge>) {
    let op_places: Vec<Symbol> = kb.symbols.arg_places(op_sym).to_vec();
    let op_qn = kb.qualified_name_of(op_sym).to_owned();
    let result = match kb.try_resolve_symbol(&format!("{}.result", op_qn)) {
        Some(s) => s,
        None => return,
    };
    // Accumulator param indices: op params returned bare in a base (tail)
    // position — `nil() -> z` makes `z`'s index the loop-carried accumulator
    // (the one-unfold provenance fixpoint, 046 §1).
    let mut acc: Vec<usize> = Vec::new();
    find_accumulators(&op_places, body, &mut acc);

    let mut d = Deriver { kb, op_sym, op_places: &op_places, result, acc: &acc, edges };
    let env: HashMap<Symbol, Origin> = HashMap::new();
    d.analyze(body, &env, true);
}

struct Deriver<'a> {
    kb: &'a KnowledgeBase,
    op_sym: Symbol,
    op_places: &'a [Symbol],
    result: Symbol,
    acc: &'a [usize],
    edges: &'a mut Vec<Edge>,
}

impl<'a> Deriver<'a> {
    fn emit(&mut self, kind: Fk, from: Symbol, to: Symbol) {
        // Skip self-loops (`xs -> xs`, `f -> f`): harmless for reachability and
        // not part of the declared form.
        if from != to {
            self.edges.push(Edge { kind, from, to });
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
        let expr = occ.as_expr()?;
        match expr {
            Expr::VarRef { name } => {
                let o = self.origin_of_name(*name, env);
                if is_tail {
                    if let Some(o) = o {
                        self.emit(o.kind, o.src, self.result);
                    }
                }
                o
            }
            Expr::Apply { functor, pos_args, named_args, .. } => {
                if *functor == self.op_sym {
                    // Self-recursion: each arg feeds the op's own i-th param
                    // (loop-carried), and — in tail position — the accumulator
                    // arg(s) flow to the op result.
                    for (i, arg) in pos_args.iter().enumerate() {
                        if let Some(o) = self.analyze(arg, env, false) {
                            if i < self.op_places.len() {
                                self.emit(o.kind, o.src, self.op_places[i]);
                            }
                        }
                    }
                    // Named args map to the op's own places by param name.
                    for (key, arg) in named_args {
                        if let Some(o) = self.analyze(arg, env, false) {
                            if let Some(place) = place_by_name(self.kb, self.op_places, *key) {
                                self.emit(o.kind, o.src, place);
                            }
                        }
                    }
                    if is_tail {
                        for &k in self.acc {
                            if let Some(arg) = pos_args.get(k) {
                                // Re-analyse for the value-origin; duplicate
                                // feeds dedup at assert time.
                                if let Some(o) = self.analyze(arg, env, false) {
                                    self.emit(o.kind, o.src, self.result);
                                }
                            }
                        }
                    }
                    None
                } else if self.is_callback(*functor) {
                    // Callback application: arg i feeds the callback's i-th
                    // place; the value of `f(...)` is `f.result`.
                    let f_places: Vec<Symbol> = self.kb.symbols.arg_places(*functor).to_vec();
                    for (i, arg) in pos_args.iter().enumerate() {
                        if let Some(o) = self.analyze(arg, env, false) {
                            if i < f_places.len() {
                                self.emit(o.kind, o.src, f_places[i]);
                            }
                        }
                    }
                    // Named callback args map to the callback's places by name.
                    for (key, arg) in named_args {
                        if let Some(o) = self.analyze(arg, env, false) {
                            if let Some(place) = place_by_name(self.kb, &f_places, *key) {
                                self.emit(o.kind, o.src, place);
                            }
                        }
                    }
                    let f_qn = self.kb.qualified_name_of(*functor).to_owned();
                    let val = self
                        .kb
                        .try_resolve_symbol(&format!("{}.result", f_qn))
                        .map(|r| Origin { kind: Fk::Direct, src: r });
                    if is_tail {
                        if let Some(o) = val {
                            self.emit(o.kind, o.src, self.result);
                        }
                    }
                    val
                } else {
                    // Ordinary call / constructor: walk args (pos + named) for
                    // nested feeds.
                    for arg in pos_args {
                        self.analyze(arg, env, false);
                    }
                    for (_, arg) in named_args {
                        self.analyze(arg, env, false);
                    }
                    None
                }
            }
            Expr::Match { scrutinee, branches } => {
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
            Expr::Let { pattern, value, body, .. } => {
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
                // Unrecognised: walk children for nested feeds (no return/value).
                for_each_child(expr, |c| {
                    self.analyze(c, env, false);
                });
                None
            }
        }
    }

    fn origin_of_name(&self, name: Symbol, env: &HashMap<Symbol, Origin>) -> Option<Origin> {
        if let Some(o) = env.get(&name) {
            return Some(*o);
        }
        // An op parameter is its own `input` place (kind `Param`).
        if self.kb.kind_of(name) == Some(SymbolKind::Param) {
            return Some(Origin { kind: Fk::Direct, src: name });
        }
        None
    }

    /// A callback-typed parameter: a `Param` with non-empty `arg_places`.
    fn is_callback(&self, functor: Symbol) -> bool {
        self.kb.kind_of(functor) == Some(SymbolKind::Param)
            && !self.kb.symbols.arg_places(functor).is_empty()
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
    let kn = kb.resolve_sym(key);
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
        Some(Pattern::Constructor { pos_args, named_args, .. }) => {
            let sub = scrutinee.map(|o| Origin { kind: Fk::ElementOf, src: o.src });
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
        Some(Expr::VarRef { name }) => {
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
        Some(Expr::If { then_branch, else_branch, .. }) => {
            find_accumulators(op_places, then_branch, acc);
            find_accumulators(op_places, else_branch, acc);
        }
        _ => {}
    }
}
