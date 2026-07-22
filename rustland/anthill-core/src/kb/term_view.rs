//! Unified view over `TermId`-backed and `Value`-backed terms.
//!
//! Per proposal 026.1 Q2. The resolver needs to unify a rule-head pattern
//! (always `TermId`) against a target that could be either KB-resident
//! (`TermId`) or an external-sourced runtime `Value`. `TermView` is the
//! read-only shape used on the target side of unification.
//!
//! WI-276: `Value::Node` (a reflect `Expr` occurrence) is now *structural*
//! here — its `head`/`pos_arg`/`named_arg` expose the underlying `Expr` so a
//! `[simp]` rule LHS can match against expression occurrences (the substrate
//! for the typer-phase rewriting engine, proposal 043). Previously it was
//! `Opaque`.
//!
//! This module defines the trait and implementations. Direct structural
//! unification via `match_view` lives in `kb::mod`.

use std::rc::Rc;

use crate::eval::value::Value;
use crate::intern::Symbol;

use super::node_occurrence::{
    EffectExprNode, Expr, MatchBranch, NodeOccurrence, Pattern, TypeChild, TypeNode,
};
use super::persist_subst::BindValue;
use super::term::{Literal, Term, TermId, Var};
use super::KnowledgeBase;

/// The outermost shape of a term/value, enough to drive unification
/// dispatch. Structural details beneath a head are fetched via
/// [`TermView::pos_arg`] / [`TermView::named_arg`].
#[derive(Clone, Debug)]
pub enum ViewHead {
    /// Logic variable of any kind — flex `Global`, `Rigid` skolem, or bound
    /// `DeBruijn` (mirroring `Term::Var(Var)` / `Value::Var(Var)`). The
    /// discrimination tree reads the *kind* off this `Var` to decide how it
    /// indexes/matches: a flex `Global` (and a bound `DeBruijn` rule var) is a
    /// **wildcard** (a var-edge that matches any subterm); a `Rigid` skolem is a
    /// **constant** identified by its `VarId` (a `DiscrimKey::RigidVar` concrete
    /// edge that matches only the same rigid). So a rigid goal var can't
    /// over-match a concrete fact, and two distinct skolems never conflate.
    Var(Var),
    /// Literal constant.
    Const(Literal),
    /// Function / constructor application. Used for both `Term::Fn` and
    /// `Value::Entity` / `Value::Tuple`, distinguished by whether `functor`
    /// is `Some`.
    Functor { functor: Option<Symbol>, pos_arity: usize, named_arity: usize },
    /// Reference to a named symbol.
    Ref(Symbol),
    /// Bare identifier (not yet resolved).
    Ident(Symbol),
    /// Bottom term `⊥`.
    Bottom,
    /// Anything else — closures, streams, lazies. Treated as opaque by
    /// unification (compare by pointer identity if needed).
    Opaque,
}

impl ViewHead {
    /// WI-436 — the head's functor symbol, treating a bare [`ViewHead::Ref`] as
    /// the 0-ary application it denotes: `Ref(c) ≡ Fn{c}`. Returns the symbol for
    /// both a `Functor { functor: Some(s), .. }` and a `Ref(s)` head, and `None`
    /// for a functor-less aggregate / var / const / opaque head.
    ///
    /// The reader counterpart of the canonicalization in [`functor_view_head`]: a
    /// 0-ary constructor canonicalizes to the bare `Ref`, so a reader that
    /// identifies a head by its *symbol* (an effect-row label, a reflect Expr
    /// ctor, a sort functor) must read `c` off either spelling. Keying on the
    /// symbol is also stronger than a qualified-name string match — symbol
    /// identity can't collide with a same-named user sort.
    pub(crate) fn functor_sym(&self) -> Option<Symbol> {
        match self {
            ViewHead::Functor { functor: Some(s), .. } => Some(*s),
            ViewHead::Ref(s) => Some(*s),
            _ => None,
        }
    }
}

/// WI-436 — canonicalize a functor application head: a **0-ary application of a
/// registered constructor** reads as the bare [`ViewHead::Ref`]. A 0-ary
/// constructor `c` has two indistinguishable spellings — bare `Ref(c)` and the
/// nullary application `Fn{c}` / `Constructor{c}` / `Entity{c}` — that PRINT
/// identically (`c`); the bare `Ref` is the single canonical form (the only one
/// `print → parse` produces). So every carrier reads a 0-ary constructor THROUGH
/// `Ref`, closing the divergence where a fact stored as `Fn{c}` was invisible to
/// a rule spelled `Ref(c)` (and vice versa).
///
/// SOUND and KIND-ISOLATED via the `is_constructor_symbol` gate: an op-as-value
/// is a `Value::OpRef`, never a `Term::Ref`, so no op/eta case depends on the
/// `Ref`-vs-`Fn` shape; and a concrete SORT (`Fn{Int}`) or type-PARAM is not a
/// constructor, so the type/dispatch wildcard-vs-concrete distinction (WI-391,
/// recovered from the symbol's kind) is untouched. Readers that identify a head
/// by symbol use [`ViewHead::functor_sym`] to accept the `Ref` spelling.
fn functor_view_head(
    kb: &KnowledgeBase,
    functor: Symbol,
    pos_arity: usize,
    named_arity: usize,
) -> ViewHead {
    if pos_arity == 0 && named_arity == 0 && kb.is_constructor_symbol(functor) {
        ViewHead::Ref(functor)
    } else {
        ViewHead::Functor { functor: Some(functor), pos_arity, named_arity }
    }
}

/// A child of a [`TermView`] — a `TermId` (borrowed from the KB's
/// hash-consed store), a `Value` (borrowed from the owning [`TermView`]),
/// or a reflect `Expr` occurrence child (`Node`). The `Node` variant *owns*
/// an `Rc<NodeOccurrence>` (a cheap clone) rather than borrowing, so that
/// [`TermView::as_bind_value`] can bind a matched child as `Value::Node`
/// (WI-276). `'a` is the lifetime of the borrowed `Value`.
///
/// `Clone` but **not** `Copy`: the `Node` variant carries an `Rc`.
#[derive(Clone, Debug)]
pub enum ViewItem<'a> {
    Term(TermId),
    Value(&'a Value),
    Node(Rc<NodeOccurrence>),
}

impl ViewItem<'_> {
    /// The ground hash-consed `TermId` this child carries, if any. A `Term`
    /// carrier — or a `Value::Term` — yields its `TermId`; a `Node` (denoted /
    /// occurrence carrier) or any other `Value` has no `TermId` → `None`. The
    /// carrier-agnostic peer of reading a child as a term: a reader that only
    /// makes sense for ground children (a `SortAlias` target `Var`, a positional
    /// sort ref) uses this and treats `None` as "not a ground term, skip".
    pub fn as_term_id(&self) -> Option<TermId> {
        match self {
            ViewItem::Term(t) => Some(*t),
            ViewItem::Value(Value::Term { id: t, .. }) => Some(*t),
            _ => None,
        }
    }

    /// Materialize this child as an owned, carrier-agnostic [`Value`] — a cheap
    /// clone (`Term`→`Value::Term`, `Node`→`Rc` clone, borrowed `Value`→clone).
    /// Lets a `&mut KnowledgeBase` walker (e.g. the guard engine reading a
    /// `LogicalQuery` through [`TermView`]) own each structural child without
    /// holding a borrow of the parent across a mutating call.
    pub fn to_value(&self) -> Value {
        match self {
            ViewItem::Term(t) => Value::term(*t),
            ViewItem::Value(v) => (*v).clone(),
            ViewItem::Node(occ) => Value::Node(Rc::clone(occ)),
        }
    }
}

// ── Occurrence views (WI-276) ──────────────────────────────────
//
// `Value::Node` / `ViewItem::Node` expose a reflect `Expr` occurrence to the
// matcher. The Apply / Constructor / DotApply / ListLit / leaf forms are
// structural — those a `[simp]` rule LHS matches — as are `Lambda` and the
// Pattern-kind occurrences it binds (WI-814: `head()` also backs IDENTITY and
// GoalKey fingerprints, where `Opaque` is a false negative, and WI-550's
// globally-unique binder gensyms make descending under the binder capture-free).
// The remaining control-flow / post-elaboration forms (Match / If / Let /
// *Within / …) stay `Opaque`.

// ── DotApply ↔ `dot_apply` term isomorphism (WI-425) ────────────
//
// A DotApply occurrence reads byte-identically to the term twin the loader
// emits for the same `r.name(args)` — `dot_apply(receiver, name,
// args: List[ApplyArg])`, always arity-3 named, `args = nil` for a bare field
// access (load.rs `LoadBuildFrame::DotApply` / `convert_term`'s dot_apply
// re-encode). Same head, same named keys in the same (builder slice) order,
// same `args` list structure — so the two carriers produce identical discrim
// keys and a fact stored under one carrier matches a query in the other
// (discrim-query-is-the-unifier: a cross-carrier miss is a wrong answer).

/// A field key of a reflect form's term twin, panicking if it was never
/// interned: any KB holding such an occurrence interned every one of that
/// form's keys when the loader built the occurrence's term twin (`ExprSyms`),
/// so a miss is an inconsistent KB — and silently dropping a key would desync
/// `named_keys` from `head`'s `named_arity` and mis-depth a discrim walk.
///
/// ONE owner for the whole file's field-key reads (`form` names the twin in the
/// message): the DotApply, VarRef and WI-814 Lambda/Pattern arms all resolve
/// keys the same way, and each restating the panic invited them to drift.
fn reflect_field_key(kb: &KnowledgeBase, k: &str, form: &str) -> Symbol {
    kb.lookup_symbol(k).unwrap_or_else(|| {
        panic!(
            "{form} view: field key `{k}` not interned — KB holds a \
             {form} occurrence but never built a {form} term twin"
        )
    })
}

/// A reflect/prelude CONSTRUCTOR symbol a view arm synthesizes a child from,
/// panicking for the same reason as [`reflect_field_key`]: the occurrence
/// exists, so its twin's constructors were resolved when the loader built it.
fn reflect_ctor_sym(kb: &KnowledgeBase, qname: &str, form: &str) -> Symbol {
    kb.try_resolve_symbol(qname).unwrap_or_else(|| {
        panic!(
            "{form} view: `{qname}` unresolved — KB holds a {form} \
             occurrence but never built a {form} term twin"
        )
    })
}

fn dot_apply_key(kb: &KnowledgeBase, k: &str) -> Symbol {
    reflect_field_key(kb, k, "dot_apply")
}

/// A synthesized constructor-occurrence child, carrying the parent's span and
/// owner. Every view arm that must present a term twin's *wrapper* node — an
/// `ApplyArg`, a `cons`/`nil` cell, an `Option.some`/`none`, a `NamedPattern` —
/// builds it through here, so the wrappers are shaped identically across arms.
/// `from_projection: false`: a synthesized wrapper is never the `.( )`
/// desugaring's tuple (WI-762).
fn synth_ctor(
    occ: &NodeOccurrence,
    name: Symbol,
    named: Vec<(Symbol, Rc<NodeOccurrence>)>,
) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(
        Expr::Constructor { name, pos_args: Vec::new(), named_args: named, from_projection: false },
        occ.span,
        occ.owner,
    )
}

/// Synthesize a DotApply occurrence's `args` child — the `List[ApplyArg]`
/// occurrence mirroring the loader's `mk_apply_arg` + `build_list` encoding:
/// a positional call arg rides as `ApplyArg(name: none(), value: …)`, a named
/// one as `ApplyArg(name: some(value: Ref(k)), value: …)`, on a cons/nil
/// spine over the prelude List constructors. The arg-value children are the
/// existing occurrences (shared `Rc`s); only the spine is fresh per call —
/// same cost class as the `name` child's synthesized `Ref`. Panics on an
/// unresolvable constructor for the same reason as [`dot_apply_key`].
///
/// NOT `build_occurrence_cons_list`: that helper follows the bare-pattern
/// convention — nullary `nil` as an `Expr::Ref` leaf, matching how a bare
/// `nil` in source loads (`Term::Ref`) — whereas the dot_apply term twin's
/// `build_list` emits a nullary `Fn{nil}`, which reads as a `Functor` head.
/// Reusing it would re-open exactly the cross-carrier key divergence this
/// function exists to close (the Ref ≡ nullary-Fn identification is WI-436).
fn dot_apply_args_child(
    occ: &NodeOccurrence,
    kb: &KnowledgeBase,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Rc<NodeOccurrence> {
    let resolve = |q: &str| reflect_ctor_sym(kb, q, "dot_apply");
    let cons = resolve("anthill.prelude.List.cons");
    let nil = resolve("anthill.prelude.List.nil");
    let some = resolve("anthill.prelude.Option.some");
    let none = resolve("anthill.prelude.Option.none");
    let apply_arg = resolve("anthill.reflect.ApplyArg");
    let (k_head, k_tail) = (dot_apply_key(kb, "head"), dot_apply_key(kb, "tail"));
    let (k_name, k_value) = (dot_apply_key(kb, "name"), dot_apply_key(kb, "value"));
    let mk = |name: Symbol, named: Vec<(Symbol, Rc<NodeOccurrence>)>| {
        synth_ctor(occ, name, named)
    };
    let none_occ = mk(none, Vec::new());
    let mut items: Vec<Rc<NodeOccurrence>> =
        Vec::with_capacity(pos_args.len() + named_args.len());
    for value in pos_args {
        items.push(mk(
            apply_arg,
            vec![(k_name, Rc::clone(&none_occ)), (k_value, Rc::clone(value))],
        ));
    }
    for (arg_sym, value) in named_args {
        let name_ref = NodeOccurrence::new_expr(Expr::Ref(*arg_sym), occ.span, occ.owner);
        let some_occ = mk(some, vec![(k_value, name_ref)]);
        items.push(mk(apply_arg, vec![(k_name, some_occ), (k_value, Rc::clone(value))]));
    }
    let mut list = mk(nil, Vec::new());
    for item in items.into_iter().rev() {
        list = mk(cons, vec![(k_head, item), (k_tail, list)]);
    }
    list
}

// ── VarRef ↔ `var_ref(name)` term isomorphism (WI-537) ──────────
//
// A `let` / lambda / op-param binder reference is an `Expr::VarRef { name }`,
// whose reflect term twin is `var_ref(name: Ref(name))` (`reflect.anthill`:
// `entity var_ref(name: Symbol)`; `build_expr_leaf` reads that `Fn{var_ref}`
// back to `Expr::VarRef`). So — exactly like DotApply ↔ `dot_apply` above — the
// occurrence reads with head `Functor{var_ref}` and one named child `name`
// (a synthesized `Ref`), NOT as a bare `Ident` (which would conflate the
// distinct `var_ref` and `ident` reflect forms) and NOT as `Opaque` (which made
// a Γ fact over a binder non-indexable, so silently dropped by
// `view_is_indexable`).

/// The `ListLiteral` functor symbol, or `None` when reflect isn't loaded — the
/// occurrence then reads `Opaque` (fail-soft: such a KB holds no reflect list
/// literal). WI-683: a `[…]` list-literal occurrence reads STRUCTURALLY as its
/// `ListLiteral(e…)` term twin (`occurrence_to_term` builds exactly that
/// `Fn{anthill.reflect.ListLiteral, pos_args: e…}`), so a carrier-neutral reader
/// — the bounded-quant collection walk, a `[simp]` LHS — walks a list literal in
/// ANY carrier, instead of the former `Opaque` collapse that forced a lowering.
fn list_literal_functor(kb: &KnowledgeBase) -> Option<Symbol> {
    kb.try_resolve_symbol("anthill.reflect.ListLiteral")
}

// ── Lambda ↔ `lambda_expr` term isomorphism (WI-814) ────────────
//
// A `lambda p -> e` occurrence reads byte-identically to the term twin the
// loader emits for the same source: `LoadBuildFrame::Lambda` (load.rs) allocs
// `Fn{anthill.reflect.Expr.lambda_expr, named: [param, body]}` — 0 positional,
// 2 named, in that builder order — alongside the occurrence it builds from the
// same parse node. So the twin is not invented here; it already existed, and
// `Expr::Lambda` merely stopped reading as `Opaque`.
//
// WHY THE OPACITY WAS NOT LOAD-BEARING. `head()` is read by three consumers,
// and the binder question lands differently on each:
//
//  - MATCHING (discrim insert/query, `match_view`). Descending under a binder is
//    unsound only where two distinct binders can share a name, because then a
//    substitution can CAPTURE. They cannot here: WI-550 mints every binder symbol
//    through `intern_unique`, memoized on the binder's PARSE-NODE id (load.rs),
//    so a binder symbol is globally unique by construction and a `var_ref` names
//    exactly one binder. That is Barendregt's convention enforced at the producer,
//    which is what makes the descent capture-free — NOT the `Opaque` collapse,
//    which merely declined to look. (The DeBruijn arms in `discrim.rs` and
//    `resolve.rs`'s `unify_match_values` stay the second line of defence: a
//    `Var::DeBruijn` reached inside a body still keys as an inert var-edge and
//    still refuses to bind.)
//  - IDENTITY (`views_structurally_equal`). `Opaque` has no `(Opaque, Opaque)`
//    arm, so it answered FALSE for two lambdas — including a lambda and itself.
//    Correct as a matching predicate, a false negative as an identity test; this
//    is what blocked WI-762's receiver-divergence guard.
//  - FINGERPRINT (`goal_fingerprint`/`GoalKey`). `Opaque` is payload-free, so it
//    made a lambda-bearing goal both non-cacheable and OVER-deduped in
//    `seen_goals` (two answers differing only inside a lambda collapsed to one
//    key and the second was dropped). Structural tokens fix both.
//
// ALPHA-EQUIVALENCE — the view is SYNTACTIC, deliberately. Two lambdas compare
// equal iff their binder SYMBOLS and bodies match, so `lambda x -> x` and
// `lambda y -> y` written independently are UNEQUAL (WI-550 gives them distinct
// gensyms), while the N copies `convert.rs`'s distribute-dot makes of ONE source
// receiver are EQUAL (they share the parse node, hence the gensym) — which is
// exactly what WI-762's guard needs. Making the view alpha-aware would require
// normalizing binder symbols de-Bruijn-style HERE, and that is the wrong place:
// the view's whole contract is that it reads what the term twin reads, and the
// twin is a hash-consed `Fn{lambda_expr, param: Ref(gensym), …}` compared by
// structure, not up to alpha. An alpha-aware view would DISAGREE with its own
// twin — a cross-carrier miss, which is a wrong answer, not a precision loss
// (WI-425). Alpha-equivalence is a relation over both carriers; if it is ever
// wanted it belongs beside `views_structurally_equal`, not inside `head()`.

// ── The reflect-WRAPPED `Expr` forms (WI-814) ───────────────────
//
// READ THIS BEFORE ADDING AN ARM. An `Expr` occurrence is born on one of TWO
// paths that emit DIFFERENT terms for the same source, and the loader says so
// itself ("the children differ on purpose … Do NOT 'unify' the two paths",
// `load.rs`, `convert_term`):
//
//   A. an OPERATION / CONST BODY (`convert_expr_term`) → a reflect-WRAPPED term:
//      `f(a, b)` becomes `Fn{Expr.apply, fn: Ref(f), args: List[ApplyArg]}`.
//   B. a FACT / RULE HEAD / RULE BODY (`convert_term` → `materialize_from_handle`)
//      → the DIRECT term `Fn{f, a, b}`.
//
// `occ_head` is faithful to B for `Apply` / `Constructor` / `Const` (an
// `Expr::Apply` heads as `Functor{f, pos, named}`, its DIRECT spelling) and to A
// for the forms in the table below. That split is not arbitrary: the forms below
// EXIST ONLY ON PATH A — there is no direct-term spelling of an `if` or a
// `lambda` — so for them "the term twin" is unambiguous. `Apply`/`Constructor`/
// `Const` are provenance-overloaded and a single head can only be right for one
// provenance; which one they should read is a separate question and NOT settled
// here (see the note at the `_ => Opaque` arm).
//
// The table is the SINGLE owner of each form's functor and named keys, so
// `head`'s `named_arity` and `named_keys`' list cannot disagree — the desync
// `reflect_field_key`'s panic exists to catch, here made structurally
// impossible. Keys are in the loader's BUILDER SLICE order, not sorted: the
// discrim walk descends in `named_keys` order, so matching the term's stored
// order is what keeps a term-side insert and an occurrence-side query in
// lockstep.

/// A shape table's key list must be DUPLICATE-FREE. Checked, not assumed,
/// because [`views_structurally_equal`] compares using only ONE side's keys:
/// it iterates `a.named_keys` and looks each up in `b`, concluding the key SETS
/// are identical from `named_arity` equality plus `keys(a) ⊆ keys(b)`. That
/// inference is a cardinality argument — |keys(a)| = na = nb = |keys(b)| — and
/// it collapses the moment `keys(a)` repeats a name: `b` could then carry an
/// extra key that is never compared, and two structurally DIFFERENT views would
/// answer EQUAL.
///
/// It is the same failure the duplicate-label rules already refuse at their own
/// producers — a repeated label leaves a component reachable by neither name nor
/// position, so it is never checked (WI-805 tuples, WI-808 entity fields, WI-809
/// named args). Those guard what an AUTHOR writes; this guards what the shape
/// table declares, which no parser sees. Debug-only: the lists are static, so a
/// violation is a source bug caught the first time the arm is exercised, not a
/// runtime condition.
fn debug_assert_keys_distinct(qname: &str, keys: &[&str]) {
    debug_assert!(
        keys.iter().enumerate().all(|(i, k)| !keys[..i].contains(k)),
        "shape table for `{qname}` repeats a key in {keys:?} — \
         `views_structurally_equal` compares only one side's keys, so a repeat \
         lets an uncompared child on the other side pass as equal",
    );
}

/// The path-A reflect twin of `expr`: functor qualified name + named keys in
/// builder order. `None` for a form that is not reflect-wrapped (path B, a leaf,
/// or still `Opaque`).
fn expr_wrapped_shape(expr: &Expr) -> Option<(&'static str, &'static [&'static str])> {
    let shape = expr_wrapped_shape_inner(expr)?;
    debug_assert_keys_distinct(shape.0, shape.1);
    Some(shape)
}

fn expr_wrapped_shape_inner(expr: &Expr) -> Option<(&'static str, &'static [&'static str])> {
    Some(match expr {
        // WI-278 / WI-397 / WI-425 — always arity-3, `args = nil` for a bare
        // field access.
        Expr::DotApply { .. } => {
            ("anthill.reflect.Expr.dot_apply", &["receiver", "name", "args"])
        }
        // WI-537.
        Expr::VarRef { .. } => ("anthill.reflect.Expr.var_ref", &["name"]),
        // WI-814 — `LoadBuildFrame::Lambda`.
        Expr::Lambda { .. } => ("anthill.reflect.Expr.lambda_expr", &["param", "body"]),
        // WI-814 — `LoadBuildFrame::IfExpr`. Binds nothing at all; it was opaque
        // only because no `[simp]` LHS had ever needed it.
        Expr::If { .. } => {
            ("anthill.reflect.Expr.if_expr", &["cond", "then_branch", "else_branch"])
        }
        // WI-814 — `LoadBuildFrame::LetExpr`, exactly THREE keys, unconditionally.
        //
        // `Expr::Let.type_annotation` is NOT among them, and that is now exact
        // rather than lossy: WI-342 deleted the term-side `type_name` slot as
        // write-only, and WI-814 finished the deletion — the reflect field and
        // `visit_fn`'s reader are gone too, so no `let_expr` term anywhere can
        // carry an annotation. A conditional 4th key would describe a term shape
        // that no longer exists.
        //
        // What this means for identity, stated because it is real: two `let`s
        // differing ONLY in their annotation compare structurally EQUAL through
        // this view. The annotation is genuinely absent from the term carrier,
        // so any view that distinguished them would disagree with the term — a
        // cross-carrier miss, which is a wrong answer (WI-425). A consumer that
        // needs annotations in an identity test must read
        // `Let.type_annotation` off the occurrence directly, its sole carrier.
        //
        // AND THAT IS FIXABLE, so do not read the loss as permanent: WI-390 gave
        // a denoted-bearing type a faithful hash-consed twin (`value_to_term`
        // lowers a `Value::Node` type losslessly through `occurrence_to_term`),
        // so the annotation CAN be restored to the `let_expr` term and to this
        // key list. The older "a denoted type cannot be hash-consed" reasoning is
        // out of date and must not be repeated here.
        Expr::Let { .. } => ("anthill.reflect.Expr.let_expr", &["pattern", "value", "body"]),
        // WI-814 — `LoadBuildFrame::ProofStmt`, in its push order
        // `target, strategy?, using, body, conclude?`.
        //
        // `using` IS here because WI-814 put it on the TERM, which is where the
        // defect was. It had been withheld as "citation metadata, not a child",
        // and that was wrong: `proof Y using X` and `proof Y using Z` are
        // DIFFERENT proofs, because the premise set differs. A carrier omitting
        // it does not represent proofs — it is INCOMPLETE, not merely smaller —
        // so every consumer reading the term as a proof's identity conflated two
        // distinct proofs. The fix belonged in the loader, NOT in a view that
        // diverges from its term: carrier-neutral comparison presupposes the
        // carriers hold the SAME INFORMATION, so the repair is to make them
        // equivalent, never to truncate the complete one or to enrich only the
        // view. Always present as a possibly-`nil` list (the `dot_apply.args`
        // precedent) — a proof always has a premise set; it may be empty.
        //
        // `strategy` / `conclude` stay CONDITIONAL because the term pushes them
        // conditionally; that is a faithful mirror, not a loss — an absent key
        // and a `none()` payload carry the same information, and the arity
        // difference keeps the two shapes distinct on both carriers.
        Expr::Proof { strategy, conclude, .. } => (
            "anthill.reflect.Expr.proof_stmt",
            match (strategy.is_some(), conclude.is_some()) {
                (false, false) => &["target", "using", "body"],
                (true, false) => &["target", "strategy", "using", "body"],
                (false, true) => &["target", "using", "body", "conclude"],
                (true, true) => &["target", "strategy", "using", "body", "conclude"],
            },
        ),
        // WI-814 — `LoadBuildFrame::MatchExpr`; `branches` is a `List[MatchBranch]`
        // cons/nil spine (see [`match_branches_child`]).
        Expr::Match { .. } => ("anthill.reflect.Expr.match_expr", &["scrutinee", "branches"]),
        _ => return None,
    })
}

/// `expr`'s reflect-wrapped head, or `None` when the form is not wrapped or
/// reflect isn't loaded (the caller then falls through to the direct-form arms /
/// `Opaque` — fail-soft, as such a KB holds no loader-built occurrence of it).
fn wrapped_expr_head(expr: &Expr, kb: &KnowledgeBase) -> Option<ViewHead> {
    let (qname, keys) = expr_wrapped_shape(expr)?;
    let f = kb.try_resolve_symbol(qname)?;
    Some(ViewHead::Functor { functor: Some(f), pos_arity: 0, named_arity: keys.len() })
}

/// `expr`'s reflect-wrapped named keys, in builder order — empty when the form
/// is not wrapped or reflect isn't loaded (consistent with the `Opaque` head
/// [`wrapped_expr_head`] then yields).
fn wrapped_expr_keys(expr: &Expr, kb: &KnowledgeBase) -> Vec<Symbol> {
    let Some((qname, keys)) = expr_wrapped_shape(expr) else { return Vec::new() };
    if kb.try_resolve_symbol(qname).is_none() {
        return Vec::new();
    }
    let form = qname.rsplit('.').next().unwrap_or(qname);
    keys.iter().map(|k| reflect_field_key(kb, k, form)).collect()
}

/// The named child `sym` of a reflect-WRAPPED form, mirroring the child the
/// loader puts in that slot. Sub-expression children are the EXISTING
/// occurrences (shared `Rc`s); leaves (`Ref`) and wrappers (`ApplyArg` /
/// `MatchBranch` / `Option` / cons cells) are synthesized per call, the same
/// cost class as `DotApply`'s `name` child.
///
/// `sym` is matched back to its NAME in [`expr_wrapped_shape`]'s key slice, and
/// the arms below dispatch on `(variant, name)`. By NAME, not by position:
/// `Let` and `Proof` have CONDITIONAL keys, so a position would mean different
/// fields for different occurrences of the same variant. Adding a key without an
/// arm for it is what the `debug_assert` catches.
fn wrapped_expr_child(
    occ: &NodeOccurrence,
    expr: &Expr,
    kb: &KnowledgeBase,
    sym: Symbol,
) -> Option<Rc<NodeOccurrence>> {
    let (qname, names) = expr_wrapped_shape(expr)?;
    // Reflect not loaded ⇒ head reads `Opaque`, so this yields no children too.
    kb.try_resolve_symbol(qname)?;
    // Resolved lazily and short-circuited rather than through `wrapped_expr_keys`,
    // which allocates a `Vec<Symbol>` — this runs once per named-child access on
    // the discrim / `views_structurally_equal` / `goal_fingerprint` paths, so the
    // allocation was pure waste (the code this replaced used a stack array).
    let form = qname.rsplit('.').next().unwrap_or(qname);
    let idx = names.iter().position(|k| reflect_field_key(kb, k, form) == sym)?;
    let name = names[idx];
    let leaf = |e: Expr| NodeOccurrence::new_expr(e, occ.span, occ.owner);
    Some(match (expr, name) {
        (Expr::DotApply { receiver, .. }, "receiver") => Rc::clone(receiver),
        (Expr::DotApply { name: m, .. }, "name") => leaf(Expr::Ref(*m)),
        (Expr::DotApply { pos_args, named_args, .. }, "args") => {
            dot_apply_args_child(occ, kb, pos_args, named_args)
        }
        (Expr::VarRef { name: n }, "name") => leaf(Expr::Ref(*n)),
        (Expr::Lambda { param, .. }, "param") => Rc::clone(param),
        (Expr::Lambda { body, .. }, "body") => Rc::clone(body),
        (Expr::If { condition, .. }, "cond") => Rc::clone(condition),
        (Expr::If { then_branch, .. }, "then_branch") => Rc::clone(then_branch),
        (Expr::If { else_branch, .. }, "else_branch") => Rc::clone(else_branch),
        (Expr::Let { pattern, .. }, "pattern") => Rc::clone(pattern),
        (Expr::Let { value, .. }, "value") => Rc::clone(value),
        (Expr::Let { body, .. }, "body") => Rc::clone(body),
        // `Ident`, NOT `Ref` — `LoadBuildFrame::ProofStmt` spells both the
        // proof target and the strategy as `Term::Ident`, and a synthesized
        // `Ref` would head as `ViewHead::Ref` against the term's `Ident`.
        (Expr::Proof { target, .. }, "target") => leaf(Expr::Ident(*target)),
        (Expr::Proof { strategy: Some(s), .. }, "strategy") => leaf(Expr::Ident(*s)),
        // The premise set, as the `List[Ident]` the loader now emits.
        (Expr::Proof { using, .. }, "using") => {
            let cites = using.iter().map(|s| leaf(Expr::Ident(*s))).collect();
            synth_cons_list(occ, kb, cites)
        }
        (Expr::Proof { body, .. }, "body") => Rc::clone(body),
        (Expr::Proof { conclude: Some(c), .. }, "conclude") => Rc::clone(c),
        (Expr::Match { scrutinee, .. }, "scrutinee") => Rc::clone(scrutinee),
        (Expr::Match { branches, .. }, "branches") => match_branches_child(occ, kb, branches),
        _ => {
            debug_assert!(
                false,
                "wrapped_expr_child: key `{name}` of {qname} has no child arm — \
                 `expr_wrapped_shape` declared a key this function does not build, \
                 which desyncs `named_keys` from the children a discrim walk reads",
            );
            return None;
        }
    })
}

/// Synthesize a Match occurrence's `branches` child — the `List[MatchBranch]`
/// spine mirroring `LoadBuildFrame::MatchBranch`: each cell is
/// `MatchBranch(pattern, guard, body)` with `guard` ALWAYS present as
/// `some(g)`/`none()` (unlike `constructor_pattern`'s `named`, which the twin
/// omits when empty). `pattern` is the branch's Pattern-kind occurrence, which
/// reads through the WI-814 Pattern arms.
fn match_branches_child(
    occ: &NodeOccurrence,
    kb: &KnowledgeBase,
    branches: &[MatchBranch],
) -> Rc<NodeOccurrence> {
    let branch_sym = reflect_ctor_sym(kb, "anthill.reflect.MatchBranch", "match_expr");
    let (k_pattern, k_guard, k_body) = (
        reflect_field_key(kb, "pattern", "match_expr"),
        reflect_field_key(kb, "guard", "match_expr"),
        reflect_field_key(kb, "body", "match_expr"),
    );
    let cells = branches
        .iter()
        .map(|b| {
            synth_ctor(
                occ,
                branch_sym,
                vec![
                    (k_pattern, Rc::clone(&b.pattern)),
                    (k_guard, synth_option(occ, kb, b.guard.as_ref().map(Rc::clone))),
                    (k_body, Rc::clone(&b.body)),
                ],
            )
        })
        .collect();
    synth_cons_list(occ, kb, cells)
}

// ── Pattern ↔ reflect `Pattern` term isomorphism (WI-814) ───────
//
// Reached BECAUSE `Expr::Lambda` became structural: `param` is a Pattern-kind
// occurrence, and a `Functor` head over an `Opaque` child is worse than no head
// at all — `views_structurally_equal` would answer false on every lambda (the
// gap this ticket exists to close) and `GoalKey` would keep the `Opaque` token
// that makes the goal non-cacheable. So the head and its children land together.
//
// The twin is `pattern_to_term` (`node_occurrence.rs`), which `try_occurrence_to_term`
// already routes to — i.e. the `TermId` carrier of a pattern has been fully
// structural all along while the occurrence carrier read `Opaque`. This closes a
// CARRIER ASYMMETRY, it does not invent a representation.
//
// Every variant is 0-positional; `wildcard` is nullary and therefore reads as
// `ViewHead::Ref` through `functor_view_head` on BOTH carriers (WI-436).
//
// LOSSY, IDENTICALLY ON BOTH CARRIERS: `Pattern::Tuple.labels` has nowhere to go
// in the reflect surface (`entity tuple_pattern(elements: List[Pattern])`), so
// `pattern_to_term` drops it — see the WI-803 "KNOWN LOSSY AND UNCOVERED" note at
// that arm. This view drops it too, and must: diverging would make a labelled
// tuple pattern key differently in the two carriers, and a cross-carrier miss is
// a wrong answer (WI-425) — strictly worse than the shared imprecision, which is
// a defect of the reflect surface and is tracked at the site that drops it. The
// consequence to know: `lambda (a: x, b: y) -> e` and `lambda (x, y) -> e`
// compare structurally EQUAL.

/// Pattern-variant metadata: the twin's functor qualified name and its named
/// keys IN BUILDER ORDER (`pattern_to_term`). One table so `pattern_head`'s
/// arity and `pattern_named_keys`' list can never disagree — the desync
/// `reflect_field_key`'s panic exists to prevent, here made structural.
/// `Constructor`'s `named` key is present only when non-empty, exactly as the
/// twin omits it "keeping the positional form byte-identical".
fn pattern_shape(pat: &Pattern) -> (&'static str, &'static [&'static str]) {
    let shape = pattern_shape_inner(pat);
    debug_assert_keys_distinct(shape.0, shape.1);
    shape
}

fn pattern_shape_inner(pat: &Pattern) -> (&'static str, &'static [&'static str]) {
    match pat {
        Pattern::Var { .. } => ("anthill.reflect.Pattern.var_pattern", &["name", "type_ann"]),
        Pattern::Wildcard => ("anthill.reflect.Pattern.wildcard", &[]),
        Pattern::Literal { .. } => ("anthill.reflect.Pattern.literal_pattern", &["value"]),
        Pattern::Constructor { named_args, .. } => (
            "anthill.reflect.Pattern.constructor_pattern",
            if named_args.is_empty() { &["name", "args"] } else { &["name", "args", "named"] },
        ),
        Pattern::Tuple { .. } => ("anthill.reflect.Pattern.tuple_pattern", &["elements"]),
    }
}

fn pattern_head(pat: &Pattern, kb: &KnowledgeBase) -> ViewHead {
    let (qname, keys) = pattern_shape(pat);
    match kb.try_resolve_symbol(qname) {
        Some(f) => functor_view_head(kb, f, 0, keys.len()),
        // Reflect not loaded ⇒ no pattern twin exists in this KB (fail-soft,
        // mirroring the wrapped-form arms); its children then read none, which is
        // consistent with this head.
        None => ViewHead::Opaque,
    }
}

fn pattern_named_keys(pat: &Pattern, kb: &KnowledgeBase) -> Vec<Symbol> {
    let (qname, keys) = pattern_shape(pat);
    if kb.try_resolve_symbol(qname).is_none() {
        return Vec::new();
    }
    keys.iter().map(|k| reflect_field_key(kb, k, "pattern")).collect()
}

/// A cons/nil spine of occurrences over the prelude List constructors, mirroring
/// `build_list_termid` (the `pattern_to_term` list builder). NOT
/// `build_occurrence_cons_list`, for the reason spelled out on
/// [`dot_apply_args_child`]: that helper emits `nil` as a bare `Expr::Ref`,
/// while the term twin emits a nullary `Fn{nil}`.
fn synth_cons_list(
    occ: &NodeOccurrence,
    kb: &KnowledgeBase,
    items: Vec<Rc<NodeOccurrence>>,
) -> Rc<NodeOccurrence> {
    let cons = reflect_ctor_sym(kb, "anthill.prelude.List.cons", "pattern");
    let nil = reflect_ctor_sym(kb, "anthill.prelude.List.nil", "pattern");
    let (k_head, k_tail) =
        (reflect_field_key(kb, "head", "pattern"), reflect_field_key(kb, "tail", "pattern"));
    let mut acc = synth_ctor(occ, nil, Vec::new());
    for item in items.into_iter().rev() {
        acc = synth_ctor(occ, cons, vec![(k_head, item), (k_tail, acc)]);
    }
    acc
}

/// `some(value: inner)` / `none()` as occurrences, mirroring `build_some` /
/// `build_none`.
fn synth_option(
    occ: &NodeOccurrence,
    kb: &KnowledgeBase,
    inner: Option<Rc<NodeOccurrence>>,
) -> Rc<NodeOccurrence> {
    match inner {
        Some(v) => {
            let some = reflect_ctor_sym(kb, "anthill.prelude.Option.some", "pattern");
            synth_ctor(occ, some, vec![(reflect_field_key(kb, "value", "pattern"), v)])
        }
        None => {
            let none = reflect_ctor_sym(kb, "anthill.prelude.Option.none", "pattern");
            synth_ctor(occ, none, Vec::new())
        }
    }
}

/// The named child `sym` of a Pattern-kind occurrence, mirroring the child
/// `pattern_to_term` builds for the same key. Sub-pattern children are the
/// EXISTING occurrences (shared `Rc`s, themselves Pattern-kind and so viewed
/// through these same arms); only leaves (`Ref`/`Const`) and wrappers
/// (`Option`/`cons`/`NamedPattern`) are synthesized, as in
/// [`dot_apply_args_child`].
fn pattern_named_child(
    occ: &NodeOccurrence,
    pat: &Pattern,
    kb: &KnowledgeBase,
    sym: Symbol,
) -> Option<Rc<NodeOccurrence>> {
    let (qname, names) = pattern_shape(pat);
    kb.try_resolve_symbol(qname)?; // reflect not loaded ⇒ head reads Opaque (no children)
    // Located by NAME via the shape table, mirroring `wrapped_expr_child` — so
    // the two halves of the WI-814 view share one dispatch shape, and a key with
    // no arm is caught by the same tripwire rather than silently yielding `None`.
    // `Wildcard` declares no keys, so it exits here without needing an arm.
    let idx = names.iter().position(|k| reflect_field_key(kb, k, "pattern") == sym)?;
    let name = names[idx];
    let leaf = |e: Expr| NodeOccurrence::new_expr(e, occ.span, occ.owner);
    Some(match (pat, name) {
        (Pattern::Var { name: n, .. }, "name") => leaf(Expr::Ref(*n)),
        (Pattern::Var { type_ann, .. }, "type_ann") => {
            synth_option(occ, kb, type_ann.as_ref().map(Rc::clone))
        }
        (Pattern::Literal { value }, "value") => leaf(Expr::Const(value.clone())),
        (Pattern::Constructor { name: n, .. }, "name") => leaf(Expr::Ref(*n)),
        (Pattern::Constructor { pos_args, .. }, "args") => {
            synth_cons_list(occ, kb, pos_args.to_vec())
        }
        // Declared by `pattern_shape` only when non-empty, exactly as the twin
        // omits it — so this arm is unreachable for the all-positional form.
        (Pattern::Constructor { named_args, .. }, "named") => {
            let named_pattern = reflect_ctor_sym(kb, "anthill.reflect.NamedPattern", "pattern");
            let (k_name, k_pattern) = (
                reflect_field_key(kb, "name", "pattern"),
                reflect_field_key(kb, "pattern", "pattern"),
            );
            let items = named_args
                .iter()
                .map(|(field, sub)| {
                    synth_ctor(
                        occ,
                        named_pattern,
                        vec![(k_name, leaf(Expr::Ref(*field))), (k_pattern, Rc::clone(sub))],
                    )
                })
                .collect();
            synth_cons_list(occ, kb, items)
        }
        // `labels` is dropped — see the LOSSY note above (WI-803 / WI-819).
        (Pattern::Tuple { positional, .. }, "elements") => {
            synth_cons_list(occ, kb, positional.to_vec())
        }
        _ => {
            debug_assert!(
                false,
                "pattern_named_child: key `{name}` of {qname} has no child arm — \
                 `pattern_shape` declared a key this function does not build, which \
                 desyncs `named_keys` from the children a discrim walk reads, and \
                 makes the pattern compare unequal to ITSELF",
            );
            return None;
        }
    })
}

fn occ_head(occ: &NodeOccurrence, kb: &KnowledgeBase) -> ViewHead {
    // WI-342: a Value-carried Type / EffectExpression occurrence reads through
    // the same `ViewHead::Functor` as its hash-consed `Term::Fn` twin, so a
    // carrier-blind walker (resolver `match_view` today; the typer's
    // `unify_types` after P3) sees identical structure regardless of carrier.
    if let Some(tn) = occ.as_type() {
        return type_node_head(tn, kb);
    }
    if let Some(en) = occ.as_effect_expr() {
        return effect_expr_head(en, kb);
    }
    // WI-814: a Pattern-kind occurrence reads as its `pattern_to_term` twin —
    // the carrier asymmetry that made a lambda's `param` child `Opaque`.
    if let Some(pat) = occ.as_pattern() {
        return pattern_head(pat, kb);
    }
    // WI-814: the reflect-WRAPPED forms (DotApply / VarRef / Lambda / If / Let /
    // Match) read as the path-A term twin the loader emits — one table owns
    // functor + keys, so arity and `named_keys` cannot drift apart.
    if let Some(expr) = occ.as_expr() {
        if let Some(head) = wrapped_expr_head(expr, kb) {
            return head;
        }
    }
    match occ.as_expr() {
        Some(Expr::Apply { functor, pos_args, named_args, .. }) => {
            functor_view_head(kb, *functor, pos_args.len(), named_args.len())
        }
        // WI-520: `Instantiation` (`Name{bindings}`) is shaped exactly like
        // `Constructor` and `occurrence_to_term` materializes BOTH via the same
        // `Term::Fn{name, …}` twin — so it reads the same `Functor` head (a
        // reflect-`Expr` instantiation occurrence must match its own term twin,
        // not collapse to `Opaque`).
        Some(Expr::Constructor { name, pos_args, named_args, .. })
        | Some(Expr::Instantiation { name, pos_args, named_args }) => {
            functor_view_head(kb, *name, pos_args.len(), named_args.len())
        }
        Some(Expr::Const(lit)) => ViewHead::Const(lit.clone()),
        // WI-714: a `Spliced` occurrence carries a structured `Value` (which
        // itself implements `TermView`) — present the value's head, never
        // `Opaque`. This is the mirror of the `Value::Node(occ) => occ_head(occ)`
        // delegation below: a value carrying an occurrence views through to the
        // occurrence, so an occurrence carrying a value views through to the value.
        Some(Expr::Spliced(v)) => v.head(kb),
        Some(Expr::Ref(s)) => ViewHead::Ref(*s),
        Some(Expr::Ident(s)) => ViewHead::Ident(*s),
        // A var of ANY kind surfaces its `Var` — the discrim tree keys a flex
        // `Global` / bound `DeBruijn` as a wildcard var-edge and a `Rigid`
        // skolem as a `RigidVar` constant (mirrors `TermIdView`/`Value`). The
        // goal-side anti-wildcard guard for rigids is now the constant-key match,
        // not an `Opaque` collapse.
        Some(Expr::Var(v)) => ViewHead::Var(*v),
        // WI-520: a concrete nullary leaf whose term twin is `Term::Bottom`
        // (`ViewHead::Bottom`) — not opaque.
        Some(Expr::Bottom) => ViewHead::Bottom,
        // WI-683: a `[…]` list literal reads as its `ListLiteral(e…)` term twin —
        // the elements are the positional children, no tail (`occurrence_to_term`
        // builds `Fn{ListLiteral, pos_args: e…}`). Through `functor_view_head`,
        // an empty `[]` and its `Fn{ListLiteral}` twin canonicalize to the same
        // head. Reflect-not-loaded ⇒ `Opaque` (no reflect list literal exists).
        Some(Expr::ListLit(es)) => match list_literal_functor(kb) {
            Some(f) => functor_view_head(kb, f, es.len(), 0),
            None => ViewHead::Opaque,
        },
        // WHAT IS STILL `Opaque`, AND WHY — each for a NAMED reason, not because
        // the arm is unwritten (WI-814 retired that catch-all reading):
        //
        //  - Rigid / DeBruijn vars and rule-head occurrences, as before.
        //  - The `*Within` family. Their TERM side is LIVE, not vestigial: the
        //    requirement-insertion pass (`req_insertion.rs`, WI-231) does rewrite
        //    a classified call to `apply_within` — but as a `Term::Fn` recorded in
        //    `kb.dispatch_rewrites` (`record_apply_within_concrete`, typing.rs),
        //    NOT as an occurrence. The occurrence stays `Expr::Apply` carrying its
        //    `CallClass` tag, which is what the runtime reads post-WI-248 ("the
        //    term-keyed redirect is now diagnostic-only"). So `Expr::ApplyWithin`
        //    is reached only by reading such a term BACK through `visit_fn`, and
        //    the occurrence↔term pair a head would keep in lockstep is not one the
        //    pipeline actually produces side by side. `HoApplyWithin` /
        //    `ConstructorWithin` / `LambdaWithin` go further: NOTHING constructs
        //    them, in either carrier. `LambdaWithin` is SUPERSEDED — NOT an
        //    "unimplemented gap", which would predict a failure nobody can
        //    reproduce. A lambda whose body calls a spec op ALREADY gets its
        //    dictionaries, by a different mechanism: WI-223 has `reduce_lambda`
        //    (`eval/eval.rs`) SNAPSHOT the enclosing `frame.requirements` into
        //    `Closure.requirements` at lambda-CONSTRUCTION time and restore them
        //    on invocation, so the requirement scope rides the closure VALUE and
        //    the IR node is not needed. Whether to FINISH that supersession
        //    (delete the variants) or REVERSE it is WI-816. Either way, a head
        //    here could not be tested against a producer.
        //  - `HoApply` / `RequirementAtSort` / `ConstructRequirement`:
        //    rebuild-only — `visit_fn` materializes them from terms nothing in
        //    the pipeline emits, so again there is no live pair to align.
        //  - `SetLit` / `TupleLit`: path-B siblings of `ListLit`. `TupleLit`
        //    especially is entangled with tuple IDENTITY (WI-788 order, WI-803
        //    labels, WI-805 distinctness), where a wrong key set is a wrong
        //    answer about type identity — not a place to guess.
        _ => ViewHead::Opaque,
    }
}

/// The logic variable at an occurrence's head, for discrimination-tree
/// *indexing* — `Expr::Var` of ANY kind (Global / Rigid / DeBruijn), the
/// occurrence twin of `TermIdView`'s `Term::Var(v) => Some(*v)` (WI-373). The
/// *index* side keys every binder kind as a distinct var-edge, so a stored value
/// rule head's De Bruijn vars index exactly like a term head's. (Goal-side,
/// [`occ_head`] now surfaces every var kind as `ViewHead::Var`; a rigid goal var
/// is kept from matching concrete keys not by an `Opaque` collapse but by the
/// discrim tree's `RigidVar` constant edge — see `discrim::DiscrimKey`.) `None`
/// for a non-`Var` head — the walk then keys on [`occ_head`].
fn occ_index_var(occ: &Rc<NodeOccurrence>) -> Option<Var> {
    match occ.as_expr() {
        Some(Expr::Var(v)) => Some(*v),
        _ => None,
    }
}

/// The i-th positional child occurrence of an Apply/Constructor occurrence.
/// Type / EffectExpression occurrences expose only named children (none
/// positional), so this is `None` for them.
fn occ_pos_child(occ: &NodeOccurrence, _kb: &KnowledgeBase, i: usize) -> Option<Rc<NodeOccurrence>> {
    match occ.as_expr()? {
        // WI-425: a DotApply has NO positional children — its call args live
        // inside the `args` named child, mirroring the term twin.
        Expr::Apply { pos_args, .. }
        | Expr::Constructor { pos_args, .. }
        // WI-520: `Instantiation` reads like `Constructor` — expose its children.
        | Expr::Instantiation { pos_args, .. } => pos_args.get(i).map(Rc::clone),
        // WI-683: a list literal's elements are its positional children, mirroring
        // the `Fn{ListLiteral, pos_args: e…}` term twin.
        Expr::ListLit(es) => es.get(i).map(Rc::clone),
        _ => None,
    }
}

/// The named child keyed by `sym` of an Apply/Constructor occurrence, or — for
/// a Value-carried Type / EffectExpression occurrence (WI-342) — the matching
/// named field. A poisoned `TypeChild::Node` child is itself a child
/// occurrence; a `TypeChild::Ground` child is a hash-consed `TermId`, which
/// `occ_named_child` cannot return as an `Rc<NodeOccurrence>` — Type/EffectExpr
/// callers go through [`type_node_named`] / [`effect_expr_named`] (returning a
/// `ViewItem`) instead. This `Rc`-returning helper stays Expr-only.
fn occ_named_child(occ: &NodeOccurrence, kb: &KnowledgeBase, sym: Symbol) -> Option<Rc<NodeOccurrence>> {
    // WI-814: a Pattern-kind occurrence's children mirror its `pattern_to_term`
    // twin (checked before `as_expr()`, which is `None` for a Pattern).
    if let Some(pat) = occ.as_pattern() {
        return pattern_named_child(occ, pat, kb, sym);
    }
    // WI-814: the reflect-WRAPPED forms expose exactly their twin's children.
    // A wrapped form NEVER falls through to the direct-form lookup below — its
    // `named_args` (a call's arguments) are not addressable at the top level;
    // they ride inside the twin's `args` list, as in the term.
    if let Some(expr) = occ.as_expr() {
        if expr_wrapped_shape(expr).is_some() {
            return wrapped_expr_child(occ, expr, kb, sym);
        }
    }
    let named = match occ.as_expr()? {
        Expr::Apply { named_args, .. }
        | Expr::Constructor { named_args, .. }
        // WI-520: `Instantiation` reads like `Constructor`.
        | Expr::Instantiation { named_args, .. } => named_args,
        _ => return None,
    };
    named.iter().find(|(s, _)| *s == sym).map(|(_, c)| Rc::clone(c))
}

fn occ_named_keys(occ: &NodeOccurrence, kb: &KnowledgeBase) -> Vec<Symbol> {
    if let Some(tn) = occ.as_type() {
        return type_node_keys(tn, kb);
    }
    if let Some(en) = occ.as_effect_expr() {
        return effect_expr_keys(en, kb);
    }
    // WI-814: a Pattern-kind occurrence's keys, in `pattern_to_term`'s builder
    // order (the discrim walk descends in this order).
    if let Some(pat) = occ.as_pattern() {
        return pattern_named_keys(pat, kb);
    }
    // WI-814: the reflect-WRAPPED forms' keys, from the same table `head`'s
    // `named_arity` counts — so the two cannot disagree.
    if let Some(expr) = occ.as_expr() {
        if expr_wrapped_shape(expr).is_some() {
            return wrapped_expr_keys(expr, kb);
        }
    }
    match occ.as_expr() {
        Some(Expr::Apply { named_args, .. })
        | Some(Expr::Constructor { named_args, .. })
        // WI-520: `Instantiation` reads like `Constructor`.
        | Some(Expr::Instantiation { named_args, .. }) => {
            named_args.iter().map(|(s, _)| *s).collect()
        }
        // Every reflect-WRAPPED form returned above, from the shape table.
        _ => Vec::new(),
    }
}

// ── Type / EffectExpression view arms (WI-342) ──────────────────
//
// These read a `Value`-carried Type / EffectExpression occurrence through the
// SAME functor + named-key surface as its `Term::Fn` twin. Functor symbols are
// resolved via the (immutable) qualified-name table; field keys via the bare
// intern table — the exact symbols the `make_*` `TermId` builders used, so the
// two carriers are indistinguishable through `TermView`.
//
// Rep A (collapse): `parameterized.bindings` (a `List[TypeBinding]` of generic
// entities) is NOT exposed through the generic named-key surface in this slice
// — it is read type-specifically (`as_type`) and its carrier-faithful generic
// view is deferred to P3 (where `unify_parameterized`-on-`TermView` drives it).
//
// DEFERRED TO P3 (decided): symbol resolution here is provisional. (1) The
// `format!` + table lookup runs per view call; (2) `type_node_head` /
// `effect_expr_head` report `named_arity` from a hardcoded count while
// `type_node_keys` / `effect_expr_keys` resolve keys via `lookup_symbol` and
// `filter_map`-drop any not-yet-interned key — so on a KB where a field key was
// never interned, `head` arity and `named_keys` can disagree (a discrim walk
// would then mis-depth). Neither bites this slice: the only caller is the
// producer↔view test on a `register_prelude`d KB where every field key is
// interned. P3 replaces all of this with a KB-cached `TypeSyms` (mirroring
// `ReflectSyms` below) resolved once at prelude time — one source of truth for
// functor + field-key symbols, no per-call alloc, no silent drop — validated by
// the first live consumer.

fn type_functor_sym(kb: &KnowledgeBase, short: &str) -> Option<Symbol> {
    kb.try_resolve_symbol(&format!("anthill.prelude.TypeExtractor.{short}"))
}

fn effect_functor_sym(kb: &KnowledgeBase, short: &str) -> Option<Symbol> {
    kb.try_resolve_symbol(&format!("anthill.prelude.EffectExpression.{short}"))
}

/// A `TypeChild` as a non-borrowing [`ViewItem`]: ground → `Term`, poisoned →
/// `Node` (a cheap `Rc` clone). Neither variant borrows from `child`, so the
/// returned item is free of the caller's borrow.
pub(crate) fn type_child_view_item<'a>(child: &TypeChild) -> ViewItem<'a> {
    match child {
        TypeChild::Ground(t) => ViewItem::Term(*t),
        TypeChild::Node(rc) => ViewItem::Node(Rc::clone(rc)),
    }
}

/// The base sort symbol of a `Parameterized` carrier's `base` child. WI-361: the
/// occurrence carrier mirrors the term-backed `Fn{S, named}`, so this symbol is
/// the view-head *functor* (no `parameterized` wrapper). A parameterized base is
/// always a concrete sort `Ref(S)` (spec gate: a type param "must be a concrete
/// type, not a type constructor"); anything else is malformed → `None`.
fn parameterized_base_functor(base: &TypeChild, kb: &KnowledgeBase) -> Option<Symbol> {
    match base {
        TypeChild::Ground(t) => match kb.get_term(*t) {
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            _ => None,
        },
        TypeChild::Node(_) => None,
    }
}

fn type_node_head(tn: &TypeNode, kb: &KnowledgeBase) -> ViewHead {
    let (functor, named_arity) = match tn {
        // WI-361: a parameterized type's occurrence carrier mirrors the term-backed
        // `Fn{S, named}` — its head functor IS the base sort and the named args ARE
        // the bindings (no `parameterized` wrapper), so `TermView` reads the carrier
        // and its term twin identically. The other forms are genuine structural
        // entities whose head functor is the form name.
        TypeNode::Parameterized { base, bindings } => {
            (parameterized_base_functor(base, kb), bindings.len())
        }
        TypeNode::Denoted { .. } => (type_functor_sym(kb, "Denoted"), 1),
        TypeNode::EffectsRows { .. } => (type_functor_sym(kb, "EffectsRows"), 1),
        // WI-791: four children — `arity` joined `param`/`result`/`effects`.
        TypeNode::Arrow { .. } => (type_functor_sym(kb, "Arrow"), 4),
        // WI-361: one `fields` child (a `Value`-carried `List[NamedTupleElement]`),
        // matching the term form `NamedTuple(fields: List[NamedTupleElement])`.
        TypeNode::NamedTuple { .. } => (type_functor_sym(kb, "NamedTuple"), 1),
        // WI-397: the Node carrier for a compound-receiver projection reads as the
        // same `ExprCarried(value, member)` head/arity as its single-ref term twin.
        TypeNode::ExprCarried { .. } => (type_functor_sym(kb, "ExprCarried"), 2),
    };
    match functor {
        Some(f) => ViewHead::Functor { functor: Some(f), pos_arity: 0, named_arity },
        None => ViewHead::Opaque,
    }
}

fn type_node_keys(tn: &TypeNode, kb: &KnowledgeBase) -> Vec<Symbol> {
    let short_keys: &[&str] = match tn {
        // Bindings ARE the named args (WI-361) — the keys are the binding params,
        // which come from terms (already interned), so return them directly.
        TypeNode::Parameterized { bindings, .. } => {
            return bindings.iter().map(|(s, _)| *s).collect();
        }
        TypeNode::Denoted { .. } => &["value"],
        TypeNode::EffectsRows { .. } => &["effects_expr"],
        TypeNode::Arrow { .. } => &["param", "result", "effects", "arity"],
        // WI-361: the single `fields` child (the `List[TypeField]` Value).
        TypeNode::NamedTuple { .. } => &["fields"],
        TypeNode::ExprCarried { .. } => &["value", "member"],
    };
    short_keys.iter().filter_map(|k| kb.lookup_symbol(k)).collect()
}

fn type_node_named<'a>(tn: &'a TypeNode, kb: &KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
    let key = |k: &str| kb.lookup_symbol(k);
    match tn {
        TypeNode::Denoted { value } if Some(sym) == key("value") => {
            Some(ViewItem::Node(Rc::clone(value)))
        }
        // WI-361: the single `fields` child — the `Value`-carried `List[TypeField]`,
        // borrowed (`ViewItem::Value`) so `TermView` walks it like the term's list.
        TypeNode::NamedTuple { fields } if Some(sym) == key("fields") => {
            Some(ViewItem::Value(fields))
        }
        // Bindings ARE the named args (WI-361): resolve the child by binding param.
        TypeNode::Parameterized { bindings, .. } => bindings
            .iter()
            .find(|(s, _)| *s == sym)
            .map(|(_, c)| type_child_view_item(c)),
        TypeNode::EffectsRows { effects_expr } if Some(sym) == key("effects_expr") => {
            Some(type_child_view_item(effects_expr))
        }
        TypeNode::Arrow { param, result, effects, arity } => {
            if Some(sym) == key("param") {
                Some(type_child_view_item(param))
            } else if Some(sym) == key("result") {
                Some(type_child_view_item(result))
            } else if Some(sym) == key("effects") {
                Some(type_child_view_item(effects))
            } else if Some(sym) == key("arity") {
                Some(type_child_view_item(arity))
            } else {
                None
            }
        }
        // WI-397: `value` (receiver occurrence, a `Node`) and `member` (a ground
        // `Ref` child) — read identically to the term twin's named args, so
        // `extract_type` yields `TypeExtractor::ExprCarried { value, member }`.
        TypeNode::ExprCarried { value, member } => {
            if Some(sym) == key("value") {
                Some(type_child_view_item(value))
            } else if Some(sym) == key("member") {
                Some(type_child_view_item(member))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn effect_expr_head(en: &EffectExprNode, kb: &KnowledgeBase) -> ViewHead {
    let (short, named_arity) = match en {
        EffectExprNode::Merge { .. } => ("merge", 2),
        EffectExprNode::Present { .. } => ("present", 1),
        EffectExprNode::Guarded { .. } => ("guarded", 2),
        EffectExprNode::Absent { .. } => ("absent", 1),
        EffectExprNode::Open { .. } => ("open", 1),
        EffectExprNode::EmptyRow => ("empty_row", 0),
    };
    match effect_functor_sym(kb, short) {
        Some(f) => ViewHead::Functor { functor: Some(f), pos_arity: 0, named_arity },
        None => ViewHead::Opaque,
    }
}

fn effect_expr_keys(en: &EffectExprNode, kb: &KnowledgeBase) -> Vec<Symbol> {
    let keys: &[&str] = match en {
        EffectExprNode::Merge { .. } => &["left", "right"],
        EffectExprNode::Present { .. } | EffectExprNode::Absent { .. } => &["label"],
        // Declared field order `guarded(label, guard)` — matches the term twin's
        // canonical named-arg order (as `merge`'s `[left, right]`).
        EffectExprNode::Guarded { .. } => &["label", "guard"],
        EffectExprNode::Open { .. } => &["tail"],
        EffectExprNode::EmptyRow => &[],
    };
    keys.iter().filter_map(|k| kb.lookup_symbol(k)).collect()
}

fn effect_expr_named<'a>(
    en: &'a EffectExprNode,
    kb: &KnowledgeBase,
    sym: Symbol,
) -> Option<ViewItem<'a>> {
    let key = |k: &str| kb.lookup_symbol(k);
    match en {
        EffectExprNode::Merge { left, right } => {
            if Some(sym) == key("left") {
                Some(type_child_view_item(left))
            } else if Some(sym) == key("right") {
                Some(type_child_view_item(right))
            } else {
                None
            }
        }
        EffectExprNode::Present { label } | EffectExprNode::Absent { label }
            if Some(sym) == key("label") =>
        {
            Some(type_child_view_item(label))
        }
        // `label` is a `TypeChild`; `guard` is the `Value`-carried `List[reflect.Term]`
        // (borrowed as `ViewItem::Value`, walked like the term's list — as NamedTuple).
        EffectExprNode::Guarded { label, guard } => {
            if Some(sym) == key("label") {
                Some(type_child_view_item(label))
            } else if Some(sym) == key("guard") {
                Some(ViewItem::Value(guard))
            } else {
                None
            }
        }
        EffectExprNode::Open { tail } if Some(sym) == key("tail") => {
            Some(type_child_view_item(tail))
        }
        _ => None,
    }
}

/// Shared `named_arg` for a Value-carried Type / EffectExpression occurrence —
/// returns a `ViewItem` (a ground child is a `Term`, a poisoned child a
/// `Node`). Returns `None` for any other kind, so Expr callers fall back to the
/// `Rc`-returning `occ_named_child`.
fn occ_type_named<'a>(
    occ: &'a NodeOccurrence,
    kb: &KnowledgeBase,
    sym: Symbol,
) -> Option<ViewItem<'a>> {
    if let Some(tn) = occ.as_type() {
        return type_node_named(tn, kb, sym);
    }
    if let Some(en) = occ.as_effect_expr() {
        return effect_expr_named(en, kb, sym);
    }
    None
}

/// Read-only view over a term or value, used on the target side of
/// unification. The blanket impls on `TermId` and `Value` mean callers can
/// pass either representation into `match_view` / future Value-aware
/// resolver paths.
pub trait TermView {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead;
    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>>;
    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>>;

    /// The symbol keys of all named args, in canonical order. Used by the
    /// discrim tree walker to iterate named positions without needing GATs
    /// or borrow-through-trait. Allocating a `Vec` here parallels the
    /// existing SmallVec-clone that `query_node` already did on the
    /// TermId path.
    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol>;

    /// Capture this view's identity as a [`BindValue`] — used when the
    /// tree's variable-edge captures the current query side. TermId-backed
    /// views produce `BindValue::Term`; Value-backed views clone into
    /// `BindValue::Value`. Called at the top level (when the query's head
    /// itself matches a tree-var) and at sub-arg var-edge captures.
    fn as_bind_value(&self) -> BindValue;

    /// The logic variable at this view's head, returning the full `Var` of
    /// *any* kind (Global / Rigid / DeBruijn) — so the discrimination-tree
    /// insert can route a flex `Global` / bound `DeBruijn` to a wildcard
    /// var-edge and a `Rigid` skolem to its `RigidVar` constant key, and the
    /// unifier / structural-equality test can compare two var heads by full
    /// `Var` identity. `None` for non-variable heads — the walk then keys on
    /// [`head`]. (`head` now also surfaces every var kind as `ViewHead::Var`, so
    /// the default suffices; the `TermId` / `Value` carriers keep a direct
    /// override that reads the carrier without a `head` round-trip.)
    fn index_var(&self, kb: &KnowledgeBase) -> Option<Var> {
        match self.head(kb) {
            ViewHead::Var(var) => Some(var),
            _ => None,
        }
    }
}

/// Representation-independent structural equality between two term views.
///
/// Two views are equal iff their heads match and every child recurses equal —
/// regardless of whether either side rides as a hash-consed `TermId`, a
/// `Value`, or a `Value::Node` occurrence (children are themselves [`ViewItem`]s,
/// which are `TermView`, so the recursion is carrier-blind). This is the
/// structural primitive consumers should reach for instead of comparing
/// rendered display names: a name compare is fragile in both directions — two
/// distinct terms can render the same string, and one logical term can render
/// two ways across representations (an abstract sort's row-variable effect `E`
/// reads as `Ref(S.E)` → `"E"` in a signature but as its `SortAlias` `Var` →
/// `"?_"` once walked; see the WI-365 op-boundary effect check). Variables
/// compare by `VarId`, constants by value, functors/refs/idents by symbol plus
/// recursive children. `Opaque` heads (closures, streams, Rigid/DeBruijn vars)
/// and head-kind mismatches are conservatively unequal — there is no shared
/// structure to compare. WI-486 made this the SINGLE structural `Value` compare,
/// replacing the carrier-blind `Value::structural_eq` (which returned `false` for
/// every cross-carrier `Term`-vs-`Node`/`Entity` pair) and subsuming the
/// `Value::Node`-only `occurrence_structural_eq`.
///
/// Purely structural: it does NOT resolve a substitution or a `SortAlias`.
/// Callers that need two differently-encoded-but-equal forms to agree (e.g.
/// `Ref(S.E)` vs its alias `Var`) canonicalize first (walk through the subst),
/// then compare.
pub fn views_structurally_equal<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    b: &B,
) -> bool {
    // WI-392: a rigid (Skolem) or DeBruijn var has a comparable identity (its
    // `Var`); `head` now surfaces it (no `Opaque` collapse), so the `Var`/`Var`
    // arm below compares two var heads by full `Var` identity for every kind —
    // two occurrences of the same rigid effect / type parameter are the same.
    // A rigid vs a different-flavoured var or a non-var head is unequal (`Var`'s
    // `Eq`, else the `_ => false` arm). `Global` vars are handled identically.
    match (a.head(kb), b.head(kb)) {
        (ViewHead::Var(va), ViewHead::Var(vb)) => va == vb,
        (ViewHead::Const(la), ViewHead::Const(lb)) => la == lb,
        (ViewHead::Ref(sa), ViewHead::Ref(sb)) => sa == sb,
        (ViewHead::Ident(sa), ViewHead::Ident(sb)) => sa == sb,
        (ViewHead::Bottom, ViewHead::Bottom) => true,
        (
            ViewHead::Functor { functor: fa, pos_arity: pa, named_arity: na },
            ViewHead::Functor { functor: fb, pos_arity: pb, named_arity: nb },
        ) => {
            if fa != fb || pa != pb || na != nb {
                return false;
            }
            for i in 0..pa {
                match (a.pos_arg(kb, i), b.pos_arg(kb, i)) {
                    (Some(ca), Some(cb)) if views_structurally_equal(kb, &ca, &cb) => {}
                    _ => return false,
                }
            }
            // `named_arity` equal + every one of `a`'s keys found-and-equal in
            // `b` ⇒ identical key sets (named args are duplicate-free and in
            // canonical order, so no extra-key escape).
            for key in a.named_keys(kb) {
                match (a.named_arg(kb, key), b.named_arg(kb, key)) {
                    (Some(ca), Some(cb)) if views_structurally_equal(kb, &ca, &cb) => {}
                    _ => return false,
                }
            }
            true
        }
        _ => false,
    }
}

/// A single node of a [`GoalKey`] — a kb-free structural token. `Const` carries
/// the literal value, `Open` the functor (or `None` for a functor-less
/// aggregate) plus arities, the rest a leaf symbol/var. Derives `Hash`/`Eq`, so
/// a `Vec<StructToken>` is self-contained — no `kb` needed to compare or hash.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StructToken {
    Open(Option<Symbol>, usize, usize),
    NamedKey(Symbol),
    Const(Literal),
    Ref(Symbol),
    Ident(Symbol),
    Var(Var),
    Bottom,
    Opaque,
}

/// A **carrier-agnostic structural fingerprint** of a goal, walked through σ
/// (WI-348). Two goals that are structurally identical after substitution —
/// regardless of carrier (`Term` / `Node` / `Entity`) — produce the same
/// `GoalKey`, because the walk reads everything through [`TermView`] (which
/// abstracts the carrier) and the tokens hold no `TermId`. So it keys the
/// resolver's answer-dedup set directly with **no materialization** to a
/// `TermId` and **no `kb` in `Hash`/`Eq`**, replacing the former
/// materialized `HashSet<TermId>` key.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GoalKey(Vec<StructToken>);

impl GoalKey {
    /// True when this key may safely index the resolver's per-query cache. Two
    /// conditions, both restoring exactly what the former hash-consed `TermId`
    /// cache key guaranteed:
    ///
    /// - **No unresolved flex (`Global`) var.** Its candidate substitutions are
    ///   tied to specific var-ids, so they aren't reusable. `fingerprint_into`
    ///   emits a `Var` token only for a var that didn't resolve through the
    ///   substitution; a `Rigid` skolem / `DeBruijn` binder is instead a
    ///   *constant* whose identity is baked into the key, so it stays cacheable —
    ///   mirroring [`KnowledgeBase::collect_vars`] (Global-only, DeBruijn/Rigid
    ///   ignored), the predicate the old key used.
    /// - **No `Opaque` leaf.** A `StructToken::Opaque` (a `Map`/`Cell`/`Closure`/
    ///   `OpRef`/… carrier — and one may itself hide unbound vars the fingerprint
    ///   can't see, so it is not truly "ground") is payload-free and not even
    ///   structurally self-comparable (`views_structurally_equal` is `false` for
    ///   it), so two genuinely distinct goals differing only inside an `Opaque`
    ///   child collapse to one key. The old `TermId` key never faced this (a
    ///   `Term` can't hold an `Opaque` child); excluding it restores that immunity
    ///   locally, mirroring the explicit non-`Term`/`Node` guard the answer-dedup
    ///   sibling `is_duplicate_projection` already applies for the same reason.
    pub fn is_cacheable(&self) -> bool {
        !self.0.iter().any(|t| matches!(
            t,
            StructToken::Var(Var::Global(_)) | StructToken::Opaque
        ))
    }
}

/// Append `view`'s structural fingerprint to `out`, resolving each `Var`
/// through `subst` (so the key is over the *reified* goal). Named args are
/// emitted in **sorted** key order — `named_keys` order differs by carrier
/// (a `Term::Fn` is sorted-by-name, an occurrence is a fixed slice), so sorting
/// is what makes a `Term` and a `Node` of the same structure agree.
fn fingerprint_into<V: TermView>(
    kb: &KnowledgeBase,
    view: &V,
    subst: &crate::kb::subst::Substitution,
    out: &mut Vec<StructToken>,
) {
    match view.head(kb) {
        // Only a flex `Global` resolves through σ; a `Rigid` skolem / `DeBruijn`
        // binder is a constant whose identity IS the fingerprint (two distinct
        // skolems must key distinct goals), so emit its `Var` token directly.
        ViewHead::Var(var @ (Var::Rigid(_) | Var::DeBruijn(_))) => {
            out.push(StructToken::Var(var))
        }
        ViewHead::Var(var) => match subst.resolve_as_value(var.as_vid()) {
            None => out.push(StructToken::Var(var)),
            // Self-referential binding (a var bound to itself) — stop, mirroring
            // `walk`/`walk_view`'s guard, so a cyclic σ can't recurse unboundedly.
            Some(Value::Var(Var::Global(w))) if *w == var.as_vid() => {
                out.push(StructToken::Var(var))
            }
            Some(Value::Term { id: t, .. })
                if matches!(kb.get_term(*t), Term::Var(Var::Global(w)) if *w == var.as_vid()) =>
            {
                out.push(StructToken::Var(var))
            }
            // Resolve through σ and fingerprint the binding's own view.
            Some(bound) => {
                let bound = bound.clone();
                fingerprint_into(kb, &bound, subst, out);
            }
        },
        ViewHead::Const(lit) => out.push(StructToken::Const(lit)),
        ViewHead::Ref(s) => out.push(StructToken::Ref(s)),
        ViewHead::Ident(s) => out.push(StructToken::Ident(s)),
        ViewHead::Bottom => out.push(StructToken::Bottom),
        ViewHead::Opaque => out.push(StructToken::Opaque),
        ViewHead::Functor { functor, pos_arity, named_arity } => {
            out.push(StructToken::Open(functor, pos_arity, named_arity));
            for i in 0..pos_arity {
                if let Some(child) = view.pos_arg(kb, i) {
                    fingerprint_into(kb, &child, subst, out);
                }
            }
            let mut keys = view.named_keys(kb);
            keys.sort_by_key(|s| s.index());
            for key in keys {
                out.push(StructToken::NamedKey(key));
                if let Some(child) = view.named_arg(kb, key) {
                    fingerprint_into(kb, &child, subst, out);
                }
            }
        }
    }
}

/// Carrier-agnostic structural fingerprint of `view` reified through `subst`
/// (WI-348) — see [`GoalKey`].
pub fn goal_fingerprint<V: TermView>(
    kb: &KnowledgeBase,
    view: &V,
    subst: &crate::kb::subst::Substitution,
) -> GoalKey {
    let mut out = Vec::new();
    fingerprint_into(kb, view, subst, &mut out);
    GoalKey(out)
}

/// Wrapper so we can `impl TermView for TermIdView` without orphan-rule
/// issues on the bare `TermId` type.
#[derive(Clone, Copy, Debug)]
pub struct TermIdView(pub TermId);

impl TermView for TermIdView {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead {
        match kb.get_term(self.0) {
            // A var of ANY kind surfaces its `Var`; the discrim tree decides
            // wildcard-vs-constant by the kind (Global/DeBruijn → var-edge,
            // Rigid → `RigidVar` constant key). WI-108's goal-side anti-wildcard
            // guard for a rigid is now the constant-key match itself: a rigid
            // goal var keys `RigidVar(id)`, which can't match a concrete fact.
            Term::Var(v) => ViewHead::Var(*v),
            Term::Const(lit) => ViewHead::Const(lit.clone()),
            Term::Fn { functor, pos_args, named_args } => {
                functor_view_head(kb, *functor, pos_args.len(), named_args.len())
            }
            Term::Ref(s) => ViewHead::Ref(*s),
            Term::Ident(s) => ViewHead::Ident(*s),
            Term::Bottom => ViewHead::Bottom,
            Term::ParseAux(_) => unreachable!(
                "parse-only Term::ParseAux variant reached the KB-side TermIdView",
            ),
        }
    }

    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>> {
        match kb.get_term(self.0) {
            Term::Fn { pos_args, .. } => pos_args.get(i).copied().map(ViewItem::Term),
            _ => None,
        }
    }

    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        match kb.get_term(self.0) {
            Term::Fn { named_args, .. } => named_args.iter()
                .find(|(s, _)| *s == sym)
                .map(|(_, t)| ViewItem::Term(*t)),
            _ => None,
        }
    }

    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        match kb.get_term(self.0) {
            Term::Fn { named_args, .. } => named_args.iter().map(|(s, _)| *s).collect(),
            _ => Vec::new(),
        }
    }

    fn as_bind_value(&self) -> BindValue {
        BindValue::Term(self.0)
    }

    fn index_var(&self, kb: &KnowledgeBase) -> Option<Var> {
        match kb.get_term(self.0) {
            Term::Var(v) => Some(*v),
            _ => None,
        }
    }
}

/// WI-349: a bare `TermId` is itself a `TermView` (delegating to [`TermIdView`]),
/// so the representation-neutral KB query/resolution interface (`query` /
/// `resolve`, generic over `V: TermView`) accepts a `TermId` ground pattern
/// directly — alongside a `Value` or a `Value::Node` occurrence — with no
/// term-only entry point and no caller churn. `TermView` is local and `TermId`
/// is local, so this is not an orphan-rule violation (the `TermIdView` wrapper's
/// original rationale notwithstanding); the wrapper stays for callers that hold
/// a `TermId` where a distinct view type reads better.
impl TermView for TermId {
    // Bodies mirror `TermIdView` (a `TermId` *is* a `TermIdView(self)`); inlined
    // rather than delegated because `ViewItem<'a>` would otherwise tie `'a` to a
    // borrowed temporary `TermIdView` instead of the caller's `&'a self`/`&'a kb`.
    fn head(&self, kb: &KnowledgeBase) -> ViewHead {
        match kb.get_term(*self) {
            // A var of ANY kind surfaces its `Var` (see `TermIdView::head`).
            Term::Var(v) => ViewHead::Var(*v),
            Term::Const(lit) => ViewHead::Const(lit.clone()),
            Term::Fn { functor, pos_args, named_args } => {
                functor_view_head(kb, *functor, pos_args.len(), named_args.len())
            }
            Term::Ref(s) => ViewHead::Ref(*s),
            Term::Ident(s) => ViewHead::Ident(*s),
            Term::Bottom => ViewHead::Bottom,
            Term::ParseAux(_) => unreachable!(
                "parse-only Term::ParseAux variant reached the KB-side TermView for TermId",
            ),
        }
    }
    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>> {
        match kb.get_term(*self) {
            Term::Fn { pos_args, .. } => pos_args.get(i).copied().map(ViewItem::Term),
            _ => None,
        }
    }
    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        match kb.get_term(*self) {
            Term::Fn { named_args, .. } => named_args.iter()
                .find(|(s, _)| *s == sym)
                .map(|(_, t)| ViewItem::Term(*t)),
            _ => None,
        }
    }
    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        match kb.get_term(*self) {
            Term::Fn { named_args, .. } => named_args.iter().map(|(s, _)| *s).collect(),
            _ => Vec::new(),
        }
    }
    fn as_bind_value(&self) -> BindValue {
        BindValue::Term(*self)
    }
    fn index_var(&self, kb: &KnowledgeBase) -> Option<Var> {
        match kb.get_term(*self) {
            Term::Var(v) => Some(*v),
            _ => None,
        }
    }
}

impl TermView for Value {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead {
        match self {
            Value::Term { id: tid, .. } => TermIdView(*tid).head(kb),
            Value::Int(n) => ViewHead::Const(Literal::Int(*n)),
            Value::BigInt(n) => ViewHead::Const(Literal::BigInt(n.clone())),
            Value::Float(f) => ViewHead::Const(Literal::Float(ordered_float::OrderedFloat(*f))),
            Value::Bool(b) => ViewHead::Const(Literal::Bool(*b)),
            Value::Str(s) => ViewHead::Const(Literal::String(s.clone())),
            Value::Unit => ViewHead::Functor {
                functor: None,
                pos_arity: 0,
                named_arity: 0,
            },
            Value::Tuple { pos, named, .. } => ViewHead::Functor {
                functor: None,
                pos_arity: pos.len(),
                named_arity: named.len(),
            },
            Value::Entity { functor, pos, named, .. } => {
                functor_view_head(kb, *functor, pos.len(), named.len())
            }
            // WI-276: a reflect Expr occurrence is structural — expose its Expr.
            // WI-342: Type / EffectExpr occurrences expose their functor too.
            Value::Node(occ) => occ_head(occ, kb),
            // WI-109: a value-level logic variable views the same as the
            // matching `Term::Var` (TermIdView) — a var of ANY kind surfaces its
            // `Var`, and the discrim tree keys flex `Global`/`DeBruijn` as a
            // wildcard var-edge, `Rigid` as a `RigidVar` constant.
            Value::Var(v) => ViewHead::Var(*v),
            Value::Closure(_)
            | Value::OpRef { .. }
            | Value::Stream(_)
            | Value::Substitution(_)
            | Value::Map(_)
            | Value::Cell(_)
            | Value::Requirement(_)
            // WI-714: a `Relation` is an intensional query value, not structural
            // data — opaque to the term view (it never unifies or indexes; it is
            // consumed only through `Relation.splitFirst`).
            | Value::Relation { .. } => ViewHead::Opaque,
        }
    }

    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>> {
        // Can't construct a temporary TermIdView and delegate — the
        // returned ViewItem would outlive it. Inline the TermId path.
        match self {
            Value::Term { id: tid, .. } => match kb.get_term(*tid) {
                Term::Fn { pos_args, .. } => pos_args.get(i).copied().map(ViewItem::Term),
                _ => None,
            },
            Value::Tuple { pos, .. } => pos.get(i).map(ViewItem::Value),
            Value::Entity { pos, .. } => pos.get(i).map(ViewItem::Value),
            Value::Node(occ) => occ_pos_child(occ, kb, i).map(ViewItem::Node),
            _ => None,
        }
    }

    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        match self {
            Value::Term { id: tid, .. } => match kb.get_term(*tid) {
                Term::Fn { named_args, .. } => named_args.iter()
                    .find(|(s, _)| *s == sym)
                    .map(|(_, t)| ViewItem::Term(*t)),
                _ => None,
            },
            Value::Tuple { named, .. } => {
                named.iter().find(|(s, _)| *s == sym).map(|(_, v)| ViewItem::Value(v))
            }
            Value::Entity { named, .. } => {
                named.iter().find(|(s, _)| *s == sym).map(|(_, v)| ViewItem::Value(v))
            }
            // WI-342: a Type/EffectExpr child may be ground (`Term`) — handle
            // both via `occ_type_named`; fall back to the Expr `Rc` reader.
            Value::Node(occ) => occ_type_named(occ, kb, sym)
                .or_else(|| occ_named_child(occ, kb, sym).map(ViewItem::Node)),
            _ => None,
        }
    }

    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        match self {
            Value::Term { id: tid, .. } => match kb.get_term(*tid) {
                Term::Fn { named_args, .. } => named_args.iter().map(|(s, _)| *s).collect(),
                _ => Vec::new(),
            },
            Value::Tuple { named, .. } => named.iter().map(|(s, _)| *s).collect(),
            Value::Entity { named, .. } => named.iter().map(|(s, _)| *s).collect(),
            Value::Node(occ) => occ_named_keys(occ, kb),
            _ => Vec::new(),
        }
    }

    fn as_bind_value(&self) -> BindValue {
        match self {
            Value::Term { id: tid, .. } => BindValue::Term(*tid),
            // Value::Node clones cheaply (Rc), preserving occurrence identity.
            other => BindValue::Value(other.clone()),
        }
    }

    fn index_var(&self, kb: &KnowledgeBase) -> Option<Var> {
        match self {
            Value::Term { id: tid, .. } => match kb.get_term(*tid) {
                Term::Var(v) => Some(*v),
                _ => None,
            },
            Value::Var(v) => Some(*v),
            // An occurrence head surfaces a var of ANY kind (Global / Rigid /
            // DeBruijn) as a var-edge — same form as the `Term` / `Value::Var`
            // arms above and `TermIdView` (WI-373). A stored value rule head's
            // De Bruijn binder thus indexes like a term head's, instead of
            // collapsing to `Opaque` and panicking at insert.
            Value::Node(occ) => occ_index_var(occ),
            _ => None,
        }
    }
}

/// WI-277: an occurrence is itself a first-class match target. Implementing
/// `TermView` directly on `Rc<NodeOccurrence>` keeps the typer-phase rewrite
/// loop `Rc<NodeOccurrence> → Rc<NodeOccurrence>` — `match_view(lhs, &occ)`
/// reads the occurrence in place, the rebuilt result is the next `Rc` — with
/// no `Value::Node` wrap/unwrap between match and rebuild on each iteration.
/// (`Value::Node` still appears *inside* the substitution as a bound child,
/// which is intrinsic and a single `Rc` bump.) Reuses the `occ_*` helpers.
/// WI-714: if `occ` is a `Spliced(value)` leaf, the carried `Value` — which
/// itself implements [`TermView`] — is the structural view. The occurrence-child
/// helpers (`occ_pos_child`, …) return *occurrence* children, and a `Spliced`
/// leaf has none, so the occurrence `TermView` impl delegates to the value here
/// (the head delegates in `occ_head`). Symmetric to `Value::Node`'s delegation
/// to its occurrence — the two carriers view through to whatever they carry.
fn spliced_value(occ: &NodeOccurrence) -> Option<&Value> {
    match occ.as_expr() {
        Some(Expr::Spliced(v)) => Some(v),
        _ => None,
    }
}

impl TermView for Rc<NodeOccurrence> {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead {
        occ_head(self, kb)
    }

    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>> {
        if let Some(v) = spliced_value(self) {
            return v.pos_arg(kb, i);
        }
        occ_pos_child(self, kb, i).map(ViewItem::Node)
    }

    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        if let Some(v) = spliced_value(self) {
            return v.named_arg(kb, sym);
        }
        occ_type_named(self, kb, sym)
            .or_else(|| occ_named_child(self, kb, sym).map(ViewItem::Node))
    }

    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        if let Some(v) = spliced_value(self) {
            return v.named_keys(kb);
        }
        occ_named_keys(self, kb)
    }

    fn as_bind_value(&self) -> BindValue {
        if let Some(v) = spliced_value(self) {
            return v.as_bind_value();
        }
        BindValue::Value(Value::Node(Rc::clone(self)))
    }

    /// Override the `Global`-only default: an occurrence keys a stored-pattern
    /// var of any kind (Global / Rigid / DeBruijn) as a var-edge, like the
    /// `TermId` carrier (WI-373).
    fn index_var(&self, kb: &KnowledgeBase) -> Option<Var> {
        if let Some(v) = spliced_value(self) {
            return v.index_var(kb);
        }
        occ_index_var(self)
    }
}

impl TermView for ViewItem<'_> {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead {
        match self {
            ViewItem::Term(t) => TermIdView(*t).head(kb),
            ViewItem::Value(v) => (**v).head(kb),
            ViewItem::Node(occ) => occ_head(occ, kb),
        }
    }

    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>> {
        match self {
            ViewItem::Term(t) => match kb.get_term(*t) {
                Term::Fn { pos_args, .. } => pos_args.get(i).copied().map(ViewItem::Term),
                _ => None,
            },
            ViewItem::Value(v) => (*v).pos_arg(kb, i),
            ViewItem::Node(occ) => occ_pos_child(occ, kb, i).map(ViewItem::Node),
        }
    }

    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        match self {
            ViewItem::Term(t) => match kb.get_term(*t) {
                Term::Fn { named_args, .. } => named_args.iter()
                    .find(|(s, _)| *s == sym)
                    .map(|(_, t)| ViewItem::Term(*t)),
                _ => None,
            },
            ViewItem::Value(v) => (*v).named_arg(kb, sym),
            ViewItem::Node(occ) => occ_type_named(occ, kb, sym)
                .or_else(|| occ_named_child(occ, kb, sym).map(ViewItem::Node)),
        }
    }

    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        match self {
            ViewItem::Term(t) => match kb.get_term(*t) {
                Term::Fn { named_args, .. } => named_args.iter().map(|(s, _)| *s).collect(),
                _ => Vec::new(),
            },
            ViewItem::Value(v) => (*v).named_keys(kb),
            ViewItem::Node(occ) => occ_named_keys(occ, kb),
        }
    }

    fn as_bind_value(&self) -> BindValue {
        match self {
            ViewItem::Term(t) => BindValue::Term(*t),
            ViewItem::Value(v) => BindValue::Value((*v).clone()),
            ViewItem::Node(occ) => BindValue::Value(Value::Node(Rc::clone(occ))),
        }
    }

    fn index_var(&self, kb: &KnowledgeBase) -> Option<Var> {
        match self {
            ViewItem::Term(t) => match kb.get_term(*t) {
                Term::Var(v) => Some(*v),
                _ => None,
            },
            ViewItem::Value(v) => (*v).index_var(kb),
            // An occurrence surfaces a var of any kind as a var-edge — see
            // `occ_index_var` / `Value::index_var` (WI-373).
            ViewItem::Node(occ) => occ_index_var(occ),
        }
    }
}

// ── Reflect lens over an occurrence (WI-297) ────────────────────
//
// The plain `Rc<NodeOccurrence>` view (above) reads an occurrence in its
// *goal* shape — `Expr::Const(42)` → the literal `42`, `Expr::Apply{foo}` →
// `foo(...)`. The typing relation, however, matches expression structure as
// *reflect data*: `int_lit(value: ?)`, `apply(fn: ?f, args: ?Args)`, … . The
// `occurrence_term` builtin bridges the two by *showing* the same occurrence
// through this reflect lens — no hash-consed term is built and no subtree is
// copied: a leaf's payload child is the occurrence itself (read in its plain
// shape), compound children are the existing child occurrences, and only the
// head label is supplied by the lens.

/// Reflect-`Expr` constructor symbols the [`ReflectedExpr`] lens reports as
/// functors, resolved once from the KB. `None` when reflect isn't loaded (the
/// lens then reads `Opaque`, so nothing matches — fail-soft, not a panic).
#[derive(Clone, Copy, Default, Debug)]
pub struct ReflectSyms {
    pub int_lit: Option<Symbol>,
    pub bigint_lit: Option<Symbol>,
    pub float_lit: Option<Symbol>,
    pub string_lit: Option<Symbol>,
    pub bool_lit: Option<Symbol>,
    /// Field key `value` (the single named arg of every `*_lit` entity).
    pub value: Option<Symbol>,
}

impl ReflectSyms {
    /// Resolve the reflect symbols the lens needs. Qualified entity names go
    /// through `try_resolve_symbol` (already interned by the stdlib load);
    /// the bare field key `value` is interned so it matches the key the
    /// loader stored on the rule pattern.
    pub fn resolve(kb: &mut KnowledgeBase) -> Self {
        Self {
            int_lit: kb.try_resolve_symbol("anthill.reflect.Expr.int_lit"),
            bigint_lit: kb.try_resolve_symbol("anthill.reflect.Expr.bigint_lit"),
            float_lit: kb.try_resolve_symbol("anthill.reflect.Expr.float_lit"),
            string_lit: kb.try_resolve_symbol("anthill.reflect.Expr.string_lit"),
            bool_lit: kb.try_resolve_symbol("anthill.reflect.Expr.bool_lit"),
            value: Some(kb.intern("value")),
        }
    }
}

/// Reflect-shape `TermView` over a `NodeOccurrence` (WI-297). See the module
/// note above. Currently covers literal leaves (`Expr::Const` →
/// `int_lit`/`float_lit`/`string_lit`/`bool_lit`/`bigint_lit(value: …)`);
/// other `Expr` forms read `Opaque` until their reflected reading is added.
pub struct ReflectedExpr {
    occ: Rc<NodeOccurrence>,
    syms: ReflectSyms,
}

impl ReflectedExpr {
    pub fn new(occ: Rc<NodeOccurrence>, syms: ReflectSyms) -> Self {
        Self { occ, syms }
    }

    /// The reflect functor for a literal payload (e.g. `Int` → `int_lit`).
    fn lit_functor(&self, lit: &Literal) -> Option<Symbol> {
        match lit {
            Literal::Int(_) => self.syms.int_lit,
            Literal::BigInt(_) => self.syms.bigint_lit,
            Literal::Float(_) => self.syms.float_lit,
            Literal::String(_) => self.syms.string_lit,
            Literal::Bool(_) => self.syms.bool_lit,
            // Opaque handle literals have no reflect `*_lit` form.
            Literal::Handle(_, _) => None,
        }
    }
}

impl TermView for ReflectedExpr {
    fn head(&self, _kb: &KnowledgeBase) -> ViewHead {
        match self.occ.as_expr() {
            // A literal reflects as `*_lit(value: <the literal>)` — one named
            // arg, no positionals.
            Some(Expr::Const(lit)) => match self.lit_functor(lit) {
                Some(f) => ViewHead::Functor { functor: Some(f), pos_arity: 0, named_arity: 1 },
                None => ViewHead::Opaque,
            },
            _ => ViewHead::Opaque,
        }
    }

    fn pos_arg<'a>(&'a self, _kb: &'a KnowledgeBase, _i: usize) -> Option<ViewItem<'a>> {
        // Reflect `Expr` entities use named fields only.
        None
    }

    fn named_arg<'a>(&'a self, _kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        match self.occ.as_expr() {
            // `value` is the occurrence itself, read in its plain `Const`
            // shape — no new term, no copy.
            Some(Expr::Const(_)) if Some(sym) == self.syms.value => {
                Some(ViewItem::Node(Rc::clone(&self.occ)))
            }
            _ => None,
        }
    }

    fn named_keys(&self, _kb: &KnowledgeBase) -> Vec<Symbol> {
        match self.occ.as_expr() {
            Some(Expr::Const(_)) => self.syms.value.into_iter().collect(),
            _ => Vec::new(),
        }
    }

    fn as_bind_value(&self) -> BindValue {
        // If the whole reflected term binds a var (`occurrence_term(?e, ?t)`),
        // bind the occurrence itself — identity preserved.
        BindValue::Value(Value::Node(Rc::clone(&self.occ)))
    }
}

#[cfg(test)]
mod wi436_tests {
    //! WI-436 — a 0-ary constructor reads as the bare `Ref(c)` across every
    //! carrier (stored `Term`, `Value::Entity`, reflect `Expr` occurrence), so
    //! `Ref(c)` and the nullary application `Fn{c}` are one representation. A
    //! non-constructor functor keeps its `Functor` head (the gate is exactly
    //! `is_constructor_symbol`, isolating the rule by symbol kind).
    use super::*;
    use crate::span::{SourceId, SourceSpan};
    use smallvec::SmallVec;
    use std::rc::Rc;

    fn dummy_span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 0)
    }

    /// A KB with `red` registered as a constructor of sort `Color`, plus a
    /// non-constructor functor `plain` of the same (zero) arity for the control.
    fn kb_with_constructor() -> (KnowledgeBase, Symbol, Symbol) {
        let mut kb = KnowledgeBase::new();
        let red = kb.intern("Color.red");
        let color = kb.intern("Color");
        let red_entity = kb.alloc(Term::Fn {
            functor: red,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let color_t = kb.alloc(Term::Ref(color));
        kb.register_entity_of(red_entity, color_t);
        assert!(kb.is_constructor_symbol(red));
        let plain = kb.intern("plain");
        assert!(!kb.is_constructor_symbol(plain));
        (kb, red, plain)
    }

    #[test]
    fn nullary_constructor_reads_as_bare_ref_across_carriers() {
        let (mut kb, red, _) = kb_with_constructor();

        let bare_ref = kb.alloc(Term::Ref(red));
        let nullary_fn = kb.alloc(Term::Fn {
            functor: red,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let entity_val = Value::Entity {
            functor: red,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        let ctor_occ = Value::Node(NodeOccurrence::new_expr(
            Expr::Constructor {
                name: red,
                pos_args: Vec::new(),
                named_args: Vec::new(),
                from_projection: false,
            },
            dummy_span(),
            None,
        ));

        // Every carrier's head is the bare `Ref(red)` — not a `Functor` — and
        // `functor_sym` reads `red` off it.
        for h in [bare_ref.head(&kb), nullary_fn.head(&kb), entity_val.head(&kb), ctor_occ.head(&kb)] {
            assert!(matches!(h, ViewHead::Ref(s) if s == red));
            assert_eq!(h.functor_sym(), Some(red));
        }

        // …so all four compare structurally equal in both directions.
        assert!(views_structurally_equal(&kb, &bare_ref, &nullary_fn));
        assert!(views_structurally_equal(&kb, &nullary_fn, &bare_ref));
        assert!(views_structurally_equal(&kb, &bare_ref, &entity_val));
        assert!(views_structurally_equal(&kb, &bare_ref, &ctor_occ));
        assert!(views_structurally_equal(&kb, &entity_val, &ctor_occ));
    }

    #[test]
    fn nullary_non_constructor_stays_functor_and_distinct_from_ref() {
        let (mut kb, _, plain) = kb_with_constructor();
        let plain_ref = kb.alloc(Term::Ref(plain));
        let plain_fn = kb.alloc(Term::Fn {
            functor: plain,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        assert!(matches!(
            plain_fn.head(&kb),
            ViewHead::Functor { functor: Some(s), pos_arity: 0, named_arity: 0 } if s == plain
        ));
        assert!(!views_structurally_equal(&kb, &plain_ref, &plain_fn));
    }
}

#[cfg(test)]
mod wi520_tests {
    //! WI-520 — a reflect-`Expr` `Instantiation`/`Bottom` occurrence reads through
    //! the SAME head as its `occurrence_to_term` twin (`Term::Fn{name}` /
    //! `Term::Bottom`) instead of collapsing to `Opaque`. So `views_structurally_equal`
    //! (the single WI-486 comparator) compares two such occurrences structurally,
    //! and an `Instantiation` occurrence matches its own materialized term.
    use super::*;
    use crate::kb::node_occurrence::occurrence_to_term;
    use crate::kb::term::Literal;
    use crate::span::{SourceId, SourceSpan};
    use std::rc::Rc;

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 0)
    }

    fn inst(name: Symbol, key: Symbol, child: Expr) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_expr(
            Expr::Instantiation {
                name,
                pos_args: Vec::new(),
                named_args: vec![(key, NodeOccurrence::new_expr(child, span(), None))],
            },
            span(),
            None,
        )
    }

    #[test]
    fn instantiation_reads_like_its_term_twin_and_compares_structurally() {
        let mut kb = KnowledgeBase::new();
        let foo = kb.intern("Foo");
        let x = kb.intern("x");

        let a = inst(foo, x, Expr::Const(Literal::Int(1)));
        let b = inst(foo, x, Expr::Const(Literal::Int(1))); // structurally equal
        let c = inst(foo, x, Expr::Const(Literal::Int(2))); // distinct child

        let av = Value::Node(Rc::clone(&a));
        // Head is the SAME `Functor` head its term twin produces — NOT `Opaque`.
        assert!(matches!(av.head(&kb), ViewHead::Functor { functor: Some(s), .. } if s == foo));
        let twin = occurrence_to_term(&mut kb, &a);
        assert_eq!(av.head(&kb).functor_sym(), twin.head(&kb).functor_sym());

        // Two structurally-equal instantiations compare equal; a distinct one not.
        assert!(views_structurally_equal(&kb, &av, &Value::Node(b)));
        assert!(!views_structurally_equal(&kb, &av, &Value::Node(c)));
    }

    #[test]
    fn bottom_occurrence_reads_as_bottom_not_opaque() {
        let kb = KnowledgeBase::new();
        let a = Value::Node(NodeOccurrence::new_expr(Expr::Bottom, span(), None));
        let b = Value::Node(NodeOccurrence::new_expr(Expr::Bottom, span(), None));
        assert!(matches!(a.head(&kb), ViewHead::Bottom));
        assert!(views_structurally_equal(&kb, &a, &b));
    }
}
