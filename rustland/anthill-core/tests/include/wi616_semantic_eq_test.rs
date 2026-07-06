//! WI-616 / proposal 051 Phase 2 — `=`/`eq` dispatch through the carrier's
//! `Eq` instance.
//!
//! `Eq.eq`/`Eq.neq` are now `BuiltinTag::SemEq`/`SemNeq`: structurally
//! identical operands succeed by reflexivity (every current ground use keeps
//! its answer), and structurally DISTINCT operands dispatch to the carrier
//! sort's OWN `eq` override (the WI-350/WI-444 short-name convention) when one
//! exists — `Set.eq`/`Map.eq`, the first non-structural instances, resolved as
//! ordinary SLD rules over the symbolic `insert`/`empty` (`put`/`empty`)
//! algebra. A carrier with no override keeps the structural compare (that IS
//! its `Eq` instance). `===` (struct_eq) stays structural on every carrier.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// Rules driving `eq`/`neq` as rule-body goals over sets and maps built from
/// the symbolic algebra. `se`/`sne` take two already-built values; the point
/// is the body `eq`/`neq` goal dispatching (or not) by carrier.
const SRC: &str = r#"
    namespace test.wi616
      import anthill.prelude.{Int64, Eq, Option}
      sort Tag
        entity red
        entity blue
      end
      sort Box
        entity box(v: Int64)
      end
      rule se(?x, ?y) :- eq(?x, ?y)
      rule sne(?x, ?y) :- neq(?x, ?y)
      rule sid(?x, ?y) :- ?x === ?y
      rule unbox0(box(v: ?v), ?v)
      rule unbox1(box(v: ?v), ?v) :- eq(1, 1)
    end
"#;

fn load_kb() -> KnowledgeBase {
    crate::common::load_kb_with(SRC)
}

fn int_term(kb: &mut KnowledgeBase, n: i64) -> TermId {
    kb.alloc(Term::Const(Literal::Int(n)))
}

fn fn_term(kb: &mut KnowledgeBase, qualified: &str, args: &[TermId]) -> TermId {
    let sym = kb
        .try_resolve_symbol(qualified)
        .unwrap_or_else(|| panic!("symbol {qualified} not in KB"));
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

/// `insert(insert(… empty(), e1 …), en)` over `anthill.prelude.Set`.
fn set_of(kb: &mut KnowledgeBase, elems: &[TermId]) -> TermId {
    let mut s = fn_term(kb, "anthill.prelude.Set.empty", &[]);
    for &e in elems {
        s = fn_term(kb, "anthill.prelude.Set.insert", &[s, e]);
    }
    s
}

/// `put(put(… empty(), k1, v1 …), kn, vn)` over `anthill.prelude.Map`.
fn map_of(kb: &mut KnowledgeBase, entries: &[(TermId, TermId)]) -> TermId {
    let mut m = fn_term(kb, "anthill.prelude.Map.empty", &[]);
    for &(k, v) in entries {
        m = fn_term(kb, "anthill.prelude.Map.put", &[m, k, v]);
    }
    m
}

fn solutions(kb: &mut KnowledgeBase, pred: &str, a: TermId, b: TermId) -> usize {
    let goal = fn_term(kb, &format!("test.wi616.{pred}"), &[a, b]);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// Carrier-agnostic "reified to this int" check — a binding can come back as
/// `Value::Int`, a hash-consed `Value::Term(Const)`, or a `Value::Node`
/// occurrence (`Expr::Const` via the `<=>` path); `TermView::head` reads all
/// three.
fn reifies_to_int(kb: &KnowledgeBase, v: &anthill_core::eval::Value, n: i64) -> bool {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    matches!(v.head(kb), ViewHead::Const(Literal::Int(m)) if m == n)
}

fn int_set(kb: &mut KnowledgeBase, elems: &[i64]) -> TermId {
    let elems: Vec<TermId> = elems.iter().map(|&n| int_term(kb, n)).collect();
    set_of(kb, &elems)
}

// ── ground structural uses keep their answers ─────────────────────────────

#[test]
fn eq_on_ints_unchanged() {
    let mut kb = load_kb();
    let (a, b) = (int_term(&mut kb, 7), int_term(&mut kb, 7));
    assert_eq!(solutions(&mut kb, "se", a, b), 1, "eq(7,7) must hold");
    let (a, b) = (int_term(&mut kb, 7), int_term(&mut kb, 8));
    assert_eq!(solutions(&mut kb, "se", a, b), 0, "eq(7,8) must not hold");
}

#[test]
fn neq_on_ints_unchanged() {
    let mut kb = load_kb();
    let (a, b) = (int_term(&mut kb, 7), int_term(&mut kb, 8));
    assert_eq!(solutions(&mut kb, "sne", a, b), 1, "neq(7,8) must hold");
    let (a, b) = (int_term(&mut kb, 7), int_term(&mut kb, 7));
    assert_eq!(solutions(&mut kb, "sne", a, b), 0, "neq(7,7) must not hold");
}

#[test]
fn eq_on_entities_without_instance_stays_structural() {
    let mut kb = load_kb();
    let red = kb.try_resolve_symbol("test.wi616.Tag.red").unwrap();
    let blue = kb.try_resolve_symbol("test.wi616.Tag.blue").unwrap();
    let (r1, r2) = (kb.alloc(Term::Ref(red)), kb.alloc(Term::Ref(red)));
    assert_eq!(solutions(&mut kb, "se", r1, r2), 1, "eq(red,red) must hold");
    let (r, b) = (kb.alloc(Term::Ref(red)), kb.alloc(Term::Ref(blue)));
    assert_eq!(solutions(&mut kb, "se", r, b), 0, "eq(red,blue) must not hold");
}

// ── Set: membership equality via the dispatched carrier eq ────────────────

#[test]
fn set_eq_ignores_insertion_order() {
    let mut kb = load_kb();
    let a = int_set(&mut kb, &[1, 2]);
    let b = int_set(&mut kb, &[2, 1]);
    assert_eq!(
        solutions(&mut kb, "se", a, b),
        1,
        "eq({{1,2}}, {{2,1}}) must hold EXACTLY ONCE — membership equality, and \
         the dispatch sub-resolution keeps eq semi-deterministic (no duplicate \
         proofs leak from overlapping member/subset rules)"
    );
}

#[test]
fn set_eq_ignores_duplicates() {
    let mut kb = load_kb();
    let a = int_set(&mut kb, &[1]);
    let b = int_set(&mut kb, &[1, 1]);
    assert_eq!(
        solutions(&mut kb, "se", a, b),
        1,
        "eq({{1}}, {{1,1}}) must hold exactly once — insert is idempotent"
    );
}

#[test]
fn set_eq_distinguishes_different_members() {
    let mut kb = load_kb();
    let a = int_set(&mut kb, &[1, 2]);
    let b = int_set(&mut kb, &[1, 3]);
    assert_eq!(solutions(&mut kb, "se", a, b), 0, "eq({{1,2}}, {{1,3}}) must not hold");
    let a = int_set(&mut kb, &[1]);
    let b = int_set(&mut kb, &[1, 2]);
    assert_eq!(solutions(&mut kb, "se", a, b), 0, "eq({{1}}, {{1,2}}) must not hold");
}

#[test]
fn set_eq_structurally_identical_sets_hold_by_reflexivity() {
    let mut kb = load_kb();
    let a = int_set(&mut kb, &[1, 2]);
    let b = int_set(&mut kb, &[1, 2]);
    assert_eq!(solutions(&mut kb, "se", a, b), 1, "eq({{1,2}}, {{1,2}}) must hold");
}

#[test]
fn set_neq_negates_membership_equality() {
    let mut kb = load_kb();
    let a = int_set(&mut kb, &[1, 2]);
    let b = int_set(&mut kb, &[1, 3]);
    assert_eq!(solutions(&mut kb, "sne", a, b), 1, "neq({{1,2}}, {{1,3}}) must hold");
    let a = int_set(&mut kb, &[1, 2]);
    let b = int_set(&mut kb, &[2, 1]);
    assert_eq!(
        solutions(&mut kb, "sne", a, b),
        0,
        "neq({{1,2}}, {{2,1}}) must not hold — the sets are equal by membership"
    );
}

#[test]
fn nested_set_eq_dispatches_elementwise() {
    // Set[Set[Int]]: inner sets compare by membership too — the element compare
    // in `member` is the SEMANTIC `Eq.eq`, so dispatch recurses.
    let mut kb = load_kb();
    let i12 = int_set(&mut kb, &[1, 2]);
    let i21 = int_set(&mut kb, &[2, 1]);
    let i3 = int_set(&mut kb, &[3]);
    let a = set_of(&mut kb, &[i12, i3]);
    let b = set_of(&mut kb, &[i3, i21]);
    assert_eq!(
        solutions(&mut kb, "se", a, b),
        1,
        "eq({{{{1,2}},{{3}}}}, {{{{3}},{{2,1}}}}) must hold — elementwise membership equality"
    );
    let i13 = int_set(&mut kb, &[1, 3]);
    let c = set_of(&mut kb, &[i13]);
    let i12b = int_set(&mut kb, &[1, 2]);
    let d = set_of(&mut kb, &[i12b]);
    assert_eq!(
        solutions(&mut kb, "se", c, d),
        0,
        "eq({{{{1,3}}}}, {{{{1,2}}}}) must not hold"
    );
}

#[test]
fn struct_eq_on_sets_stays_structural() {
    // `===` never dispatches: two membership-equal but structurally distinct
    // sets are NOT `===`.
    let mut kb = load_kb();
    let a = int_set(&mut kb, &[1, 2]);
    let b = int_set(&mut kb, &[2, 1]);
    assert_eq!(
        solutions(&mut kb, "sid", a, b),
        0,
        "{{1,2}} === {{2,1}} must not hold — `===` is structural"
    );
    let c = int_set(&mut kb, &[1, 2]);
    let d = int_set(&mut kb, &[1, 2]);
    assert_eq!(solutions(&mut kb, "sid", c, d), 1, "identical spellings are `===`");
}

// ── Map: membership equality incl. put-shadowing ───────────────────────────

#[test]
fn map_eq_ignores_put_order() {
    let mut kb = load_kb();
    let (k1, v1) = (int_term(&mut kb, 1), int_term(&mut kb, 10));
    let (k2, v2) = (int_term(&mut kb, 2), int_term(&mut kb, 20));
    let a = map_of(&mut kb, &[(k1, v1), (k2, v2)]);
    let b = map_of(&mut kb, &[(k2, v2), (k1, v1)]);
    assert_eq!(
        solutions(&mut kb, "se", a, b),
        1,
        "eq({{1→10,2→20}}, {{2→20,1→10}}) must hold"
    );
}

#[test]
fn map_eq_honors_put_shadowing() {
    // put(put(m, k, 10), k, 20): the LATER (outer) put wins — the map equals
    // {k→20}, and does NOT equal {k→10}.
    let mut kb = load_kb();
    let k = int_term(&mut kb, 1);
    let (v10, v20) = (int_term(&mut kb, 10), int_term(&mut kb, 20));
    let shadowed = map_of(&mut kb, &[(k, v10), (k, v20)]);
    let latest = map_of(&mut kb, &[(k, v20)]);
    let stale = map_of(&mut kb, &[(k, v10)]);
    assert_eq!(
        solutions(&mut kb, "se", shadowed, latest),
        1,
        "a shadowed put must equal the latest-binding map"
    );
    assert_eq!(
        solutions(&mut kb, "se", shadowed, stale),
        0,
        "a shadowed put must not equal the stale-binding map"
    );
}

#[test]
fn map_eq_distinguishes_values_and_domains() {
    let mut kb = load_kb();
    let (k1, k2) = (int_term(&mut kb, 1), int_term(&mut kb, 2));
    let (v10, v11) = (int_term(&mut kb, 10), int_term(&mut kb, 11));
    let a = map_of(&mut kb, &[(k1, v10)]);
    let b = map_of(&mut kb, &[(k1, v11)]);
    assert_eq!(solutions(&mut kb, "se", a, b), 0, "same key, different value");
    let c = map_of(&mut kb, &[(k1, v10)]);
    let d = map_of(&mut kb, &[(k1, v10), (k2, v10)]);
    assert_eq!(solutions(&mut kb, "se", c, d), 0, "extra key on one side");
    let e = map_of(&mut kb, &[(k1, v10), (k2, v10)]);
    let f = map_of(&mut kb, &[(k1, v10)]);
    assert_eq!(solutions(&mut kb, "se", e, f), 0, "extra key on the other side");
}

// ── flex operands still delay (Tier B stays gated) ─────────────────────────

#[test]
fn eq_with_unbound_var_still_residualizes() {
    // eq(?x, 1) with ?x unbound: no definite solution — the goal delays and
    // residualizes (WI-519), exactly the pre-WI-616 discipline.
    let mut kb = load_kb();
    let x_name = kb.intern("x");
    let x_vid = kb.fresh_var(x_name);
    let x = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));
    let one = int_term(&mut kb, 1);
    let goal = fn_term(&mut kb, "anthill.prelude.PartialEq.eq", &[x, one]);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert!(
        !sols.is_empty(),
        "eq(?x, 1) must SUSPEND (residual solution), not fail outright"
    );
    assert!(
        sols.iter().all(|s| !s.residual.is_empty()),
        "eq(?x, 1) must not produce a definite solution"
    );
}

// ── nonlinear-head output var (WI-624 regression; Map.binds keeps its LINEAR
// head + `<=>` as an explicit spelling, no longer as a workaround — WI-633
// made the nonlinear form equivalent) ────────────────────────────────────────

#[test]
fn nonlinear_head_output_var_repro() {
    // `rule unbox0(box(v: ?v), ?v)` / `rule unbox1(box(v: ?v), ?v) :- eq(1,1)`:
    // the head is NONLINEAR — ?v occurs inside the compound first arg AND as
    // the whole second arg. Querying with a flex second arg must bind it to
    // the boxed value. Before WI-624 the bodyless variant answered the rule's
    // own `Var(DeBruijn(0))` (the fact fast-path bound `tree_subst` raw) and
    // the bodied variant left the output UNBOUND (`with_fresh_vars` never
    // threaded the head-match value from `body_rename` into the answer link),
    // floundering downstream goals — the shape Map.binds originally had.
    let mut kb = load_kb();
    for pred in ["unbox0", "unbox1"] {
        let v42 = int_term(&mut kb, 42);
        let v_field = kb.intern("v");
        let box_sym = kb.try_resolve_symbol("test.wi616.Box.box").unwrap();
        let boxed = kb.alloc(Term::Fn {
            functor: box_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(v_field, v42)]),
        });
        let out_name = kb.intern("out");
        let out_vid = kb.fresh_var(out_name);
        let out = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(out_vid)));
        let goal = fn_term(&mut kb, &format!("test.wi616.{pred}"), &[boxed, out]);
        let sols = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(sols.len(), 1, "{pred}(box(42), ?out) must have one solution");
        let bound = kb.reify(out, &sols[0].subst);
        assert!(
            reifies_to_int(&kb, &bound, 42),
            "{pred}: ?out must bind to 42 through the nonlinear head, got {bound:?}"
        );
    }
}

#[test]
fn nonlinear_head_cyclic_link_occurs_fails() {
    // `p(box(v: box(v: ?q)), ?q)` against head `p(box(v: ?v), ?v)` requires
    // ?q = box(v: ?q) — an occurs violation, so the match must FAIL (0
    // solutions). The WI-624 link threading routes the query var's own term
    // back into its answer link; without the occurs check in
    // `with_fresh_vars` pass 2 the cyclic σ overflowed the stack in
    // reify/fingerprint (observed: `fatal runtime error: stack overflow`).
    let mut kb = load_kb();
    for pred in ["unbox0", "unbox1"] {
        let v_field = kb.intern("v");
        let box_sym = kb.try_resolve_symbol("test.wi616.Box.box").unwrap();
        let q_name = kb.intern("q");
        let q_vid = kb.fresh_var(q_name);
        let q = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(q_vid)));
        let inner = kb.alloc(Term::Fn {
            functor: box_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(v_field, q)]),
        });
        let outer = kb.alloc(Term::Fn {
            functor: box_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(v_field, inner)]),
        });
        let goal = fn_term(&mut kb, &format!("test.wi616.{pred}"), &[outer, q]);
        let sols = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(
            sols.len(),
            0,
            "{pred}(box(box(?q)), ?q) must occurs-fail with zero solutions"
        );
    }
}

// Nonlinear-head match completeness (WI-633, fixed) — a repeated head var's
// two matched query subterms UNIFY at the discrim leaf
// (`bind_value_unifying` → `unify_match_values`), no longer demanding
// structural identity; the inverse orientation (query var inside the compound
// occurrence, concrete at the bare one) threads through WI-624's
// link-through-rename. Both locked here.

#[test]
fn nonlinear_head_doubly_concrete_unifies() {
    // unbox0(box(v: some(?x)), some(42)): the two ?v occurrences unify,
    // binding ?x = 42. Before WI-633 the discrim match double-bound the
    // rule var structurally (some(?x) vs some(42) differ) and dropped the
    // candidate: silent 0 solutions.
    let mut kb = load_kb();
    let some_sym = kb.try_resolve_symbol("anthill.prelude.Option.some").unwrap();
    let x_name = kb.intern("x");
    let x_vid = kb.fresh_var(x_name);
    let x = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));
    let some_x = kb.alloc(Term::Fn {
        functor: some_sym,
        pos_args: SmallVec::from_elem(x, 1),
        named_args: SmallVec::new(),
    });
    let v42 = int_term(&mut kb, 42);
    let some_42 = kb.alloc(Term::Fn {
        functor: some_sym,
        pos_args: SmallVec::from_elem(v42, 1),
        named_args: SmallVec::new(),
    });
    let v_field = kb.intern("v");
    let box_sym = kb.try_resolve_symbol("test.wi616.Box.box").unwrap();
    let boxed = kb.alloc(Term::Fn {
        functor: box_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(v_field, some_x)]),
    });
    let goal = fn_term(&mut kb, "test.wi616.unbox0", &[boxed, some_42]);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(sols.len(), 1, "unbox0(box(some(?x)), some(42)) must unify");
    let bound = kb.reify(x, &sols[0].subst);
    assert!(
        reifies_to_int(&kb, &bound, 42),
        "?x must unify to 42 through the repeated head var, got {bound:?}"
    );
}

#[test]
fn nonlinear_head_inverse_orientation_binds() {
    // unbox0(box(v: ?out), 42): the query var sits INSIDE the compound
    // occurrence and the concrete value at the bare one — must bind
    // ?out = 42 (the WI-624 review observed it answering definitely with
    // ?out silently unbound; the final link-through-rename fix covers it).
    let mut kb = load_kb();
    let v_field = kb.intern("v");
    let box_sym = kb.try_resolve_symbol("test.wi616.Box.box").unwrap();
    let out_name = kb.intern("out");
    let out_vid = kb.fresh_var(out_name);
    let out = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(out_vid)));
    let boxed = kb.alloc(Term::Fn {
        functor: box_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(v_field, out)]),
    });
    let v42 = int_term(&mut kb, 42);
    let goal = fn_term(&mut kb, "test.wi616.unbox0", &[boxed, v42]);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(sols.len(), 1, "unbox0(box(?out), 42) must have one solution");
    let bound = kb.reify(out, &sols[0].subst);
    assert!(
        reifies_to_int(&kb, &bound, 42),
        "?out must bind to 42 through the inverse orientation, got {bound:?}"
    );
}

#[test]
fn map_binds_unifies_non_ground_stored_value() {
    // Locks the behavior of Map.binds rule 1 (spelled linear + `?v <=> ?v2`):
    // a non-ground stored value must UNIFY with the queried value —
    // binds(put(empty, 1, some(?x)), 1, some(42)) binds ?x = 42, and
    // binds(put(empty, 1, ?y), 1, 42) binds ?y = 42. The nonlinear spelling
    // (`binds(put(?, ?k2, ?v), ?k, ?v)`) used to false-fail the first
    // (structural contradiction drop) and leave ?y unbound in the second —
    // the WI-624 review caught exactly this when the head was briefly made
    // nonlinear; WI-633's leaf unification made the two spellings equivalent.
    let mut kb = load_kb();
    let some_sym = kb.try_resolve_symbol("anthill.prelude.Option.some").unwrap();
    let x_name = kb.intern("x");
    let x_vid = kb.fresh_var(x_name);
    let x = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));
    let some_x = kb.alloc(Term::Fn {
        functor: some_sym,
        pos_args: SmallVec::from_elem(x, 1),
        named_args: SmallVec::new(),
    });
    let k1 = int_term(&mut kb, 1);
    let m = map_of(&mut kb, &[(k1, some_x)]);
    let v42 = int_term(&mut kb, 42);
    let some_42 = kb.alloc(Term::Fn {
        functor: some_sym,
        pos_args: SmallVec::from_elem(v42, 1),
        named_args: SmallVec::new(),
    });
    let k1b = int_term(&mut kb, 1);
    let goal = fn_term(&mut kb, "anthill.prelude.Map.binds", &[m, k1b, some_42]);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let definite: Vec<_> = sols.iter().filter(|s| s.residual.is_empty()).collect();
    assert_eq!(definite.len(), 1, "binds must unify the stored some(?x) with some(42)");
    let bound = kb.reify(x, &definite[0].subst);
    assert!(
        reifies_to_int(&kb, &bound, 42),
        "?x must unify to 42 through binds' body `<=>`, got {bound:?}"
    );

    let y_name = kb.intern("y");
    let y_vid = kb.fresh_var(y_name);
    let y = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(y_vid)));
    let k2 = int_term(&mut kb, 1);
    let m2 = map_of(&mut kb, &[(k2, y)]);
    let k2b = int_term(&mut kb, 1);
    let v42b = int_term(&mut kb, 42);
    let goal2 = fn_term(&mut kb, "anthill.prelude.Map.binds", &[m2, k2b, v42b]);
    let sols2 = kb.resolve(&[goal2], &ResolveConfig::default());
    let definite2: Vec<_> = sols2.iter().filter(|s| s.residual.is_empty()).collect();
    assert_eq!(definite2.len(), 1, "binds must accept the stored bare var ?y");
    let bound2 = kb.reify(y, &definite2[0].subst);
    assert!(
        reifies_to_int(&kb, &bound2, 42),
        "?y must bind to 42 through binds' body `<=>`, got {bound2:?}"
    );
}

// ── soundness guards from the WI-616 code review ───────────────────────────

/// (definite, undecided-residual) solution counts — the first is what a
/// `definite_only` consumer (constraint guards, prove) would see; the second
/// distinguishes SUSPENDED from FAILED.
fn solution_split(kb: &mut KnowledgeBase, pred: &str, a: TermId, b: TermId) -> (usize, usize) {
    let goal = fn_term(kb, &format!("test.wi616.{pred}"), &[a, b]);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let definite = sols.iter().filter(|s| s.residual.is_empty()).count();
    (definite, sols.len() - definite)
}

#[test]
fn dispatch_on_non_ground_operand_suspends_and_never_binds() {
    // eq(put(empty,1,?x), put(empty,1,2)): the carrier overrides eq, but the
    // operand is NON-GROUND — `=` is a test and must never bind (?x := 2 via
    // Map rules would be unification through the back door), and neither may
    // it decide structurally-false. It suspends: no DEFINITE solution either
    // way, for eq and for neq.
    let mut kb = load_kb();
    let k = int_term(&mut kb, 1);
    let v2 = int_term(&mut kb, 2);
    let xn = kb.intern("x");
    let xv = kb.fresh_var(xn);
    let x = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(xv)));
    let m1 = map_of(&mut kb, &[(k, x)]);
    let m2 = map_of(&mut kb, &[(k, v2)]);
    let (def_eq, susp_eq) = solution_split(&mut kb, "se", m1, m2);
    assert_eq!(def_eq, 0, "eq over a non-ground overriding carrier must not decide");
    assert!(susp_eq > 0, "eq over a non-ground overriding carrier must SUSPEND, not fail");
    let (def_ne, susp_ne) = solution_split(&mut kb, "sne", m1, m2);
    assert_eq!(def_ne, 0, "neq over a non-ground overriding carrier must not decide");
    assert!(susp_ne > 0, "neq over a non-ground overriding carrier must SUSPEND, not fail");
    // `=` never binds: the suspended solutions must leave ?x unbound.
    let goal = fn_term(&mut kb, "test.wi616.se", &[m1, m2]);
    for sol in kb.resolve(&[goal], &ResolveConfig::default()) {
        let bound = kb.reify(x, &sol.subst);
        assert!(
            matches!(
                &bound,
                anthill_core::eval::Value::Term { id, .. }
                    if matches!(kb.get_term(*id), Term::Var(_))
            ),
            "eq must never bind an operand variable; ?x got {bound:?}"
        );
    }
}

#[test]
fn buried_override_suspends_instead_of_structural_verdict() {
    // some({1,2}) vs some({2,1}): the operand heads (Option.some) carry no eq
    // override, but a membership-equal Set is BURIED inside — a structural
    // verdict would be wrong in both directions, so the compare suspends
    // (undecided), for eq and neq alike.
    let mut kb = load_kb();
    let s12 = int_set(&mut kb, &[1, 2]);
    let s21 = int_set(&mut kb, &[2, 1]);
    let some1 = fn_term(&mut kb, "anthill.prelude.Option.some", &[s12]);
    let some2 = fn_term(&mut kb, "anthill.prelude.Option.some", &[s21]);
    let (def_eq, susp_eq) = solution_split(&mut kb, "se", some1, some2);
    assert_eq!(def_eq, 0, "eq(some({{1,2}}), some({{2,1}})) must not decide structurally");
    assert!(susp_eq > 0, "eq over a buried override must SUSPEND, not fail");
    let (def_ne, susp_ne) = solution_split(&mut kb, "sne", some1, some2);
    assert_eq!(def_ne, 0, "neq(some({{1,2}}), some({{2,1}})) must not decide structurally");
    assert!(susp_ne > 0, "neq over a buried override must SUSPEND, not fail");
    // Purely structural nesting still decides: some(1) vs some(2) has no
    // reachable override.
    let (one, two) = (int_term(&mut kb, 1), int_term(&mut kb, 2));
    let sa = fn_term(&mut kb, "anthill.prelude.Option.some", &[one]);
    let sb = fn_term(&mut kb, "anthill.prelude.Option.some", &[two]);
    assert_eq!(solutions(&mut kb, "sne", sa, sb), 1, "neq(some(1), some(2)) must hold");
    let sc = fn_term(&mut kb, "anthill.prelude.Option.some", &[one]);
    let sd = fn_term(&mut kb, "anthill.prelude.Option.some", &[two]);
    assert_eq!(solutions(&mut kb, "se", sc, sd), 0, "eq(some(1), some(2)) must not hold");
}

#[test]
fn larger_set_eq_uses_fresh_sub_budget() {
    // 12-element sets in reversed insertion order: the relational derivation
    // consumes O(n²) resolution steps — far past the outer default max_depth
    // of 100. The dispatch sub-resolution runs on its OWN generous budget, so
    // this must still be a definite verdict, not a truncation flounder.
    let mut kb = load_kb();
    let fwd: Vec<i64> = (1..=12).collect();
    let rev: Vec<i64> = (1..=12).rev().collect();
    let a = int_set(&mut kb, &fwd);
    let b = int_set(&mut kb, &rev);
    assert_eq!(solutions(&mut kb, "se", a, b), 1, "12-element permuted sets are equal");
    let a2 = int_set(&mut kb, &fwd);
    let b2 = int_set(&mut kb, &rev);
    assert_eq!(solutions(&mut kb, "sne", a2, b2), 0, "equal 12-element sets are not neq");
    let mut fwd13 = fwd.clone();
    fwd13.push(13);
    let c = int_set(&mut kb, &fwd13);
    let d = int_set(&mut kb, &rev);
    assert_eq!(solutions(&mut kb, "se", c, d), 0, "13-vs-12-element sets differ");
    let c2 = int_set(&mut kb, &fwd13);
    let d2 = int_set(&mut kb, &rev);
    assert_eq!(solutions(&mut kb, "sne", c2, d2), 1, "13-vs-12-element sets are neq");
}
