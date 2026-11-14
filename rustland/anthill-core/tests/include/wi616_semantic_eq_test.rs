//! WI-616 / proposal 051 Phase 2 — `=`/`eq` dispatch through the carrier's
//! `Eq` instance.
//!
//! `Eq.eq`/`Eq.neq` are now `BuiltinTag::SemEq`/`SemNeq`: structurally
//! identical operands succeed by reflexivity (every current ground use keeps
//! its answer), and structurally DISTINCT operands dispatch to the carrier
//! sort's OWN `eq` override (the WI-350/WI-444 short-name convention) when one
//! exists — `Set.eq` is the backed non-structural instance, resolved as
//! ordinary SLD rules over the symbolic `insert`/`empty` (membership) algebra.
//! A carrier with no override keeps the structural compare (that IS its `Eq`
//! instance). `===` (struct_eq) stays structural on every carrier.
//!
//! SINCE WI-20260926-K4JGC (proposal 068 §2.3) the `Set` rows answer UNDECIDED: an
//! `insert` / `empty` chain is an operation application no implementation runs, not data,
//! so no comparison over it is decided either way. The dispatch rows over `Int64` and
//! entities are unchanged. `Set`'s route back is WI-20260926-QCJ0B's.
//!
//! `Map` also `provides Eq[T = Map]`, but WI-650 dropped its relational eq and
//! left the override a bodyless placeholder (the WI-625 host bridge will fill
//! it); comparing two Maps is now a LOUD load error, exercised in
//! `map_eq_error_test.rs`.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// Rules driving `eq`/`neq` as rule-body goals over sets and maps built from
/// the symbolic algebra. `se`/`sne` take two already-built values; the point
/// is the body `eq`/`neq` goal dispatching (or not) by carrier.
///
/// SINCE WI-20261105-CBRD2 an equality is its carrier's member (kernel-language §5.3): `se` and
/// `sne` declare `PartialEq` at their own type parameter, and each row asks a query, which
/// passes the instance at its arguments' type to the body's `eq`. Written untyped, both rules
/// are refused at load.
const SRC: &str = r#"
    namespace test.wi616
      import anthill.prelude.{Int64, Eq, Option, PartialEq}
      import anthill.prelude.PartialEq.{eq, neq}
      import anthill.prelude.Option.{some}
      sort Tag
        entity red
        entity blue
      end
      sort Box
        entity box(v: Int64)
      end
      rule se[A](?x: A, ?y: A) :- PartialEq[T = A], eq(?x, ?y)
      rule sne[A](?x: A, ?y: A) :- PartialEq[T = A], neq(?x, ?y)
      rule sid(?x, ?y) :- ?x === ?y
      rule unbox0(box(v: ?v), ?v) :- true
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

/// The query `test.wi616.{pred}(a, b)`, its arguments written in full: the solutions it gets.
fn solutions(kb: &mut KnowledgeBase, pred: &str, a: &str, b: &str) -> usize {
    crate::common::pattern_answer_counts(kb, &format!("test.wi616.{pred}({a}, {b})")).1
}

/// `insert(insert(… empty(), e1 …), en)` over `anthill.prelude.Set`, as query text.
fn set_text(elems: &[String]) -> String {
    elems.iter().fold("anthill.prelude.Set.empty()".to_string(), |s, e| {
        format!("anthill.prelude.Set.insert({s}, {e})")
    })
}

/// [`set_text`] of integers.
fn int_set_text(elems: &[i64]) -> String {
    set_text(&elems.iter().map(|n| n.to_string()).collect::<Vec<_>>())
}

/// Carrier-agnostic "reified to this int" check — a binding can come back as
/// `Value::Int`, a hash-consed `Value::Term(Const)`, or a `Value::Node`
/// occurrence (`Expr::Const` via the `<=>` path); `TermView::head` reads all
/// three.
fn reifies_to_int(kb: &KnowledgeBase, v: &anthill_core::eval::Value, n: i64) -> bool {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    matches!(v.head(kb), ViewHead::Const(Literal::Int(m)) if m == n)
}


// ── ground structural uses keep their answers ─────────────────────────────

#[test]
fn eq_on_ints_unchanged() {
    let mut kb = load_kb();
    assert_eq!(solutions(&mut kb, "se", "7", "7"), 1, "eq(7,7) must hold");
    assert_eq!(solutions(&mut kb, "se", "7", "8"), 0, "eq(7,8) must not hold");
}

#[test]
fn neq_on_ints_unchanged() {
    let mut kb = load_kb();
    assert_eq!(solutions(&mut kb, "sne", "7", "8"), 1, "neq(7,8) must hold");
    assert_eq!(solutions(&mut kb, "sne", "7", "7"), 0, "neq(7,7) must not hold");
}

#[test]
fn eq_on_entities_without_instance_stays_structural() {
    let mut kb = load_kb();
    let (red, blue) = ("test.wi616.Tag.red", "test.wi616.Tag.blue");
    assert_eq!(solutions(&mut kb, "se", red, red), 1, "eq(red,red) must hold");
    assert_eq!(
        solutions(&mut kb, "se", red, blue),
        0,
        "eq(red,blue) must not hold"
    );
}

// ── Set: UNDECIDED since WI-20260926-K4JGC (proposal 068 §2.3) ─────────────
//
// These rows used to answer by MEMBERSHIP: `Set.eq`'s relational rules matched the
// unevaluated `insert` / `empty` terms in their heads. Under 068 an operation application
// is a computation, not data: `Set.insert` / `Set.empty` have no body, no host mapping and
// no provider, so each `insert` chain is an UNREDUCED call and every comparison over one is
// UNDECIDED — never true, never false (068 §2: an UNREDUCED operand makes the comparison
// UNREDUCED). The rows now pin that reading, both directions, so a regression to deciding
// either way shows. `Set`'s own route back to deciding — an implementation, or a quoted
// algebra (068 §1.3) — is WI-20260926-QCJ0B's, and these rows are its acceptance.
//
// FAILS with K4JGC backed out: every row below decides again (`(1, 0)` for an equal pair,
// `(0, 0)` for a different one).

/// `(0, 1)`: no definite answer, one undecided — what every comparison over the symbolic
/// algebra answers now.
const UNDECIDED: (usize, usize) = (0, 1);

#[test]
fn set_eq_over_the_symbolic_algebra_is_undecided() {
    let mut kb = load_kb();
    for (x, y) in [(&[1, 2][..], &[2, 1][..]), (&[1], &[1, 1]), (&[1, 2], &[1, 2])] {
        let (a, b) = (int_set_text(x), int_set_text(y));
        assert_eq!(
            split_at(&mut kb, "se", INT_SET, &a, &b),
            UNDECIDED,
            "eq({x:?}, {y:?}) over `insert` chains: undecided, not held",
        );
    }
    for (x, y) in [(&[1, 2][..], &[1, 3][..]), (&[1], &[1, 2])] {
        let (a, b) = (int_set_text(x), int_set_text(y));
        assert_eq!(
            split_at(&mut kb, "se", INT_SET, &a, &b),
            UNDECIDED,
            "eq({x:?}, {y:?}) over `insert` chains: undecided, not refuted",
        );
    }
}

#[test]
fn set_neq_over_the_symbolic_algebra_is_undecided() {
    let mut kb = load_kb();
    for (x, y) in [(&[1, 2][..], &[1, 3][..]), (&[1, 2], &[2, 1])] {
        let (a, b) = (int_set_text(x), int_set_text(y));
        assert_eq!(
            split_at(&mut kb, "sne", INT_SET, &a, &b),
            UNDECIDED,
            "neq({x:?}, {y:?}) over `insert` chains is undecided",
        );
    }
}

#[test]
fn nested_set_eq_over_the_symbolic_algebra_is_undecided() {
    let mut kb = load_kb();
    let (i12, i21, i3) = (int_set_text(&[1, 2]), int_set_text(&[2, 1]), int_set_text(&[3]));
    let a = set_text(&[i12, i3.clone()]);
    let b = set_text(&[i3, i21]);
    let nested = format!("anthill.prelude.Set[T = {INT_SET}]");
    assert_eq!(split_at(&mut kb, "se", &nested, &a, &b), UNDECIDED);
}

#[test]
fn struct_eq_over_the_symbolic_algebra_is_undecided() {
    // `===` compares the VALUES of its operands (068 §5), and an unreduced call has none —
    // not even two identical spellings are `===` any more.
    let mut kb = load_kb();
    let (a, b) = (int_set_text(&[1, 2]), int_set_text(&[2, 1]));
    assert_eq!(solution_split(&mut kb, "sid", &a, &b), UNDECIDED);
    assert_eq!(solution_split(&mut kb, "sid", &a, &a), UNDECIDED);
}

// ── Map: `Eq[Map]` declared-but-unimplemented is a LOUD type error (WI-650) ──
// The relational `map_eq`/`binds`/`strip_is` apparatus was dropped; `Map` keeps
// `provides Eq[T = Map]` + a bodyless `eq` slot (the WI-625 host bridge will fill
// it). A `=`/`eq`/`neq` over two Maps would otherwise SILENTLY misdecide at
// resolution (`sem_eq_dispatch` sub-resolves the empty override, exhausts, returns
// "not equal"), so the typer rejects it at LOAD. See `map_eq_error_test.rs` for
// the load-failure assertions (this file's `load_kb` never compares maps).

// ── flex operands still delay (Tier B stays gated) ─────────────────────────

#[test]
fn eq_with_unbound_var_still_residualizes() {
    // eq(?x, 1) with ?x unbound: no definite solution — the goal delays and
    // residualizes (WI-519). WI-899 does not reinterpret equations stored under
    // the connective as explicit clauses about the `eq` predicate.
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

// ── nonlinear-head output var (WI-624 regression). The `box`/`unbox` pair
// below is the standalone repro; Map.binds (once the motivating case) is gone
// as of WI-650, but the general nonlinear-head invariants it exercised stay
// covered here and by the WI-633 doubly-concrete/inverse tests. ──────────────

#[test]
fn nonlinear_head_output_var_repro() {
    // `rule unbox0(box(v: ?v), ?v)` / `rule unbox1(box(v: ?v), ?v) :- eq(1,1)`:
    // the head is NONLINEAR — ?v occurs inside the compound first arg AND as
    // the whole second arg. Querying with a flex second arg must bind it to
    // the boxed value. Before WI-624 the bodyless variant answered the rule's
    // own `Var(DeBruijn(0))` (the fact fast-path bound `tree_subst` raw) and
    // the bodied variant left the output UNBOUND (`with_fresh_vars` never
    // threaded the head-match value from `body_rename` into the answer link),
    // floundering downstream goals — the shape Map.binds originally had (WI-650
    // has since removed Map.binds itself).
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
        assert_eq!(
            sols.len(),
            1,
            "{pred}(box(42), ?out) must have one solution"
        );
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
    let some_sym = kb
        .try_resolve_symbol("anthill.prelude.Option.some")
        .unwrap();
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
    assert_eq!(
        sols.len(),
        1,
        "unbox0(box(?out), 42) must have one solution"
    );
    let bound = kb.reify(out, &sols[0].subst);
    assert!(
        reifies_to_int(&kb, &bound, 42),
        "?out must bind to 42 through the inverse orientation, got {bound:?}"
    );
}

// ── soundness guards from the WI-616 code review ───────────────────────────

/// (definite, undecided-residual) solution counts — the first is what a
/// `definite_only` consumer (constraint guards, prove) would see; the second
/// distinguishes SUSPENDED from FAILED.
fn solution_split(kb: &mut KnowledgeBase, pred: &str, a: &str, b: &str) -> (usize, usize) {
    let (definite, total) =
        crate::common::pattern_answer_counts(kb, &format!("test.wi616.{pred}({a}, {b})"));
    (definite, total - definite)
}

/// [`solution_split`] with the relation's type parameter written at `at`: an `insert` chain is
/// an unreduced call, whose type the query does not read off it, so the goal's bracket says it.
fn split_at(kb: &mut KnowledgeBase, pred: &str, at: &str, a: &str, b: &str) -> (usize, usize) {
    solution_split(kb, &format!("{pred}[A = {at}]"), a, b)
}

/// `Set[T = Int64]`, written in full.
const INT_SET: &str = "anthill.prelude.Set[T = anthill.prelude.Int64]";

#[test]
fn dispatch_on_non_ground_operand_suspends_and_never_binds() {
    // eq(insert(empty,?x), insert(empty,2)): the carrier (Set) overrides eq, but
    // the operand is NON-GROUND — `=` is a test and must never bind (?x := 2 via
    // Set rules would be unification through the back door), and neither may it
    // decide structurally-false. It suspends: no DEFINITE solution either way,
    // for eq and for neq. (Re-vehicled from Map onto Set by WI-650, which dropped
    // Map's relational eq; Set keeps its backed membership eq.)
    let mut kb = load_kb();
    let (s1, s2) = (set_text(&["?x".to_string()]), int_set_text(&[2]));
    let (s1, s2) = (s1.as_str(), s2.as_str());
    let (def_eq, susp_eq) = split_at(&mut kb, "se", INT_SET, s1, s2);
    assert_eq!(
        def_eq, 0,
        "eq over a non-ground overriding carrier must not decide"
    );
    assert!(
        susp_eq > 0,
        "eq over a non-ground overriding carrier must SUSPEND, not fail"
    );
    let (def_ne, susp_ne) = split_at(&mut kb, "sne", INT_SET, s1, s2);
    assert_eq!(
        def_ne, 0,
        "neq over a non-ground overriding carrier must not decide"
    );
    assert!(
        susp_ne > 0,
        "neq over a non-ground overriding carrier must SUSPEND, not fail"
    );
    // `=` never binds: the suspended solutions must leave ?x unbound.
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let goal = crate::common::query_pattern_term(&mut kb, &format!("test.wi616.se[A = {INT_SET}]({s1}, {s2})"));
    let written = anthill_core::kb::load::query_goal_as_written(&mut kb, &goal);
    let x = TermView::pos_arg(&written, &kb, 0)
        .and_then(|set| TermView::pos_arg(&set, &kb, 1).map(|x| x.to_value()))
        .expect("`?x` is the inner `insert`'s element");
    for sol in kb.resolve(&[goal], &ResolveConfig::default()) {
        let bound = kb.reify_value(&x, &sol.subst);
        assert!(
            matches!(TermView::head(&bound, &kb), ViewHead::Var(_)),
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
    let some1 = format!("anthill.prelude.Option.some({})", int_set_text(&[1, 2]));
    let some2 = format!("anthill.prelude.Option.some({})", int_set_text(&[2, 1]));
    let (some1, some2) = (some1.as_str(), some2.as_str());
    let some_set = format!("anthill.prelude.Option[T = {INT_SET}]");
    let (def_eq, susp_eq) = split_at(&mut kb, "se", &some_set, some1, some2);
    assert_eq!(
        def_eq, 0,
        "eq(some({{1,2}}), some({{2,1}})) must not decide structurally"
    );
    assert!(
        susp_eq > 0,
        "eq over a buried override must SUSPEND, not fail"
    );
    let (def_ne, susp_ne) = split_at(&mut kb, "sne", &some_set, some1, some2);
    assert_eq!(
        def_ne, 0,
        "neq(some({{1,2}}), some({{2,1}})) must not decide structurally"
    );
    assert!(
        susp_ne > 0,
        "neq over a buried override must SUSPEND, not fail"
    );
    // Purely structural nesting still decides: some(1) vs some(2) has no
    // reachable override.
    let (sa, sb) = ("anthill.prelude.Option.some(1)", "anthill.prelude.Option.some(2)");
    assert_eq!(
        solutions(&mut kb, "sne", sa, sb),
        1,
        "neq(some(1), some(2)) must hold"
    );
    assert_eq!(
        solutions(&mut kb, "se", sa, sb),
        0,
        "eq(some(1), some(2)) must not hold"
    );
}

#[test]
fn larger_set_eq_over_the_symbolic_algebra_is_undecided() {
    // It measured the dispatch sub-resolution's own budget (a 12-element permutation took
    // O(n²) steps and must not truncate). Under 068 §2.3 the comparison never reaches that
    // sub-resolution — its operands are UNREDUCED calls — so it is undecided, the same as
    // the small rows above; the budget is re-measured when WI-20260926-QCJ0B gives `Set` a
    // route back.
    let mut kb = load_kb();
    let fwd: Vec<i64> = (1..=12).collect();
    let rev: Vec<i64> = (1..=12).rev().collect();
    let (a, b) = (int_set_text(&fwd), int_set_text(&rev));
    assert_eq!(split_at(&mut kb, "se", INT_SET, &a, &b), UNDECIDED);
    assert_eq!(split_at(&mut kb, "sne", INT_SET, &a, &b), UNDECIDED);
}
