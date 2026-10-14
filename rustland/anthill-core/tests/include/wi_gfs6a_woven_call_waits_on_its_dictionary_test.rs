//! WI-20261013-GFS6A — proposal 068 §2.1–2.2, the dictionary half: a woven call is SUSPENDED
//! on its dictionary and UNREDUCED where no provider supplies it.
//!
//! A rule-body call of a sort's operation whose carrier is not known at load is woven
//! (WI-20260925-P7VP4): an inferred read `find_dictionary(Sp, op, ?s, out: ?d)` stands before
//! it, and the call carries `?d`. The read derives `?d` from the carrier's VALUE when it runs
//! and waits while the carrier is unbound; the call waits with `?d` among its blockers
//! (WI-20260926-CYNPE's coarse ones), answers once it is bound, and is a conditional answer if
//! it never is. A ground carrier that provides no instance leaves the call UNREDUCED —
//! undecided, its cause named — never a definite failure.
//!
//! BEFORE, measured on the ticket's two programs and on WI-20260923-KCNA0's three:
//!   * over `Sp` with a type parameter (`Car provides Sp[T = Int64]`), the read built `Sp[T =
//!     <wildcard>]` at `Car`, the wildcard met `Car`'s concrete `T = Int64` and was refused, so
//!     a carrier that provides `Sp` found no provider: `sized(car(n: 1), ?x)` and
//!     `dflted(car(n: 1), ?x)` were conditional residuals;
//!   * over `Sp` with none, the read's goal at `Car` took the refinement leaf every sort with no
//!     parameter takes, so `?d` was `Sp`'s own dictionary and `dflted(car(n: 1), ?x)` ran
//!     `Sp`'s default, 7, where `Car` declares 43;
//!   * a read run before its carrier was bound took the variable's BOUND, `Sp`, for the
//!     carrier and bound `Sp`'s own dictionary: `Sp.dflt(?s, ?x), ?s <=> car(n: 1)` answered 7,
//!     and with `?s` never bound, a definite 7;
//!   * a read at a carrier that provides nothing FAILED: `dflted(van(n: 1), ?x)` answered no
//!     solutions and `not(…)` over it held;
//!   * an operation's own `requires` that the call's arguments pin at a carrier no provider
//!     answers was skipped at the bridge, and the body's read of it died
//!     `DeferToRequirement: … not bound in caller frame` — a debug build aborted.
//!
//! ## Back-out
//!
//! MEASURED against this module and `wi_prva2_pre_existing_defects_test` alone
//! (`scripts/test.sh -p anthill-core --test wi_tests -- wi_gfs6a wi_prva2`), each back-out on
//! its own:
//!   * the sibling elements left to the wildcard tail (`witness_sort_goal` not reading the
//!     carrier's provision) — `the_first_program_answers_the_body_less_member` and
//!     `the_first_program_answers_the_defaulted_member` (a conditional row each), and the
//!     parameter half of `a_rule_citing_the_clause_answers`,
//!     `a_dictionary_bound_by_a_later_goal_answers`,
//!     `a_value_slot_whose_dictionary_a_later_goal_binds_answers` and
//!     `a_body_less_call_a_later_goal_grounds_answers` (a conditional row each);
//!   * the provision's element taken where the written bracket names one
//!     (`self_represented_elements`) — `a_written_element_still_selects_the_row` (`wrongT`
//!     answers 42, definitely);
//!   * the anchor's goal left to the wildcard tail (`anchor_sort_goal` not reading the
//!     provision) — the parameter half of
//!     `a_require_anchored_at_a_typed_head_reads_the_carriers_provision`;
//!   * the refinement leaf taken at a goal a receiver made (`resolve_inner`) —
//!     `the_second_program_answers_the_defaulted_member`, and the no-parameter half of
//!     `a_rule_citing_the_clause_answers`, `a_dictionary_bound_by_a_later_goal_answers` and
//!     `a_value_slot_whose_dictionary_a_later_goal_binds_answers` (7 each) and of
//!     `a_require_anchored_at_a_typed_head_reads_the_carriers_provision` (`Sp`'s own);
//!   * an unbound carrier read at its abstract bound (`guard_over_arg_types`) — the
//!     no-parameter half of `a_dictionary_bound_by_a_later_goal_answers` and
//!     `a_value_slot_whose_dictionary_a_later_goal_binds_answers` (7 each), and of
//!     `a_dictionary_never_bound_is_a_conditional_answer` (the read answers);
//!   * an inferred read that finds no provider failing again (`read_dictionary_into`) —
//!     `a_carrier_that_provides_none_leaves_the_call_unreduced` (no solutions), and the four
//!     PRVA2 rows that read `assert_unreduced`;
//!   * the op half's pinned no-provider slot skipped again (`resolve_bridge_requirements_
//!     supplied`) — the three KCNA0 rows (the debug-build panic in `bridge_op_to_eval`);
//!   * the read of that absence a FAULT, as every marker read is (`bridge_disposition`) — the
//!     three KCNA0 rows (a conditional row with no cause).
//!
//! The PRVA2 rows' own back-out — a guard that fires where no provision binds the carriers —
//! leaves a conditional row with NO cause, which `assert_unreduced` refuses: measured with the
//! guard made to fire wherever it refused, which fails those four rows and
//! `a_carrier_that_provides_none_leaves_the_call_unreduced`.
//!
//! NOT DRIVEN: the no-provider arm keeps FAILING a read whose dictionary a citation
//! SUPPLIED (`read_dictionary_into`, `!supplied`) — no program here reaches a supplied
//! dictionary at a carrier that provides nothing.
//!
//! The CONTROLS pass either way, by design, and each says why at its site. Outside this module
//! the ticket's controls pass unchanged: P7VP4's and SHED7's rows, and `classic_mini_test`
//! (tiny-sat 2, alphabet-words 27/12/100, map-colouring 6).

use anthill_core::kb::resolve::{ResolveConfig, Solution, UnknownCause};
use anthill_core::kb::KnowledgeBase;

/// `test.<ns>`: `Sp`, with a type parameter when `param` (and `Car` provides it at `T =
/// Int64`) or without one; `Car`, which declares both members; `Van`, which provides nothing;
/// then `rules`. `Sp.size` is body-less, `Sp.dflt` defaulted.
fn program(ns: &str, param: bool, rules: &str) -> String {
    let (t, provides) = if param {
        ("    sort T = ?\n", "Sp[T = Int64]")
    } else {
        ("", "Sp")
    };
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64}}\n  \
         sort Sp\n{t}    operation size(s: Sp) -> Int64\n    operation dflt(s: Sp) -> Int64 = 7\n  end\n  \
         sort Car\n    entity car(n: Int64)\n    provides {provides}\n    \
         operation size(c: Car) -> Int64 = 42\n    operation dflt(c: Car) -> Int64 = 43\n  end\n  \
         sort Van\n    entity van(n: Int64)\n  end\n{rules}end\n"
    )
}

/// The ticket's two relations.
const SIZED: &str = "  rule sized(?s, ?x) :- Sp.size(?s, ?x)\n";
const DFLTED: &str = "  rule dflted(?s, ?x) :- Sp.dflt(?s, ?x)\n";

/// The solutions of the query `pattern` — asked as a query, untyped, as the ticket asked it.
fn ask(kb: &mut KnowledgeBase, pattern: &str) -> Vec<Solution> {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
}

/// `pattern`'s answers as `(its LAST positional under the solution, the solution is
/// definite)` — the result column of a functional-relation goal, which is where `?r` stands.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> Vec<(Option<i64>, bool)> {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let goal = crate::common::query_pattern_term(kb, pattern);
    let r = match TermView::head(&goal, kb) {
        ViewHead::Functor { pos_arity, .. } if pos_arity > 0 => TermView::pos_arg(&goal, kb, pos_arity - 1)
            .expect("the last positional is readable")
            .to_value(),
        other => panic!("`{pattern}` is not an application: {other:?}"),
    };
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .map(|sol| {
            let v = kb.reify_value(&r, &sol.subst);
            (crate::common::scalar_int(kb, &v), sol.is_definite())
        })
        .collect()
}

/// `pattern`'s one answer, when it is definite and an integer; any other answer set panics,
/// naming it.
#[track_caller]
fn one_int(kb: &mut KnowledgeBase, pattern: &str) -> Option<i64> {
    match answers(kb, pattern).as_slice() {
        [(v, true)] => *v,
        other => panic!("`{pattern}`: expected one definite row, got {other:?}"),
    }
}

/// The causes each solution of `pattern` names for its undecided goals.
fn causes(kb: &mut KnowledgeBase, pattern: &str) -> Vec<Vec<UnknownCause>> {
    ask(kb, pattern)
        .iter()
        .map(|s| s.undecided.iter().map(|(_, c)| *c).collect())
        .collect()
}

// ── the ticket's two programs ───────────────────────────────────────────────────────────

/// (1) `Car provides Sp[T = Int64]`: the read's goal takes `T` from that provision, and the
/// woven body-less call answers `Car`'s member. The body is woven, so the dictionary — not a
/// dispatch on the value — is what answers. Before: a conditional row, the read left as a
/// residual.
#[test]
fn the_first_program_answers_the_body_less_member() {
    let mut kb = crate::common::load_kb_with(&program("gfs6a.one", true, SIZED));
    assert_eq!(
        crate::common::body_calls(&kb, "test.gfs6a.one.sized"),
        vec![
            ("find_dictionary".to_string(), false, Vec::new()),
            ("size".to_string(), true, Vec::new()),
        ],
        "the call is woven behind an inferred read",
    );
    assert_eq!(one_int(&mut kb, "test.gfs6a.one.sized(test.gfs6a.one.Car.car(n: 1), ?r)"), Some(42));
}

/// (1), the defaulted member: `Car`'s, not `Sp`'s default. Before: a conditional row.
#[test]
fn the_first_program_answers_the_defaulted_member() {
    let mut kb = crate::common::load_kb_with(&program("gfs6a.oned", true, DFLTED));
    assert_eq!(
        one_int(&mut kb, "test.gfs6a.oned.dflted(test.gfs6a.oned.Car.car(n: 1), ?r)"),
        Some(43)
    );
}

/// (2) `Sp` with no type parameter: the read's goal at `Car` is answered by `Car`, whose
/// member the defaulted call runs. Before: 7, `Sp`'s default, from `Sp`'s own dictionary.
#[test]
fn the_second_program_answers_the_defaulted_member() {
    let mut kb = crate::common::load_kb_with(&program("gfs6a.twod", false, DFLTED));
    assert_eq!(
        one_int(&mut kb, "test.gfs6a.twod.dflted(test.gfs6a.twod.Car.car(n: 1), ?r)"),
        Some(43)
    );
}

/// (2), the body-less member — CONTROL, passes either way BY DESIGN: `Sp`'s own dictionary
/// named `Sp.size`, which has no body, and the call was then dispatched on its carrier's
/// value. It pins that the same call reads the same member now that the dictionary is `Car`'s.
#[test]
fn the_second_program_answers_the_body_less_member() {
    let mut kb = crate::common::load_kb_with(&program("gfs6a.two", false, SIZED));
    assert_eq!(
        one_int(&mut kb, "test.gfs6a.two.sized(test.gfs6a.two.Car.car(n: 1), ?r)"),
        Some(42)
    );
}

/// The relation CITED from another rule body at a `Car`, over both spellings of `Sp`: the
/// citation's types decide the instance at load, through the same goal the read builds.
/// Before: a conditional row over the parameter, 7 without one.
#[test]
fn a_rule_citing_the_clause_answers() {
    for (ns, param) in [("gfs6a.citep", true), ("gfs6a.cite", false)] {
        let rules = format!("{DFLTED}  rule q(?r) :- dflted(car(n: 1), ?r)\n");
        let mut kb = crate::common::load_kb_with(&program(ns, param, &rules));
        assert_eq!(
            crate::common::one_definite_int(&mut kb, &format!("test.{ns}.q")),
            Some(43),
            "param: {param}",
        );
    }
}

/// CONTROL for the element read off the provision: an element the author WROTE still selects
/// the row. `require[Sp[T = String]]` at a `Car`, which provides `Sp` at `T = Int64` only, has
/// no dictionary and the clause waits — a conditional row; written `T = Int64` it answers 42.
/// FAILS with the provision's element taking the place of the written one: `wrongT` answers 42,
/// definitely, through a requirement that does not hold.
#[test]
fn a_written_element_still_selects_the_row() {
    let rules = "  import anthill.prelude.{String}\n  \
                 rule wrongT(?s, ?r) :- require[Sp[T = String]], Sp.size(?s, ?r)\n  \
                 rule rightT(?s, ?r) :- require[Sp[T = Int64]], Sp.size(?s, ?r)\n";
    let mut kb = crate::common::load_kb_with(&program("gfs6a.written", true, rules));
    assert_eq!(
        answers(&mut kb, "test.gfs6a.written.wrongT(test.gfs6a.written.Car.car(n: 1), ?r)"),
        vec![(None, false)],
        "no row of `Sp` at `T = String` for a `Car`",
    );
    assert_eq!(
        one_int(&mut kb, "test.gfs6a.written.rightT(test.gfs6a.written.Car.car(n: 1), ?r)"),
        Some(42)
    );
}

/// A `require[Sp]` ANCHORED at a typed head, with no call it covers: bound to a `Car` by a
/// later goal, the dictionary it reads is `Car`'s, over both spellings of `Sp`. Before: a
/// conditional row over the parameter (the anchor's goal took `T` as the wildcard), and
/// `Sp`'s own dictionary without one.
#[test]
fn a_require_anchored_at_a_typed_head_reads_the_carriers_provision() {
    for (ns, param) in [("gfs6a.anchp", true), ("gfs6a.anch", false)] {
        let rules = "  rule anchored(s: Sp, ?d) :- ?d = require[Sp]\n  \
                     rule q(?r) :- anchored(?s, ?r), ?s <=> car(n: 1)\n";
        let mut kb = crate::common::load_kb_with(&program(ns, param, rules));
        let rows: Vec<(Option<String>, bool)> = crate::common::query_unary(&mut kb, &format!("test.{ns}.q"))
            .into_iter()
            .map(|(v, definite)| (dictionary_impl(&kb, &v), definite))
            .collect();
        assert_eq!(rows, vec![(Some("Car".to_string()), true)], "param: {param}");
    }
}

/// The local name of the sort a dictionary value's `impl` names, read through the view.
fn dictionary_impl(kb: &KnowledgeBase, v: &anthill_core::eval::Value) -> Option<String> {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let key = v
        .named_keys(kb)
        .into_iter()
        .find(|k| kb.local_name_of(*k) == "impl")?;
    match v.named_arg(kb, key)?.to_value().head(kb) {
        ViewHead::Ident(s) | ViewHead::Functor { functor: Some(s), .. } => {
            Some(kb.local_name_of(s).to_string())
        }
        _ => None,
    }
}

// ── a dictionary a later goal binds ─────────────────────────────────────────────────────

/// The read runs before `?s` is bound, waits on it, and is asked again once `?s <=> car(n: 1)`
/// binds it; the call waits on `?d` and runs `Car`'s member. Before, without the parameter:
/// the read took `?s`'s bound, `Sp`, bound `Sp`'s own dictionary, and the call answered 7.
#[test]
fn a_dictionary_bound_by_a_later_goal_answers() {
    for (ns, param) in [("gfs6a.latep", true), ("gfs6a.latenp", false)] {
        let rules = "  rule late(?r) :- Sp.dflt(?s, ?r), ?s <=> car(n: 1)\n";
        let mut kb = crate::common::load_kb_with(&program(ns, param, rules));
        assert_eq!(
            crate::common::one_definite_int(&mut kb, &format!("test.{ns}.late")),
            Some(43),
            "param: {param}",
        );
    }
}

/// The same with the call in a VALUE slot, where `<=>` waits on the woven call. Before,
/// without the parameter: 7.
#[test]
fn a_value_slot_whose_dictionary_a_later_goal_binds_answers() {
    for (ns, param) in [("gfs6a.valp", true), ("gfs6a.valnp", false)] {
        let rules = "  rule val(?r) :- ?r <=> Sp.dflt(?s), ?s <=> car(n: 1)\n";
        let mut kb = crate::common::load_kb_with(&program(ns, param, rules));
        assert_eq!(
            crate::common::one_definite_int(&mut kb, &format!("test.{ns}.val")),
            Some(43),
            "param: {param}",
        );
    }
}

/// The body-less member under a later binding. Its no-parameter half passes either way BY
/// DESIGN: before, the dictionary `Sp`'s own named `Sp.size`, which has no body, and the call
/// waited for `?s` and was dispatched on its value — the right member by another road. Its
/// parameter half was a conditional row, the read finding no provider once `?s` was bound.
#[test]
fn a_body_less_call_a_later_goal_grounds_answers() {
    for (ns, param) in [("gfs6a.latesp", true), ("gfs6a.latesnp", false)] {
        let rules = "  rule late(?r) :- Sp.size(?s, ?r), ?s <=> car(n: 1)\n";
        let mut kb = crate::common::load_kb_with(&program(ns, param, rules));
        assert_eq!(
            crate::common::one_definite_int(&mut kb, &format!("test.{ns}.late")),
            Some(42),
            "param: {param}",
        );
    }
}

/// `?s` never bound: one CONDITIONAL row whose residual holds the read and the call, and no
/// undecided cause — the call waits, it is not unreduced. Before, without the parameter: a
/// DEFINITE 7, `Sp`'s default answered for a carrier nothing chose.
#[test]
fn a_dictionary_never_bound_is_a_conditional_answer() {
    for (ns, param) in [("gfs6a.neverp", true), ("gfs6a.nevernp", false)] {
        let mut kb = crate::common::load_kb_with(&program(ns, param, DFLTED));
        let sols = ask(&mut kb, &format!("test.{ns}.dflted(?s, ?r)"));
        let [sol] = sols.as_slice() else {
            panic!("param: {param}: one row; got {} solutions", sols.len());
        };
        assert!(!sol.is_definite(), "param: {param}: the call waits for its carrier");
        assert!(sol.undecided.is_empty(), "param: {param}: SUSPENDED, not undecided: {:?}", sol.undecided);
        let held: Vec<String> = sol
            .residual
            .iter()
            .map(|g| crate::common::show_value(&kb, g))
            .collect();
        assert!(
            held.iter().any(|g| g.starts_with("find_dictionary("))
                && held.iter().any(|g| g.starts_with("dflt(")),
            "param: {param}: the read and the call wait: {held:?}",
        );
    }
}

// ── a carrier that provides none ────────────────────────────────────────────────────────

/// `Van` provides no `Sp`: the read finds no provider, and the call has no implementation —
/// UNREDUCED, an undecided row naming its cause, and `not(…)` over it is undecided too.
/// Before: no solutions, and `not(dflted(van(n: 1), 7))` held.
#[test]
fn a_carrier_that_provides_none_leaves_the_call_unreduced() {
    let rules = format!("{DFLTED}  rule notVan(1) :- not(dflted(van(n: 1), 7))\n");
    let mut kb = crate::common::load_kb_with(&program("gfs6a.novan", false, &rules));
    assert_eq!(
        causes(&mut kb, "test.gfs6a.novan.dflted(test.gfs6a.novan.Van.van(n: 1), ?r)"),
        vec![vec![UnknownCause::Unreduced]],
    );
    assert_eq!(
        crate::common::query_unary(&mut kb, "test.gfs6a.novan.notVan")
            .into_iter()
            .map(|(_, definite)| definite)
            .collect::<Vec<_>>(),
        vec![false],
        "the negation of an undecided goal is undecided",
    );
}

// ── WI-20260923-KCNA0: an operation's own requirement no provider answers ───────────────

/// KCNA0's fixture: `Desc` with a body-less `tag`, `Red` providing it, `Blue` providing
/// nothing, `Box` holding an element; then `rest`.
fn kcna0(ns: &str, rest: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64}}\n  \
         sort Desc\n    sort T = ?\n    operation tag() -> Int64\n  end\n  \
         sort Red\n    entity red\n    provides Desc[T = Red]\n    operation tag() -> Int64 = 7\n  end\n  \
         sort Blue\n    entity blue\n  end\n  \
         sort Box\n    sort E = ?\n    entity box(v: E)\n  end\n{rest}end\n"
    )
}

/// `answer`'s one row is undecided, its cause UNREDUCED.
#[track_caller]
fn assert_kcna0_unreduced(src: &str, qn: &str) {
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(crate::common::undecided_causes(&mut kb, qn), vec![vec![UnknownCause::Unreduced]]);
}

/// (q1) A projection the call grounds: `x.E` is `Blue` at `box(v: blue())`, and `Blue`
/// provides no `Desc`. Before: the slot was skipped and the body's read aborted a debug build.
#[test]
fn a_projection_grounded_at_a_carrier_that_provides_none_is_unreduced() {
    assert_kcna0_unreduced(
        &kcna0(
            "gfs6a.q1",
            "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()\n  \
             rule answer(?r) :- pick(box(v: blue()), ?r)\n",
        ),
        "test.gfs6a.q1.answer",
    );
}

/// (q2) A structural former: nothing provides `Desc` at the row `{Red}`. Before: the abort.
#[test]
fn a_structural_former_no_provider_answers_is_unreduced() {
    assert_kcna0_unreduced(
        &kcna0(
            "gfs6a.q2",
            "  operation pick2(x: Box) -> Int64 requires Desc[T = {Red}] = Desc.tag()\n  \
             rule answer(?r) :- pick2(box(v: red()), ?r)\n",
        ),
        "test.gfs6a.q2.answer",
    );
}

/// (fwd) Forwarded through a typed caller, which the load admits — `outer` covers `pick` — and
/// `outer`'s own slot is the unprovided `Desc[T = {Red}]` at the bridge. Before: the abort.
#[test]
fn a_forwarded_requirement_no_provider_answers_is_unreduced() {
    assert_kcna0_unreduced(
        &kcna0(
            "gfs6a.fwd",
            "  operation pick(x: Box) -> Int64 requires Desc[T = {x.E}] = Desc.tag()\n  \
             operation outer(b: Box) -> Int64 requires Desc[T = {b.E}] = pick(b)\n  \
             rule answer(?r) :- outer(box(v: red()), ?r)\n",
        ),
        "test.gfs6a.fwd.answer",
    );
}

/// CONTROL, passes either way BY DESIGN: KCNA0's own — a provided carrier, a bare projection,
/// and the forward at it — each answer 7.
#[test]
fn a_provided_carrier_answers() {
    let src = kcna0(
        "gfs6a.ok",
        "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()\n  \
         operation outer(b: Box) -> Int64 requires Desc[T = b.E] = pick(b)\n  \
         rule direct(?r) :- pick(box(v: red()), ?r)\n  \
         rule forwarded(?r) :- outer(box(v: red()), ?r)\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.gfs6a.ok.direct"), Some(7));
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.gfs6a.ok.forwarded"), Some(7));
}

/// CONTROL, passes either way BY DESIGN: a body that never reads the slot no provider answers
/// runs. The slot was skipped before and is a recorded absence now, refused only where it is
/// read.
#[test]
fn a_body_that_never_reads_the_slot_runs() {
    let src = kcna0(
        "gfs6a.unread",
        "  operation noRead(x: Box) -> Int64 requires Desc[T = x.E] = 5\n  \
         rule answer(?r) :- noRead(box(v: blue()), ?r)\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.gfs6a.unread.answer"), Some(5));
}
