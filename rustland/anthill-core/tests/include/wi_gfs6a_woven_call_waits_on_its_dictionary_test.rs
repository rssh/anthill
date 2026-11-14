//! WI-20261013-GFS6A — proposal 068 §2.1–2.2, the dictionary half: a woven call is SUSPENDED
//! on its dictionary, and the dictionary a provider has reaches it; where no provider has one
//! the requirement is not available and the goal fails.
//!
//! A rule-body call of a sort's operation whose carrier is not known at load is woven
//! (WI-20260925-P7VP4): an inferred read `find_dictionary(Sp, op, ?s, out: ?d)` stands before
//! it, and the call carries `?d`. The read waits while the carrier is unbound; the call waits
//! with `?d` among its blockers (WI-20260926-CYNPE's coarse ones), answers once it is bound,
//! and is a conditional answer if it never is.
//!
//! Since proposal 073 §2 reached rule bodies (WI-20261105-CBRD2, decided with the user
//! 2026-11-14), the read takes `?d` from the instance the carrier holds, and nothing derives it
//! from the carrier's value: a column typed at `Sp` holds instances, and a goal or a query that
//! passes a `Car` there pairs it with `Car`'s dictionary at load. A call at a variable the
//! clause types as a `Car` (`Sp.dflt(?s, ?r), ?s <=> car(n: 1)`) is `Car`'s, decided at load. A
//! value whose sort provides no instance (a `Van`) is refused where the goal is read; before,
//! the goal failed when it ran, stated by a head column's type or unwritten alike — a missing
//! provider is no undecided answer (decided by the user, 2026-10-14).
//!
//! `Sp` receives on itself, so a clause states its requirement by typing a head column at it
//! (`s: Sp`), as an operation types a parameter — the introducer's guard has no carrier
//! parameter of `Sp` to bind. Four rows wrote `require[Sp]` instead, removed by proposal
//! 060.1 §5: three are written so now, and the one whose subject was the read written AFTER
//! the call it covers (`Sp.dflt(?s, ?r), require[Sp]`) is gone — no spelling puts a read
//! there. The back-outs below that name those rows were measured on the removed form.
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
//!   * an operation's own `requires` that the call's arguments pin at a carrier no provider
//!     answers was skipped at the bridge, and the body's read of it died
//!     `DeferToRequirement: … not bound in caller frame` — a debug build aborted;
//!   * an operation that selected its callee's instance (`viaRule[A = Int64, WeakOrd =
//!     Descending](1, 5)`) and was run from a rule lost the selection: the fold bridged the
//!     callee from its argument values and the cited rule answered `Int64`'s own.
//!
//! A goal at a carrier that provides nothing is refused at load: `dflted(van(n: 1), ?x)`, and
//! `not(…)` over it. It FAILED when it ran, as it did before this ticket.
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
//!     `a_value_slot_whose_dictionary_a_later_goal_binds_answers`,
//!     `a_body_less_call_a_later_goal_grounds_answers`,
//!     `a_dictionary_a_later_read_binds_answers` and `an_operation_citing_the_clause_answers`
//!     (a conditional row, or `.head` over an empty answer, each);
//!   * the provision's element taken where the written bracket names one
//!     (`self_represented_elements`) — `a_written_element_still_selects_the_row` (`wrongT`
//!     answers 42, definitely);
//!   * the anchor's goal left to the wildcard tail (`anchor_sort_goal` not reading the
//!     provision) — the parameter half of
//!     `a_require_anchored_at_a_typed_head_reads_the_carriers_provision`;
//!   * a goal built at a carrier type that pins no carrier (`witness_sort_goal` /
//!     `anchor_sort_goal` taking `Sp` itself as the carrier) — the no-parameter `viaSp` of
//!     `an_operation_citing_the_clause_answers` (the citation fills the read with `Sp`'s own
//!     dictionary, the read refuses it, and `.head` raises over an empty answer);
//!   * the refinement leaf taken at a goal a receiver made (`resolve_inner`) —
//!     `the_second_program_answers_the_defaulted_member`, and the no-parameter half of
//!     `a_rule_citing_the_clause_answers`, `a_dictionary_bound_by_a_later_goal_answers`,
//!     `a_value_slot_whose_dictionary_a_later_goal_binds_answers`,
//!     `a_dictionary_a_later_read_binds_answers` and `an_operation_citing_the_clause_answers`
//!     (7 each) and of `a_require_anchored_at_a_typed_head_reads_the_carriers_provision`
//!     (`Sp`'s own);
//!   * an unbound carrier read at its abstract bound (`guard_over_arg_types`) — the
//!     no-parameter half of `a_dictionary_bound_by_a_later_goal_answers` and
//!     `a_value_slot_whose_dictionary_a_later_goal_binds_answers` (7 each), and of
//!     `a_dictionary_never_bound_is_a_conditional_answer` (the read answers);
//!   * a read that finds no provider answered as undecided (`read_dictionary_into`) —
//!     PRVA2's four rows over carriers no provision binds, and the two `Van` rows here until
//!     a `Van` at a column of `Sp` was refused at load (CBRD2);
//!   * the op half's pinned no-provider slot skipped again (`resolve_bridge_requirements_
//!     supplied`) — the three KCNA0 rows (the debug-build panic in `bridge_op_to_eval`);
//!   * the read of that absence a FAULT, as every marker read is (`bridge_disposition`) — the
//!     three KCNA0 rows (the fault on the stream);
//!   * the call that read it left to `stuck_state` (`evaluate_call` not reading
//!     `no_provider_count`) — the three KCNA0 rows (a conditional row);
//!   * a woven call whose `?d` is unbound dispatched on its value instead of waiting
//!     (`reduce_op_value`'s `ApplyWithin` arm) — `a_dictionary_a_later_read_binds_answers`
//!     (the two clauses ask alike) and `a_written_element_still_selects_the_row` (`wrongT`
//!     answers 42);
//!   * the call site's own stamps not carried to the bridge (`WovenDispatch::Stamped`) —
//!     `a_selection_an_operation_makes_reaches_the_rule_from_a_rule_goal` and 0RRQP's
//!     `a_driver_run_as_a_rules_goal_reads_its_selection` (`-1` for `4`);
//!   * the member call a dispatched woven call is rebuilt as keeping the spec op's stamps
//!     (`reduce_op_value`'s `ApplyWithin` arm) — `wi_x9pb4_require_dictionary_element_test::
//!     an_effect_row_element_is_left_to_its_own_owner` (the bridge refuses the member's
//!     slot count: the debug-build panic in `bridge_op_to_eval`);
//!   * a stamp that forwards a caller's slot an ERROR where the bridge has no frame
//!     (`try_eval_requirement_chain_node`) — `a_forwarded_requirement_no_provider_answers_fails`
//!     and `a_provided_carrier_answers` (the debug-build panic in `bridge_op_to_eval`).
//!
//! The CONTROLS pass either way, by design, and each says why at its site. Outside this module
//! the ticket's controls pass unchanged: P7VP4's and SHED7's rows, and `classic_mini_test`
//! (tiny-sat 2, alphabet-words 27/12/100, map-colouring 6).

use anthill_core::kb::resolve::{ResolveConfig, Solution};
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

/// The solutions of the query `pattern`, typed where it is read.
fn ask(kb: &mut KnowledgeBase, pattern: &str) -> Vec<Solution> {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
}

/// `pattern`'s answers as `(its LAST positional under the solution, the solution is
/// definite)` — the result column of a functional-relation goal, which is where `?r` stands.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> Vec<(Option<i64>, bool)> {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let goal = crate::common::query_pattern_term(kb, pattern);
    // The goal as written: a goal that passes its callee a dictionary or an instance rides in
    // its citation marker.
    let written = anthill_core::kb::load::query_goal_as_written(kb, &goal);
    let r = match TermView::head(&written, kb) {
        ViewHead::Functor { pos_arity, .. } if pos_arity > 0 => TermView::pos_arg(&written, kb, pos_arity - 1)
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

/// `qn(?r)` has no answer and the search that said so is COMPLETE — a refutation, not an
/// undecided or faulted search.
#[track_caller]
fn assert_refuted(kb: &mut KnowledgeBase, qn: &str) {
    let goal = crate::common::query_pattern_term(kb, &format!("{qn}(?r)"));
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(sols.is_empty(), "{qn}: no answer; got {} solution(s)", sols.len());
    assert!(!stats.truncated && stats.errors.is_empty(), "{qn}: a complete search: {stats:?}");
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
/// the row. A head column typed `Sp[T = String]` holds no `Car`, which provides `Sp` at `T =
/// Int64` only: the query that passes one is refused where it is read (proposal 073 §2, the
/// value paired at the column at load); typed `Sp[T = Int64]` it answers 42. (Before the
/// pairing, `wrongT` had no row. It was `require[Sp[T = String]]`, removed by proposal 060.1
/// §5, whose clause WAITED — a conditional row, which a missing provider is not; and it FAILED
/// with the provision's element taking the place of the written one, `wrongT` answering 42
/// definitely.)
#[test]
fn a_written_element_still_selects_the_row() {
    let rules = "  import anthill.prelude.{String}\n  \
                 rule wrongT(s: Sp[T = String], ?r) :- Sp.size(s, ?r)\n  \
                 rule rightT(s: Sp[T = Int64], ?r) :- Sp.size(s, ?r)\n";
    let mut kb = crate::common::load_kb_with(&program("gfs6a.written", true, rules));
    let pattern = "test.gfs6a.written.wrongT(test.gfs6a.written.Car.car(n: 1), ?r)";
    crate::common::assert_refused_naming(
        &crate::common::query_pattern_refusals(&mut kb, pattern),
        &["wrongT", "Sp[T = String]", "Car"],
        pattern,
    );
    assert_eq!(
        one_int(&mut kb, "test.gfs6a.written.rightT(test.gfs6a.written.Car.car(n: 1), ?r)"),
        Some(42)
    );
}

/// A head column TYPED AT THE SPEC, bound to a `Car` by a later goal: the call it holds
/// answers `Car`'s member, over both spellings of `Sp`. The row was a `require[Sp]` anchored
/// at the typed head with no call, whose DICTIONARY was asserted to be `Car`'s (before: a
/// conditional row over the parameter — the anchor's goal took `T` as the wildcard — and
/// `Sp`'s own dictionary without one); proposal 060.1 §5 removed the form, and the dictionary
/// is checked by the answer it gives, 43 and not `Sp`'s 7.
#[test]
fn a_require_anchored_at_a_typed_head_reads_the_carriers_provision() {
    for (ns, param) in [("gfs6a.anchp", true), ("gfs6a.anch", false)] {
        let rules = "  rule anchored(s: Sp, ?r) :- Sp.dflt(s, ?r)\n  \
                     rule q(?r) :- anchored(?s, ?r), ?s <=> car(n: 1)\n";
        let mut kb = crate::common::load_kb_with(&program(ns, param, rules));
        assert_eq!(
            crate::common::one_definite_int(&mut kb, &format!("test.{ns}.q")),
            Some(43),
            "param: {param}"
        );
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

/// An OPERATION cites the clause and control passes into the rule: the read derives the
/// dictionary from the value the operation hands over. `viaOp` holds a `Car`, whose type
/// decides the instance at load; `viaSp` holds an `Sp`, which decides none, so the read is
/// left to the value. Before: a conditional row over the parameter, 7 without one; and
/// between, `viaSp` without the parameter FAILED its clause — the citation filled the read
/// with `Sp`'s own dictionary, the read derived `Car`'s, and the two disagreed.
#[test]
fn an_operation_citing_the_clause_answers() {
    for (ns, param) in [("gfs6a.opp", true), ("gfs6a.opnp", false)] {
        let rules = format!(
            "  import anthill.prelude.{{Error, EmptyStream}}\n{DFLTED}  \
             operation viaOp(c: Car) -> Int64 effects {{Error, Error[EmptyStream]}} = dflted(c).head.x\n  \
             operation viaSp(s: Sp) -> Int64 effects {{Error, Error[EmptyStream]}} = dflted(s).head.x\n  \
             operation concrete() -> Int64 effects {{Error, Error[EmptyStream]}} = viaOp(car(n: 1))\n  \
             operation abstract() -> Int64 effects {{Error, Error[EmptyStream]}} = viaSp(car(n: 1))\n"
        );
        let src = program(ns, param, &rules);
        for entry in ["concrete", "abstract"] {
            assert_eq!(
                crate::common::run_int64(&src, &format!("test.{ns}.{entry}")),
                Ok(43),
                "param: {param}, {entry}",
            );
        }
    }
}

/// An operation SELECTS the instance its callee's own `requires` gets, and the callee cites a
/// rule: the selection is the dictionary the rule's woven call runs through, also when the
/// operation is itself run from a rule's goal. `compare(1, 5)` is `4` under `Descending` and
/// `-1` under `Int64`'s own. Rows: the selecting operation run from a rule, the same two
/// operations deep, a selection passed on through an operation that forwards its own
/// requirement, and — CONTROL, either way — the call with no selection. Before: `-1` for the
/// first three, the bridge re-deriving `WeakOrd` at `Int64` from the argument values; run by
/// the interpreter they answered `4` (P7VP4's `ruleDesc`).
#[test]
fn a_selection_an_operation_makes_reaches_the_rule_from_a_rule_goal() {
    let src = r#"
namespace test.gfs6a.sel
  import anthill.prelude.{Int64, Error, EmptyStream, WeakOrd}
  rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)
  operation viaRule[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = cmp(x, y).head.c
  sort Descending
    provides WeakOrd[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = Int64.sub(b, a)
  end
  operation desc(k: Int64) -> Int64 effects {Error, Error[EmptyStream]} =
      viaRule[A = Int64, WeakOrd = Descending](1, 5)
  operation desc2(k: Int64) -> Int64 effects {Error, Error[EmptyStream]} = desc(k)
  operation fwd[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = viaRule(x, y)
  operation fwdDesc(k: Int64) -> Int64 effects {Error, Error[EmptyStream]} =
      fwd[A = Int64, WeakOrd = Descending](1, 5)
  rule selected(?r) :- ?r <=> desc(0)
  rule nested(?r) :- ?r <=> desc2(0)
  rule forwarded(?r) :- ?r <=> fwdDesc(0)
  rule own(?r) :- ?r <=> viaRule(1, 5)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    for (rel, expected) in [("selected", 4), ("nested", 4), ("forwarded", 4), ("own", -1)] {
        assert_eq!(
            crate::common::one_definite_int(&mut kb, &format!("test.gfs6a.sel.{rel}")),
            Some(expected),
            "{rel}",
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

/// `Van` provides no `Sp`, so a `Van` has no instance of it, and a goal that passes one at a
/// column of `Sp` is refused where it is read (proposal 073 §2): a rule body's goal at load,
/// under `not(…)` too, and a query. Before the pairing the goal failed when it ran and `not(…)`
/// over it held — and it FAILED with that read made undecided: one row whose cause is
/// `Unreduced`, and the negation undecided.
#[test]
fn a_carrier_that_provides_none_is_refused() {
    let rules = format!("{DFLTED}  rule notVan(1) :- not(dflted(van(n: 1), 7))\n");
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program("gfs6a.novan", false, &rules)),
        &["dflted", "Sp", "Van"],
        "a goal passing a `Van`",
    );
    let mut kb = crate::common::load_kb_with(&program("gfs6a.novan", false, DFLTED));
    let pattern = "test.gfs6a.novan.dflted(test.gfs6a.novan.Van.van(n: 1), ?r)";
    crate::common::assert_refused_naming(
        &crate::common::query_pattern_refusals(&mut kb, pattern),
        &["dflted", "Sp", "Van"],
        pattern,
    );
}

/// A requirement the AUTHOR stated — a head column typed at the spec, `s: Sp` — at a carrier
/// that provides no instance is refused the same way, as the unwritten one is (the row above).
/// It failed when it ran, before the pairing. (Stated as `require[Sp]` before proposal 060.1 §5
/// removed that form.)
#[test]
fn a_written_require_at_a_carrier_that_provides_none_is_refused() {
    let written = "  rule written(s: Sp, ?r) :- Sp.dflt(s, ?r)\n";
    let rules = format!("{written}  rule notWritten(1) :- not(written(van(n: 1), 43))\n");
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program("gfs6a.wrote", false, &rules)),
        &["written", "Sp", "Van"],
        "a goal passing a `Van`",
    );
    let mut kb = crate::common::load_kb_with(&program("gfs6a.wrote", false, written));
    let pattern = "test.gfs6a.wrote.written(test.gfs6a.wrote.Van.van(n: 1), ?r)";
    crate::common::assert_refused_naming(
        &crate::common::query_pattern_refusals(&mut kb, pattern),
        &["written", "Sp", "Van"],
        pattern,
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

/// The clause `rule answer(?r) :- {goal}` over `decls` is REFUSED AT LOAD: the call's arguments
/// fix the requirement, which no provider answers, as in its operation-body twin
/// (WI-20261013-RYDNV's pinned class). The run-time half is the goal asked as a query, built at
/// run time, which no load types: it has no answer, by a complete search — the call has no
/// value at its arguments. The clause loaded and failed so until RYDNV.
#[track_caller]
fn assert_kcna0_refused_and_fails(ns: &str, decls: &str, goal: &str, query: &str) {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&kcna0(ns, &format!("{decls}  rule answer(?r) :- {goal}\n"))),
        &[&format!("test.{ns}.Desc"), "cannot be supplied for call to", "no impl provides"],
        "the clause, whose call fixes the requirement",
    );
    let mut kb = crate::common::load_kb_with(&kcna0(ns, decls));
    let goal = crate::common::query_pattern_term(&mut kb, query);
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(sols.is_empty(), "{query}: no answer; got {} solution(s)", sols.len());
    assert!(!stats.truncated && stats.errors.is_empty(), "{query}: a complete search: {stats:?}");
}

/// (q1) A projection the call grounds: `x.E` is `Blue` at `box(v: blue())`, and `Blue`
/// provides no `Desc`, so `pick` has no value there and the goal fails. Before: the slot was
/// skipped and the body's read aborted a debug build.
#[test]
fn a_projection_grounded_at_a_carrier_that_provides_none_fails() {
    assert_kcna0_refused_and_fails(
        "gfs6a.q1",
        "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag[T = x.E]()\n",
        "pick(box(v: blue()), ?r)",
        "test.gfs6a.q1.pick(test.gfs6a.q1.Box.box(v: test.gfs6a.q1.Blue.blue()), ?r)",
    );
}

/// (q2) A structural former: nothing provides `Desc` at the row `{Red}`. Before: the abort.
/// Its operation-body twin is refused with the same account (WI-20261013-RYDNV): it loaded,
/// and the call had no value when it ran. FAILS, the twin's half, with the ground arm of
/// `build_op_scoped_dicts`' parked refusals backed out.
#[test]
fn a_structural_former_no_provider_answers_fails() {
    let decl = "  operation pick2(x: Box) -> Int64 requires Desc[T = {Red}] = Desc.tag[T = {Red}]()\n";
    assert_kcna0_refused_and_fails(
        "gfs6a.q2",
        decl,
        "pick2(box(v: red()), ?r)",
        "test.gfs6a.q2.pick2(test.gfs6a.q2.Box.box(v: test.gfs6a.q2.Red.red()), ?r)",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&kcna0(
            "gfs6a.q2op",
            &format!("{decl}  operation twin() -> Int64 = pick2(box(v: red()))\n"),
        )),
        &["test.gfs6a.q2op.Desc[T = {Red}]", "cannot be supplied for call to", "no impl provides"],
        "the operation-body twin",
    );
}

/// (fwd) Forwarded through a typed caller, which the load admits — `outer` covers `pick` — and
/// `outer`'s own slot is the unprovided `Desc[T = {Red}]` at the bridge. Before: the abort.
#[test]
fn a_forwarded_requirement_no_provider_answers_fails() {
    assert_kcna0_refused_and_fails(
        "gfs6a.fwd",
        "  operation pick(x: Box) -> Int64 requires Desc[T = {x.E}] = Desc.tag[T = {x.E}]()\n  \
         operation outer(b: Box) -> Int64 requires Desc[T = {b.E}] = pick(b)\n",
        "outer(box(v: red()), ?r)",
        "test.gfs6a.fwd.outer(test.gfs6a.fwd.Box.box(v: test.gfs6a.fwd.Red.red()), ?r)",
    );
}

/// CONTROL, passes either way BY DESIGN: KCNA0's own — a provided carrier, a bare projection,
/// and the forward at it — each answer 7.
#[test]
fn a_provided_carrier_answers() {
    let src = kcna0(
        "gfs6a.ok",
        "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag[T = x.E]()\n  \
         operation outer(b: Box) -> Int64 requires Desc[T = b.E] = pick(b)\n  \
         rule direct(?r) :- pick(box(v: red()), ?r)\n  \
         rule forwarded(?r) :- outer(box(v: red()), ?r)\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.gfs6a.ok.direct"), Some(7));
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.gfs6a.ok.forwarded"), Some(7));
}

/// CONTROL, passes either way BY DESIGN, at run time: a body that never reads the slot no
/// provider answers runs — the slot was skipped before and is a recorded absence now, refused
/// only where it is read — asked as a query. The CLAUSE that writes the call is refused at
/// load, as its operation-body twin is: the call fixes `Desc[T = Blue]`, and a declared
/// `requires` is owed because it is declared (WI-20261013-RYDNV; it loaded and answered 5).
#[test]
fn a_body_that_never_reads_the_slot_runs() {
    let decl = "  operation noRead(x: Box) -> Int64 requires Desc[T = x.E] = 5\n";
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&kcna0(
            "gfs6a.unreadrule",
            &format!("{decl}  rule answer(?r) :- noRead(box(v: blue()), ?r)\n"),
        )),
        &["test.gfs6a.unreadrule.Desc[T = test.gfs6a.unreadrule.Blue]", "cannot be supplied"],
        "the clause, as its operation-body twin",
    );
    let mut kb = crate::common::load_kb_with(&kcna0("gfs6a.unread", decl));
    assert_eq!(
        answers(
            &mut kb,
            "test.gfs6a.unread.noRead(test.gfs6a.unread.Box.box(v: test.gfs6a.unread.Blue.blue()), ?r)"
        ),
        vec![(Some(5), true)],
    );
}
