//! WI-20261013-WPVVY — a labelled call of a builtin-tagged operation answers as its positional
//! twin. A builtin's handler reads its operands by position, and a labelled call reached it
//! labelled — the typer reorders a mixed call into positional order and keeps an all-labelled
//! one's labels — so it found no operand: at a goal `Int64.lt(a: 1, b: 5)` failed definitely
//! (and `not(…)` over it held), in a value slot `Int64.sub(a: 5, b: 1)` was left an undecided
//! residual, and `PartialEq.eq(a: 1, b: 1)` there answered `false`. Both entries now put the
//! call in its parameters' order first (`KnowledgeBase::builtin_call_in_param_order`, through
//! `typing::bound_args`), a `result:` column after them.
//!
//! ## Back-out
//!
//! Each measured alone over this file:
//!   * the goal entry's rewrite skipped (`step_init`, where the builtin tag is first read) —
//!     `a_labelled_builtin_goal_answers_as_its_positional_twin`,
//!     `a_labelled_builtin_query_answers_as_its_positional_twin`,
//!     `a_labelled_builtin_goal_on_a_term_answers_as_on_an_occurrence` and
//!     `a_labelled_builtin_goal_beside_written_clauses_answers_as_its_positional_twin` (each
//!     labelled goal fails, each `not(…)` over one holds), and the goal half of
//!     `labels_that_do_not_fill_the_parameters_are_reported` (nothing is reported);
//!   * the value entry's rewrite skipped (`run_builtin_for_value`) —
//!     `a_labelled_builtin_call_in_a_value_slot_answers_as_its_positional_twin` (the arithmetic
//!     stays a residual, `eq(a: 1, b: 1)` answers `false`), and the operand half of
//!     `labels_that_do_not_fill_the_parameters_are_reported`;
//!   * the goal entry's rewrite made below WI-899's split, in the builtin's candidate alone —
//!     `a_labelled_builtin_goal_beside_written_clauses_answers_as_its_positional_twin` (the
//!     clause's `5.0` is lost);
//!   * a call whose labels do not fill the parameters read as written —
//!     `labels_that_do_not_fill_the_parameters_are_reported` (`not(…)` over it holds, nothing
//!     is reported).
//!
//! Pass either way, by design: the positional twins beside each labelled spelling, and
//! `a_name_no_parameter_list_declares_keeps_its_labels` — `find_dictionary`'s `out:` reaches
//! the rewrite and is left as written, since that name declares no parameters.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// Each answer of the query `pattern`, its names written in full, as whether it is definite:
/// `[true]` holds, `[]` fails.
fn verdicts(kb: &mut KnowledgeBase, pattern: &str) -> Vec<bool> {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .map(|sol| sol.is_definite())
        .collect()
}

const GOALS: &str = r#"
namespace wpvvy.goal
  import anthill.prelude.{PartialOrd, PartialEq}
  rule ltPos() :- Int64.lt(1, 5)
  rule ltLab() :- Int64.lt(a: 1, b: 5)
  rule ltRev() :- Int64.lt(b: 5, a: 1)
  rule ltFalse() :- Int64.lt(a: 5, b: 1)
  rule notLt() :- not(Int64.lt(a: 1, b: 5))
  rule specLt() :- PartialOrd.lt(a: 1, b: 5)
  rule gteLab() :- PartialOrd.gte(a: 5, b: 5)
  rule floatLt() :- Float.lt(a: 1.0, b: 5.0)
  rule strLt() :- String.lt(a: "a", b: "b")
  rule eqLab() :- PartialEq.eq(a: 1, b: 1)
  rule neqLab() :- PartialEq.neq(a: 1, b: 2)
  rule notEq() :- not(PartialEq.eq(a: 1, b: 1))
  rule delayed() :- Int64.lt(a: ?x, b: 5), ?x <=> 1
  fact stored(Int64.lt(a: 1, b: 5))
  rule viaFact() :- stored(?g), ?g
end
"#;

/// AT A GOAL: each labelled spelling holds or fails as `Int64.lt(1, 5)` does — reordered, at a
/// spec operation, at `Float` and `String`, an equality, a goal that waits on its operand, and
/// one read out of a fact. `Int64.lt(a: 1, b: 5)` failed definitely, so `not(…)` over it held.
/// FAILS with the goal entry's rewrite skipped: every labelled goal fails, `notLt` and `notEq`
/// hold.
#[test]
fn a_labelled_builtin_goal_answers_as_its_positional_twin() {
    let mut kb = crate::common::load_kb_with(GOALS);
    for rule in [
        "ltPos", "ltLab", "ltRev", "specLt", "gteLab", "floatLt", "strLt", "eqLab", "neqLab",
        "delayed", "viaFact",
    ] {
        assert_eq!(
            verdicts(&mut kb, &format!("wpvvy.goal.{rule}()")),
            vec![true],
            "`{rule}` holds"
        );
    }
    for rule in ["ltFalse", "notLt", "notEq"] {
        assert_eq!(
            verdicts(&mut kb, &format!("wpvvy.goal.{rule}()")),
            Vec::<bool>::new(),
            "`{rule}` fails"
        );
    }
}

/// AS A QUERY, which the load does not type, so the walk reorders nothing: the labelled goal
/// holds, `not(…)` over it fails, and a `result:` column takes the value (`4` holds, `3` does
/// not). FAILS with the goal entry's rewrite skipped: the first and the `result: 4` query
/// fail, the `not(…)` holds.
#[test]
fn a_labelled_builtin_query_answers_as_its_positional_twin() {
    let mut kb = crate::common::load_stdlib_kb();
    let lt = "anthill.prelude.Int64.lt";
    let sub = "anthill.prelude.Int64.sub";
    assert_eq!(verdicts(&mut kb, &format!("{lt}(a: 1, b: 5)")), vec![true]);
    assert_eq!(
        verdicts(&mut kb, &format!("not({lt}(a: 1, b: 5))")),
        Vec::<bool>::new()
    );
    assert_eq!(
        verdicts(&mut kb, &format!("{sub}(b: 1, a: 5, result: 4)")),
        vec![true]
    );
    assert_eq!(
        verdicts(&mut kb, &format!("{sub}(b: 1, a: 5, result: 3)")),
        Vec::<bool>::new()
    );
}

/// ON A HASH-CONSED TERM, the carrier a host builds a goal on: `lt(a: 1, b: 5)` holds and
/// `sub(b: 1, a: 5, result: ?c)` binds `?c` to 4, as on an occurrence. FAILS with the goal
/// entry's rewrite skipped: neither has an answer.
#[test]
fn a_labelled_builtin_goal_on_a_term_answers_as_on_an_occurrence() {
    let mut kb = crate::common::load_stdlib_kb();
    let int = |kb: &mut KnowledgeBase, n: i64| kb.alloc(Term::Const(Literal::Int(n)));
    let (a, b, result) = (kb.intern("a"), kb.intern("b"), kb.intern("result"));
    let lt = kb
        .try_resolve_symbol("anthill.prelude.Int64.lt")
        .expect("Int64.lt");
    let sub = kb
        .try_resolve_symbol("anthill.prelude.Int64.sub")
        .expect("Int64.sub");
    let (one, five) = (int(&mut kb, 1), int(&mut kb, 5));
    let lt_goal = kb.alloc(Term::Fn {
        functor: lt,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_vec(vec![(a, one), (b, five)]),
    });
    let sols = kb.resolve(&[lt_goal], &ResolveConfig::default());
    assert_eq!(
        sols.iter().map(|s| s.is_definite()).collect::<Vec<_>>(),
        vec![true],
        "`lt` holds"
    );
    let c_name = kb.intern("c");
    let c = kb.fresh_var(c_name);
    let c_term = kb.alloc(Term::Var(Var::Global(c)));
    let sub_goal = kb.alloc(Term::Fn {
        functor: sub,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_vec(vec![(b, one), (a, five), (result, c_term)]),
    });
    let sols = kb.resolve(&[sub_goal], &ResolveConfig::default());
    assert_eq!(
        sols.iter().map(|s| s.is_definite()).collect::<Vec<_>>(),
        vec![true],
        "`sub` answers"
    );
    let answer = kb.answer_binding(c, &sols[0].subst).expect("`?c` is bound");
    assert_eq!(crate::common::scalar_int(&kb, &answer), Some(4));
}

/// BESIDE WRITTEN CLAUSES (WI-899's two candidates, the builtin and the clauses): over
/// `rule gte(?x, 3.0) :- seed899(?x)` beside the native `gte`, `gte(a: ?x, b: 3.0)` answers as
/// `gte(?x, 3.0)` does — the builtin's residual and the clause's `5.0`. The labelled goal
/// reached the clauses labelled, matched no head, and lost the `5.0`. FAILS with the goal
/// entry's rewrite skipped (the labelled goal has no answer), and with it made below the
/// split, in the builtin's candidate alone (the `5.0` is lost).
#[test]
fn a_labelled_builtin_goal_beside_written_clauses_answers_as_its_positional_twin() {
    let src = r#"
namespace wpvvy.clauses
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte}
  fact seed899(5.0)
  rule gte(?x, 3.0) :- seed899(?x)
  rule pos(?x) :- gte(?x, 3.0)
  rule lab(?x) :- gte(a: ?x, b: 3.0)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let pos = crate::common::shown_rows(&mut kb, "wpvvy.clauses.pos");
    assert!(
        pos.contains(&("5.0".to_string(), true)),
        "the clause answers the positional goal: {pos:?}"
    );
    assert_eq!(crate::common::shown_rows(&mut kb, "wpvvy.clauses.lab"), pos);
}

/// LABELS THAT DO NOT FILL THE PARAMETERS ARE SAID, NOT ANSWERED: `Int64.lt(x: 1, y: 5)` —
/// a query, which the load does not type — compares nothing, so `not(…)` over it is
/// undecided and the search names the call, where it held; and `Int64.sub(x: 5, y: 1)` as an
/// operand is a fault of the same text. FAILS with `builtin_call_in_param_order` answering
/// `AsWritten` for such a call: `not(…)` holds, nothing is reported.
#[test]
fn labels_that_do_not_fill_the_parameters_are_reported() {
    let mut kb = crate::common::load_stdlib_kb();
    for (pattern, call) in [
        (
            "not(anthill.prelude.Int64.lt(x: 1, y: 5))",
            "anthill.prelude.Int64.lt",
        ),
        (
            "anthill.prelude.Int64.lt(anthill.prelude.Int64.sub(x: 5, y: 1), 9)",
            "anthill.prelude.Int64.sub",
        ),
    ] {
        let goal = crate::common::query_pattern_term(&mut kb, pattern);
        let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
        assert!(
            sols.iter().all(|s| !s.is_definite()),
            "`{pattern}` has no definite answer"
        );
        let named =
            format!("this call of `{call}` does not fill the parameters it declares (a, b)");
        assert!(
            stats.errors.iter().any(|e| e.message.contains(&named)),
            "`{pattern}` names the call: {:?}",
            stats.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
    }
}

const VALUES: &str = r#"
namespace wpvvy.value
  import anthill.prelude.{PartialEq}
  rule subPos(?c) :- ?c <=> Int64.sub(5, 1)
  rule subLab(?c) :- ?c <=> Int64.sub(a: 5, b: 1)
  rule subRev(?c) :- ?c <=> Int64.sub(b: 1, a: 5)
  rule nested(?c) :- ?c <=> Int64.sub(a: Int64.sub(a: 9, b: 1), b: 3)
  rule divLab(?c) :- ?c <=> Int64.div(a: 9, b: 2)
  rule ltLab(?v) :- ?v <=> Int64.lt(a: 1, b: 5)
  rule eqYes(?v) :- ?v <=> PartialEq.eq(a: 1, b: 1)
  rule eqNo(?v) :- ?v <=> PartialEq.eq(a: 1, b: 2)
  rule operand() :- 4 = Int64.sub(a: 5, b: 1)
end
"#;

/// IN A VALUE SLOT: the labelled arithmetic computes as `Int64.sub(5, 1)` does — reordered,
/// nested and partial — a labelled comparison is its `Bool`, and an `=` operand is decided.
/// FAILS with the value entry's rewrite skipped: the arithmetic and `ltLab` stay undecided
/// residuals, `operand` a conditional one, and `eqYes` answers `false`.
#[test]
fn a_labelled_builtin_call_in_a_value_slot_answers_as_its_positional_twin() {
    let mut kb = crate::common::load_kb_with(VALUES);
    for (rule, n) in [
        ("subPos", 4),
        ("subLab", 4),
        ("subRev", 4),
        ("nested", 5),
        ("divLab", 4),
    ] {
        assert_eq!(
            crate::common::one_definite_int(&mut kb, &format!("wpvvy.value.{rule}")),
            Some(n),
            "`{rule}`"
        );
    }
    for (rule, shown) in [("ltLab", "true"), ("eqYes", "true"), ("eqNo", "false")] {
        assert_eq!(
            crate::common::shown_rows(&mut kb, &format!("wpvvy.value.{rule}")),
            vec![(shown.to_string(), true)],
            "`{rule}`"
        );
    }
    assert_eq!(verdicts(&mut kb, "wpvvy.value.operand()"), vec![true]);
}

/// A NAME NO PARAMETER LIST DECLARES KEEPS ITS LABELS: the clause's `require[…]` is read
/// through `find_dictionary(…, out: ?d)`, a labelled goal of a builtin-tagged name that
/// reaches the rewrite and is not reordered, and the call answers `Meters`' 3. Passes either
/// way by design.
#[test]
fn a_name_no_parameter_list_declares_keeps_its_labels() {
    let src = r#"
namespace wpvvy.req
  import anthill.prelude.{Int64, String}
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(a: A, b: B) -> Int64
    operation tag(b: B) -> Int64
  end
  sort Meters
    entity m(v: Int64)
    provides Conv[A = Meters, B = String]
    operation conv(a: Meters, b: String) -> Int64 = 7
    operation tag(b: String) -> Int64 = 3
  end
  rule t(?r) :- require[Conv[A = Meters, B = String]], ?r <=> Conv.tag("km")
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "wpvvy.req.t"),
        Some(3)
    );
}
