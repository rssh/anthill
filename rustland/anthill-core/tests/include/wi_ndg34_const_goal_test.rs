//! WI-20260822-NDG34 — A `const` WRITTEN AS A GOAL (spec §5.3, §5.9).
//!
//! A `Bool` const at a goal is the literal it holds, so the goal is the search that
//! literal is: `true` succeeds, `false` fails, at every goal position. It is the J38JE
//! reading of a `Bool`-valued expression in goal position, applied to the name of one.
//! The value is the load-time one a data slot takes (`kb::const_value`): a literal body,
//! another const's value, or a `language rust` `const_map` host value. Any other const at a
//! goal is refused: one of another type names no truth, as `:- 42` names none, and a
//! `Bool` one with no load-time value (a computed body; a host value only a `language cpp`
//! binding supplies) has nothing to fold. A query reads a `Bool` const at a goal the same
//! way, and evaluates a computed one, as it does in a data slot.
//!
//! `flag` is the reference and `flag()` applies a value: refused at a goal as in a value
//! slot and an operation body, and the refusal names the reference.
//!
//! MEASURED BEFORE, on the CLI (`const flag: Bool = true`, `const off: Bool = false`,
//! `const nn: Int64 = 5`):
//!
//! | goal                  | before            | now     |
//! |-----------------------|-------------------|---------|
//! | `:- flag`             | 0                 | 1       |
//! | `:- off`              | 0, by accident    | 0       |
//! | `:- not(flag)`        | **1**, a free proof | 0     |
//! | `:- not(off)`         | 1, by accident    | 1       |
//! | `:- base(2) \| flag`  | 0                 | 1       |
//! | `:- flag = true`      | 1                 | 1       |
//! | `:- nn`               | loads, 0          | refused |
//! | `:- flag()`           | loads, 0          | refused |
//! | `:- not(flag())`      | loads, **1**      | refused |
//! | `?- not(ns.flag)`     | **1**             | 0       |
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ─────────────────────────────────
//!
//! Each back-out MEASURED over this file and the J38JE and KDMQS suites, with temporary
//! switches in one build:
//!
//! * The loader's fold (`Loader::goal_const_value` answering `None`): SIX FAIL —
//!   [`a_bool_const_goal_is_the_search_its_value_is`],
//!   [`every_spelling_of_the_const_is_one_goal`],
//!   [`every_goal_position_reads_it`], [`a_host_supplied_bool_const_folds`], and the
//!   `pconst` row of `wi_j38je_boolean_goal_test::what_the_condition_reading_cannot_yet_reduce`
//!   and the `flag_goal` row of
//!   `wi_kdmqs_const_data_slot_test::a_const_in_a_rule_body_value_slot_is_its_value`. The
//!   typer does not refuse in their place: a `Bool` const whose value is known is the
//!   loader's.
//! * The typer's verdict (`check_goal_atom_reading` not collecting a const goal): FOUR
//!   FAIL — [`a_non_bool_const_goal_is_refused`],
//!   [`a_bool_const_without_a_load_time_value_is_refused`],
//!   [`a_cpp_only_host_const_is_refused_at_a_goal`] and
//!   [`an_applied_const_is_refused_naming_the_reference`] (its goal rows load).
//! * The query's fold (`query_slot_const` answering `None` at a goal): ONE FAILS —
//!   [`a_query_reads_a_bool_const_goal`].
//! * The term walk's fold at a constraint goal (`Loader::term_walk_at_goal` answering
//!   `false`): ONE FAILS — [`a_constraint_goal_reads_a_bool_const`], its `flag` rows
//!   reported violated.
//! * The repair named in the applied-const refusal (`const_applied_as_call` answering
//!   `None`): ONE FAILS — [`an_applied_const_is_refused_naming_the_reference`]; every row
//!   is refused without the repair.
//! * The dotted const refused for its value read on as a projection (the pre-change arm):
//!   ONE FAILS — [`a_dotted_const_refused_in_a_data_slot_is_one_error`], with three errors.
//! * The clause-head refusal (`Loader::refuse_if_const_head` answering `false`): ONE
//!   FAILS — [`a_clause_head_naming_a_const_is_refused`]; every row then loads.
//!
//! `ConstGoalProblem::NotFolded` is reached by no row: it is the verdict on a goal some
//! walk left unfolded, and every walk that builds a rule-body goal folds.
//!
//! PASS EITHER WAY, BY DESIGN: the `flag = true` row (a value slot, folded since
//! WI-20261001-KDMQS) and the `off` rows that answer 0 under both readings, kept beside
//! the rows that separate them; the arrow-typed const row of
//! [`an_applied_const_is_refused_naming_the_reference`], which says the repair is NOT
//! offered for a function value; and [`the_repair_for_a_computed_const_runs`].

use anthill_core::eval::{EvalError, Interpreter, Value};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// DEFINITE solutions of `pattern`: a residual is a withheld verdict, never an answer.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// `ns` with one `rule <name>(1) :- <body>` per row, after `decls`.
fn rules_program(ns: &str, decls: &str, rows: &[(&str, &str, usize)]) -> String {
    let mut src = format!("namespace {ns}\n  import anthill.prelude.{{Int64, Bool}}\n{decls}");
    src.push_str("  rule base(?x) :- ?x = 1\n");
    for (name, body, _) in rows {
        src.push_str(&format!("  rule {name}(1) :- {body}\n"));
    }
    src.push_str("end\n");
    src
}

/// Each row's DEFINITE answer count, asserted, naming the body that missed.
fn assert_rows(kb: &mut KnowledgeBase, ns: &str, rows: &[(&str, &str, usize)]) {
    for (name, body, want) in rows {
        assert_eq!(
            answers(kb, &format!("{ns}.{name}(1)")),
            *want,
            "`:- {body}`"
        );
    }
}

/// The load's errors, failing if it loads clean.
fn refusal(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a load error, but this loaded clean:\n{src}"))
}

const FLAGS: &str = "  const flag: Bool = true\n  const off: Bool = false\n";

#[test]
fn a_bool_const_goal_is_the_search_its_value_is() {
    let rows = [
        ("t_flag", "flag", 1),
        ("t_off", "off", 0),
        ("t_not_flag", "not(flag)", 0),
        ("t_not_off", "not(off)", 1),
        ("t_or_flag", "base(2) | flag", 1),
        ("t_or_off", "base(2) | off", 0),
        ("t_eq", "flag = true", 1),
    ];
    let mut kb = crate::common::load_kb_with(&rules_program("ndg34.a", FLAGS, &rows));
    assert_rows(&mut kb, "ndg34.a", &rows);
}

/// A const named dotted, imported, through another const, and as a sort's member is the
/// same goal.
#[test]
fn every_spelling_of_the_const_is_one_goal() {
    let other = "namespace ndg34.o\n  import anthill.prelude.{Bool}\n  \
                 const oflag: Bool = true\n  const ooff: Bool = false\nend\n";
    let decls = format!(
        "{FLAGS}  import ndg34.o.{{oflag}}\n  const alias_flag: Bool = flag\n  \
         const alias_off: Bool = off\n  \
         sort Cfg\n    entity cfg(n: Int64)\n    const on: Bool = true\n    \
         const down: Bool = false\n  end\n"
    );
    let rows = [
        ("d_flag", "ndg34.s.flag", 1),
        ("d_not_flag", "not(ndg34.s.flag)", 0),
        ("d_off", "ndg34.s.off", 0),
        ("i_flag", "oflag", 1),
        ("i_not_flag", "not(oflag)", 0),
        ("i_off", "ndg34.o.ooff", 0),
        ("i_not_off", "not(ndg34.o.ooff)", 1),
        ("a_flag", "alias_flag", 1),
        ("a_not_flag", "not(alias_flag)", 0),
        ("a_off", "alias_off", 0),
        ("m_on", "Cfg.on", 1),
        ("m_not_on", "not(Cfg.on)", 0),
        ("m_down", "Cfg.down", 0),
    ];
    let src = rules_program("ndg34.s", &decls, &rows);
    let mut kb =
        crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[other, &src]));
    assert_rows(&mut kb, "ndg34.s", &rows);
}

/// Every goal position reads it: a conjunction's either spelling, a disjunction's branch,
/// a bounded quantifier's body, a discharge's consequent.
#[test]
fn every_goal_position_reads_it() {
    let rows = [
        ("c_and", "flag & base(1)", 1),
        ("c_and_off", "off & base(1)", 0),
        ("c_comma", "base(1), flag", 1),
        ("c_comma_off", "base(1), off", 0),
        ("o_both", "off | flag", 1),
        ("o_none", "off | off", 0),
        ("q_all", "(forall ?x in [1, 2]: flag)", 1),
        ("q_none", "(forall ?x in [1, 2]: off)", 0),
        ("h_flag", "(forall(?x), base(?x) -: flag)", 1),
        ("h_off", "(forall(?x), base(?x) -: off)", 0),
    ];
    let mut kb = crate::common::load_kb_with(&rules_program("ndg34.p", FLAGS, &rows));
    assert_rows(&mut kb, "ndg34.p", &rows);
}

/// A non-`Bool` const names no truth, as `:- 42` names none: refused at every goal
/// position, naming the const and its type. It loaded and answered nothing, and under
/// `not(…)` answered one.
#[test]
fn a_non_bool_const_goal_is_refused() {
    let errs = refusal(
        "namespace ndg34.n\n  import anthill.prelude.{Int64, Bool}\n  \
         const nn: Int64 = 5\n  rule base(?x) :- ?x = 1\n  \
         rule r1(1) :- nn\n  rule r2(1) :- not(nn)\n  rule r3(1) :- base(2) | nn\nend\n",
    );
    let at_goal: Vec<&String> = errs
        .iter()
        .filter(|e| {
            e.contains("the const `ndg34.n.nn` of type `Int64` is written as a rule-body GOAL")
        })
        .collect();
    assert_eq!(at_goal.len(), 3, "one refusal per goal: {errs:#?}");
    assert!(
        at_goal[0].contains("`?x = nn`"),
        "the repair is named: {}",
        at_goal[0]
    );
}

/// A `Bool` const whose value the loader cannot know is refused at a goal as it is in a
/// data slot, and for the same reason.
#[test]
fn a_bool_const_without_a_load_time_value_is_refused() {
    let errs = refusal(
        "namespace ndg34.k\n  import anthill.prelude.{Int64, Bool}\n  \
         const nn: Int64 = 5\n  const big: Bool = Int64.gt(nn, 3)\n  \
         rule r(1) :- big\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains(
            "the const `ndg34.k.big` is written as a rule-body GOAL, where a `Bool` const is \
             the search its value is, and that value is not known when the clause loads"
        ) && e.contains("computes its value")),
        "{errs:#?}"
    );
}

/// The repair that refusal names runs: the computation in a `Bool` operation's body, the
/// operation written as the goal.
#[test]
fn the_repair_for_a_computed_const_runs() {
    let rows = [("r_big", "is_big", 1), ("r_not_big", "not(is_big)", 0)];
    let decls = "  const nn: Int64 = 5\n  const big: Bool = Int64.gt(nn, 3)\n  \
                 operation is_big() -> Bool = big\n";
    let mut kb = crate::common::load_kb_with(&rules_program("ndg34.r", decls, &rows));
    assert_rows(&mut kb, "ndg34.r", &rows);
}

fn host_true(_interp: &mut Interpreter, _args: &[Value]) -> Result<Value, EvalError> {
    Ok(Value::Bool(true))
}

fn host_false(_interp: &mut Interpreter, _args: &[Value]) -> Result<Value, EvalError> {
    Ok(Value::Bool(false))
}

/// A `Bool` const whose value is a `language rust` host value folds at a goal as a literal
/// one does. The host functions are an embedder's, registered before the load, because
/// the runtime ships no nullary `Bool` source.
#[test]
fn a_host_supplied_bool_const_folds() {
    let rows = [
        ("h_on", "W.hon", 1),
        ("h_not_on", "not(W.hon)", 0),
        ("h_off", "W.hoff", 0),
        ("h_not_off", "not(W.hoff)", 1),
    ];
    let decls = "  sort W\n    entity w(n: Int64)\n    const hon: Bool\n    \
                 const hoff: Bool\n  end\n  \
                 provides W language rust\n    artifact \"nowhere.rs\"\n    \
                 const_map { hon: \"ndg34_host_true\", hoff: \"ndg34_host_false\" }\n  end\n";
    let src = rules_program("ndg34.h", decls, &rows);
    let mut kb = crate::common::try_load_kb_prepared(&src, |kb| {
        kb.register_host_fn("ndg34_host_true", 0, host_true)
            .expect("an embedder key the runtime does not ship");
        kb.register_host_fn("ndg34_host_false", 0, host_false)
            .expect("an embedder key the runtime does not ship");
    })
    .unwrap_or_else(|errs| panic!("expected a clean load; got: {errs:#?}"));
    assert_rows(&mut kb, "ndg34.h", &rows);
}

/// A host const only a `language cpp` binding supplies has no value this runtime can
/// fold, at a goal as in a data slot.
#[test]
fn a_cpp_only_host_const_is_refused_at_a_goal() {
    let errs = refusal(
        "namespace ndg34.c\n  sort W\n    import anthill.prelude.{Bool}\n    \
         entity w(n: Bool)\n    const cflag: Bool\n  end\n  \
         provides W language cpp\n    artifact \"nowhere.hpp\"\n    \
         const_map { cflag: \"true\" }\n  end\n  \
         rule r(1) :- W.cflag\nend\n",
    );
    assert!(
        errs.iter().any(|e| e
            .contains("the const `ndg34.c.W.cflag` is written as a rule-body GOAL")
            && e.contains("no `language rust` binding block gives it a value")),
        "{errs:#?}"
    );
}

/// `flag` is the reference; `flag()` applies a `Bool` as a function. Refused wherever it
/// is written, and the refusal names the reference. Not for a const of a function type,
/// whose application is another question.
#[test]
fn an_applied_const_is_refused_naming_the_reference() {
    let repair = "`flag` names a const of type `Bool`, a value and not an operation, so \
                  nothing is applied to it: the reference is `flag`";
    for (site, body) in [
        ("goal", "  rule r(1) :- flag()\n"),
        ("negated goal", "  rule r(1) :- not(flag())\n"),
        ("value slot", "  rule r(1) :- flag() = true\n"),
        ("operation body", "  operation g() -> Bool = flag()\n"),
    ] {
        let errs = refusal(&format!(
            "namespace ndg34.f\n  import anthill.prelude.{{Bool}}\n  \
             const flag: Bool = true\n{body}end\n"
        ));
        assert!(
            errs.iter()
                .any(|e| e.contains("flag.apply") && e.contains(repair)),
            "{site}: {errs:#?}"
        );
    }
    let errs = refusal(
        "namespace ndg34.g\n  import anthill.prelude.{Int64}\n  \
         const inc: (Int64) -> Int64 = lambda (x: Int64) -> x + 1\n  \
         operation g() -> Int64 = inc(3)\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("inc.apply"))
            && !errs.iter().any(|e| e.contains("the reference is `inc`")),
        "CONTROL: a function-typed const is not told to drop its arguments: {errs:#?}"
    );
    // A const of another type applied at a goal is refused as one that names no truth: the
    // reference alone would be refused next, and the repairs that hold are the data ones.
    let errs = refusal(
        "namespace ndg34.n2\n  import anthill.prelude.{Int64}\n  \
         const nn: Int64 = 5\n  rule r(1) :- nn()\nend\n",
    );
    assert!(
        errs.iter().any(|e| e
            .contains("the const `ndg34.n2.nn` of type `Int64` is written as a rule-body GOAL")),
        "{errs:#?}"
    );
}

/// A constraint's goal reads a `Bool` const as a rule body's does. An enforced constraint
/// whose consequent is `flag` was reported violated by facts that satisfy it, where its
/// `true` spelling held.
#[test]
fn a_constraint_goal_reads_a_bool_const() {
    let program = |ns: &str, consequent: &str| {
        format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64, Bool}}\n  \
             const flag: Bool = true\n  const off: Bool = false\n  \
             entity item(n: Int64)\n  fact item(n: 1)\n  \
             constraint every: forall ?x: item(n: ?x) -: {consequent}\nend\n"
        )
    };
    crate::common::load_kb_with(&program("ndg34.k1", "flag"));
    crate::common::load_kb_with(&program("ndg34.k2", "ndg34.k2.flag"));
    for (ns, consequent) in [("ndg34.k3", "off"), ("ndg34.k4", "ndg34.k4.off")] {
        let errs = refusal(&program(ns, consequent));
        assert!(
            errs.iter()
                .any(|e| e.contains("integrity constraint 'every' is violated")),
            "CONTROL, `-: {consequent}`: {errs:#?}"
        );
    }
}

/// A query's goal reads a `Bool` const as a rule body's does, and evaluates one whose
/// value is computed, as a query's data slot does.
#[test]
fn a_query_reads_a_bool_const_goal() {
    let mut kb = crate::common::load_kb_with(
        "namespace ndg34.q\n  import anthill.prelude.{Int64, Bool}\n  \
         const flag: Bool = true\n  const off: Bool = false\n  \
         const nn: Int64 = 5\n  const big: Bool = Int64.gt(nn, 3)\nend\n",
    );
    for (pattern, want) in [
        ("ndg34.q.flag", 1),
        ("not(ndg34.q.flag)", 0),
        ("ndg34.q.off", 0),
        ("not(ndg34.q.off)", 1),
        ("ndg34.q.big", 1),
        ("not(ndg34.q.big)", 0),
    ] {
        assert_eq!(answers(&mut kb, pattern), want, "?- {pattern}");
    }
}

/// A dotted const refused for its value in a data slot is one error. It read on as a
/// projection and added two about the walk ("a defect in the walk that built this
/// occurrence"), found while measuring the cpp row above.
#[test]
fn a_dotted_const_refused_in_a_data_slot_is_one_error() {
    let errs = refusal(
        "namespace ndg34.e\n  sort W\n    import anthill.prelude.{Bool}\n    \
         entity w(n: Bool)\n    const cflag: Bool\n  end\n  \
         provides W language cpp\n    artifact \"nowhere.hpp\"\n    \
         const_map { cflag: \"true\" }\n  end\n  \
         rule r(1) :- W.cflag = true\nend\n",
    );
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains("is written in a data slot"), "{errs:#?}");
}

/// A clause whose head names a const is refused, at any arity: the name is one symbol, a
/// goal naming it reads the const, and the clause was reached by no bare goal. Before,
/// `rule flag :- true` beside `const flag: Bool = false` answered `:- flag` through the
/// clause; with the goal reading it would have answered `false` with nothing said.
#[test]
fn a_clause_head_naming_a_const_is_refused() {
    for (kind, clause) in [
        ("fact", "  fact flag\n"),
        ("rule", "  rule flag :- true\n"),
        ("rule", "  rule flag(?x) :- ?x <=> 1\n"),
    ] {
        let errs = refusal(&format!(
            "namespace ndg34.d\n  import anthill.prelude.{{Bool}}\n  \
             const flag: Bool = false\n{clause}end\n"
        ));
        assert!(
            errs.iter().any(|e| e.contains(&format!(
                "this {kind}'s head names the const `ndg34.d.flag`"
            ))),
            "`{}`: {errs:#?}",
            clause.trim()
        );
    }
    let mut kb = crate::common::load_kb_with(
        "namespace ndg34.d2\n  import anthill.prelude.{Bool}\n  \
         const flag: Bool = false\n  rule flagged :- true\n  rule r(1) :- flagged\nend\n",
    );
    assert_eq!(
        answers(&mut kb, "ndg34.d2.r(1)"),
        1,
        "CONTROL: a relation of its own name"
    );
}
