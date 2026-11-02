//! `make_fn` called from a rule body: its list argument is read on the carrier the rule
//! hands it, and the term it builds is DATA, not a call (proposal 068 §1.3: a `Term` is a
//! quote's product, and a call is data only inside one).
//!
//! TWO DEFECTS, found delivering WI-20260827-4XXSD, each a repair of its own:
//!   R — `reflect_cons_to_vec` (eval/builtins.rs) matched a `cons`/`nil` spine as a
//!       `Value::Entity` only. A rule body hands its list over as occurrences (`Apply {
//!       cons, head, tail }` down to `Ref(nil)`), so every `make_fn(…, [ … ])` written in a
//!       rule was a type mismatch ("expected List[Term], got Node") and answered nothing,
//!       where the same call in an operation body answers. It reads the spine through the
//!       view now, by the reflect `cons` / `nil` symbols.
//!   E — `evaluate_call` (kb/resolve/evaluate.rs) evaluated again any value a call
//!       returned that is shaped like a call, the bridge's included. With R repaired,
//!       `term_to_string(make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]))`
//!       answered "3", definite: the reflected term `add(1, 2)` was run as `Int64.add(1,
//!       2)`. Only a projection's call (`Box.zero`, a dotted nullary operation) is
//!       evaluated in turn now.
//!
//! BACK-OUT LEDGER, measured: R restored — `a_rule_body_list_reaches_make_fn` and
//! `a_term_make_fn_builds_is_data_not_a_call` FAIL (every row a fault, no definite
//! answer); E restored — `a_term_make_fn_builds_is_data_not_a_call` FAILS (`add` "3",
//! `as_int` some(3), `functor` none, `not_none` holds) and so does
//! `through_a_variable_it_is_undecided` (`var_print` "3", definite);
//! `the_operation_body_twin_agrees` passes either way, by design.
//!
//! WHAT STAYS UNDECIDED: the same term bound to a variable first. The binding holds the
//! entity `add(1, 2)`, and on that carrier an operation-headed application is read as a
//! call wherever a binding is read (the term- and entity-carried goal of
//! WI-20260910-FDPJ8); nothing tells data apart there but a quote (WI-189). The rows are
//! conditional, never a definite wrong answer — `through_a_variable_it_is_undecided`
//! pins that. Tracked by WI-20261102-ED298.

use anthill_core::kb::resolve::ResolveConfig;

use crate::common::shown_rows as rows;

const SRC: &str = r#"
namespace t.mkfn
  import anthill.prelude.{Int64, String, Bool, Option, List}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term, term_to_string, as_term, make_fn, term_functor_name, term_as_int}

  operation callIt(f: () -> Term) -> String = term_to_string(f())
  operation viaOp() -> String =
    term_to_string(make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]))

  rule some1(?r) :- ?r <=> make_fn("anthill.prelude.Option.some", [as_term(1)])
  rule none0(?r) :- ?r <=> make_fn("anthill.prelude.Option.none", [])
  rule listvar(?r) :- ?l <=> [as_term(1)], ?r <=> make_fn("anthill.prelude.Option.some", ?l)
  rule captured(?r) :- ?l <=> [as_term(1)], ?r <=> callIt(lambda () -> make_fn("anthill.prelude.Option.some", ?l))

  rule add(?r) :- ?r <=> term_to_string(make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]))
  rule add_as_term(?r) :- ?r <=> term_to_string(as_term(make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)])))
  rule as_int(?r) :- ?r <=> term_as_int(make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]))
  rule functor(?r) :- ?r <=> term_functor_name(make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]))
  rule not_none(1) :- not(term_as_int(make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)])) = none)

  rule var_print(?r) :- ?t <=> make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]), ?r <=> term_to_string(?t)
  rule var_int(?r) :- ?t <=> make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]), ?r <=> term_as_int(?t)
  rule var_not_none(1) :- ?t <=> make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]), not(term_as_int(?t) = none)

  rule op(?r) :- ?r <=> viaOp()
end
"#;

/// Each relation's answers, rendered and marked definite, compared as one table.
fn table(rels: &[&str]) -> Vec<(String, Vec<(String, bool)>)> {
    let mut kb = crate::common::load_kb_with(SRC);
    rels.iter()
        .map(|rel| (rel.to_string(), rows(&mut kb, &format!("t.mkfn.{rel}"))))
        .collect()
}

fn expected(rows: &[(&str, &[(&str, bool)])]) -> Vec<(String, Vec<(String, bool)>)> {
    rows.iter()
        .map(|(rel, answers)| {
            let answers = answers.iter().map(|(v, d)| (v.to_string(), *d)).collect();
            (rel.to_string(), answers)
        })
        .collect()
}

/// R: the list a rule writes reaches `make_fn` — literal, empty, bound to a variable, and
/// captured by a lambda the rule hands an operation.
#[test]
fn a_rule_body_list_reaches_make_fn() {
    assert_eq!(
        table(&["some1", "none0", "listvar", "captured"]),
        expected(&[
            ("some1", &[("some(value: 1)", true)]),
            ("none0", &[("none", true)]),
            ("listvar", &[("some(value: 1)", true)]),
            ("captured", &[("\"some(value: 1)\"", true)]),
        ]),
    );
}

/// E: the term `make_fn` builds is read as the term it is. `add(1, 2)` has no integer
/// reading, and its functor is `add`.
#[test]
fn a_term_make_fn_builds_is_data_not_a_call() {
    assert_eq!(
        table(&["add", "add_as_term", "as_int", "functor", "not_none"]),
        expected(&[
            ("add", &[("\"add(1, 2)\"", true)]),
            ("add_as_term", &[("\"add(1, 2)\"", true)]),
            ("as_int", &[("none", true)]),
            ("functor", &[("some(value: \"add\")", true)]),
            ("not_none", &[]),
        ]),
    );
}

/// The known limit, held to soundness: through a variable the answers are conditional,
/// and none is definite.
#[test]
fn through_a_variable_it_is_undecided() {
    let mut kb = crate::common::load_kb_with(SRC);
    for rel in ["var_print", "var_int", "var_not_none"] {
        let goal = crate::common::query_pattern_term(&mut kb, &format!("t.mkfn.{rel}(?r)"));
        let sols = kb.resolve(&[goal], &ResolveConfig::default());
        assert!(
            sols.iter().all(|s| !s.is_definite()),
            "`{rel}`: a term read as a call through a binding answers nothing definite"
        );
    }
}

/// The same call in an operation body, run by the bridge: the interpreter has always read
/// the term as data.
#[test]
fn the_operation_body_twin_agrees() {
    assert_eq!(
        table(&["op"]),
        expected(&[("op", &[("\"add(1, 2)\"", true)])]),
    );
}
