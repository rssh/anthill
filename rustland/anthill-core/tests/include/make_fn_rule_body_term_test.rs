//! `make_fn` called from a rule body: its list argument is read on the carrier the rule
//! hands it, and the term it builds is DATA, not a call (proposal 068 §1.3: a `Term` is a
//! quote's product, and a call is data only inside one).
//!
//! THREE DEFECTS, each a repair of its own. R and E were found delivering
//! WI-20260827-4XXSD:
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
//!   Q — WI-20261102-ED298: the same term read LATER was still a call. `make_fn` returns
//!       the application `add(1, 2)`, which on every carrier is the shape a written call
//!       has, so whatever read it next took it for one: `<=>`'s structural step in the
//!       same goal as a SYMBOLIC call (it waited, so `?t <=> make_fn(…)` bound nothing),
//!       the evaluation of a goal it was spliced into as `Int64.add(1, 2)`. A value a call
//!       returns that is shaped like a call is now carried as `Value::Quoted`, which every
//!       structural reader reads through and no evaluation runs; a child a pattern binds
//!       out of it is marked in turn. Measured at HEAD before Q, the rows of
//!       `through_a_binding_it_is_the_term`, `a_child_bound_by_a_pattern_is_data` and
//!       `through_an_operation_it_is_the_term`: CONDITIONAL rows only, none definite,
//!       except `in_list`, `in_box` and `beside_a_variable`, "3", DEFINITE — a wrong
//!       answer.
//!
//! BACK-OUT LEDGER, measured: R restored — `a_rule_body_list_reaches_make_fn` and
//! `a_term_make_fn_builds_is_data_not_a_call` FAIL (every row a fault, no definite
//! answer); E restored — `a_term_make_fn_builds_is_data_not_a_call` FAILS (`add` "3",
//! `as_int` some(3), `functor` none, `not_none` holds); Q's parts, one switch each — the
//! mint (`quote_returned_value`) and `Value::is_quoted` reading through a σ splice each
//! FAIL `through_a_binding_it_is_the_term`, `a_child_bound_by_a_pattern_is_data`,
//! `through_an_operation_it_is_the_term` and `a_query_reads_the_term_as_a_rule_does`; the
//! child re-mark (`term_view::quoted_child`) FAILS the first two. A first cut that marked
//! a whole value, and none mentioning a variable, answered `beside_a_variable` "3". The
//! FDPJ8 predicates' checks and `evaluation_descends`' drive no row.
//! `the_operation_body_twin_agrees` passes either way, by design, and so do FDPJ8's
//! carrier rows and SHED7's rigid-variable row (D7's symbolic call is unmarked).
//!
//! NOT HERE: a `Term` held in a FACT's field (`fact Holder(code: Int64.add(1, 2))`, read
//! back through `Holder(code: ?c)`) is unmarked — a term stored is its content, and the
//! fact's field is a head, read as a pattern — so it is still read as a call.

use anthill_core::kb::resolve::ResolveConfig;

use crate::common::shown_rows as rows;

const SRC: &str = r#"
namespace t.mkfn
  import anthill.prelude.{Int64, String, Bool, Option, List}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons}
  import anthill.prelude.Pair.{pair}
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
  rule var_bound(?t) :- ?t <=> make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)])

  entity Box(t: Term)
  operation addT() -> Term = make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)])
  operation nested() -> Term =
    make_fn("anthill.prelude.Int64.add", [make_fn("anthill.prelude.Int64.mul", [as_term(2), as_term(3)]), as_term(1)])
  operation show(t: Term) -> String = term_to_string(t)

  rule to_op(?r) :- ?t <=> addT(), ?r <=> show(?t)
  rule shown(?t, ?s) :- ?s <=> term_to_string(?t)
  rule through_rule(?r) :- ?t <=> addT(), shown(?t, ?r)
  rule eq_same(1) :- ?t <=> addT(), ?u <=> addT(), ?t = ?u
  rule eq_diff(1) :- ?t <=> addT(), ?u <=> nested(), ?t = ?u
  rule unify_diff(1) :- ?t <=> addT(), ?u <=> nested(), ?t <=> ?u
  rule not_eq_diff(1) :- ?t <=> addT(), ?u <=> nested(), not(?t = ?u)

  rule in_list(?r) :- ?l <=> [addT()], ?l <=> [?t], ?r <=> term_to_string(?t)
  rule in_box(?r) :- ?b <=> Box(t: addT()), ?b <=> Box(t: ?t), ?r <=> term_to_string(?t)
  rule left(Int64.add(?a, ?), ?a) :- true
  rule head_child(?r) :- ?t <=> nested(), left(?t, ?a), ?r <=> term_to_string(?a)

  rule beside_a_variable(?r) :-
    ?p <=> List.splitFirst(cons(head: addT(), tail: ?tl)),
    ?p <=> some(value: pair(fst: ?h, snd: ?)),
    ?r <=> term_to_string(?h)
  rule nested_arg(?r) :- ?t <=> addT(), ?r <=> term_to_string(make_fn("anthill.prelude.Option.some", [?t]))

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

/// Q: the term bound to a variable is the term wherever the binding is read — printed,
/// read as an integer, compared, handed to an operation, through a rule's head.
#[test]
fn through_a_binding_it_is_the_term() {
    assert_eq!(
        table(&[
            "var_print",
            "var_int",
            "var_not_none",
            "var_bound",
            "to_op",
            "through_rule",
            "eq_same",
            "eq_diff",
            "unify_diff",
            "not_eq_diff",
        ]),
        expected(&[
            ("var_print", &[("\"add(1, 2)\"", true)]),
            ("var_int", &[("none", true)]),
            ("var_not_none", &[]),
            ("var_bound", &[("add(1, 2)", true)]),
            ("to_op", &[("\"add(1, 2)\"", true)]),
            ("through_rule", &[("\"add(1, 2)\"", true)]),
            ("eq_same", &[("1", true)]),
            ("eq_diff", &[]),
            ("unify_diff", &[]),
            ("not_eq_diff", &[("1", true)]),
        ]),
    );
}

/// Q: a term inside a list or an entity, and a child of a term a rule head binds, stay
/// data when a pattern reads them out.
#[test]
fn a_child_bound_by_a_pattern_is_data() {
    assert_eq!(
        table(&["in_list", "in_box", "head_child"]),
        expected(&[
            ("in_list", &[("\"add(1, 2)\"", true)]),
            ("in_box", &[("\"add(1, 2)\"", true)]),
            ("head_child", &[("\"mul(2, 3)\"", true)]),
        ]),
    );
}

/// Q through the interpreter: a term an operation hands back beside a variable it could
/// not bind (`List.splitFirst` over a list whose tail is unbound), and a term nested in an
/// argument a host function reads.
#[test]
fn through_an_operation_it_is_the_term() {
    assert_eq!(
        table(&["beside_a_variable", "nested_arg"]),
        expected(&[
            ("beside_a_variable", &[("\"add(1, 2)\"", true)]),
            ("nested_arg", &[("\"some(value: add(1, 2))\"", true)]),
        ]),
    );
}

/// Q on the carriers no load types (proposal 068 §6): the same conjunction asked as a
/// query, on the occurrences a query pattern is converted to and lowered to terms.
#[test]
fn a_query_reads_the_term_as_a_rule_does() {
    use anthill_core::eval::value::Value;
    use anthill_core::kb::node_occurrence::occurrence_to_term;
    use anthill_core::kb::term::{Term, Var};
    let mut kb = crate::common::load_kb_with(SRC);
    let goals = crate::common::query_goals(
        &mut kb,
        &[
            "?t <=> anthill.reflect.make_fn(\"anthill.prelude.Int64.add\", \
             [anthill.reflect.as_term(1), anthill.reflect.as_term(2)])",
            "?r <=> anthill.reflect.term_to_string(?t)",
        ],
    );
    let terms: Vec<_> = goals.iter().map(|g| occurrence_to_term(&mut kb, g)).collect();
    let Term::Fn { pos_args, .. } = kb.get_term(terms[1]).clone() else {
        panic!("`?r <=> …` is an application")
    };
    let Term::Var(Var::Global(r)) = kb.get_term(pos_args[0]).clone() else {
        panic!("`?r` is a variable")
    };
    for (carrier, goals) in [
        ("occurrence", goals.iter().map(|g| Value::Node(g.clone())).collect::<Vec<_>>()),
        ("term", terms.iter().map(|&t| Value::term(t)).collect()),
    ] {
        let answers: Vec<(String, bool)> = kb
            .resolve(&goals, &ResolveConfig::default())
            .iter()
            .map(|s| {
                let v = kb.answer_binding(r, &s.subst).expect("`?r` is bound");
                (crate::common::show_value(&kb, &v), s.is_definite())
            })
            .collect();
        assert_eq!(answers, vec![("\"add(1, 2)\"".to_string(), true)], "{carrier} carrier");
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
