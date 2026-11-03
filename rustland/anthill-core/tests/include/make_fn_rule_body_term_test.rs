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
//!   Q — WI-20261102-ED298: the same term read LATER was still a call. `make_fn` returned
//!       the application `add(1, 2)`, which is the shape a written call has, so whatever
//!       read it next took it for one: `<=>`'s structural step in the same goal as a
//!       SYMBOLIC call (it waited, so `?t <=> make_fn(…)` bound nothing), the evaluation of
//!       a goal it was spliced into as `Int64.add(1, 2)`. And a call written in a FACT's
//!       field declared `Term` — a head is a pattern, never evaluated — was read back as a
//!       call: `fact Item(code: Int64.add(1, 2))` printed "3". A call held as data is now
//!       the ordinary entity `anthill.reflect.quoted(term: …)`, its own call-shaped parts
//!       quoted too, on whatever carrier it rides: `make_fn` builds one, a value a call
//!       returns is put in that shape (`quoted_code`), and the loader stores a head's
//!       `Term` field so. The evaluation does not go into one; `<=>` unifies two as data;
//!       the code readers (`term_to_string`, `term_functor_name`, `term_field`) read the
//!       code inside; a query whose goal is one runs the call (`lower_leaf`), and a quote
//!       inside a goal stays data, as in the rule-body twin. Measured at
//!       HEAD before Q, the rows of `through_a_binding_it_is_the_term`,
//!       `a_child_bound_by_a_pattern_is_data` and `through_an_operation_it_is_the_term`:
//!       CONDITIONAL rows only, none definite, except `in_list`, `in_box` and
//!       `beside_a_variable`, "3", DEFINITE — a wrong answer; and
//!       `a_head_stores_a_call_in_a_term_field_as_data`'s fact and rule-head rows "3" /
//!       some(3) / "11", definite.
//!
//! BACK-OUT LEDGER, measured: R restored — `a_rule_body_list_reaches_make_fn` and
//! `a_term_make_fn_builds_is_data_not_a_call` FAIL (every row a fault, no definite
//! answer); E restored — `a_term_make_fn_builds_is_data_not_a_call` FAILS (`add` "3",
//! `as_int` some(3), `functor` none, `not_none` holds). Q's parts, one switch each in one
//! build: the evaluator's mint (`evaluate_call`'s `quoted_code`) and `make_fn`'s are each
//! enough for a rule body's `make_fn` — either alone backed out fails nothing, both FAIL
//! `through_a_binding_it_is_the_term`, `a_child_bound_by_a_pattern_is_data`,
//! `through_an_operation_it_is_the_term` and `a_query_reads_the_term_as_a_rule_does`; the
//! loader's head wrap FAILS `a_head_stores_a_call_in_a_term_field_as_data`, and its skip
//! of an equation's head `an_equation_head_is_not_quoted`; `unify_concrete`'s
//! quote arm FAILS `through_a_binding_it_is_the_term` (`unify_diff` waits); the stop in
//! `evaluation_descends` FAILS five tests, the code printer seven, the code readers
//! `a_term_make_fn_builds_is_data_not_a_call` (`functor`), the splice of a quoted goal
//! `a_query_answers_as_its_rule_body_twin` (`runsGoal`). `the_operation_body_twin_agrees` and
//! `a_body_computes_a_term_field_as_an_operation_body_does` pass either way, by design, and
//! so do FDPJ8's carrier rows and SHED7's rigid-variable row (D7's symbolic call is no
//! quote).

use anthill_core::kb::resolve::ResolveConfig;

use crate::common::shown_rows as rows;

const SRC: &str = r#"
namespace t.mkfn
  import anthill.prelude.{Int64, String, Bool, Option, List}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.{Stream, Error}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.reflect.KB.{kb, execute}
  import anthill.reflect.{ResolveStreamFailure}
  import anthill.reflect.LogicalQuery.{pattern_query}
  import anthill.reflect.{Term, term_to_string, as_term, make_fn, term_functor_name, term_as_int, quoted}

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
  rule left(quoted(term: Int64.add(?a, ?)), ?a) :- true
  rule head_child(?r) :- ?t <=> nested(), left(?t, ?a), ?r <=> term_to_string(?a)

  rule beside_a_variable(?r) :-
    ?p <=> List.splitFirst(cons(head: addT(), tail: ?tl)),
    ?p <=> some(value: pair(fst: ?h, snd: ?)),
    ?r <=> term_to_string(?h)
  rule nested_arg(?r) :- ?t <=> addT(), ?r <=> term_to_string(make_fn("anthill.prelude.Option.some", [?t]))

  entity Item(code: Term)
  entity Wrap(i: Item)
  fact Item(code: Int64.add(1, 2))
  fact Wrap(i: Item(code: Int64.add(3, 4)))
  rule mk(Item(code: Int64.add(5, 6))) :- true
  rule fact_field(?s) :- Item(code: ?c), ?s <=> term_to_string(?c)
  rule fact_int(?s) :- Item(code: ?c), ?s <=> term_as_int(?c)
  rule fact_stored(?c) :- Item(code: ?c)
  rule fact_nested(?s) :- Wrap(i: ?i), ?i <=> Item(code: ?c), ?s <=> term_to_string(?c)
  rule rule_head(?s) :- mk(Item(code: ?c)), ?s <=> term_to_string(?c)

  operation built() -> String = term_to_string(Item(code: Int64.add(7, 8)).code)
  rule body_built(?s) :- ?i <=> Item(code: Int64.add(7, 8)), ?i <=> Item(code: ?c), ?s <=> term_to_string(?c)
  rule op_built(?s) :- ?s <=> built()

  fact atLeast(3)
  operation found(goal: Term) -> Int64 effects Error[ResolveStreamFailure] =
    match splitFirst(execute(kb(), pattern_query(term: goal)))
      case none() -> 0
      case some(_) -> 1
  operation runsGoal() -> Int64 effects Error[ResolveStreamFailure] =
    found(make_fn("anthill.prelude.Int64.lt", [as_term(1), as_term(2)]))
  operation findsCode() -> Int64 effects Error[ResolveStreamFailure] =
    found(make_fn("t.mkfn.Item", [addT()]))
  operation codeArg() -> Int64 effects Error[ResolveStreamFailure] =
    found(make_fn("t.mkfn.atLeast", [addT()]))
  rule body_finds_code(1) :- Item(code: quoted(term: Int64.add(1, 2)))
  rule body_code_arg(1) :- atLeast(quoted(term: Int64.add(1, 2)))

  operation tag(i: Item) -> Int64
  rule tag(Item(code: Int64.add(?a, ?b))) <=> ?a @[simp]
  operation useTag() -> Int64 = tag(Item(code: Int64.add(1, 2)))
  rule tagged(?v) :- ?v <=> useTag()

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
            ("var_bound", &[("quoted(term: add(1, 2))", true)]),
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

/// Q in a head: a call written in a field declared `Term` of a fact or a rule head is stored
/// as the data it is there, and read back as the code — at any depth of the head.
#[test]
fn a_head_stores_a_call_in_a_term_field_as_data() {
    assert_eq!(
        table(&["fact_field", "fact_int", "fact_stored", "fact_nested", "rule_head"]),
        expected(&[
            ("fact_field", &[("\"add(1, 2)\"", true)]),
            ("fact_int", &[("none", true)]),
            ("fact_stored", &[("quoted(term: add(1, 2))", true)]),
            ("fact_nested", &[("\"add(3, 4)\"", true)]),
            ("rule_head", &[("\"add(5, 6)\"", true)]),
        ]),
    );
}

/// The control: a construction in a BODY computes, a rule body's as an operation body's —
/// the field holds the value `15`, not a quote, in both.
#[test]
fn a_body_computes_a_term_field_as_an_operation_body_does() {
    assert_eq!(
        table(&["body_built", "op_built"]),
        expected(&[("body_built", &[("\"15\"", true)]), ("op_built", &[("\"15\"", true)])]),
    );
}

/// Q through `execute`, which answers as the same goal written in a rule body (068 §6): a
/// goal `make_fn` built is a quoted call, and it runs (`Int64.lt(1, 2)`); a quote INSIDE a
/// goal stays data — it finds the fact storing that code, and it does not meet `fact
/// atLeast(3)` — and so does the rule-body twin of each.
#[test]
fn a_query_answers_as_its_rule_body_twin() {
    let mut interp = crate::common::interp_for(SRC);
    for (op, want) in [("runsGoal", 1), ("findsCode", 1), ("codeArg", 0)] {
        let r = interp.call(&format!("t.mkfn.{op}"), &[]).expect("the query runs");
        assert!(
            matches!(r, anthill_core::eval::value::Value::Int(n) if n == want),
            "`{op}`: {want} answer(s); got {r:?}"
        );
    }
    assert_eq!(
        table(&["body_finds_code", "body_code_arg"]),
        expected(&[("body_finds_code", &[("1", true)]), ("body_code_arg", &[])]),
    );
}

/// An equation's head is not a pattern stored as data: its subject matches the calls written
/// in the bodies it rewrites, so `tag(Item(code: Int64.add(1, 2)))` is rewritten to `1`.
/// With the loader quoting the subject's `Term` field as a fact's, the rewrite does not fire
/// and the row is one conditional answer (measured).
#[test]
fn an_equation_head_is_not_quoted() {
    assert_eq!(table(&["tagged"]), expected(&[("tagged", &[("1", true)])]));
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

