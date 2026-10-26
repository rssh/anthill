//! WI-20261024-QJ6X1 — a host builtin judges a value, not its carrier.
//!
//! THE RULE. A `Map` key, and a reflect builder's or decoder's `Term` argument, is read
//! through the carrier-neutral view: an entity or a tuple an operation built
//! (`Value::Entity`, `Value::Tuple`), the term a fact holds (`Value::Term`) and an
//! occurrence a rule body binds (`Value::Node`) are one value, so they address one `Map`
//! slot, build one term and decode alike. Keying a map interns nothing. An unbound
//! variable is no key, and a value with nothing to read — a closure, a runtime handle —
//! stays a type error. A store keeps a TERM, so `persist` / `update` / `retrieve` lower
//! their row, through the boundary that reads every carrier.
//!
//! EVERY ROW HAS ITS OWN SOURCE: a row that shares a fixture with another measures the
//! fixture.
//!
//! CONTROLS — measured on the parent commit, the whole change backed out.
//!
//!   FAIL, the key refused (`expected Map key (Int / Bool / String / Symbol / Term)`):
//!     a_let_bound_tuple_keys_a_map, a_tuple_parameter_keys_a_map,
//!     an_operation_built_tuple_keys_a_map — `got Tuple`
//!     an_operation_built_entity_keys_a_map, one_value_is_one_key_on_every_carrier,
//!     two_values_are_two_keys_on_every_carrier,
//!     make_fn_of_a_constructor_is_the_constructors_value — `got Entity`
//!   FAIL, answering nothing (the operation-built key refused, the clause undecided):
//!     a_facts_tuple_and_an_operation_built_one_are_one_key
//!     an_operation_built_tuple_and_a_facts_one_are_one_key
//!     a_facts_entity_and_an_operation_built_one_are_one_key
//!   FAIL, the argument refused (`expected Term`):
//!     make_fn_takes_an_entity_an_operation_built, make_fn_builds_one_term_from_every_carrier,
//!     replace_named_arg_takes_an_entity_an_operation_built,
//!     replace_named_arg_reads_every_carrier — `got Entity`
//!     make_fn_takes_a_tuple_an_operation_built, a_tuple_decodes_as_no_entity,
//!     a_tuple_decodes_as_no_entity_on_every_carrier — `got Tuple`
//!   FAIL, a wrong answer:
//!     an_application_with_an_undeclared_argument_decodes_as_no_entity — `some(…)` on the
//!       native carrier, the undeclared argument dropped
//!     make_fn_refuses_more_arguments_than_the_constructor_declares — built `bx(1, 2)`
//!     a_variable_is_no_key — a term-carried variable was keyed
//!     a_map_lookup_interns_nothing — the occurrence key was interned, two terms
//!   FAIL, the store refusing an occurrence (`UnsupportedVariant("Node")`):
//!     a_fact_an_occurrence_carries_is_persisted, retrieve_takes_a_pattern_an_occurrence_carries
//!       — as an `Internal` error
//!     an_update_an_occurrence_carries_replaces_the_row — raised, `update failed`
//!
//!   FAIL with one mechanism backed out, and no other row:
//!     a_tuple_decodes_as_no_entity_on_every_carrier — the ordered-product test in
//!       `materialize_entity`: the unit decodes as `some(TupleLiteral())`. A tuple with
//!       components is caught by the undeclared-argument test as well.
//!     an_application_with_an_undeclared_argument_decodes_as_no_entity — that test
//!     make_fn_of_a_constructor_is_the_constructors_value,
//!     make_fn_refuses_more_arguments_than_the_constructor_declares — `make_fn` naming a
//!       constructor's arguments by its fields; with it out, the three `make_fn` rows that
//!       print fail as well, on the positional text `pk(bx(v: 1), 1)`
//!     a_runtime_handle_inside_a_builders_argument_is_no_term — the depth half of
//!       `expect_term_operand` (`bears_opaque`)
//!     a_variable_is_no_key — the variable arm of `MapKey::of_value`
//!     a_runtime_handle_is_no_key — `is_opaque_free` in `MapKey::of_value`, for the handle
//!       inside an entity
//!
//!   PASS with the change backed out, by design:
//!     a_tuple_written_in_the_call_keys_a_map, the_unit_keys_a_map — a tuple written inside
//!       the call reaches the builtin as a term or an occurrence, which keyed
//!     a_facts_tuple_keys_a_map, a_facts_entity_keys_a_map — the fact's own key, put and got
//!     a_key_read_back_addresses_its_slot — the occurrence key was interned and read back
//!       as its term
//!     an_entity_decodes_on_every_carrier, a_literal_decodes_as_no_entity
//!     a_runtime_handle_is_no_key, a_runtime_handle_is_no_term,
//!     a_runtime_handle_inside_a_builders_argument_is_no_term, replace_named_arg_refuses_a_literal
//!       — a type error either way; the parent refused every entity argument
//!
//! NOT A ROW: a rule-body call of an operation whose body is one expression hands a host
//! builtin the operation's PARAMETER as an occurrence of its name — `?r <=> op(1)` with
//! `op(n) = term_to_string(as_term(n))` answers `"n"`, on the parent too. A rule-body row
//! through `replace_named_arg` would measure that, so the rows that need a fact-read or an
//! occurrence-carried argument hand it to the operation directly.

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::node_occurrence::{value_as_occurrence, value_to_term};
use anthill_core::persistence::file_store::{FileConvention, FileStore};
use anthill_core::persistence::indexed_file_store::IndexedFileStore;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{interp_for, load_kb_with, query_unary, run_int64};

/// `test.<name>`, holding the declarations the rows share and `body`.
fn ns(name: &str, body: &str) -> String {
    format!(
        "namespace test.{name}
  import anthill.prelude.{{Int64, String, List, Map, Option, Unit}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.reflect.{{Term, make_fn, replace_named_arg, term_as_entity, as_term, term_to_string}}
  sort Box
    entity bx(v: Int64)
  end
  sort Pk
    entity pk(a: Int64, b: Int64)
  end
  operation mkb(n: Int64) -> Box = Box.bx(n)
  operation mp(n: Int64) -> (Int64, Int64) = (n, 2)
  operation look(m: Map[K = (Int64, Int64), V = Int64], k: (Int64, Int64)) -> Int64 =
    match m.get(k)
      case some(v) -> v
      case none() -> 0
  operation lookB(m: Map[K = Box, V = Int64], k: Box) -> Int64 =
    match m.get(k)
      case some(v) -> v
      case none() -> 0
{body}
end
"
    )
}

#[track_caller]
fn assert_runs(src: &str, entry: &str, expected: i64) {
    assert_eq!(run_int64(src, entry), Ok(expected), "{entry}");
}

#[track_caller]
fn assert_answers(src: &str, rule: &str, expected: i64) {
    let mut kb = load_kb_with(src);
    let answers = query_unary(&mut kb, rule);
    assert!(
        matches!(answers.as_slice(), [(Value::Int(n), true)] if *n == expected),
        "{rule}: {answers:?}"
    );
}

/// What the entry point answers, printed.
#[track_caller]
fn call_printed(interp: &mut Interpreter, entry: &str, args: &[Value]) -> String {
    let v = interp
        .call(entry, args)
        .unwrap_or_else(|e| panic!("{entry}: {e:?}"));
    match v {
        Value::Str(s) => s,
        other => TermPrinter::new(interp.kb()).print_value(&other),
    }
}

/// `v` on its three carriers: as built, as the term a fact holds, as an occurrence.
fn carriers(interp: &mut Interpreter, v: &Value) -> [(&'static str, Value); 3] {
    let term = value_to_term(interp.kb_mut(), v).expect("the value has a term form");
    let node = value_as_occurrence(interp.kb_mut(), v);
    [
        ("native", v.clone()),
        ("term", Value::term(term)),
        ("node", Value::Node(node)),
    ]
}

fn empty_map(interp: &mut Interpreter) -> Value {
    interp.call("anthill.prelude.Map.empty", &[]).expect("Map.empty")
}

/// `Map.get(Map.put(empty, put_key, 4), get_key)`, as the `Int64` it holds, or `None`.
fn put_then_get(interp: &mut Interpreter, put_key: &Value, get_key: &Value) -> Option<i64> {
    let m = empty_map(interp);
    let m = interp
        .call("anthill.prelude.Map.put", &[m, put_key.clone(), Value::Int(4)])
        .expect("Map.put");
    let got = interp
        .call("anthill.prelude.Map.get", &[m, get_key.clone()])
        .expect("Map.get");
    option_int(interp, &got)
}

fn option_int(interp: &Interpreter, v: &Value) -> Option<i64> {
    let Value::Entity { functor, named, .. } = v else {
        panic!("expected an Option, got {v:?}");
    };
    match interp.kb().local_name_of(*functor) {
        "some" => match named.first().map(|(_, v)| v) {
            Some(Value::Int(n)) => Some(*n),
            other => panic!("some(…) holds {other:?}"),
        },
        "none" => None,
        other => panic!("expected an Option, got `{other}`"),
    }
}

#[track_caller]
fn assert_type_error(interp: &mut Interpreter, entry: &str, args: &[Value]) {
    match interp.call(entry, args) {
        Err(anthill_core::eval::error::EvalError::TypeMismatch { .. }) => {}
        other => panic!("{entry}: expected a type error, got {other:?}"),
    }
}

// ── a map key, in an operation body ─────────────────────────────────────────

#[test]
fn a_let_bound_tuple_keys_a_map() {
    assert_runs(
        &ns(
            "qjlet",
            "  operation run() -> Int64 =\n    let k = (1, 2)\n    look(Map[K = (Int64, Int64), V = Int64].empty().put(k, 4), k)",
        ),
        "test.qjlet.run",
        4,
    );
}

#[test]
fn a_tuple_parameter_keys_a_map() {
    assert_runs(
        &ns(
            "qjparam",
            "  operation byParam(k: (Int64, Int64)) -> Int64 =\n    look(Map[K = (Int64, Int64), V = Int64].empty().put(k, 4), k)\n  operation run() -> Int64 = byParam((1, 2))",
        ),
        "test.qjparam.run",
        4,
    );
}

#[test]
fn an_operation_built_tuple_keys_a_map() {
    assert_runs(
        &ns(
            "qjoptup",
            "  operation run() -> Int64 =\n    look(Map[K = (Int64, Int64), V = Int64].empty().put(mp(1), 4), mp(1))",
        ),
        "test.qjoptup.run",
        4,
    );
}

#[test]
fn an_operation_built_entity_keys_a_map() {
    assert_runs(
        &ns(
            "qjopent",
            "  operation run() -> Int64 =\n    lookB(Map[K = Box, V = Int64].empty().put(mkb(1), 4), mkb(1))",
        ),
        "test.qjopent.run",
        4,
    );
}

#[test]
fn the_unit_keys_a_map() {
    assert_runs(
        &ns(
            "qjunit",
            "  operation run() -> Int64 =\n    match Map[K = Unit, V = Int64].empty().put((), 4).get(())\n      case some(v) -> v\n      case none() -> 0",
        ),
        "test.qjunit.run",
        4,
    );
}

/// The twin the ticket measured against: a tuple written inside the call's own expression.
#[test]
fn a_tuple_written_in_the_call_keys_a_map() {
    assert_runs(
        &ns(
            "qjchain",
            "  operation run() -> Int64 =\n    match Map[K = (Int64, Int64), V = Int64].empty().put((1, 1), 4).get((1, 1))\n      case some(v) -> v\n      case none() -> 0",
        ),
        "test.qjchain.run",
        4,
    );
}

// ── a map key, read from a fact ─────────────────────────────────────────────

/// The twins the ticket measured against: the key a fact holds, put and got.
#[test]
fn a_facts_tuple_keys_a_map() {
    assert_answers(
        &ns(
            "qjfacttup",
            "  operation byKey(k: (Int64, Int64)) -> Int64 =\n    look(Map[K = (Int64, Int64), V = Int64].empty().put(k, 4), k)\n  rule hp((1, 2)) :- true\n  rule value(?r) :- hp(?k), ?r <=> byKey(?k)",
        ),
        "test.qjfacttup.value",
        4,
    );
}

#[test]
fn a_facts_entity_keys_a_map() {
    assert_answers(
        &ns(
            "qjfactent",
            "  operation byKey(k: Box) -> Int64 =\n    lookB(Map[K = Box, V = Int64].empty().put(k, 4), k)\n  rule hb(Box.bx(1)) :- true\n  rule value(?r) :- hb(?k), ?r <=> byKey(?k)",
        ),
        "test.qjfactent.value",
        4,
    );
}

#[test]
fn a_facts_tuple_and_an_operation_built_one_are_one_key() {
    assert_answers(
        &ns(
            "qjcrosstup",
            "  operation byKey(k: (Int64, Int64)) -> Int64 =\n    look(Map[K = (Int64, Int64), V = Int64].empty().put(k, 4), mp(1))\n  rule hp((1, 2)) :- true\n  rule value(?r) :- hp(?k), ?r <=> byKey(?k)",
        ),
        "test.qjcrosstup.value",
        4,
    );
}

#[test]
fn an_operation_built_tuple_and_a_facts_one_are_one_key() {
    assert_answers(
        &ns(
            "qjcrosstupr",
            "  operation byKey(k: (Int64, Int64)) -> Int64 =\n    look(Map[K = (Int64, Int64), V = Int64].empty().put(mp(1), 4), k)\n  rule hp((1, 2)) :- true\n  rule value(?r) :- hp(?k), ?r <=> byKey(?k)",
        ),
        "test.qjcrosstupr.value",
        4,
    );
}

#[test]
fn a_facts_entity_and_an_operation_built_one_are_one_key() {
    assert_answers(
        &ns(
            "qjcrossent",
            "  operation byKey(k: Box) -> Int64 =\n    lookB(Map[K = Box, V = Int64].empty().put(k, 4), mkb(1))\n  rule hb(Box.bx(1)) :- true\n  rule value(?r) :- hb(?k), ?r <=> byKey(?k)",
        ),
        "test.qjcrossent.value",
        4,
    );
}

// ── a map key, on every carrier ─────────────────────────────────────────────

/// A literal, a name, an entity, a tuple, the unit and an entity holding a tuple, each
/// put on one carrier and got on another: one slot for every pair.
#[test]
fn one_value_is_one_key_on_every_carrier() {
    let mut interp = interp_for(&ns(
        "qjcarriers",
        "  sort Holder\n    entity h(p: (Int64, Int64))\n  end\n  operation mkh() -> Holder = Holder.h(p: (1, 2))\n  operation red() -> Box = Box.bx(0)",
    ));
    let entity = interp.call("test.qjcarriers.mkb", &[Value::Int(1)]).expect("mkb");
    let tuple = interp.call("test.qjcarriers.mp", &[Value::Int(1)]).expect("mp");
    let holder = interp.call("test.qjcarriers.mkh", &[]).expect("mkh");
    let none = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Option.none")
        .expect("none");
    let values = [
        Value::Int(3),
        Value::Str("alice".into()),
        Value::SymbolRef(none),
        entity,
        tuple,
        Value::Unit,
        holder,
    ];
    for v in &values {
        let on = carriers(&mut interp, v);
        for (put_on, put_key) in &on {
            for (get_on, get_key) in &on {
                assert_eq!(
                    put_then_get(&mut interp, put_key, get_key),
                    Some(4),
                    "{v:?}: put as {put_on}, got as {get_on}"
                );
            }
        }
    }
}

/// Two different values are two slots on every carrier: an entity is not its field, a
/// tuple is not its reversal.
#[test]
fn two_values_are_two_keys_on_every_carrier() {
    let mut interp = interp_for(&ns("qjdistinct", ""));
    let one = interp.call("test.qjdistinct.mkb", &[Value::Int(1)]).expect("mkb");
    let two = interp.call("test.qjdistinct.mkb", &[Value::Int(2)]).expect("mkb");
    let a = interp.call("test.qjdistinct.mp", &[Value::Int(1)]).expect("mp");
    let b = Value::Tuple {
        pos: vec![Value::Int(2), Value::Int(1)].into(),
        named: Vec::new().into(),
    };
    for (x, y) in [(&one, &two), (&one, &Value::Int(1)), (&a, &b)] {
        let xs = carriers(&mut interp, x);
        let ys = carriers(&mut interp, y);
        for (put_on, put_key) in &xs {
            for (get_on, get_key) in &ys {
                assert_eq!(
                    put_then_get(&mut interp, put_key, get_key),
                    None,
                    "{x:?} as {put_on} and {y:?} as {get_on}"
                );
            }
        }
    }
}

/// Keying a map interns nothing: a lookup that misses on an occurrence key leaves the
/// term store as it was.
#[test]
fn a_map_lookup_interns_nothing() {
    let mut interp = interp_for(&ns("qjnointern", ""));
    let absent = interp
        .call("test.qjnointern.mkb", &[Value::Int(987_654)])
        .expect("mkb");
    let node = Value::Node(value_as_occurrence(interp.kb_mut(), &absent));
    let m = empty_map(&mut interp);
    let before = interp.kb().term_store_len();
    let got = interp
        .call("anthill.prelude.Map.get", &[m, node])
        .expect("Map.get");
    assert_eq!(option_int(&interp, &got), None);
    assert_eq!(interp.kb().term_store_len(), before, "the lookup wrote to the store");
}

/// A key read back out of `Map.keys` addresses its slot.
#[test]
fn a_key_read_back_addresses_its_slot() {
    let mut interp = interp_for(&ns("qjkeysback", ""));
    let entity = interp.call("test.qjkeysback.mkb", &[Value::Int(1)]).expect("mkb");
    let node = Value::Node(value_as_occurrence(interp.kb_mut(), &entity));
    let m = empty_map(&mut interp);
    let m = interp
        .call("anthill.prelude.Map.put", &[m, node, Value::Int(4)])
        .expect("Map.put");
    let keys = interp
        .call("anthill.prelude.Map.keys", &[m.clone()])
        .expect("Map.keys");
    let Value::Entity { named, pos, .. } = &keys else {
        panic!("Map.keys: {keys:?}");
    };
    let head = named
        .iter()
        .find(|(s, _)| interp.kb().local_name_of(*s) == "head")
        .map(|(_, v)| v.clone())
        .or_else(|| pos.first().cloned())
        .expect("one key");
    let got = interp
        .call("anthill.prelude.Map.get", &[m, head])
        .expect("Map.get");
    assert_eq!(option_int(&interp, &got), Some(4));
}

/// An unbound variable is no key, on any carrier.
#[test]
fn a_variable_is_no_key() {
    let mut interp = interp_for(&ns("qjvarkey", ""));
    let x = interp.kb_mut().intern("x");
    let vid = interp.kb_mut().fresh_var(x);
    let var = anthill_core::kb::term::Var::Global(vid);
    let tid = interp.kb_mut().alloc(anthill_core::kb::term::Term::Var(var));
    for key in [Value::Var(var), Value::term(tid)] {
        let m = empty_map(&mut interp);
        assert_type_error(&mut interp, "anthill.prelude.Map.put", &[m, key, Value::Int(4)]);
    }
}

/// A runtime handle is no key, at the top and inside an entity: nothing reads it.
#[test]
fn a_runtime_handle_is_no_key() {
    let mut interp = interp_for(&ns("qjhandlekey", ""));
    let handle = empty_map(&mut interp);
    let bx = interp
        .kb()
        .try_resolve_symbol("test.qjhandlekey.Box.bx")
        .expect("bx");
    let v = interp.kb_mut().intern("v");
    let holding = Value::Entity {
        functor: bx,
        pos: Vec::new().into(),
        named: vec![(v, handle.clone())].into(),
    };
    for key in [handle, holding] {
        let m = empty_map(&mut interp);
        assert_type_error(&mut interp, "anthill.prelude.Map.put", &[m.clone(), key.clone(), Value::Int(4)]);
        assert_type_error(&mut interp, "anthill.prelude.Map.get", &[m, key]);
    }
}

// ── reflect: building a term ────────────────────────────────────────────────

#[test]
fn make_fn_takes_an_entity_an_operation_built() {
    let mut interp = interp_for(&ns(
        "qjmfent",
        "  operation run() -> String =\n    let b = mkb(1)\n    term_to_string(make_fn(\"test.qjmfent.Pk.pk\", cons(as_term(b), cons(as_term(1), nil()))))",
    ));
    assert_eq!(call_printed(&mut interp, "test.qjmfent.run", &[]), "pk(a: bx(v: 1), b: 1)");
}

#[test]
fn make_fn_takes_a_tuple_an_operation_built() {
    let mut interp = interp_for(&ns(
        "qjmftup",
        "  operation run() -> String =\n    let t = mp(1)\n    term_to_string(make_fn(\"test.qjmftup.Pk.pk\", cons(as_term(t), cons(as_term(1), nil()))))",
    ));
    assert_eq!(call_printed(&mut interp, "test.qjmftup.run", &[]), "pk(a: (1, 2), b: 1)");
}

/// One argument on each carrier builds one term.
#[test]
fn make_fn_builds_one_term_from_every_carrier() {
    let mut interp = interp_for(&ns(
        "qjmfcarriers",
        "  operation mfOf(x: Term) -> Term = make_fn(\"test.qjmfcarriers.Pk.pk\", cons(x, cons(as_term(1), nil())))",
    ));
    let entity = interp.call("test.qjmfcarriers.mkb", &[Value::Int(1)]).expect("mkb");
    for (on, arg) in carriers(&mut interp, &entity) {
        assert_eq!(
            call_printed(&mut interp, "test.qjmfcarriers.mfOf", &[arg]),
            "pk(a: bx(v: 1), b: 1)",
            "{on}"
        );
    }
}

/// `make_fn` of a declared constructor builds the value the constructor builds: its
/// positional arguments are named by the constructor's fields, so it is one key with
/// `Box.bx(1)` on every carrier, and its field reads back.
#[test]
fn make_fn_of_a_constructor_is_the_constructors_value() {
    let mut interp = interp_for(&ns(
        "qjmfctor",
        "  operation mfBx(n: Int64) -> Term = make_fn(\"test.qjmfctor.Box.bx\", cons(as_term(n), nil()))",
    ));
    let built = interp.call("test.qjmfctor.mfBx", &[Value::Int(1)]).expect("mfBx");
    let entity = interp.call("test.qjmfctor.mkb", &[Value::Int(1)]).expect("mkb");
    let built_on = carriers(&mut interp, &built);
    let entity_on = carriers(&mut interp, &entity);
    for (put_on, put_key) in &built_on {
        for (get_on, get_key) in &entity_on {
            assert_eq!(
                put_then_get(&mut interp, put_key, get_key),
                Some(4),
                "make_fn's value as {put_on}, the constructor's as {get_on}"
            );
        }
    }
    use anthill_core::kb::term_view::TermView;
    assert_eq!(
        built
            .named_field(interp.kb(), "v")
            .and_then(|f| f.literal_int64(interp.kb())),
        Some(1)
    );
}

/// More arguments than the constructor declares is refused, not built into a term no
/// reader decodes.
#[test]
fn make_fn_refuses_more_arguments_than_the_constructor_declares() {
    let mut interp = interp_for(&ns(
        "qjmfover",
        "  operation mfOver() -> Term = make_fn(\"test.qjmfover.Box.bx\", cons(as_term(1), cons(as_term(2), nil())))",
    ));
    assert_type_error(&mut interp, "test.qjmfover.mfOver", &[]);
}

#[test]
fn replace_named_arg_takes_an_entity_an_operation_built() {
    let mut interp = interp_for(&ns(
        "qjrnent",
        "  operation run() -> String =\n    term_to_string(replace_named_arg(as_term(mkb(1)), \"v\", as_term(7)))",
    ));
    assert_eq!(call_printed(&mut interp, "test.qjrnent.run", &[]), "bx(v: 7)");
}

/// The term and the value replaced into it, each on every carrier: one answer.
#[test]
fn replace_named_arg_reads_every_carrier() {
    let mut interp = interp_for(&ns(
        "qjrncarriers",
        "  operation rnOf(t: Term, x: Term) -> Term = replace_named_arg(t, \"v\", x)",
    ));
    let entity = interp.call("test.qjrncarriers.mkb", &[Value::Int(1)]).expect("mkb");
    let tuple = interp.call("test.qjrncarriers.mp", &[Value::Int(1)]).expect("mp");
    for (t_on, t) in carriers(&mut interp, &entity) {
        for (x_on, x) in carriers(&mut interp, &tuple) {
            assert_eq!(
                call_printed(&mut interp, "test.qjrncarriers.rnOf", &[t.clone(), x]),
                "bx(v: (1, 2))",
                "the term as {t_on}, the value as {x_on}"
            );
        }
    }
}

/// A term that is no application has no argument to replace.
#[test]
fn replace_named_arg_refuses_a_literal() {
    let mut interp = interp_for(&ns(
        "qjrnlit",
        "  operation rnOf(t: Term, x: Term) -> Term = replace_named_arg(t, \"v\", x)",
    ));
    assert_type_error(&mut interp, "test.qjrnlit.rnOf", &[Value::Int(1), Value::Int(7)]);
}

// ── reflect: decoding an entity ─────────────────────────────────────────────

const DECODE: &str = "  operation teOf(t: Term) -> Int64 =\n    match term_as_entity[Box](t)\n      case some(b) -> 1\n      case none() -> 0";

#[test]
fn a_tuple_decodes_as_no_entity() {
    assert_runs(
        &ns(
            "qjtetup",
            &format!("{DECODE}\n  operation run() -> Int64 = teOf(as_term(mp(1)))"),
        ),
        "test.qjtetup.run",
        0,
    );
}

/// A tuple on every carrier, the unit among them: `none()`, as a literal answers.
#[test]
fn a_tuple_decodes_as_no_entity_on_every_carrier() {
    let mut interp = interp_for(&ns("qjtetupc", DECODE));
    let tuple = interp.call("test.qjtetupc.mp", &[Value::Int(1)]).expect("mp");
    for v in [tuple, Value::Unit] {
        for (on, arg) in carriers(&mut interp, &v) {
            let got = interp.call("test.qjtetupc.teOf", &[arg]).expect("teOf");
            assert!(matches!(got, Value::Int(0)), "{v:?} as {on}: {got:?}");
        }
    }
}

/// An entity decodes on every carrier.
#[test]
fn an_entity_decodes_on_every_carrier() {
    let mut interp = interp_for(&ns("qjteent", DECODE));
    let entity = interp.call("test.qjteent.mkb", &[Value::Int(1)]).expect("mkb");
    for (on, arg) in carriers(&mut interp, &entity) {
        let got = interp.call("test.qjteent.teOf", &[arg]).expect("teOf");
        assert!(matches!(got, Value::Int(1)), "{on}: {got:?}");
    }
}

/// An application carrying an argument the entity does not declare is not that entity.
#[test]
fn an_application_with_an_undeclared_argument_decodes_as_no_entity() {
    let mut interp = interp_for(&ns("qjteextra", DECODE));
    let bx = interp
        .kb()
        .try_resolve_symbol("test.qjteextra.Box.bx")
        .expect("bx");
    let v = interp.kb_mut().intern("v");
    let w = interp.kb_mut().intern("w");
    let extra = Value::Entity {
        functor: bx,
        pos: Vec::new().into(),
        named: vec![(v, Value::Int(1)), (w, Value::Int(2))].into(),
    };
    for (on, arg) in carriers(&mut interp, &extra) {
        let got = interp.call("test.qjteextra.teOf", &[arg]).expect("teOf");
        assert!(matches!(got, Value::Int(0)), "{on}: {got:?}");
    }
}

/// The twin: a literal answers `none()`.
#[test]
fn a_literal_decodes_as_no_entity() {
    assert_runs(
        &ns(
            "qjtelit",
            &format!("{DECODE}\n  operation run() -> Int64 = teOf(as_term(1))"),
        ),
        "test.qjtelit.run",
        0,
    );
}

/// A runtime handle is no term, at each builder and at the decoder.
#[test]
fn a_runtime_handle_is_no_term() {
    let mut interp = interp_for(&ns(
        "qjhandleterm",
        &format!(
            "{DECODE}\n  operation mfOf(x: Term) -> Term = make_fn(\"test.qjhandleterm.Pk.pk\", cons(x, nil()))\n  operation rnOf(t: Term, x: Term) -> Term = replace_named_arg(t, \"v\", x)"
        ),
    ));
    let handle = empty_map(&mut interp);
    let entity = interp.call("test.qjhandleterm.mkb", &[Value::Int(1)]).expect("mkb");
    assert_type_error(&mut interp, "test.qjhandleterm.mfOf", &[handle.clone()]);
    assert_type_error(&mut interp, "test.qjhandleterm.rnOf", &[handle.clone(), Value::Int(7)]);
    assert_type_error(&mut interp, "test.qjhandleterm.rnOf", &[entity, handle.clone()]);
    assert_type_error(&mut interp, "test.qjhandleterm.teOf", &[handle]);
}

/// A builder's argument holding a runtime handle below its head is no term either: what
/// is built from it is a term.
#[test]
fn a_runtime_handle_inside_a_builders_argument_is_no_term() {
    let mut interp = interp_for(&ns(
        "qjhandledeep",
        "  operation mfOf(x: Term) -> Term = make_fn(\"test.qjhandledeep.Pk.pk\", cons(x, nil()))\n  operation rnOf(t: Term, x: Term) -> Term = replace_named_arg(t, \"v\", x)",
    ));
    let handle = empty_map(&mut interp);
    let bx = interp
        .kb()
        .try_resolve_symbol("test.qjhandledeep.Box.bx")
        .expect("bx");
    let v = interp.kb_mut().intern("v");
    let holding = Value::Entity {
        functor: bx,
        pos: Vec::new().into(),
        named: vec![(v, handle)].into(),
    };
    let entity = interp.call("test.qjhandledeep.mkb", &[Value::Int(1)]).expect("mkb");
    assert_type_error(&mut interp, "test.qjhandledeep.mfOf", &[holding.clone()]);
    assert_type_error(&mut interp, "test.qjhandledeep.rnOf", &[entity, holding]);
}

// ── a store keeps a term ────────────────────────────────────────────────────

const STORE_SRC: &str = "namespace test.qjstore
  import anthill.prelude.Int64
  import anthill.reflect.{fact_monotonicity, non_monotone}
  entity Bar(value: Int64)
  rule fact_monotonicity(Bar) <=> non_monotone() @[simp]
end
";

/// A store value, `functor(root: <root>, convention: Flat)`, with `store` registered
/// under its key.
fn mount(
    interp: &mut Interpreter,
    functor: &str,
    root: &std::path::Path,
    store: Box<dyn anthill_core::persistence::Store>,
) -> Value {
    let fs = interp.kb_mut().intern(functor);
    let flat = interp.kb_mut().intern("Flat");
    let root_sym = interp.kb_mut().intern("root");
    let convention = interp.kb_mut().intern("convention");
    let store_val = Value::Entity {
        functor: fs,
        pos: Vec::new().into(),
        named: vec![
            (root_sym, Value::Str(root.to_str().unwrap().to_string())),
            (
                convention,
                Value::Entity {
                    functor: flat,
                    pos: Vec::new().into(),
                    named: Vec::new().into(),
                },
            ),
        ]
        .into(),
    };
    let key = interp.store_canonical_key(&store_val).expect("canonical key");
    interp
        .register_mirror(key, store, &[])
        .expect("a file store declares no intrinsic policy");
    store_val
}

fn bar(interp: &mut Interpreter, n: i64) -> Value {
    let bar = interp.kb().try_resolve_symbol("test.qjstore.Bar").expect("Bar");
    let value = interp.kb_mut().intern("value");
    Value::Entity {
        functor: bar,
        pos: Vec::new().into(),
        named: vec![(value, Value::Int(n))].into(),
    }
}

fn node_of(interp: &mut Interpreter, v: &Value) -> Value {
    Value::Node(value_as_occurrence(interp.kb_mut(), v))
}

#[test]
fn a_fact_an_occurrence_carries_is_persisted() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut interp = interp_for(STORE_SRC);
    let store = mount(
        &mut interp,
        "FileStore",
        dir.path(),
        Box::new(FileStore::new(dir.path().to_path_buf(), FileConvention::Flat)),
    );
    let row = bar(&mut interp, 1);
    let fact = node_of(&mut interp, &row);
    interp
        .call("anthill.persistence.Store.persist", &[store.clone(), fact, Value::Unit])
        .expect("persist");
    interp
        .call("anthill.persistence.Store.flush", &[store, Value::Unit])
        .expect("flush");
    let text = std::fs::read_to_string(dir.path().join("facts.anthill")).expect("read facts");
    assert!(text.contains("Bar(value: 1)"), "got:\n{text}");
}

#[test]
fn an_update_an_occurrence_carries_replaces_the_row() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut interp = interp_for(STORE_SRC);
    let store = mount(
        &mut interp,
        "FileStore",
        dir.path(),
        Box::new(FileStore::new(dir.path().to_path_buf(), FileConvention::Flat)),
    );
    let row = bar(&mut interp, 1);
    let stored = interp
        .call("anthill.persistence.Store.persist", &[store.clone(), row, Value::Unit])
        .expect("persist");
    let reference_sym = interp.kb_mut().intern("reference");
    let Value::Entity { named, .. } = &stored else {
        panic!("persist: {stored:?}");
    };
    let reference = named
        .iter()
        .find(|(s, _)| *s == reference_sym)
        .map(|(_, v)| v.clone())
        .expect("a StoredRef carries its reference");
    let replacement = bar(&mut interp, 2);
    let replacement = node_of(&mut interp, &replacement);
    interp
        .call(
            "anthill.persistence.NonMonotonicStore.update",
            &[store.clone(), reference, replacement],
        )
        .expect("update");
    interp
        .call("anthill.persistence.Store.flush", &[store, Value::Unit])
        .expect("flush");
    let text = std::fs::read_to_string(dir.path().join("facts.anthill")).expect("read facts");
    assert!(
        text.contains("Bar(value: 2)") && !text.contains("Bar(value: 1)"),
        "got:\n{text}"
    );
}

#[test]
fn retrieve_takes_a_pattern_an_occurrence_carries() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut interp = interp_for(STORE_SRC);
    let store = mount(
        &mut interp,
        "IndexedFileStore",
        dir.path(),
        Box::new(IndexedFileStore::new(dir.path().to_path_buf(), FileConvention::Flat)),
    );
    let row = bar(&mut interp, 1);
    interp
        .call("anthill.persistence.Store.persist", &[store.clone(), row.clone(), Value::Unit])
        .expect("persist");
    let pattern = node_of(&mut interp, &row);
    let hits = interp
        .call("anthill.persistence.QueryableStore.retrieve", &[store, pattern])
        .expect("retrieve");
    let Value::Stream(mut h) = hits else {
        panic!("retrieve: {hits:?}");
    };
    let mut found = Vec::new();
    while let Some((v, rest)) = interp.stream_split_first(&h).expect("split_first") {
        found.push(TermPrinter::new(interp.kb()).print_value(&v));
        h = rest;
    }
    assert_eq!(found, vec!["Bar(value: 1)".to_string()]);
}
