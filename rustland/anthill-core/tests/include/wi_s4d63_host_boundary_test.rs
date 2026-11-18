//! WI-20261113-S4D63 — proposal 074 stage 10: THE HOST BOUNDARY (074 §1.4, "A host call and
//! the code generators"; 073 §6.1).
//!
//! A host call (`Interpreter::call`) is typed as the same call written in an operation body:
//! `op(x1, …, xn)`, each `xi` a local at the type its argument is held at (a `HostValue`'s
//! type, or the type its value reads as). The typer fixes the type parameters and builds the
//! dictionaries, and what it refuses is refused before anything runs
//! (`EvalError::HostCallRefused`), in the sentence the body's load error has:
//!
//!  * `zeroOf()` over `zeroOf[X]() -> X requires Additive[T = X]`, naming `X`;
//!  * `add2(7, 2, 3)` over `add2(x: Additive, …)`, naming `add2.x`.
//!
//! Each died inside the run before, with an `Internal` error naming a frame slot
//! (`DeferToRequirement: requirement param __req_additive not bound`, "… its argument is a
//! Int64, not the instance"; the host's untyped call, measured on bf311200 — the typed call
//! is the change itself, and has no switch).
//!
//! CONTROLS — answered before too: `sum2(2, 3)` 5 and `sum2(1.5, 2.5)` 4.0,
//! `add2(intInstance(), 2, 3)` 5, `gen(leaf)` 7 (073 §6.1's row).
//!
//! BACK-OUTS, MEASURED: with a host refusal rendered as the load error's `Display` (its
//! position `at 0..0` appended), the three rows that compare it with the body twin fail; with
//! the open-slot refusal of `build_op_scoped_dicts` removed,
//! `a_slot_the_arguments_type_leaves_open_is_refused` fails (its body twin loads), and so do
//! five rows of `wi_ee0ep_param_dictionary_test`.
//!
//! THE HOST'S BRACKET (`Interpreter::call_bracketed`), the last section: with the bracket not
//! put on the call, `a_host_writes_the_calls_bracket`, `a_bracket_the_call_does_not_fit_is_
//! refused_as_in_a_body` and `wi_qj6x1`'s `retrieve_takes_a_pattern_an_occurrence_carries`
//! fail; `a_bracket_on_a_function_no_operation_declares_is_refused` passes either way by
//! design (it is refused before a bracket is read). Measured by a temporary switch.

use anthill_core::eval::{EvalError, HostValue, Interpreter, Value};

use crate::common::{interp_for, load_errors_of};

const SRC: &str = r#"
namespace s4d63.host
  import anthill.prelude.{Int64, Float, Additive, List}
  import anthill.realization.runtime.Dictionary
  operation add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b
  operation sum2[X](a: X, b: X) -> X requires Additive[T = X] = a + b
  operation zeroOf[X]() -> X requires Additive[T = X] = Additive.zero[T = X]()
  operation intInstance() -> Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()
  operation one[X]() -> Int64 = 1
  operation zeroM() -> Additive.T = Additive.zero()
  operation add3(x: Additive.T, y: Additive.T) -> Additive.T = x + y
  operation sumList[X](xs: List[T = X]) -> X requires Additive[T = X] =
    match xs
      case nil() -> Additive.zero[T = X]()
      case cons(h, t) -> h + sumList(t)
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
  operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)
end
"#;

fn op(name: &str) -> String {
    format!("s4d63.host.{name}")
}

fn answer(interp: &mut Interpreter, name: &str, args: &[Value]) -> Value {
    interp
        .call(&op(name), &HostValue::all(args))
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`{name}` must answer; got {e:?}"))
}

/// The refusal at the boundary: `HostCallRefused` naming `param`; its sentence is returned.
fn refused_at(interp: &mut Interpreter, name: &str, args: &[Value], param: &str) -> String {
    match interp.call(&op(name), &HostValue::all(args)).map(|h| h.value) {
        Err(EvalError::HostCallRefused { detail, .. }) => {
            assert!(detail.contains(param), "the sentence names `{param}`: {detail}");
            detail
        }
        other => panic!("`{name}` must be refused at the host boundary naming `{param}`; got {other:?}"),
    }
}

/// The body twin: `SRC` with `twin` added to its namespace is refused at load, each line of
/// `host` one of its errors, at the twin's location.
fn the_body_twin_says(twin: &str, host: &str) {
    let src = SRC.replacen("\nend\n", &format!("\n{twin}\nend\n"), 1);
    let errors = load_errors_of(&src);
    for line in host.lines() {
        assert!(
            errors.iter().any(|e| e.ends_with(line)),
            "the body twin is refused in the host's sentence `{line}`: {errors:#?}"
        );
    }
}

fn list_of(interp: &Interpreter, xs: Vec<Value>) -> Value {
    let kb = interp.kb();
    let nil = kb.try_resolve_symbol("anthill.prelude.List.nil").expect("List.nil");
    let cons = kb.try_resolve_symbol("anthill.prelude.List.cons").expect("List.cons");
    let mut v = Value::Entity {
        functor: nil,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
    for x in xs.into_iter().rev() {
        v = Value::Entity {
            functor: cons,
            pos: vec![x, v].into(),
            named: Vec::new().into(),
        };
    }
    v
}

/// 074 §1.4: no argument fixes `X`, and nothing the call is expected at does: refused as
/// `let z = zeroOf()` is in a body.
/// Before: `Internal("DeferToRequirement: …")`.
#[test]
fn a_parameter_no_argument_fixes_is_refused_naming_it() {
    let mut interp = interp_for(SRC);
    let shown = refused_at(&mut interp, "zeroOf", &[], "'X'");
    the_body_twin_says("  operation twin() -> Int64 =\n    let z = zeroOf()\n    1", &shown);
    // `one` declares no requirement at `X`, and the call is refused all the same: what a body
    // refuses is refused, whether or not anything at run time reads the parameter.
    let shown = refused_at(&mut interp, "one", &[], "'X'");
    the_body_twin_says("  operation twin() -> Int64 =\n    let z = one()\n    1", &shown);
}

/// The member spelling is the operation's type parameter (074 §1.3): written only in the
/// result, nothing fixes it. `add3(1, 2)` is the control, its arguments fixing it.
/// The `zeroM` half FAILS with the unfixed-parameter refusal backed out.
#[test]
fn a_member_spelling_no_argument_fixes_is_refused_naming_it() {
    let mut interp = interp_for(SRC);
    refused_at(&mut interp, "zeroM", &[], "Additive.T");
    assert!(matches!(answer(&mut interp, "add3", &[Value::Int(1), Value::Int(2)]), Value::Int(3)));
}

/// An argument that mentions `X` and does not fix it: the empty list fixes no element type,
/// and the two-element one does.
/// The empty-list half FAILS with the unfixed-parameter refusal backed out; the other half is
/// a control.
#[test]
fn an_argument_that_leaves_the_parameter_open_fixes_nothing() {
    let mut interp = interp_for(SRC);
    let two = list_of(&interp, vec![Value::Int(1), Value::Int(2)]);
    assert!(matches!(answer(&mut interp, "sumList", &[two]), Value::Int(3)));
    let empty = list_of(&interp, Vec::new());
    refused_at(&mut interp, "sumList", &[empty], "X");
}

/// 074 §1.4: `x` takes a dictionary, and `7` is none: refused as `add2(7, 2, 3)` is in a body.
/// Before: `Internal("… not the instance")`.
#[test]
fn an_argument_that_is_no_dictionary_where_one_is_expected_is_refused_naming_it() {
    let mut interp = interp_for(SRC);
    let shown = refused_at(&mut interp, "add2", &[Value::Int(7), Value::Int(2), Value::Int(3)], "add2.x");
    the_body_twin_says("  operation twin() -> Int64 = add2(7, 2, 3)", &shown);
}

/// CONTROL: the argument values fix `X`, and the requirement is built there.
#[test]
fn the_argument_values_fix_the_type_parameter() {
    let mut interp = interp_for(SRC);
    assert!(matches!(answer(&mut interp, "sum2", &[Value::Int(2), Value::Int(3)]), Value::Int(5)));
    match answer(&mut interp, "sum2", &[Value::Float(1.5), Value::Float(2.5)]) {
        Value::Float(f) => assert_eq!(f, 4.0),
        other => panic!("`sum2(1.5, 2.5)` must answer 4.0; got {other:?}"),
    }
    // 073 §6.1: `leaf` fixes `A = Leaf`, and `Desc[T = Leaf]` is built there.
    let leaf = Value::Entity {
        functor: interp.kb().try_resolve_symbol("s4d63.host.Leaf.leaf").expect("leaf"),
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
    assert!(matches!(answer(&mut interp, "gen", &[leaf]), Value::Int(7)));
}

/// CONTROL: a dictionary an operation returns, passed at the type that call answered.
/// At another type than the arguments', the call is refused as its body twin is: `x.T` is
/// `Int64`, and `1.5` is no `Int64`. Before, the boundary could not tell (a dictionary holds
/// no types, 074 §3) and the call died inside `Int64`'s `add`.
#[test]
fn a_dictionary_the_host_passes_is_used_at_its_type() {
    let mut interp = interp_for(SRC);
    let ints = interp.call(&op("intInstance"), &[]).expect("intInstance");
    let five = interp
        .call(&op("add2"), &[ints.clone(), Value::Int(2).into(), Value::Int(3).into()])
        .map(|h| h.value);
    assert!(matches!(five, Ok(Value::Int(5))), "`add2(intInstance(), 2, 3)`: {five:?}");
    match interp.call(&op("add2"), &[ints, Value::Float(1.5).into(), Value::Float(2.5).into()]) {
        Err(EvalError::HostCallRefused { detail, .. }) => {
            assert!(detail.contains("add2.a"), "names `a`: {detail}");
            the_body_twin_says("  operation twin() -> Float = add2(intInstance(), 1.5, 2.5)", &detail);
        }
        other => panic!("a dictionary at Int64 over Float arguments is refused; got {other:?}"),
    }
}

/// The set carrier of `wi_ee0ep_param_dictionary_test`, its ordering a named slot, with a
/// rival ordering of `String` beside `String`'s own.
const SETS: &str = r#"
namespace s4d63.sets
  import anthill.prelude.{WeakOrd, String, Int64, Bool}
  sort ByLength
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end
  enum MySet
    import anthill.prelude.PartialOrd.{lt, gt}
    sort T = ?
    requires O: WeakOrd[T]
    entity nothing
    entity node(elem: T, rest: MySet[T = T, O = O])
    operation contains(s: MySet[T = T, O = O], x: T) -> Bool =
      match s
        case nothing() -> false
        case node(y, r) ->
          let c = WeakOrd.compare(x, y)
          if lt(c, 0) then false
          else if gt(c, 0) then contains(r, x)
          else true
    operation empty() -> MySet[T = T, O = O] = nothing()
    operation insert(s: MySet[T = T, O = O], x: T) -> MySet[T = T, O = O] = node(x, s)
  end
  sort Bulk
    operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)
  end
  operation byLength() -> MySet[T = String, O = ByLength] = MySet.empty[T = String, O = ByLength]()
  operation byString() -> MySet[T = String, O = String] = MySet.empty[T = String, O = String]()
end
"#;

/// 074 §1.4: a host holding `s` holds `s.O`. `call` hands each set back at its type,
/// `insert` keeps the `O` its argument's type gives it (its declared result at the
/// argument's `T` and `O`), and `has` reads `s.O` off that type: `"aa"` is in `{"zz"}`
/// ordered by length and not in it ordered as strings. The two values are the same entity,
/// `node(elem: "zz", rest: nothing)`; only their types differ.
/// FAILS with each set handed over bare, its type read off its value (`MySet[T = String]`,
/// `O` open): `has` is refused, naming `O`
/// ([`a_slot_the_arguments_type_leaves_open_is_refused`]).
#[test]
fn a_typed_value_keeps_the_ordering_its_type_names() {
    let mut interp = interp_for(SETS);
    let mut has_aa = |interp: &mut Interpreter, empty: &str| {
        let set = interp.call(&format!("s4d63.sets.{empty}"), &[]).expect(empty);
        let zz = interp.host_value(Value::Str("zz".into())).expect("a host value at its own type");
        let set = interp
            .call("s4d63.sets.MySet.insert", &[set, zz])
            .expect("insert");
        let shown = anthill_core::kb::typing::type_display_name_value(interp.kb(), set.ty().expect("a result's type"));
        let aa = interp.host_value(Value::Str("aa".into())).expect("a host value at its own type");
        let got = interp.call("s4d63.sets.Bulk.has", &[set, aa]).map(|h| h.value);
        (shown, got)
    };
    let (by_length_ty, by_length) = has_aa(&mut interp, "byLength");
    assert!(by_length_ty.contains("ByLength"), "insert keeps `O = ByLength` in its result type: {by_length_ty}");
    assert!(matches!(by_length, Ok(Value::Bool(true))), "ordered by length, `aa` is `zz`'s class: {by_length:?}");
    let (by_string_ty, by_string) = has_aa(&mut interp, "byString");
    assert!(by_string_ty.contains("O = String"), "insert keeps `O = String` in its result type: {by_string_ty}");
    assert!(matches!(by_string, Ok(Value::Bool(false))), "ordered as strings, `aa` is not `zz`: {by_string:?}");
}

/// CONTROL: `call`'s result is at the type the typer gave the call, the declared result at
/// the type parameters the arguments fix: `sum2(2, 3)` is an `Int64`. Passes with the result
/// type read off the value instead, `5` reading as an `Int64`.
#[test]
fn a_typed_result_is_at_the_declared_result_type() {
    let mut interp = interp_for(SRC);
    let two = interp.host_value(Value::Int(2)).expect("a host value at its own type");
    let three = interp.host_value(Value::Int(3)).expect("a host value at its own type");
    let five = interp.call(&op("sum2"), &[two, three]).expect("sum2");
    assert!(matches!(five.value, Value::Int(5)));
    let shown = anthill_core::kb::typing::type_display_name_value(interp.kb(), five.ty().expect("a result's type"));
    assert_eq!(shown, "Int64", "`sum2`'s `X` at `Int64`");
}

/// A slot the argument's type leaves open is refused where it is read, in a body as at the
/// host: `mkOpen()` answers a `MySet[T = String]`, built ordered by length, and `has(s, "aa")`
/// would read `s.O` off a type that does not write it. Before, the call was given `String`'s
/// own ordering (§8.7's order at the goal), which is not the one the value was built with, and
/// answered `false`. The advised repair, writing `O` where the value is produced, answers
/// `true`.
/// FAILS with the open-slot refusal backed out: the body loads. The spec's rule is §5.2's for
/// an existential return, which this call did not reach through a `let`.
#[test]
fn a_slot_the_arguments_type_leaves_open_is_refused() {
    let open = "  operation mkOpen() -> MySet[T = String] =
    MySet.insert(MySet.empty[T = String, O = ByLength](), \"zz\")
  operation q() -> Bool =
    let s = mkOpen()
    Bulk.has(s, \"aa\")";
    let errors = load_errors_of(&SETS.replacen("\nend\n", &format!("\n{open}\nend\n"), 1));
    assert!(
        errors.iter().any(|e| e.contains("Bulk.has") && e.contains("leaves `O` open")),
        "the body's call is refused naming `O`: {errors:#?}"
    );
    let repaired = "  operation mkLen() -> MySet[T = String, O = ByLength] =
    MySet.insert(MySet.empty[T = String, O = ByLength](), \"zz\")
  operation q() -> Bool =
    let s = mkLen()
    Bulk.has(s, \"aa\")";
    let mut interp = interp_for(&SETS.replacen("\nend\n", &format!("\n{repaired}\nend\n"), 1));
    let got = interp.call("s4d63.sets.q", &[]).map(|h| h.value);
    assert!(matches!(got, Ok(Value::Bool(true))), "ordered by length, `aa` is `zz`'s class: {got:?}");
    // At the host: the set handed over bare is at the type its value reads as, `O` open.
    let set = interp.call("s4d63.sets.mkLen", &[]).expect("mkLen").value;
    match interp.call("s4d63.sets.Bulk.has", &HostValue::all(&[set, Value::Str("aa".into())])) {
        Err(EvalError::HostCallRefused { detail, .. }) => {
            assert!(detail.contains("leaves `O` open"), "names `O`: {detail}")
        }
        other => panic!("a bare set's `O` is open, and `has` is refused; got {other:?}"),
    }
}

// ── the host's bracket ──────────────────────────────────────────────────────────────────

/// 074 §1.4: A HOST WRITES THE CALL'S BRACKET (`Interpreter::call_bracketed`), and it is read as
/// a body's: `zeroOf` with `[X = Int64]` is `zeroOf[X = Int64]()`, `0`, as its body twin
/// answers; with `[Float]`, positionally, `0.0`. Bare, the call is refused naming `X`
/// ([`a_parameter_no_argument_fixes_is_refused_naming_it`]). FAILS with the bracket not put on
/// the call: refused naming `X`.
#[test]
fn a_host_writes_the_calls_bracket() {
    let twin = "  operation zeroInt() -> Int64 = zeroOf[X = Int64]()";
    let mut interp = interp_for(&SRC.replacen("\nend\n", &format!("\n{twin}\nend\n"), 1));
    assert!(matches!(answer(&mut interp, "zeroInt", &[]), Value::Int(0)), "the body twin");
    let int64 = crate::common::sort_type(interp.kb_mut(), "anthill.prelude.Int64");
    let float = crate::common::sort_type(interp.kb_mut(), "anthill.prelude.Float");
    let got = interp.call_bracketed(&op("zeroOf"), &[(Some("X"), int64)], &[]).map(|h| h.value);
    assert!(matches!(got, Ok(Value::Int(0))), "`[X = Int64]`: {got:?}");
    let got = interp.call_bracketed(&op("zeroOf"), &[(None, float)], &[]).map(|h| h.value);
    assert!(matches!(got, Ok(Value::Float(z)) if z == 0.0), "`[Float]`: {got:?}");
}

/// A bracket the call does not fit is refused before anything runs, in the sentence its body
/// twin's load error has: a key `zeroOf` does not declare, and a type nothing provides
/// `Additive` at.
#[test]
fn a_bracket_the_call_does_not_fit_is_refused_as_in_a_body() {
    let mut interp = interp_for(SRC);
    for (key, sort, written) in [
        ("Y", "anthill.prelude.Int64", "Y = Int64"),
        ("X", "anthill.prelude.String", "X = anthill.prelude.String"),
    ] {
        let ty = crate::common::sort_type(interp.kb_mut(), sort);
        match interp.call_bracketed(&op("zeroOf"), &[(Some(key), ty)], &[]) {
            Err(EvalError::HostCallRefused { detail, .. }) => the_body_twin_says(
                &format!("  operation twin() -> Int64 =\n    let z = zeroOf[{written}]()\n    1"),
                &detail,
            ),
            other => panic!("`zeroOf[{written}]` from the host is refused; got {other:?}"),
        }
    }
}

/// A host function under a name no operation declares (here a sort's) has nothing a bracket
/// binds: the call with one is refused, and the call without runs the function.
#[test]
fn a_bracket_on_a_function_no_operation_declares_is_refused() {
    let mut interp = interp_for(SRC);
    interp
        .register_builtin(&op("Leaf"), |_, _| Ok(Value::Int(3)))
        .expect("the name resolves");
    let got = interp.call(&op("Leaf"), &[]).map(|h| h.value);
    assert!(matches!(got, Ok(Value::Int(3))), "the control runs it: {got:?}");
    let int64 = crate::common::sort_type(interp.kb_mut(), "anthill.prelude.Int64");
    match interp.call_bracketed(&op("Leaf"), &[(Some("X"), int64)], &[]) {
        Err(EvalError::HostCallRefused { detail, .. }) => {
            assert!(detail.contains("a bracket has nothing to bind"), "{detail}")
        }
        other => panic!("a bracket on a signature-less function is refused; got {other:?}"),
    }
}
