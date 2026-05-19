//! Map runtime builtins (proposal 035).
//!
//! Covers the three surface forms of `Map.empty()` insofar as they reach the
//! evaluator today:
//!
//! - **Form (2)** — `Map.empty()` constrained by surrounding expression
//!   (`put(Map.empty(), "a", 1)`). Parses and runs as-is; HM inference of
//!   K/V is a separate concern that lands with the typing pass.
//! - **Form (3)** — `Map[K = String, V = Int].empty()`. The
//!   instantiation-term-as-receiver shape, enabled by extending the parser's
//!   `field_access` segment collection. Bindings are erased at runtime.
//!
//! Direct programmatic invocation through `interp.call` covers the builtin
//! contracts (empty/put/get/contains/remove/keys/values/entries/size) so the
//! arena, refcounting, and value plumbing are exercised independently of the
//! parser change.


use anthill_core::eval::{Interpreter, Value};

use crate::common::interp_for;

fn empty_map(interp: &mut Interpreter) -> Value {
    interp.call("anthill.prelude.Map.empty", &[]).expect("Map.empty")
}

fn unwrap_some(interp: &Interpreter, v: Value) -> Value {
    match v {
        Value::Entity { functor, named, .. } => {
            let name = interp.kb().resolve_sym(functor);
            assert!(
                name == "some" || name == "anthill.prelude.Option.some",
                "expected some, got {name}",
            );
            named.into_iter().find_map(|(s, v)| {
                if interp.kb().resolve_sym(s) == "value" { Some(v) } else { None }
            }).expect("some has value field")
        }
        other => panic!("expected some(...), got {:?}", other),
    }
}

fn is_none(interp: &Interpreter, v: &Value) -> bool {
    match v {
        Value::Entity { functor, .. } => {
            let name = interp.kb().resolve_sym(*functor);
            name == "none" || name == "anthill.prelude.Option.none"
        }
        _ => false,
    }
}

#[test]
fn map_empty_via_builtin_call() {
    let src = r#"
namespace test.map_empty
  operation main() -> Int
    = 0
end
"#;
    let mut interp = interp_for(src);
    let m = empty_map(&mut interp);
    match m {
        Value::Map(_) => {}
        other => panic!("expected Map, got {:?}", other),
    }
}

#[test]
fn map_put_get_round_trip() {
    let src = r#"
namespace test.map_put_get
  operation main() -> Int
    = 0
end
"#;
    let mut interp = interp_for(src);
    let m = empty_map(&mut interp);
    let m = interp.call("anthill.prelude.Map.put", &[
        m,
        Value::Str("a".into()),
        Value::Int(1),
    ]).expect("put");
    let v = interp.call("anthill.prelude.Map.get", &[
        m.clone(),
        Value::Str("a".into()),
    ]).expect("get");
    let inner = unwrap_some(&interp, v);
    assert_eq!(inner.as_int(), Some(1));

    // Missing key → none.
    let v = interp.call("anthill.prelude.Map.get", &[
        m,
        Value::Str("missing".into()),
    ]).expect("get missing");
    assert!(is_none(&interp, &v));
}

#[test]
fn map_contains_size_remove() {
    let src = r#"
namespace test.map_extras
  operation main() -> Int
    = 0
end
"#;
    let mut interp = interp_for(src);
    let m = empty_map(&mut interp);
    assert_eq!(
        interp.call("anthill.prelude.Map.size", &[m.clone()]).unwrap().as_int(),
        Some(0),
    );
    let m = interp.call("anthill.prelude.Map.put", &[
        m, Value::Str("k".into()), Value::Int(7),
    ]).unwrap();
    assert_eq!(
        interp.call("anthill.prelude.Map.size", &[m.clone()]).unwrap().as_int(),
        Some(1),
    );
    assert_eq!(
        interp.call("anthill.prelude.Map.contains", &[
            m.clone(), Value::Str("k".into()),
        ]).unwrap().as_bool(),
        Some(true),
    );
    let m = interp.call("anthill.prelude.Map.remove", &[
        m, Value::Str("k".into()),
    ]).unwrap();
    assert_eq!(
        interp.call("anthill.prelude.Map.size", &[m]).unwrap().as_int(),
        Some(0),
    );
}

#[test]
fn form_2_inferred_from_use_parses_and_runs() {
    // Form (2): Map.empty() constrained by surrounding expression.
    // No HM inference needed at runtime — types are erased.
    let src = r#"
namespace test.map_form2
  import anthill.prelude.Map.{empty, put, get, size}

  operation build() -> Int
    = size(put(empty(), "a", 1))
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.map_form2.build", &[]).expect("call build");
    assert_eq!(result.as_int(), Some(1));
}

#[test]
fn dotted_call_without_instantiation_baseline() {
    // Sanity check before exercising form (3): does the dotted call form
    // `Map.empty()` work today at all? If so, form (3) is a parser change;
    // if not, we have an additional dispatch issue to fix first.
    let src = r#"
namespace test.map_dotted
  import anthill.prelude.{Map}
  import anthill.prelude.Map.{put, get, size}

  operation build() -> Int
    = size(put(Map.empty(), "a", 1))
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.map_dotted.build", &[]).expect("call build");
    assert_eq!(result.as_int(), Some(1));
}

#[test]
fn form_3_instantiation_receiver_parses_and_runs() {
    // Form (3): `Map[K = String, V = Int].empty()`. The parser change in
    // `convert.rs` extracts the sort name from the instantiation term, so the
    // call resolves to `anthill.prelude.Map.empty` just like a bare
    // `Map.empty()` would.
    let src = r#"
namespace test.map_form3
  import anthill.prelude.{Map}
  import anthill.prelude.Map.{put, get, size}

  operation build() -> Int
    = size(put(Map[K = String, V = Int].empty(), "a", 1))
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.map_form3.build", &[]).expect("call build");
    assert_eq!(result.as_int(), Some(1));
}

#[test]
fn form_1_let_with_type_annotation() {
    // Form (1) of proposal 035: type annotation on the LHS supplies K, V.
    // Runtime is type-erased — the call dispatches identically to forms
    // (2) and (3). The annotation is parsed via the let_chain grammar
    // extension (WI-185), embedded inline as a `Term::ParseAux(TypeExpr)`
    // child of the parse let_expr (WI-271; previously a side-channel
    // HashMap), then threaded onto the kb-side `let_expr` as a
    // `type_name: <type>` named arg so the typer can later use it as
    // the expected type for the value and as the bound variable's type
    // in the body.
    let src = r#"
namespace test.map_form1
  import anthill.prelude.{Map}
  import anthill.prelude.Map.{put, get, size}

  operation build() -> Int
    = let m: Map[K = String, V = Int] = Map.empty()
      size(put(m, "a", 1))
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.map_form1.build", &[]).expect("call build");
    assert_eq!(result.as_int(), Some(1));
}

#[test]
fn form_1_simple_int_annotation() {
    // The annotation can be any type, not just parameterized. Smoke test
    // for the simple case `let x: Int = 7`.
    let src = r#"
namespace test.let_anno_int
  operation main() -> Int
    = let x: Int = 7
      x
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.let_anno_int.main", &[]).expect("call main");
    assert_eq!(result.as_int(), Some(7));
}

#[test]
fn proposal_acceptance_fixture() {
    // The fixture from proposal 035 §Acceptance:
    //   Map[K = String, V = Int].empty()
    //     |> put(_, "a", 1)
    //     |> get(_, "a") = some(1)
    //
    // Anthill doesn't have a pipe operator, so the literal form below is
    // the equivalent nested call.
    let src = r#"
namespace test.map_acceptance
  import anthill.prelude.{Map, Option}
  import anthill.prelude.Map.{put, get}

  operation lookup() -> Option[T = Int]
    = get(put(Map[K = String, V = Int].empty(), "a", 1), "a")
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.map_acceptance.lookup", &[]).expect("lookup");
    let inner = unwrap_some(&interp, result);
    assert_eq!(inner.as_int(), Some(1));
}

#[test]
fn map_keys_values_entries_preserve_insertion_order() {
    let src = r#"
namespace test.map_iter_order
  operation main() -> Int = 0
end
"#;
    let mut interp = interp_for(src);
    let m = empty_map(&mut interp);
    let m = interp.call("anthill.prelude.Map.put", &[
        m, Value::Str("first".into()), Value::Int(1),
    ]).unwrap();
    let m = interp.call("anthill.prelude.Map.put", &[
        m, Value::Str("second".into()), Value::Int(2),
    ]).unwrap();
    let m = interp.call("anthill.prelude.Map.put", &[
        m, Value::Str("third".into()), Value::Int(3),
    ]).unwrap();

    let keys = interp.call("anthill.prelude.Map.keys", &[m.clone()]).unwrap();
    let values = interp.call("anthill.prelude.Map.values", &[m]).unwrap();

    fn is_cons(interp: &Interpreter, sym: anthill_core::intern::Symbol) -> bool {
        let name = interp.kb().resolve_sym(sym);
        name == "cons" || name == "anthill.prelude.List.cons"
    }
    fn collect_list(interp: &Interpreter, list: Value) -> Vec<Value> {
        let mut out = Vec::new();
        let mut cur = list;
        loop {
            match cur {
                Value::Entity { functor, named, .. } if is_cons(interp, functor) => {
                    let head = named.iter().find(|(s, _)| interp.kb().resolve_sym(*s) == "head")
                        .map(|(_, v)| v.clone()).expect("head");
                    let tail = named.iter().find(|(s, _)| interp.kb().resolve_sym(*s) == "tail")
                        .map(|(_, v)| v.clone()).expect("tail");
                    out.push(head);
                    cur = tail;
                }
                _ => break,
            }
        }
        out
    }

    let key_strs: Vec<String> = collect_list(&interp, keys).into_iter()
        .filter_map(|v| if let Value::Str(s) = v { Some(s) } else { None })
        .collect();
    let value_ints: Vec<i64> = collect_list(&interp, values).into_iter()
        .filter_map(|v| if let Value::Int(n) = v { Some(n) } else { None })
        .collect();
    assert_eq!(key_strs, vec!["first", "second", "third"]);
    assert_eq!(value_ints, vec![1, 2, 3]);
}
