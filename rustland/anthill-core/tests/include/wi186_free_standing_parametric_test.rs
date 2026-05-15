//! WI-186 — Free-standing parametric operations (proposal 035).
//!
//! Surface: anthill's logical-variable syntax (`?a`, `?b`, ...) doubles
//! as parametric polymorphism for free-standing operations. Each `?x`
//! in a signature is a logical variable in the operation's scope; the
//! typer instantiates it at each call site.
//!
//! No grammar, converter, loader, or typer changes were required —
//! `?name` was already a valid `variable_term` in type positions, the
//! resolver already opens fresh variables per query, and the typer
//! already handles polymorphic operation signatures. WI-186's
//! deliverable is therefore the *test coverage* that pins down this
//! behavior so future changes can't regress it.
//!
//! This file gives the runtime / end-to-end coverage. The typing-only
//! coverage lives in `typing_test.rs::wi186_*`.
//!
//! Companion to WI-185 (let-binding type annotations) under the same
//! proposal — the two close out the proposal-035 surface forms.


use anthill_core::eval::Value;
use crate::common::interp_for;

#[test]
fn id_polymorphic_free_standing_int() {
    let src = r#"
namespace test.wi186_id_int
  operation id(x: ?a) -> ?a
    = x
  operation main() -> Int
    = id(42)
end
"#;
    let mut interp = interp_for(src);
    let r = interp.call("test.wi186_id_int.main", &[]).expect("call main");
    assert_eq!(r.as_int(), Some(42));
}

#[test]
fn id_polymorphic_free_standing_string() {
    let src = r#"
namespace test.wi186_id_str
  operation id(x: ?a) -> ?a
    = x
  operation main() -> String
    = id("hello")
end
"#;
    let mut interp = interp_for(src);
    let r = interp.call("test.wi186_id_str.main", &[]).expect("call main");
    match r {
        Value::Str(s) => assert_eq!(s, "hello"),
        other => panic!("expected Str(\"hello\"), got {:?}", other),
    }
}

#[test]
fn id_polymorphic_two_distinct_call_sites() {
    // The same op called once at Int and once at String — exercises
    // independent instantiation of ?a per call site.
    let src = r#"
namespace test.wi186_id_two
  operation id(x: ?a) -> ?a
    = x
  operation as_int() -> Int
    = id(7)
  operation as_str() -> String
    = id("ok")
  operation main() -> Int
    = as_int()
end
"#;
    let mut interp = interp_for(src);
    let n = interp.call("test.wi186_id_two.as_int", &[]).expect("as_int");
    assert_eq!(n.as_int(), Some(7));
    let s = interp.call("test.wi186_id_two.as_str", &[]).expect("as_str");
    match s {
        Value::Str(t) => assert_eq!(t, "ok"),
        other => panic!("expected Str, got {:?}", other),
    }
}

#[test]
fn make_pair_free_standing_parametric_returns_pair() {
    // Proposal-035 acceptance fixture: a free-standing parametric
    // operation whose return type is a parameterized sort with bindings
    // pinned by the operation's logical variables. The runtime
    // assertion is conservative — types are erased, so we just verify
    // the entity functor is `Pair.pair` and the payload contains the
    // expected values somewhere (positional or named, depending on
    // call shape — `pair(a, b)` from source flows as positional).
    let src = r#"
namespace test.wi186_make_pair
  import anthill.prelude.{Pair}
  operation make_pair(a: ?a, b: ?b) -> Pair[A = ?a, B = ?b]
    = pair(a, b)
  operation main() -> Pair[A = String, B = Int]
    = make_pair("wi", 186)
end
"#;
    let mut interp = interp_for(src);
    let r = interp.call("test.wi186_make_pair.main", &[]).expect("call main");
    match r {
        Value::Entity { functor, pos, named, .. } => {
            let name = interp.kb().resolve_sym(functor);
            assert!(
                name == "pair" || name == "anthill.prelude.Pair.pair",
                "expected Pair.pair functor, got {name}",
            );
            // The two arguments live somewhere in the entity. Take
            // them from whichever bag is populated.
            let mut values: Vec<Value> = pos.clone();
            for (_, v) in &named {
                values.push(v.clone());
            }
            let saw_str = values.iter().any(|v| matches!(v, Value::Str(s) if s == "wi"));
            let saw_int = values.iter().any(|v| v.as_int() == Some(186));
            assert!(saw_str, "expected to see 'wi' string in pair, got {:?}", values);
            assert!(saw_int, "expected to see 186 in pair, got {:?}", values);
        }
        other => panic!("expected Pair entity, got {:?}", other),
    }
}
