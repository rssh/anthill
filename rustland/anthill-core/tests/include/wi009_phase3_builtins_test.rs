//! WI-009 phase 3 prerequisites — `find_fact` / `replace_named_arg`.
//!
//! These are the building blocks for the retract+assert mutating
//! commands (claim / deliver / verify / update / delete /
//! add-dependency / remove-dependency). cmd_claim's full landing is
//! gated on a separate canonical-mismatch fix in the FileStore retract
//! path; the builtins themselves are useful in isolation and tested
//! here so future ports can reuse them with confidence.


use anthill_core::eval::Value;
use crate::common::interp_for;

#[test]
fn find_fact_locates_asserted_fact_by_head() {
    // Sanity: assert a fact, look up its head via facts_of, then call
    // find_fact to recover a FactId. The returned Term should be a
    // Const(Handle(Fact, _)) — Store.retract accepts that shape.
    let src = r#"
namespace test.find_fact
  sort Item
    entity Box(id: String)
  end
  fact Box(id: "B-001")
end
"#;
    let mut interp = interp_for(src);
    // facts_of ignores its KB arg — pass a placeholder. The entity is passed
    // by reference (a nullary Fn term for the qualified functor), matching the
    // `facts_of(kb(), WorkItem)` source form.
    let box_ref = Value::Term(interp.kb_mut().resolve_qualified_name_term("test.find_fact.Item.Box"));
    let facts = interp.call(
        "anthill.reflect.KB.facts_of",
        &[Value::Unit, box_ref],
    ).expect("facts_of");

    // Drill down to the first cons head.
    let head = match &facts {
        Value::Entity { named, .. } => named.iter()
            .find(|(s, _)| interp.kb().resolve_sym(*s) == "head")
            .map(|(_, v)| v.clone())
            .expect("cons.head"),
        _ => panic!("expected list, got {facts:?}"),
    };

    let result = interp.call("anthill.reflect.find_fact", &[head]).expect("find_fact");
    match result {
        Value::Entity { functor, named, .. } => {
            let name = interp.kb().resolve_sym(functor);
            assert!(name == "some" || name.ends_with(".some"),
                "expected some(...), got {name}: {named:?}");
            let inner = named.iter().find(|(s, _)| interp.kb().resolve_sym(*s) == "value")
                .map(|(_, v)| v.clone()).expect("some.value");
            // Inner is a Term wrapping a Const(Handle).
            match inner {
                Value::Term(_) => (),
                other => panic!("expected Term, got {other:?}"),
            }
        }
        other => panic!("expected Entity, got {other:?}"),
    }
}

#[test]
fn replace_named_arg_swaps_one_field() {
    // Build Pair(fst: 1, snd: 2), replace `snd` with 99, expect
    // Pair(fst: 1, snd: 99). Pair is a stdlib entity with named-args.
    let src = r#"
namespace test.replace_arg
  import anthill.prelude.Pair.{Pair, pair}
  import anthill.reflect.{Term, replace_named_arg}

  fact pair(fst: 1, snd: 2)
end
"#;
    let mut interp = interp_for(src);
    let pair_ref = Value::Term(interp.kb_mut().resolve_qualified_name_term("anthill.prelude.Pair.pair"));
    let facts = interp.call(
        "anthill.reflect.KB.facts_of",
        &[Value::Unit, pair_ref],
    ).expect("facts_of");
    // facts_of returns both the user fact AND the synthetic entity
    // declaration (whose field values are unbound logical vars). Walk
    // the cons-list and pick the first head whose `fst` field is the
    // ground Int literal — that's the user fact.
    use anthill_core::kb::term::{Literal, Term};
    let head = {
        let mut cur = facts.clone();
        let mut found = None;
        loop {
            match cur {
                Value::Entity { ref named, .. } => {
                    let h = named.iter()
                        .find(|(s, _)| interp.kb().resolve_sym(*s) == "head")
                        .map(|(_, v)| v.clone());
                    let t = named.iter()
                        .find(|(s, _)| interp.kb().resolve_sym(*s) == "tail")
                        .map(|(_, v)| v.clone());
                    match (h, t) {
                        (Some(Value::Term(tid)), Some(tail)) => {
                            if let Term::Fn { named_args, .. } = interp.kb().get_term(tid) {
                                let is_user_fact = named_args.iter().any(|(s, t)| {
                                    interp.kb().resolve_sym(*s) == "fst" &&
                                    matches!(interp.kb().get_term(*t), Term::Const(Literal::Int(_)))
                                });
                                if is_user_fact { found = Some(Value::Term(tid)); break; }
                            }
                            cur = tail;
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        found.expect("user pair fact in facts_of result")
    };

    let new_val = Value::Int(99);
    let result = interp.call(
        "anthill.reflect.replace_named_arg",
        &[head, Value::Str("snd".into()), new_val],
    ).expect("replace_named_arg");

    let new_term_id = match result {
        Value::Term(tid) => tid,
        other => panic!("expected Term, got {other:?}"),
    };

    // Walk the new term and confirm `snd` is now 99 while `fst` still 1.
    let term = interp.kb().get_term(new_term_id).clone();
    match term {
        Term::Fn { named_args, .. } => {
            let snd = named_args.iter()
                .find(|(s, _)| interp.kb().resolve_sym(*s) == "snd")
                .map(|(_, t)| *t).expect("snd field");
            let fst = named_args.iter()
                .find(|(s, _)| interp.kb().resolve_sym(*s) == "fst")
                .map(|(_, t)| *t).expect("fst field");
            assert!(matches!(interp.kb().get_term(snd),
                Term::Const(Literal::Int(99))),
                "snd should be 99, got {:?}", interp.kb().get_term(snd));
            assert!(matches!(interp.kb().get_term(fst),
                Term::Const(Literal::Int(1))),
                "fst should still be 1, got {:?}", interp.kb().get_term(fst));
        }
        other => panic!("expected Fn term, got {other:?}"),
    }
}
