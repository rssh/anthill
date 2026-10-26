//! WI-009 phase 3 prerequisites — `stored_facts_of` / `replace_named_arg`.
//!
//! These are the building blocks for the retract+assert mutating
//! commands (claim / deliver / verify / update / delete /
//! add-dependency / remove-dependency). cmd_claim's full landing is
//! gated on a separate canonical-mismatch fix in the FileStore retract
//! path; the builtins themselves are useful in isolation and tested
//! here so future ports can reuse them with confidence.

use crate::common::interp_for;
use anthill_core::eval::Value;

#[test]
fn stored_facts_of_pairs_an_asserted_fact_with_a_native_reference() {
    // Sanity: assert a fact, then enumerate it through the capability-carrying
    // read. The row arrives with its opaque FactRef — no content-to-RuleId
    // lookup or Handle literal is involved.
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
    let box_ref = Value::term(
        interp
            .kb_mut()
            .resolve_qualified_name_term("test.find_fact.Item.Box"),
    );
    let facts = interp
        .call(
            "anthill.reflect.KB.stored_facts_of",
            &[Value::Unit, box_ref],
        )
        .expect("facts_of");

    // Drill down to the first cons head.
    let stored = match &facts {
        Value::Entity { named, .. } => named
            .iter()
            .find(|(s, _)| interp.kb().local_name_of(*s) == "head")
            .map(|(_, v)| v.clone())
            .expect("cons.head"),
        _ => panic!("expected list, got {facts:?}"),
    };
    match stored {
        Value::Entity {
            functor, ref named, ..
        } => {
            assert_eq!(interp.kb().local_name_of(functor), "stored_ref");
            assert!(named.iter().any(|(s, v)| {
                interp.kb().local_name_of(*s) == "reference" && matches!(v, Value::FactRef(_))
            }));
        }
        other => panic!("expected StoredRef entity, got {other:?}"),
    }
}

#[test]
fn replace_named_arg_swaps_one_field() {
    // Build Pair(fst: 1, snd: 2), replace `snd` with 99, expect
    // Pair(fst: 1, snd: 99). Pair is a stdlib entity with named-args.
    let src = r#"
namespace test.replace_arg
  import anthill.prelude.{Pair}
  import anthill.prelude.Pair.{pair}
  import anthill.reflect.{Term, replace_named_arg}

  fact pair(fst: 1, snd: 2)
end
"#;
    let mut interp = interp_for(src);
    let pair_ref = Value::term(
        interp
            .kb_mut()
            .resolve_qualified_name_term("anthill.prelude.Pair.pair"),
    );
    let facts = interp
        .call("anthill.reflect.KB.facts_of", &[Value::Unit, pair_ref])
        .expect("facts_of");
    // Walk the cons-list and pick the head whose `fst` field is the
    // ground Int64 literal — the user fact. (WI-515: facts_of now returns
    // only data facts; the synthetic entity declaration that used to ride
    // along is no longer asserted, so the filter is just shape-checking.)
    use anthill_core::kb::term::{Literal, Term};
    let head = {
        let mut cur = facts.clone();
        let mut found = None;
        loop {
            match cur {
                Value::Entity { ref named, .. } => {
                    let h = named
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "head")
                        .map(|(_, v)| v.clone());
                    let t = named
                        .iter()
                        .find(|(s, _)| interp.kb().local_name_of(*s) == "tail")
                        .map(|(_, v)| v.clone());
                    match (h, t) {
                        (Some(Value::Term { id: tid, .. }), Some(tail)) => {
                            if let Term::Fn { named_args, .. } = interp.kb().get_term(tid) {
                                let is_user_fact = named_args.iter().any(|(s, t)| {
                                    interp.kb().local_name_of(*s) == "fst"
                                        && matches!(
                                            interp.kb().get_term(*t),
                                            Term::Const(Literal::Int(_))
                                        )
                                });
                                if is_user_fact {
                                    found = Some(Value::term(tid));
                                    break;
                                }
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
    let result = interp
        .call(
            "anthill.reflect.replace_named_arg",
            &[head, Value::Str("snd".into()), new_val],
        )
        .expect("replace_named_arg");

    // Read the result on whatever carrier it rides: `snd` is now 99, `fst` still 1.
    use anthill_core::kb::term_view::TermView;
    let field = |name: &str| {
        result
            .named_field(interp.kb(), name)
            .and_then(|f| f.to_value().literal_int64(interp.kb()))
            .unwrap_or_else(|| panic!("{name}: no Int64 field in {result:?}"))
    };
    assert_eq!(field("snd"), 99, "snd should be 99");
    assert_eq!(field("fst"), 1, "fst should still be 1");
}
