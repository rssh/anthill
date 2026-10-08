//! Explicit carrier types and dictionary obligations (8DXVK).
//! Back-out against ef6a3b09: shared carrier identity, automatic dictionary
//! dispatch, rigid selected caller and equation RHS execution fail. The
//! independent-member control passes either way. WI-582's representation
//! assertion also fails; all remaining 69 focused tests pass before the change.
use crate::common;

#[test]
fn shared_introducer_requires_one_carrier_type() {
    let mut kb = common::load_kb_with(
        r#"
namespace test.dxvkShared
 import anthill.prelude.{Int64, Bool}
 sort Marker
  sort T = ?
  operation tag(x: T) -> Int64
 end
 fact src(1, true, 42)
 fact src(1, 2, 43)
 fact src(true, false, 44)
 rule keep[A](?x: A, ?y: A, ?r) :- src(?x, ?y, ?r), Marker[A]
 rule answer(?r) :- keep(?x, ?y, ?r)
end
namespace anthill.prelude.Int64
 import test.dxvkShared.Marker
 provides Marker[T = Int64]
 operation tag(x: Int64) -> Int64 = 1
end
namespace anthill.prelude.Bool
 import test.dxvkShared.Marker
 provides Marker[T = Bool]
 operation tag(x: Bool) -> Int64 = 2
end
"#,
    );
    let answers = common::query_unary(&mut kb, "test.dxvkShared.answer");
    assert_eq!(
        answers.len(),
        2,
        "different carriers cannot instantiate one shared A: {answers:?}"
    );
    assert!(
        answers
            .iter()
            .all(|(v, definite)| *definite && matches!(v, anthill_core::eval::Value::Int(43 | 44))),
        "{answers:?}"
    );
}

#[test]
fn introduced_requirement_threads_dictionary_without_authored_require() {
    let mut kb = common::load_kb_with(
        r#"
namespace test.dxvkAutomatic
 import anthill.prelude.{Int64}
 sort Tagger
  sort C = ?
  sort Out = ?
  operation tag(x: C) -> Out
  operation code() -> Int64 = 1
 end
 sort Red
  entity red
  provides Tagger[C = Red, Out = Int64]
  operation tag(x: Red) -> Int64 = 7
  operation code() -> Int64 = 7
 end
 fact src(red())
 rule keep[A](?x: A, ?r) :- src(?x), Tagger[C = A, Out = Int64], Tagger.code(?r)
 rule answer(?r) :- keep(?x, ?r)
end
"#,
    );
    assert_eq!(
        common::one_definite_int(&mut kb, "test.dxvkAutomatic.answer"),
        Some(7)
    );
}

#[test]
fn rigid_caller_threads_selected_dictionary_to_introduced_requirement() {
    let src = r#"
namespace test.dxvkRigid
 import anthill.prelude.{Int64, Bool, Error, EmptyStream}
 sort Tagger
  sort C = ?
  sort Out = ?
  operation tag(x: C) -> Out
  operation code() -> Int64 = 1
 end
 sort Red
  entity red
  provides Tagger[C = Red, Out = Int64]
  operation tag(x: Red) -> Int64 = 7
  operation code() -> Int64 = 7
 end
 sort Other
  provides Tagger[C = Red, Out = Int64]
  operation tag(x: Red) -> Int64 = 17
  operation code() -> Int64 = 17
 end
 rule keep[A](?x: A, ?r) :- Tagger[C = A, Out = Int64], Tagger.code(?r)
 sort Driver
  operation generic[A](x: A) -> Int64 effects {Error, Error[EmptyStream]}
    requires Tagger[C = A, Out = Int64] = keep(x).head.r
  operation selected() -> Int64 effects {Error, Error[EmptyStream]} = generic[A = Red, Tagger = Other](red())
 end
end
"#;
    for variant in 0..3 {
        let src = if variant != 0 {
            src.replace(
                "rule keep[A](?x: A, ?r) :- Tagger[C = A, Out = Int64]",
                "rule keep[A](?x: A, ?r) :- Tagger[A]",
            )
        } else {
            src.into()
        };
        let src = if variant == 2 {
            src.replace(
                "provides Tagger[C = Red, Out = Int64]\n  operation tag(x: Red) -> Int64 = 17",
                "provides Tagger[C = Red, Out = Bool]\n  operation tag(x: Red) -> Bool = true",
            )
            .replace(
                "requires Tagger[C = A, Out = Int64]",
                "requires Tagger[C = A, Out = Bool]",
            )
        } else {
            src
        };
        let mut interp = common::interp_for(&src);
        let result = interp.call("test.dxvkRigid.Driver.selected", &[]);
        assert!(
            matches!(result, Ok(anthill_core::eval::Value::Int(17))),
            "{result:?}"
        );
    }
}

#[test]
fn equation_rhs_uses_the_carriers_separate_dictionary() {
    let mut interp = common::interp_for(
        r#"
namespace test.dxvkEquation
 import anthill.prelude.{Int64}
 sort Tagger
  sort C = ?
  sort Out = ?
  operation tag(x: C) -> Out
  operation code() -> Int64 = 1
 end
 sort Red
  entity red
  provides Tagger[C = Red, Out = Int64]
  operation tag(x: Red) -> Int64 = 7
  operation code() -> Int64 = 7
 end
 sort Lib
  sort A = ?
  operation pick(x: A) -> Int64 = 1
  rule pick_id: pick[T](?x: T) <=> Tagger.code() :- Tagger[C = T, Out = Int64] @[simp]
  operation answer() -> Int64 = pick[A = Red](red())
 end
end
"#,
    );
    let kb = interp.kb_mut();
    let answer = kb
        .try_resolve_symbol("test.dxvkEquation.Lib.answer")
        .unwrap();
    let pick = kb.try_resolve_symbol("test.dxvkEquation.Lib.pick").unwrap();
    let red = kb.try_resolve_symbol("test.dxvkEquation.Red.red").unwrap();
    let value = kb.alloc(anthill_core::kb::term::Term::Ref(red));
    let term = kb.alloc(anthill_core::kb::term::Term::Fn {
        functor: pick,
        pos_args: smallvec::smallvec![value],
        named_args: smallvec::SmallVec::new(),
    });
    let rewritten_term = kb.simplify(term);
    let redex = anthill_core::kb::node_occurrence::materialize_from_handle(kb, term);
    let (rewritten, changes) = kb.apply_eq_rules(
        &anthill_core::eval::Value::Node(redex),
        100,
        &anthill_core::kb::subst::Substitution::new(),
    );
    assert!(!changes.is_empty(), "the typed equation must fire");
    let anthill_core::eval::Value::Node(rhs) = rewritten else {
        panic!("the RHS must retain its dictionary call")
    };
    kb.set_op_body_node(answer, rhs);
    let result = interp.call("test.dxvkEquation.Lib.answer", &[]);
    assert!(
        matches!(result, Ok(anthill_core::eval::Value::Int(7))),
        "{result:?}"
    );
    let term_result = interp.run_with_requirements(rewritten_term, smallvec::SmallVec::new());
    assert!(
        matches!(term_result, Ok(anthill_core::eval::Value::Int(7))),
        "{term_result:?}"
    );
}

/// Control: anonymous member annotations introduce independent carrier slots.
/// This passes before the representation change too; sharing A is what changes.
#[test]
fn member_annotations_keep_independent_carriers_and_dictionaries() {
    let src = r#"
namespace test.dxvkShared
 import anthill.prelude.{Int64, Bool}
 sort Marker
  sort T = ?
  operation tag(x: T) -> Int64
 end
 fact src(1, true, 42)
 fact src(1, 2, 43)
 fact src(true, false, 44)
 rule keep[A](?x: A, ?y: A, ?r) :- src(?x, ?y, ?r), Marker[A]
 rule answer(?r) :- keep(?x, ?y, ?r)
end
namespace anthill.prelude.Int64
 import test.dxvkShared.Marker
 provides Marker[T = Int64]
 operation tag(x: Int64) -> Int64 = 1
end
namespace anthill.prelude.Bool
 import test.dxvkShared.Marker
 provides Marker[T = Bool]
 operation tag(x: Bool) -> Int64 = 2
end
"#
        .replace("rule keep[A](?x: A, ?y: A, ?r) :- src(?x, ?y, ?r), Marker[A]",
            "rule keep(?x: Marker.T, ?y: Marker.T, ?r) :- src(?x, ?y, ?r)")
        .replace("rule answer(?r) :- keep(?x, ?y, ?r)",
            "rule answer(?r) :- keep(?x, ?y, ?r)\n rule tags(?x: Marker.T, ?y: Marker.T, ?a, ?b) :- Marker.tag(?x, ?a), Marker.tag(?y, ?b)\n rule first(?a) :- tags(1, true, ?a, ?)\n rule second(?b) :- tags(1, true, ?, ?b)");
    let mut kb = common::load_kb_with(&src);
    let answers = common::query_unary(&mut kb, "test.dxvkShared.answer");
    assert_eq!(answers.len(), 3, "{answers:?}");
    assert!(answers.iter().all(|(_, definite)| *definite));
    assert_eq!(
        common::one_definite_int(&mut kb, "test.dxvkShared.first"),
        Some(1)
    );
    assert_eq!(
        common::one_definite_int(&mut kb, "test.dxvkShared.second"),
        Some(2)
    );
}
