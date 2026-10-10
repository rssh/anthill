//! WI-929 items 4 and 8 — a dotted declaration belongs to the address its prefix
//! names. Item 4 applies proposal 059 classification there: `entity E.Child` is the
//! same secondary-entry content as `namespace E { entity Child }` when `E` is already
//! a sort. Item 8 applies the same address rule to entity ownership: `entity a.B`
//! written syntactically in `sort S` belongs to namespace `S.a`, not to S.
//!
//! THE OLD FINDING SAID THE CHILD BECAME A CONSTRUCTOR OF `E`. That is obsolete:
//! constructor registration was repaired elsewhere. The live defect was the quieter
//! one: `SecondaryEntryPass::at_item` did nothing, so the dotted
//! spelling bypassed R3 while the explicit spelling was refused.
//!
//! BACK-OUT MEASUREMENT: with the `at_item` classification removed, the dotted entity
//! and body-less-operation rows both load without an R3 refusal. Their explicit
//! controls still refuse. Both bodied-operation rows pass either way; they guard the
//! allowed side and DRIVE the member by calling it.

use anthill_core::eval::{self, Interpreter, Value};

fn errors_of(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

fn r3_errors(src: &str) -> Vec<String> {
    errors_of(src)
        .into_iter()
        .filter(|e| e.contains("is not allowed in a secondary entry"))
        .collect()
}

fn fixture(ns: &str, declaration: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.Int64
  entity E(x: Int64)
{declaration}
end
"#
    )
}

fn eval_int(src: &str, op: &str) -> i64 {
    let kb = crate::common::try_load_kb_with(src)
        .unwrap_or_else(|errs| panic!("fixture must load clean; got {errs:#?}"));
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("register eval builtins");
    match interp.call(op, &[]) {
        Ok(Value::Int(n)) => n,
        Ok(other) => panic!("expected Int, got {}", other.type_name()),
        Err(e) => panic!("operation call failed: {e}"),
    }
}

#[test]
fn dotted_entity_is_refused_like_the_explicit_secondary_entry() {
    let dotted = fixture("test.wi929.entity_dot", "  entity E.Child(y: Int64)");
    let explicit = fixture(
        "test.wi929.entity_explicit",
        "  namespace E\n    entity Child(y: Int64)\n  end",
    );

    for (label, sort, written, src) in [
        ("dotted", "test.wi929.entity_dot.E", "E.Child", dotted),
        (
            "explicit",
            "test.wi929.entity_explicit.E",
            "Child",
            explicit,
        ),
    ] {
        let errs = r3_errors(&src);
        assert_eq!(
            errs.len(),
            1,
            "{label}: expected one R3 refusal; got {errs:#?}"
        );
        assert!(
            errs[0].contains(&format!("`entity` '{written}'"))
                && errs[0].contains(&format!("'{sort}'")),
            "{label}: diagnostic must name the entity and E's address; got {:?}",
            errs[0]
        );
    }
}

#[test]
fn dotted_bodyless_operation_is_refused_like_the_explicit_secondary_entry() {
    let dotted = fixture(
        "test.wi929.operation_dot",
        "  operation E.answer(x: E) -> Int64",
    );
    let explicit = fixture(
        "test.wi929.operation_explicit",
        "  namespace E\n    operation answer(x: E) -> Int64\n  end",
    );

    for (label, written, src) in [
        ("dotted", "E.answer", dotted),
        ("explicit", "answer", explicit),
    ] {
        let errs = r3_errors(&src);
        assert_eq!(
            errs.len(),
            1,
            "{label}: expected one R3 refusal; got {errs:#?}"
        );
        assert!(
            errs[0].contains(&format!("`operation` '{written}'"))
                && errs[0].contains("runnable Anthill body"),
            "{label}: diagnostic must identify R4's missing body; got {:?}",
            errs[0]
        );
    }
}

#[test]
fn dotted_bodied_operation_executes_like_the_explicit_secondary_entry() {
    let dotted = fixture(
        "test.wi929.run_dot",
        "  operation E.answer(x: E) -> Int64 = 929\n  operation drive() -> Int64 = E(x: 1).answer()",
    );
    let explicit = fixture(
        "test.wi929.run_explicit",
        "  namespace E\n    operation answer(x: E) -> Int64 = 929\n  end\n  operation drive() -> Int64 = E(x: 1).answer()",
    );

    assert_eq!(eval_int(&dotted, "test.wi929.run_dot.drive"), 929);
    assert_eq!(eval_int(&explicit, "test.wi929.run_explicit.drive"), 929);
}

/// WI-929 item 8 — a dotted entity is owned by the address its prefix names, not
/// by the syntactic sort block containing the spelling. The explicit namespace row
/// is the control: it passed before and after the fix. BACK-OUT: the dotted row says
/// `strict_parent_sort(B) == Some(S)`, files B in S's constructor list, and does not
/// make the free-standing B its own sort.
#[test]
fn dotted_entity_inside_sort_matches_explicit_namespace_ownership() {
    for (label, ns, declaration) in [
        (
            "dotted",
            "test.wi929.item8_dot",
            "  sort S\n    namespace a\n      sort Local = Int64\n      namespace a\n        entity B(y: Int64)\n      end\n    end\n    entity a.B(x: Local)\n  end",
        ),
        (
            "explicit control",
            "test.wi929.item8_explicit",
            "  sort S\n    namespace a\n      sort Local = Int64\n      namespace a\n        entity B(y: Int64)\n      end\n      entity B(x: Local)\n    end\n  end",
        ),
    ] {
        let src = format!(
            "namespace {ns}\n  import anthill.prelude.Int64\n{declaration}\n  operation drive() -> Int64 = S.a.B(x: 929).x\nend\n"
        );
        let kb = crate::common::try_load_kb_with(&src)
            .unwrap_or_else(|errs| panic!("{label}: fixture must load; got {errs:#?}"));
        let s = kb
            .try_resolve_symbol(&format!("{ns}.S"))
            .expect("S resolves");
        let b = kb
            .try_resolve_symbol(&format!("{ns}.S.a.B"))
            .expect("B resolves");
        let a = kb
            .try_resolve_symbol(&format!("{ns}.S.a"))
            .expect("a resolves");
        let decoy = kb
            .try_resolve_symbol(&format!("{ns}.S.a.a.B"))
            .expect("the nested same-spelled decoy resolves");
        assert_ne!(b, decoy, "{label}: the two addresses are distinct");
        assert_eq!(
            kb.strict_parent_sort(b),
            None,
            "{label}: B is not a constructor of the syntactically enclosing S",
        );
        assert_eq!(
            kb.sort_of_constructor(b),
            Some(b),
            "{label}: a namespace-level entity is its own single-constructor sort",
        );
        assert!(
            !kb.constructors_of_sort(s).contains(&b),
            "{label}: S's constructor inventory must not contain B",
        );
        assert!(
            kb.constructors_of_sort(b).contains(&b),
            "{label}: B's constructor inventory must contain itself",
        );
        let member_info = kb
            .try_resolve_symbol("anthill.reflect.MemberInfo")
            .expect("MemberInfo resolves");
        let b_member_rows = |domain| {
            kb.by_domain(domain)
                .iter()
                .filter(|&&fid| {
                    let head = kb.rule_head_value(fid);
                    eval::value_functor(&kb, head) == Some(member_info)
                        && anthill_core::kb::op_info::head_name_ref(&kb, head) == Some(b)
                })
                .count()
        };
        assert_eq!(
            b_member_rows(a),
            1,
            "{label}: reflection must list B once under its actual namespace",
        );
        assert_eq!(
            b_member_rows(s),
            0,
            "{label}: reflection must not list B as a constructor member of S",
        );
        assert_eq!(eval_int(&src, &format!("{ns}.drive")), 929);
    }
}
