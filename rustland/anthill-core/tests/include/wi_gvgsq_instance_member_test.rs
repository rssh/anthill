//! GVGSQ: omitted members are rigid at one requirement instance across calls.
//! Backed out: the first eight tests have four failing regressions and four passing
//! controls (the named-member refusal and the three same-instance executions).
//! The final foreign-carrier naming test separately fails without the naming guard.
use crate::common::{assert_refused_naming, load_errors_of, run_int64};
const HEADER: &str = r#"
namespace instanceMember
 import anthill.prelude.{Int64, String}
 sort Tagger
   sort C = ?
   sort Out = ?
   operation out(self: C) -> Out
   operation useOut(self: C, o: Out) -> Int64
 end
 sort B
   entity b(n: Int64)
   provides Tagger[C = B, Out = String]
   operation out(self: B) -> String = "s"
   operation useOut(self: B, o: String) -> Int64 = 3
 end
 import instanceMember.B.b
"#;
fn program(body: &str) -> String {
    format!("{HEADER}\n{body}\nend")
}
#[test]
fn omitted_return_member_cannot_be_chosen_by_the_result_annotation() {
    let src = program("operation f(x: Tagger.C) -> Int64 = Tagger.out(x)");
    assert_refused_naming(
        &load_errors_of(&src),
        &["expected Int64, got Tagger.Out"],
        "omitted return member",
    );
}
#[test]
fn named_return_member_control_is_also_rigid() {
    let src = program("operation h(x: Tagger.C, o: Tagger.Out) -> Int64 = Tagger.out(x)");
    assert_refused_naming(
        &load_errors_of(&src),
        &["expected Int64, got Tagger.Out"],
        "named return member control",
    );
}
#[test]
fn same_instance_calls_share_the_omitted_member_and_execute() {
    let src=program("operation k(x: Tagger.C) -> Int64 = Tagger.useOut(x, Tagger.out(x))\noperation main() -> Int64 = k(b(1))");
    assert_eq!(run_int64(&src, "instanceMember.main"), Ok(3));
}
#[test]
fn another_carriers_member_cannot_be_used_as_this_instances_member() {
    let src=program("operation bad[P,Q](x: P, y: Q) -> Int64 requires Tagger[C = P], Tagger[C = Q] = Tagger.useOut(x, Tagger.out(y))");
    assert_refused_naming(&load_errors_of(&src), &["Out"], "two requirement instances");
}
#[test]
fn undeclared_effect_names_its_own_spec_member() {
    let src = r#"
namespace instanceEffects
 import anthill.prelude.Int64
 sort Tagger
  sort C = ?
  effects E = ?
  operation tag(self: C) -> Int64 effects {E}
 end
 sort Other
  sort C = ?
  effects E = ?
  operation oth(self: C) -> Int64 effects {E}
 end
 operation both(x: Tagger.C, y: Other.C) -> Int64 effects {Tagger.E} = Tagger.tag(x) + Other.oth(y)
end
"#;
    assert_refused_naming(
        &load_errors_of(src),
        &["expected declared: [Tagger.E], got undeclared effect: Other.E"],
        "omitted effect",
    );
}

#[test]
fn an_explicit_second_instance_effect_is_not_printed_as_the_declared_one() {
    let src = r#"
namespace instanceEffects
 import anthill.prelude.Int64
 sort Tagger
  sort C = ?
  effects E = ?
  operation tag(self: C) -> Int64 effects {E}
 end
 operation f[T](x: Tagger.C, y: T) -> Int64 effects {Tagger.E} requires Tagger[C = T] = Tagger.tag(y)
end
"#;
    let errors = load_errors_of(src);
    assert_refused_naming(
        &errors,
        &[
            "expected declared: [Tagger.E]",
            "undeclared effect: Tagger[C = T].E",
        ],
        "second instance effect",
    );
}
#[test]
fn alias_instance_calls_share_the_omitted_member_and_execute() {
    let src=program("sort Alias = Tagger\noperation k(x: Alias.C) -> Int64 = Tagger.useOut(x, Tagger.out(x))\noperation main() -> Int64 = k(b(1))");
    assert_eq!(run_int64(&src, "instanceMember.main"), Ok(3));
}
#[test]
fn bracket_instance_calls_share_the_omitted_member_and_execute() {
    let src=program("operation k[P](x: P) -> Int64 requires Tagger[C = P] = Tagger.useOut(x, Tagger.out(x))\noperation main() -> Int64 = k(b(1))");
    assert_eq!(run_int64(&src, "instanceMember.main"), Ok(3));
}

// A clause can use another spec's carrier member without being that spec's instance.
// This fails with the first draft's unconditional reuse of the carrier's display head.
#[test]
fn a_requirement_on_another_specs_carrier_keeps_its_own_member_name() {
    let src = program("sort Other\n sort C = ?\nend\noperation f(x: Other.C) -> Int64 requires Tagger[C = Other.C] = Tagger.out(x)");
    assert_refused_naming(
        &load_errors_of(&src),
        &["expected Int64, got Tagger[C = Other.C].Out"],
        "foreign carrier member",
    );
}
