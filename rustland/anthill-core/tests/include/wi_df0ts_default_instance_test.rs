//! DF0TS: default bodies receive the instance they forward to other declarations.
//! Backed out, six source-call regressions fail; the host-entry control passes.
//! The extended KSSA4 own-instance execution also passes by design.
use crate::common::run_int64;
const HEADER: &str = r#"
namespace defaultInstance
 import anthill.prelude.Int64
 sort Coll
  sort C = ?
  operation size(c: C) -> Int64
  operation viaHelper(c: C) -> Int64 = Helper.twice(c)
  operation viaBuild(c: C) -> Int64 = Holder.read(hold(c))
 end
 sort Helper
  sort X = ?
  requires Coll[C = X]
  operation twice(x: X) -> Int64 = Coll.size(x) + Coll.size(x)
 end
 sort Holder
  sort X = ?
  requires Coll[C = X]
  entity hold(x: X)
  operation read(h: Self) -> Int64 = match h case hold(x) -> Coll.size(x)
 end
 sort L
  entity l(n: Int64)
  provides Coll[C = L]
  operation size(c: L) -> Int64 = c.n
 end
"#;
fn program(body: &str) -> String {
    format!("{HEADER}\n{body}\nend")
}
#[test]
fn a_direct_default_forwards_to_a_helper() {
    assert_eq!(
        run_int64(
            &program("operation go() -> Int64 = Coll.viaHelper(l(3))"),
            "defaultInstance.go"
        ),
        Ok(6)
    );
}
#[test]
fn a_direct_default_reads_the_value_it_builds() {
    assert_eq!(
        run_int64(
            &program("operation go() -> Int64 = Coll.viaBuild(l(3))"),
            "defaultInstance.go"
        ),
        Ok(3)
    );
}
#[test]
fn a_caller_requirement_supplies_the_defaults_instance() {
    let src=program("operation via[P](x: P) -> Int64 requires Coll[C = P] = Coll.viaHelper(x) + Coll.viaBuild(x)\noperation go() -> Int64 = via(l(3))");
    assert_eq!(run_int64(&src, "defaultInstance.go"), Ok(9));
}
#[test]
fn a_host_entry_supplies_the_defaults_instance() {
    let mut interp = crate::common::interp_for(&program("operation value() -> L = l(3)"));
    let value = interp.call("defaultInstance.value", &[]).unwrap();
    assert!(matches!(
        interp.call("defaultInstance.Coll.viaHelper", &[value]),
        Ok(anthill_core::eval::Value::Int(6))
    ));
}

#[test]
fn a_provider_inheriting_every_operation_still_has_its_instance() {
    let src = program("operation go() -> Int64 = Coll.viaHelper(l(3)) + Coll.viaBuild(l(3))")
        .replace(
            "operation size(c: C) -> Int64",
            "operation size(c: C) -> Int64 = 7",
        )
        .replace("operation size(c: L) -> Int64 = c.n", "");
    assert_eq!(run_int64(&src, "defaultInstance.go"), Ok(21));
}
#[test]
fn two_requirement_instances_are_selected_by_the_receiver() {
    let src=program("sort M\n entity m(value: Int64)\n provides Coll[C = M]\n operation size(c: M) -> Int64 = c.value + 20\nend\noperation via[P,Q](x: P, y: Q) -> Int64 requires Coll[C = P], Coll[C = Q] = Coll.viaHelper(x) + Coll.viaBuild(y)\noperation go() -> Int64 = via(l(3),m(5))");
    assert_eq!(run_int64(&src, "defaultInstance.go"), Ok(31));
}

#[test]
fn an_explicit_witness_is_the_instance_forwarded_by_the_default() {
    let src=program("sort Special\n provides Coll[C = L]\n operation size(c: L) -> Int64 = 100\nend\noperation via[P](x: P) -> Int64 requires Coll[C = P] = Coll.viaHelper(x) + Coll.viaBuild(x)\noperation go() -> Int64 = via[Coll = Special](l(3))");
    assert_eq!(run_int64(&src, "defaultInstance.go"), Ok(300));
}
