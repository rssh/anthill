//! P962X: clauses name the operation's signature member, with its own dictionary.
//! Eight regressions fail backed out; the bracket execution control passes either way.
use crate::common::{assert_refused_naming, load_errors_of, run_int64};
const HEADER: &str = r#"
namespace memberReq
 import anthill.prelude.{Int64, String, Type, Pair}
 import anthill.reflect.TypeValue
 sort X
   sort C = ?
   sort E = ?
   operation get(self: C) -> E
 end
 sort B
   entity b(n: Int64)
   provides X[C = B, E = Int64]
   operation get(self: B) -> Int64 = self.n
 end
 import memberReq.B.b
 sort Tag
   sort T = ?
   operation tagOf(x: T) -> Int64
 end
 sort A
   entity a
   provides X[C = A, E = String]
   operation get(self: A) -> String = "s"
   provides Tag[T = A]
   operation tagOf(x: A) -> Int64 = 50
 end
 import memberReq.A.a
 operation g[P](y: P) -> Int64 requires Tag[T = P] = Tag.tagOf(y)
"#;
fn program(body: &str) -> String {
    format!("{HEADER}\n{body}\nend")
}
#[test]
fn a_member_requirement_forwards_and_executes() {
    let src=program("operation f(x: X.C) -> Int64 requires Tag[T = X.C] = g(x)\noperation main() -> Int64 = f(a())");
    assert_eq!(run_int64(&src, "memberReq.main"), Ok(50));
}
#[test]
fn unnamed_member_in_a_clause_is_refused() {
    let src = program("operation k(x: X.C) -> Int64 requires TypeValue[T = X.E] = 1");
    assert_refused_naming(
        &load_errors_of(&src),
        &["X.E", "has no instance"],
        "clause cannot introduce a member instance",
    );
}

fn eval_type(src: &str) -> String {
    let mut interp = crate::common::interp_for(src);
    match interp.call("memberReq.main", &[]) {
        Ok(anthill_core::eval::Value::Term { id, .. }) => {
            anthill_core::persistence::print::TermPrinter::new(interp.kb()).print_term(id)
        }
        other => panic!("expected a type, got {other:?}"),
    }
}
#[test]
fn member_type_value_dictionary_is_supplied() {
    let src=program("operation only(x: X.C, z: X.E) -> Type requires TypeValue[T = X.E] = Pair[A = Int64, B = X.E]\noperation main() -> Type = only(b(7),5)");
    assert_eq!(eval_type(&src), "Pair(A: Int64, B: Int64)");
}
#[test]
fn two_members_of_one_name_have_distinct_type_value_slots() {
    let src = program(
        r#"
 sort Y
   sort C = ?
   sort E = ?
   operation get(self: C) -> E
 end
 sort D
   entity d
   provides Y[C = D, E = String]
   operation get(self: D) -> String = "s"
 end
 import memberReq.D.d
 operation only(x: X.C, y: Y.C, z: X.E, w: Y.E) -> Type requires TypeValue[T = X.E], TypeValue[T = Y.E] = Pair[A = X.E, B = Y.E]
 operation main() -> Type = only(b(7),d(),5,"s")
"#,
    );
    assert_eq!(eval_type(&src), "Pair(A: Int64, B: String)");
}
#[test]
fn member_requirement_covers_a_construction() {
    let src = program(
        r#"
 sort Box
   sort T = ?
   requires Tag[T = T]
   entity box(v: T)
 end
 import memberReq.Box.box
 operation f(x: X.C) -> Int64 requires Tag[T = X.C] =
   let b = box(x)
   Tag.tagOf(b.v)
 operation main() -> Int64 = f(a())
"#,
    );
    assert_eq!(run_int64(&src, "memberReq.main"), Ok(50));
}
#[test]
fn bracket_requirement_control_executes() {
    let src=program("operation f[P](x: P) -> Int64 requires X[C = P], Tag[T = P] = g(x)\noperation main() -> Int64 = f(a())");
    assert_eq!(run_int64(&src, "memberReq.main"), Ok(50));
}
#[test]
fn a_partially_fixed_alias_member_requirement_forwards() {
    let src=program("sort XS = X[E = String]\noperation f(x: XS.C) -> Int64 requires Tag[T = XS.C] = g(x)\noperation main() -> Int64 = f(a())");
    assert_eq!(run_int64(&src, "memberReq.main"), Ok(50));
}
#[test]
fn a_fixed_alias_member_does_not_borrow_the_open_members_variable() {
    let src=program("sort XA = X[C = A]\noperation f(x: X.C) -> Int64 requires Tag[T = XA.C] = 1\noperation main() -> Int64 = f(b(7))");
    assert_eq!(run_int64(&src, "memberReq.main"), Ok(1));
}
#[test]
fn a_dotted_member_requirement_forwards() {
    let src=program("operation f(x: memberReq.X.C) -> Int64 requires Tag[T = memberReq.X.C] = g(x)\noperation main() -> Int64 = f(a())");
    assert_eq!(run_int64(&src, "memberReq.main"), Ok(50));
}

// The new lookup must not make an alias's instance supply a different spelling
// whose instance the signature never named. Fails with a display-path based guard.
#[test]
fn a_dotted_fixed_alias_does_not_supply_a_bare_member_read() {
    let src = program(
        r#"
 sort Outer
   sort XS = X[C = A]
 end
 operation only(x: Outer.XS.E) -> Type requires TypeValue[T = Outer.XS.E] = Pair[A = Int64, B = X.E]
"#,
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["read as a VALUE", "nothing in scope requires"],
        "a different member instance",
    );
}
