//! A const is the receiver of a dot, as any value is (kernel-language.md §5.9) — found
//! while delivering WI-20261011-2QZ3F.
//!
//! THE RULE. Over `const origin: P`, `origin.x` reads a field of the const's value and
//! `origin.getX()` calls a member on it, whether the const is named by one segment or
//! dotted (`Q.origin.x`), with further members after it or arguments.
//!
//! BEFORE. Every spelling was refused in an operation body. The field read was walked as
//! a name path — `x.name: expected resolved name, got unresolved` — and the call was the
//! functor `origin.getX`, which nothing declares; `P.getX(origin)` ran. The loader's two
//! receiver ladders (the field read's and the call's) admitted a local and a rule as a
//! value a dot is applied to, through one probe they share, and not a const.
//!
//! EVERY ROW HAS ITS OWN SOURCE.
//!
//! CONTROLS — measured by having the shared probe (`Loader::value_prefix_split`) ask the
//! rule alone, as it did, and running this file. FAIL, each refused:
//!     a_field_of_a_const_is_read
//!     a_member_is_called_on_a_const
//!     a_const_named_by_its_dotted_name_is_a_receiver_too — both
//!     members_chain_after_a_const — both
//!     a_call_on_a_const_takes_its_arguments — both
//!     a_spec_operation_is_dispatched_on_a_const
//!     a_sorts_const_is_a_receiver_inside_the_sort
//!     a_consts_value_may_read_through_another_const
//!     a_const_is_a_receiver_under_a_lambda_and_in_a_scrutinee
//!     a_library_member_is_called_on_a_const
//!     a_relation_a_const_holds_is_drained_by_a_dot_on_it
//!     a_bracket_on_a_dot_call_on_a_const_is_refused_as_on_a_local — its const half
//!   PASS either way, by design:
//!     a_local_of_the_same_name_is_the_receiver
//!     a_parameter_of_the_same_name_is_the_receiver
//!     the_const_passed_as_an_argument_reads_the_same
//!     a_hidden_const_is_no_receiver_from_outside
//!
//!   The rule's half of the probe is not this file's: `wi749_…`, `wi750_…` and the
//!   `wi714_…` relation tests hold it, and pass with the const's half in or out.
//!
//!   NOT COVERED, measured the same before and after: a const's field in a rule body's
//!   data slot (`?v <=> origin.x`) is refused for a const whose value is computed, the
//!   data slot's own rule (§5.9); a precondition that reads one (`requires n >
//!   origin.x`) is not proved at a call site.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `P`, a point with a reader and an adder, and `Line`, two points.
const P: &str = "  sort P\n    entity pt(x: Int64, y: Int64)\n    operation getX(p: P) -> Int64 =\n      match p\n        case pt(a, b) -> a\n    operation plus(p: P, n: Int64) -> Int64 =\n      match p\n        case pt(a, b) -> a + n\n  end\n  sort Line\n    entity ln(a: P, b: P)\n  end\n";

/// A const of the namespace.
const ORIGIN: &str = "  const origin: P = P.pt(3, 4)\n";

/// Two consts of a sort.
const Q: &str = "  sort Q\n    const origin: P = P.pt(3, 4)\n    const line: Line = Line.ln(P.pt(5, 6), P.pt(7, 8))\n  end\n";

fn ns(name: &str, decls: &str) -> String {
    format!(
        "namespace test.{name}\n  import anthill.prelude.{{Int64, String, List, Error, Relation}}\n{P}{decls}\nend\n"
    )
}

fn assert_reads(name: &str, decls: &str, expected: i64) {
    let source = ns(name, decls);
    assert_eq!(
        run_int64(&source, &format!("test.{name}.rd")),
        Ok(expected),
        "{source}"
    );
}

#[test]
fn a_field_of_a_const_is_read() {
    assert_reads("cr1", &format!("{ORIGIN}  operation rd() -> Int64 = origin.x"), 3);
}

#[test]
fn a_member_is_called_on_a_const() {
    assert_reads("cr2", &format!("{ORIGIN}  operation rd() -> Int64 = origin.getX()"), 3);
}

#[test]
fn a_const_named_by_its_dotted_name_is_a_receiver_too() {
    assert_reads("cr3", &format!("{Q}  operation rd() -> Int64 = Q.origin.x"), 3);
    assert_reads("cr3b", &format!("{Q}  operation rd() -> Int64 = Q.origin.getX()"), 3);
}

/// A field of a field, and a member called on a field.
#[test]
fn members_chain_after_a_const() {
    assert_reads("cr4", &format!("{Q}  operation rd() -> Int64 = Q.line.a.x"), 5);
    assert_reads("cr4b", &format!("{Q}  operation rd() -> Int64 = Q.line.b.getX()"), 7);
}

/// Positional and named.
#[test]
fn a_call_on_a_const_takes_its_arguments() {
    assert_reads("cr5", &format!("{ORIGIN}  operation rd() -> Int64 = origin.plus(10)"), 13);
    assert_reads("cr5b", &format!("{Q}  operation rd() -> Int64 = Q.origin.plus(n: 10)"), 13);
}

#[test]
fn a_spec_operation_is_dispatched_on_a_const() {
    assert_reads(
        "cr6",
        "  sort Shown\n    sort T = ?\n    operation show(x: T) -> Int64\n  end\n  sort Leaf\n    entity leaf\n    provides Shown[T = Leaf]\n    operation show(x: Leaf) -> Int64 = 7\n  end\n  const l: Leaf = Leaf.leaf()\n  operation rd() -> Int64 = l.show()",
        7,
    );
}

/// The one-segment name, in scope inside the sort that declares the const.
#[test]
fn a_sorts_const_is_a_receiver_inside_the_sort() {
    assert_reads(
        "cr7",
        "  sort Q\n    const origin: P = P.pt(3, 4)\n    operation inside() -> Int64 = origin.x + origin.getX()\n  end\n  operation rd() -> Int64 = Q.inside()",
        6,
    );
}

/// A const's value is typed as an operation body is, and the purity gate judges the
/// read and the call it was dispatched to.
#[test]
fn a_consts_value_may_read_through_another_const() {
    assert_reads(
        "cr8",
        &format!(
            "{ORIGIN}  const ox: Int64 = origin.x\n  const oy: Int64 = origin.getX() + 1\n  operation rd() -> Int64 = ox + oy"
        ),
        7,
    );
}

#[test]
fn a_const_is_a_receiver_under_a_lambda_and_in_a_scrutinee() {
    assert_reads(
        "cr9",
        &format!(
            "{ORIGIN}  operation rd() -> Int64 =\n    let f = lambda n -> origin.x + n\n    match origin.getX()\n      case 3 -> f(10)\n      case _ -> 0"
        ),
        13,
    );
}

#[test]
fn a_library_member_is_called_on_a_const() {
    assert_reads(
        "cr10",
        "  import anthill.prelude.List.{length}\n  const names: List[T = Int64] = [1, 2, 3]\n  operation rd() -> Int64 = names.length()",
        3,
    );
}

/// The relation a const holds (`wi_2qz3f_const_value_equation_test` reads it through a
/// `let`): the dot is on the const.
#[test]
fn a_relation_a_const_holds_is_drained_by_a_dot_on_it() {
    assert_reads(
        "cr11",
        "  import anthill.prelude.List.{length}\n  import anthill.prelude.PartialEq.{eq}\n  sort People\n    entity person(name: String, age: Int64)\n  end\n  fact person(name: \"alice\", age: 30)\n  fact person(name: \"bob\", age: 25)\n  fact person(name: \"carol\", age: 30)\n  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)\n  const thirty: Relation[T = (name: String, age: Int64)] = person_row.where(lambda c -> eq(c.age, 30))\n  operation rd() -> Int64 effects Error = length(thirty.takeN(100))",
        2,
    );
}

/// The probe's other reader: a call-site bracket on a dot call on a const is the bracket
/// of the call it resolves to, as on a local (WI-20261026-8K7W0), so `getX`, which declares
/// no `T`, refuses it as `P.getX[T = Int64](origin)` does. It was told about the flattened
/// functor `origin.getX`, "got a callee with no type-parameter list".
#[test]
fn a_bracket_on_a_dot_call_on_a_const_is_read_as_on_a_local() {
    for (name, decls) in [
        ("cr16", format!("{ORIGIN}  operation rd() -> Int64 = origin.getX[T = Int64]()")),
        (
            "cr16l",
            "  operation rd() -> Int64 =
    let origin = P.pt(9, 9)
    origin.getX[T = Int64]()".to_string(),
        ),
        ("cr16a", format!("{ORIGIN}  operation rd() -> Int64 = P.getX[T = Int64](origin)")),
    ] {
        let errs = load_errors_of(&ns(name, &decls));
        assert_refused_naming(
            &errs,
            &["P.getX.type_arg", "unknown type-param 'T'"],
            name,
        );
        assert!(
            !errs.iter().any(|e| e.contains("no type-parameter list")),
            "{name}: {errs:?}"
        );
    }
}

// ── What does not move ───────────────────────────────────────────────

/// A `let` binder of the const's name is the receiver: the local pass runs first.
#[test]
fn a_local_of_the_same_name_is_the_receiver() {
    assert_reads(
        "cr12",
        &format!("{ORIGIN}  operation rd() -> Int64 =\n    let origin = P.pt(9, 9)\n    origin.x"),
        9,
    );
}

#[test]
fn a_parameter_of_the_same_name_is_the_receiver() {
    assert_reads(
        "cr13",
        &format!(
            "{ORIGIN}  operation read(origin: P) -> Int64 = origin.getX()\n  operation rd() -> Int64 = read(P.pt(9, 9))"
        ),
        9,
    );
}

#[test]
fn the_const_passed_as_an_argument_reads_the_same() {
    assert_reads("cr14", &format!("{Q}  operation rd() -> Int64 = P.getX(Q.origin)"), 3);
}

/// `internal` hides the const from outside its sort: no prefix of the chain names it.
#[test]
fn a_hidden_const_is_no_receiver_from_outside() {
    let errs = load_errors_of(&ns(
        "cr15",
        "  sort Q\n    internal const hidden: P = P.pt(3, 4)\n  end\n  operation rd() -> Int64 = Q.hidden.x",
    ));
    assert_refused_naming(
        &errs,
        &["hidden.name", "expected resolved name"],
        "the const is internal to `Q`",
    );
}
