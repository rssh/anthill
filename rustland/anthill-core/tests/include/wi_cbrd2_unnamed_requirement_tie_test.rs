//! TWO REQUIREMENTS WITH NO NAME THAT ONE CALL FITS (WI-20261105-CBRD2; the user, 2026-11-19,
//! kernel-language §5.2). `sort Both { sort T = ?  requires Conv[A = T, B = Int64]  requires
//! Conv[A = T, B = Bool] }` holds two dictionaries of `Conv` at one `T`, and `Conv.conv(x: A)`
//! writes nothing of `B`: nothing at the call tells the two apart. Three readings disagreed:
//!
//! * an operation's call took the FIRST written — the clause licensing the call's other
//!   parameters was the first about its carrier (`scope_clause_at_carrier`) —, `1` at `Int64`;
//! * a rule's call took a read of its own that found two providers at the value's `Int64`, and
//!   answered undecided;
//! * a goal handing the requirement to a guarded rule was refused ("the sort states two the
//!   goal fits").
//!
//! The call is refused at load now, in an operation (`TypeError::UnnamedRequirementTie`) and in
//! a rule, naming both and the repair: the bracket writing the parameter that tells them apart,
//! `Conv[A = T, B = Bool].conv(x)`, which reads the one it writes — in a rule, the requirement
//! the sort states there, read as a guard of the clause is and filled where it is cited. Two
//! requirements at two types are no such pair: the call's own element tells them apart.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every row
//! passes.
//!
//! * The licensing clause taken from the first written: [`an_operations_call_is_refused_and_its_bracket_picks`]
//!   fails, the call loading and answering `1`.
//! * The tie not looked for among unnamed requirements: the same row fails, the call loading
//!   with its `B` left open.
//! * The rule's call not refused: [`a_rules_call_is_refused_and_its_bracket_picks`] fails, the
//!   clause loading.
//! * The rule's bracket not read: the same row fails, the bracketed citation answering nothing,
//!   and so does `wi_cbrd2_sort_requirement_call_read_test`'s `viaBoth`.
//! * [`requirements_at_two_types_are_no_such_pair`] passes either way: the control.

use anthill_core::kb::resolve::value_reads_by_this_thread;

use crate::common::{interp_for, load_errors_of, load_kb_with, load_stdlib_kb, pattern_last_ints};

/// `f`'s result and the reads for a call it answered from a value, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = value_reads_by_this_thread();
    let r = f();
    (r, value_reads_by_this_thread() - before)
}

/// `Conv` and its two providers at `A = Int64`, `IntInt` (`1`) and `IntBool` (`2`); `both` is
/// the body of `sort Both`, which states `Conv` at `B = Int64` and at `B = Bool`; `tail` follows.
fn program(both: &str, tail: &str) -> String {
    format!(
        r#"
namespace test.cbrd2.tie
  import anthill.prelude.{{Int64, Bool}}
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(x: A) -> Int64
  end
  sort IntInt
    provides Conv[A = Int64, B = Int64]
    operation conv(x: Int64) -> Int64 = 1
  end
  sort IntBool
    provides Conv[A = Int64, B = Bool]
    operation conv(x: Int64) -> Int64 = 2
  end
  sort Both
    sort T = ?
    requires Conv[A = T, B = Int64]
    requires Conv[A = T, B = Bool]
{both}
  end
{tail}end
"#
    )
}

fn int(src: &str, op: &str) -> i64 {
    let mut interp = interp_for(src);
    match interp.call(&format!("test.cbrd2.tie.{op}"), &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(anthill_core::eval::Value::Int(n)) => n,
        other => panic!("{op}: expected an Int64, got {other:?}"),
    }
}

/// `operation direct(x: T) -> Int64 = Conv.conv(x)` is refused, naming both requirements and the
/// bracket; written `Conv[A = T, B = Bool].conv(x)` it reads `IntBool`'s, `2`, and at `B = Int64`
/// `IntInt`'s, `1`.
#[test]
fn an_operations_call_is_refused_and_its_bracket_picks() {
    let errors = load_errors_of(&program("    operation direct(x: T) -> Int64 = Conv.conv(x)", ""));
    assert!(
        errors.iter().any(|e| e.contains("two requirements of the enclosing declaration with no name both cover")
            && e.contains("B = anthill.prelude.Int64")
            && e.contains("B = anthill.prelude.Bool")
            && e.contains("`Conv[…, B = …].conv(…)`")),
        "refused, naming both and the bracket: {errors:?}"
    );
    for (b, want) in [("Bool", 2), ("Int64", 1)] {
        let src = program(
            &format!("    operation direct(x: T) -> Int64 = Conv[A = T, B = {b}].conv(x)"),
            "  operation go() -> Int64 = Both[T = Int64].direct(1)\n",
        );
        assert_eq!(int(&src, "go"), want, "the bracket at `B = {b}`");
    }
}

/// `rule direct(?x: T, ?r) :- Conv.conv(?x, ?r)` is refused the same way; written with the
/// bracket, a citation at `Int64` answers the provider the bracket picks, nothing read from the
/// value.
#[test]
fn a_rules_call_is_refused_and_its_bracket_picks() {
    let errors = load_errors_of(&program("    rule direct(?x: T, ?r) :- Conv.conv(?x, ?r)", ""));
    assert!(
        errors.iter().any(|e| e.contains("direct.body")
            && e.contains("the sort states two with no name the call fits")
            && e.contains("B = anthill.prelude.Int64")
            && e.contains("B = anthill.prelude.Bool")),
        "refused, naming both: {errors:?}"
    );
    for (b, want) in [("Bool", 2), ("Int64", 1)] {
        let src = program(
            &format!("    rule direct(?x: T, ?r) :- Conv[A = T, B = {b}].conv(?x, ?r)"),
            "  rule via(?r) :- Both[T = Int64].direct(1, ?r)\n",
        );
        let mut kb = load_kb_with(&src);
        let (answers, reads) = counting(|| pattern_last_ints(&mut kb, "test.cbrd2.tie.via(?r)"));
        assert_eq!(answers, vec![want], "the bracket at `B = {b}`");
        assert_eq!(reads, 0, "a dictionary read off the values");
    }
}

/// `requires Conv[A = T, B = Int64]` beside `requires Conv[A = U, B = Bool]`: a call at a `T`
/// reads the first, its own element telling the two apart (§5.2). Passes either way.
#[test]
fn requirements_at_two_types_are_no_such_pair() {
    let src = r#"
namespace test.cbrd2.tie2
  import anthill.prelude.{Int64, Bool}
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(x: A) -> Int64
  end
  sort IntInt
    provides Conv[A = Int64, B = Int64]
    operation conv(x: Int64) -> Int64 = 1
  end
  sort IntBool
    provides Conv[A = Int64, B = Bool]
    operation conv(x: Int64) -> Int64 = 2
  end
  sort Two
    sort T = ?
    sort U = ?
    requires Conv[A = T, B = Int64]
    requires Conv[A = U, B = Bool]
    operation atT(x: T) -> Int64 = Conv.conv(x)
    operation atU(y: U) -> Int64 = Conv.conv(y)
  end
  operation goT() -> Int64 = Two[T = Int64, U = Int64].atT(1)
  operation goU() -> Int64 = Two[T = Int64, U = Int64].atU(1)
end
"#;
    let mut interp = interp_for(src);
    let mut call = |op: &str| {
        interp
            .call(&format!("test.cbrd2.tie2.{op}"), &anthill_core::eval::HostValue::all(&[]))
            .map(|h| h.value)
    };
    assert!(matches!(call("goT"), Ok(anthill_core::eval::Value::Int(1))));
    assert!(matches!(call("goU"), Ok(anthill_core::eval::Value::Int(2))));
}
