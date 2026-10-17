//! A provider's own parameter written inside an arrow or a tuple of its provision is that
//! parameter where the provision is looked up.
//!
//! `sort P { sort A = ?  provides Apply[F = (A) -> A]  operation run(f: (A) -> A) … }`. Written
//! as an argument of an applied sort (`provides Apply[F = Box[T = A]]`) the `A` is a
//! reference to the parameter, which the lookup binds to what the call states and holds to
//! one type. Inside an arrow or a tuple the provision's type was lowered as a type position
//! is, and `A` was the parameter's own VARIABLE. The lookup (`impl_param_ref`) read a
//! parameter by its name only, so the variable was a wildcard: it matched anything, bound
//! nothing and counted as a written type. MEASURED, three ways:
//!
//! * `P` at `(A) -> A` answered a call at `(Int64) -> String` (30): one parameter at two
//!   types, and the member received a function its own declaration does not admit.
//! * `P` with `requires Show[T = A]` answered no call at all — "no impl matches —
//!   unresolved: `Show[T = P.A]`": its requirement was never read at the call's type.
//! * `P` at `(A, A) -> A` beside `Q` at `(Int64, Int64) -> Int64` was a tie, "ambiguous
//!   dispatch", where `Q`'s head is strictly the more specific (kernel-language §8.7).
//!
//! The lookup was first taught the variable (`impl_param_ref`); since WI-20261013-34822 the
//! loader writes the parameter inside an arrow or a tuple of a clause binding as it writes it
//! at a name and in an applied sort, its `Ref`, and the lookup reads the name only again
//! (`wi_34822_clause_parameter_one_spelling_test`).
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: the call runs, and each provider answers its own number.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! ONE PART — the variable, read as a parameter by the lookup at first. MEASURED AGAIN
//! 2026-10-14 with the loader's tuple-and-arrow arm backed out and the lookup reading the name
//! only: in a build with debug assertions all 5 fail, at `impl_param_ref`'s assertion that a
//! provision holds no variable of its provider's parameter; without the assertion the same 4
//! rows as before fail by their verdicts, and the same row of the other file. The 4:
//! [`a_parameter_standing_twice_is_held_to_one_type`] (each call loads and answers 30),
//! [`the_providers_requirement_is_read_at_the_calls_type`] (refused, naming `P.A`),
//! [`a_provider_at_the_types_themselves_is_the_more_specific`] (refused as a tie) and
//! [`a_callers_own_parameters_are_held_apart`] (loads); each call a failing row makes was
//! run alone both ways, and the calls a row says pass either way do. And one row of another
//! file: `wi_f8pyz_spec_clause_alias_test::an_alias_binding_a_tuple_reads_as_the_tuple_
//! written_directly`, whose first call is the tie again.
//!
//! PASS EITHER WAY BY THEIR VERDICTS, by design:
//! [`a_parameter_standing_once_or_at_one_type_answers`], and in the rows above the calls at a
//! type only `P` answers (`specific_arrow_other`, `specific_tuple_other`) and inside
//! `same[T](f: (T) -> T)`.
//!
//! NOT COVERED HERE, and why:
//! * THE PARAMETER INSIDE AN APPLIED SORT'S ARROW (`provides Apply[F = Box[T = (A) -> A]]`)
//!   is read the same, and no row tells: a value of a sort is dispatched when the call runs
//!   where no provision was matched, and the sole provider answers a `Box` at any argument.
//! * A LAMBDA WRITTEN WITHOUT ITS PARAMETER'S TYPE (`Apply.run(lambda x -> x)`) is answered by
//!   `P` as it was: a part nothing has determined binds nothing.
//! * A PROVIDER'S `requires`, OR A PROVISION'S `:-` CONDITION, WRITTEN AT a tuple or an arrow
//!   of the parameter (`requires Mark[T = (A, Int64)]`) is read at the call's type since
//!   WI-20261013-34822, and its rows are that ticket's file.
//! * A SORT PROVIDING A SPEC AT A COMPOSITE OF ITS PARAMETER AND SUPPLYING NO MEMBER (`sort Hi
//!   { sort T = ?  provides Lo[T = (T, Int64)] }`) is a witness provision that backs nothing,
//!   refused at load since WI-20260909-M8QWJ (its shape (e); it used to load and die when the
//!   call ran) — at a tuple, an arrow and an applied sort alike, so it is not this
//!   parameter's spelling. `wi_m8qwj_unrunnable_operation_test` has the applied-sort row.
//! * A ROW PARAMETER at an arrow's effect row (`(A) -> A @ {E}`) is bound to the call's row,
//!   the two rows being one (WI-20261014-5JYH9, whose file has the rows).

use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::Value;

/// The refusal of a call at an arrow or a tuple no provision answers.
const NO_PROVISION: &[&str] = &["a tuple or an arrow, and no provision of", "answers at it"];

/// The spec `Apply`, whose one parameter `F` is the type its operation receives, `Show` with
/// one provider, at `Int64` (7), and `Buf[T, N]`, `N` the value-in-type argument. `body`
/// follows.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Apply
    sort F = ?
    operation run(f: F) -> Int64
  end

  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end

  sort ShowInt
    provides Show[T = Int64]
    operation show(x: Int64) -> Int64 = 7
  end
{body}
end
"#
    )
}

/// `P`, over its own parameters `A` and `B`, providing `Apply` at `at`; `run` answers 30.
fn generic(at: &str) -> String {
    format!(
        "\n  sort P\n    sort A = ?\n    sort B = ?\n    provides Apply[F = {at}]\n    \
         operation run(f: {at}) -> Int64 = 30\n  end\n"
    )
}

/// `operation via(f: {at}) -> Int64 = Apply.run(f)`.
fn via(at: &str) -> String {
    format!("\n  operation via(f: {at}) -> Int64 = Apply.run(f)\n")
}

fn with_go(ns: &str, body: &str, go: &str) -> String {
    program(ns, &format!("{body}\n  operation go() -> Int64 = {go}"))
}

fn answers(ns: &str, body: &str, go: &str) -> i64 {
    let src = with_go(ns, body, go);
    let mut interp = interp_for(&src);
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` must run to an Int64: {other:?}\n{src}"),
    }
}

fn refusal(ns: &str, body: &str, go: &str) -> Vec<String> {
    load_errors_of(&with_go(ns, body, go))
}

/// ONE PARAMETER IS ONE TYPE: a call that would need it at two is not answered. A sole
/// parameter and the result, two parameters of a list, two components of a tuple, the
/// parameter one bracket down, and under a type holding a value, which rides an occurrence.
/// Each loaded and answered 30.
#[test]
fn a_parameter_standing_twice_is_held_to_one_type() {
    let rows = [
        ("arrow", "(A) -> A", "(Int64) -> String", "lambda (x: Int64) -> \"s\""),
        (
            "list",
            "(A, A) -> Int64",
            "(Int64, String) -> Int64",
            "lambda (x: Int64, y: String) -> x",
        ),
        ("tuple", "(a: A, b: A)", "(a: Int64, b: String)", "(a: 1, b: \"s\")"),
        (
            "nested",
            "(List[T = A]) -> A",
            "(List[T = Int64]) -> String",
            "lambda (xs: List[T = Int64]) -> \"s\"",
        ),
        (
            "held_value",
            "(Buf[T = A, N = 3]) -> A",
            "(Buf[T = Int64, N = 3]) -> String",
            "lambda (b: Buf[T = Int64, N = 3]) -> \"s\"",
        ),
    ];
    for (name, provided, called, value) in rows {
        let body = format!("{}{}", generic(provided), via(called));
        assert_refused_naming(
            &refusal(&format!("ownparam.twice_{name}"), &body, &format!("via({value})")),
            NO_PROVISION,
            &format!("a provider at `{provided}` beside a call at `{called}`"),
        );
    }
}

/// … AND AT ONE TYPE, OR STANDING ONCE, THE PROVIDER ANSWERS, as it did. Passes with the
/// change backed out, by design.
#[test]
fn a_parameter_standing_once_or_at_one_type_answers() {
    let rows = [
        ("arrow", "(A) -> A", "(Int64) -> Int64", "lambda (x: Int64) -> x"),
        ("two", "(A) -> B", "(Int64) -> String", "lambda (x: Int64) -> \"s\""),
        (
            "list",
            "(A, A) -> Int64",
            "(String, String) -> Int64",
            "lambda (x: String, y: String) -> 1",
        ),
        ("tuple", "(a: A, b: A)", "(a: Int64, b: Int64)", "(a: 1, b: 2)"),
        (
            "nested",
            "(List[T = A]) -> A",
            "(List[T = Int64]) -> Int64",
            "lambda (xs: List[T = Int64]) -> 1",
        ),
        (
            "held_value",
            "(Buf[T = A, N = 3]) -> A",
            "(Buf[T = Int64, N = 3]) -> Int64",
            "lambda (b: Buf[T = Int64, N = 3]) -> 1",
        ),
    ];
    for (name, provided, called, value) in rows {
        let body = format!("{}{}", generic(provided), via(called));
        assert_eq!(
            answers(&format!("ownparam.once_{name}"), &body, &format!("via({value})")),
            30,
            "a provider at `{provided}` answers a call at `{called}`"
        );
    }
}

/// THE PROVIDER'S REQUIREMENT OVER THE PARAMETER IS READ AT THE TYPE THE CALL BINDS IT TO.
/// `P requires Show[T = A]` and provides `Apply` at `() -> A`; its `run` shows what the
/// callback returns. At `() -> Int64` the requirement is `Show[T = Int64]`, which `ShowInt`
/// supplies (7); at `() -> String` it is `Show[T = String]`, which nothing does, and the
/// refusal names it. Both were refused naming `Show[T = P.A]`.
#[test]
fn the_providers_requirement_is_read_at_the_calls_type() {
    let p = "\n  sort P\n    sort A = ?\n    requires Show[T = A]\n    \
             provides Apply[F = () -> A]\n    \
             operation run(f: () -> A) -> Int64 = Show.show(f())\n  end\n";
    let at_int = format!("{p}{}", via("() -> Int64"));
    assert_eq!(answers("ownparam.requires_int", &at_int, "via(lambda () -> 5)"), 7);
    let at_string = format!("{p}{}", via("() -> String"));
    let errs = refusal("ownparam.requires_string", &at_string, "via(lambda () -> \"s\")");
    assert_refused_naming(
        &errs,
        &["no impl matches", "ownparam.requires_string.Show[T = anthill.prelude.String]"],
        "`P` at `() -> String`, with no provider of `Show` at `String`",
    );
}

/// A PROVIDER AT THE TYPES THEMSELVES IS THE MORE SPECIFIC ONE, as it is where the two
/// provisions are at an applied sort: `P` at `(A, A) -> A` (30) beside `Q` at `(Int64, Int64)
/// -> Int64` (40). A call at `Int64` was refused as a tie between them; a call at `String`,
/// which `Q` does not answer, is `P`'s as it was.
#[test]
fn a_provider_at_the_types_themselves_is_the_more_specific() {
    let both = |p_at: &str, q_at: &str| {
        format!(
            "{}\n  sort Q\n    provides Apply[F = {q_at}]\n    \
             operation run(f: {q_at}) -> Int64 = 40\n  end\n",
            generic(p_at)
        )
    };
    let arrows = both("(A, A) -> A", "(Int64, Int64) -> Int64");
    assert_eq!(
        answers(
            "ownparam.specific_arrow",
            &format!("{arrows}{}", via("(Int64, Int64) -> Int64")),
            "via(lambda (x: Int64, y: Int64) -> x)"
        ),
        40
    );
    assert_eq!(
        answers(
            "ownparam.specific_arrow_other",
            &format!("{arrows}{}", via("(String, String) -> String")),
            "via(lambda (x: String, y: String) -> x)"
        ),
        30
    );
    let tuples = both("(A, Int64)", "(String, Int64)");
    assert_eq!(
        answers(
            "ownparam.specific_tuple",
            &format!("{tuples}{}", via("(String, Int64)")),
            "via((\"s\", 5))"
        ),
        40
    );
    assert_eq!(
        answers(
            "ownparam.specific_tuple_other",
            &format!("{tuples}{}", via("(Bool, Int64)")),
            "via((true, 5))"
        ),
        30
    );
}

/// A CALLER'S OWN TYPE PARAMETERS ARE HELD APART TOO: inside `via[T, U](f: (T) -> U)` the two
/// are two types whatever a caller of `via` binds them to, and `P` at `(A) -> A` does not
/// answer; inside `same[T](f: (T) -> T)` it does, at every `T`. The first loaded.
#[test]
fn a_callers_own_parameters_are_held_apart() {
    let p = generic("(A) -> A");
    let apart = format!("{p}\n  operation via[T, U](f: (T) -> U) -> Int64 = Apply.run(f)\n");
    assert_refused_naming(
        &refusal("ownparam.apart", &apart, "via[T = Int64, U = Int64](lambda (x: Int64) -> x)"),
        NO_PROVISION,
        "`Apply.run(f)` over `f: (T) -> U` beside a provider at `(A) -> A`",
    );
    let same = format!("{p}\n  operation same[T](f: (T) -> T) -> Int64 = Apply.run(f)\n");
    assert_eq!(
        answers("ownparam.same", &same, "same[T = Int64](lambda (x: Int64) -> x)"),
        30
    );
}
