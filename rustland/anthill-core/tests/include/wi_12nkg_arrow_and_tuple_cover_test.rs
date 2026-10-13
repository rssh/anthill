//! WI-20260929-12NKG — a requirement at an arrow or a tuple covers a call at THAT arrow or
//! tuple, and at no other.
//!
//! `sort User { requires Apply[F = (Int64) -> Buf[T = Int64, N = 3]]  operation via(f: (Int64)
//! -> Buf[T = Int64, N = 4]) -> Int64 = Apply.run(f) }`: the body call is at `N = 4`, the
//! requirement at `N = 3`, and they are two requirements (kernel-language §5.2 — a
//! requirement is the sort it names at the bindings written for it). The call ran the
//! requirement's provider (30) where, without the `requires`, it reaches the provider at its
//! own type (40).
//!
//! THE MECHANISM. Where a requirement is held against a call — the defer-match and its σ
//! verdict, a caller's dictionary forwarded to a callee's slot, an operation's own `requires`
//! licensing a body call — two types that `types_compatible` refused were compared by HEAD
//! (`dispatch_values_match`'s coarse fallback). WI-825 took two applications of one sort out
//! of that for the σ verdict; an arrow and a tuple stayed, and every arrow has the one head
//! `Arrow`, every tuple the one head `NamedTuple`. So ANY arrow covered any arrow and any
//! tuple any tuple — another result, another parameter, another parameter count, another
//! label, another width — at the top of a binding and one bracket down. Both are now compared
//! part by part (`parts_verdict`), in the σ mode and in the coarse one.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: the call runs, and each provider answers its own number,
//! so the answer names the provider reached. The two rows about an open part handed across a
//! call assert a refusal, by the words a back-out removes, and run the repairs it advises.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! FOUR PARTS, each backed out in place and RUN over this file's 20 rows:
//!
//! 1. THE σ VERDICT's two arms (`parts_verdict` answering `None` for two arrows and for two
//!    tuples where a σ context is passed, so they reach the head again). 9 FAIL:
//!    [`the_ticket_program_reaches_the_provider_at_the_calls_own_arrow`],
//!    [`a_requirement_at_another_arrow_is_no_cover`],
//!    [`a_requirement_at_another_tuple_is_no_cover`],
//!    [`an_arrow_or_a_tuple_inside_an_application_is_compared_too`],
//!    [`the_call_is_no_cover_wherever_it_is_written`],
//!    [`a_callers_requirement_at_another_arrow_is_not_forwarded`], and three that load
//!    where a refusal is owed: [`an_open_part_is_not_forwarded_across_a_call`],
//!    [`a_requirement_of_another_shape_is_not_named_as_a_near_miss`] and
//!    [`a_call_a_requirement_at_another_arrow_does_not_cover_is_refused_with_no_provider`].
//! 2. THE COARSE VERDICT (`coarse_pair_verdict` answering by `dispatch_values_match` either
//!    way, as it did). 1 FAILS: [`a_requirement_of_another_shape_is_not_named_as_a_near_miss`]
//!    — the refusal's account is the one reader that takes the coarse verdict alone.
//! 3. THE OPEN PART (`part_verdict` holding a part nothing has determined to
//!    `sigma_pair_verdict`). 1 FAILS: [`a_lambda_without_its_parameters_type_reads_the_requirement`]
//!    (refused by part 4; with that backed out too, it loads and dies when it runs).
//! 4. THE REFUSAL of a call at an arrow or a tuple no provision answers
//!    (`unprovided_spec_at_former` not asked). 5 FAIL, each loading clean:
//!    [`a_call_at_an_arrow_or_a_tuple_nothing_provides_is_refused`],
//!    [`a_call_a_requirement_at_another_arrow_does_not_cover_is_refused_with_no_provider`],
//!    [`a_lambda_without_its_parameters_type_and_no_requirement_is_refused`],
//!    [`a_call_at_an_arrow_over_a_type_parameter_is_refused_naming_the_requires`] and
//!    [`a_parameter_received_operation_of_a_self_receiving_spec_is_refused_too`] — the last
//!    also with the refusal skipping a self-representing spec, as the sort-carrier one does.
//!
//! HELD BY EITHER OF 1 AND 2 — they fail only with BOTH backed out, 12 in all:
//! [`two_requirements_at_two_arrows_are_each_read_by_their_own_call`],
//! [`an_operations_own_requirement_at_another_arrow_is_no_cover`] and
//! [`a_requirement_reached_through_a_required_sort_is_no_cover`]. There the defer-match is the
//! whole decision, and it asks the coarse filter and then the σ verdict. The nine of part 1
//! reach the requirement a second time, through the resolution's own scope step, which asks
//! the σ verdict only.
//!
//! PASS UNDER EVERY BACK-OUT, by design: [`a_requirement_at_the_calls_own_type_still_covers`]
//! and [`a_callers_requirement_at_the_same_arrow_is_forwarded`] — a head covers whatever
//! stands beneath it, and the rows say the parts are compared as the language relates them —
//! and [`a_call_its_operations_own_requirement_covers_is_not_refused`], which is deferred
//! before the refusal's arm is reached.
//!
//! NOT COVERED HERE, and why:
//! * AN ARROW'S EFFECT ROW is not told from another: `(Int64) -> Int64 @ {Error[String]}` and
//!   `(Int64) -> Int64` are one requirement to the cover, and one provision to direct dispatch
//!   too (a call with a provider at each is refused as ambiguous). Two rows are compared by
//!   subsumption either way and then by head, here as everywhere.
//! * A PART LEFT OPEN ON THE REQUIREMENT'S SIDE — a parameter of a required sort that the
//!   `requires` does not bind — is read by the same rule as the lambda's and is not driven: a
//!   bare `requires Mid` over a `Mid` with a parameter is refused where its dictionary is
//!   supplied, before the body call is reached.
//! * THE REFUSAL'S EXEMPTION for a call the enclosing operation's own `requires` licenses
//!   (the one the sort-carrier refusal beside it has) is not driven for an arrow or a tuple:
//!   such a call is deferred to that requirement before a provider is looked for, and asked
//!   ahead of the licence the refusal moves no row here.

use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::Value;

/// `Buf[T, N]` — `N` the value-in-type argument — `Box[T]`, whose value does not hold its
/// `T`, and the spec `Apply`, whose one parameter `F` is the type its operation receives.
/// `body` follows.
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

  sort Box
    sort T = ?
    entity box(n: Int64)
  end

  sort Apply
    sort F = ?
    operation run(f: F) -> Int64
  end
{body}
end
"#
    )
}

/// A sort `name` providing `Apply` at `at`; its `run` answers `answer`, which names it.
fn provider(name: &str, at: &str, answer: i64) -> String {
    format!(
        "\n  sort {name}\n    provides Apply[F = {at}]\n    \
         operation run(f: {at}) -> Int64 = {answer}\n  end\n"
    )
}

/// `User requires Apply[F = {req}]`, with `{decl}` before it; its `via(f: {arg})` is `{body}`.
fn user(decl: &str, req: &str, arg: &str, body: &str) -> String {
    format!(
        "\n  sort User\n    {decl}\n    requires Apply[F = {req}]\n    \
         operation via(f: {arg}) -> Int64 = {body}\n  end\n"
    )
}

/// `program(ns, body)` with `go() = {go}` appended, loaded, and `go` run.
fn answers(ns: &str, body: &str, go: &str) -> i64 {
    let src = program(ns, &format!("{body}\n  operation go() -> Int64 = {go}"));
    let mut interp = interp_for(&src);
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` must run to an Int64: {other:?}\n{src}"),
    }
}

/// THE SHAPE OF THE TICKET'S PROGRAM: `AtReq` provides `Apply` at `req` (30) and `AtCall` at
/// `call` (40); `User` requires it at `req` and calls it on an `f: {call}`; `Free` makes the
/// same call with no requirement. Both must reach `AtCall` — the requirement at `req` is no
/// cover for a call at `call`, so the call is the one `Free` makes.
fn assert_no_cover(ns: &str, req: &str, call: &str, value: &str) {
    let body = format!(
        "{}{}{}\n  sort Free\n    operation via(f: {call}) -> Int64 = Apply.run(f)\n  end\n",
        provider("AtReq", req, 30),
        provider("AtCall", call, 40),
        user("", req, call, "Apply.run(f)"),
    );
    assert_eq!(
        answers(&format!("{ns}.free"), &body, &format!("Free.via({value})")),
        40,
        "the call at `{call}` with no requirement reaches the provider at its own type"
    );
    assert_eq!(
        answers(&format!("{ns}.req"), &body, &format!("User.via({value})")),
        40,
        "`requires Apply[F = {req}]` is no cover for a call at `{call}`"
    );
}

// ── the ticket's program ──────────────────────────────────────────────────────────────

/// THE TICKET'S PROGRAM, in both spellings: the two arrows differ in a VALUE held by the
/// result's type (`N = 3` / `N = 4`), and in a TYPE there (`N = String` / `N = Bool`). Ran the
/// requirement's provider (30) on a callback of the other type.
#[test]
fn the_ticket_program_reaches_the_provider_at_the_calls_own_arrow() {
    let value = "lambda (x: Int64) -> buf(v: x)";
    assert_no_cover(
        "wi12nkg.ticket_value",
        "(Int64) -> Buf[T = Int64, N = 3]",
        "(Int64) -> Buf[T = Int64, N = 4]",
        value,
    );
    assert_no_cover(
        "wi12nkg.ticket_typed",
        "(Int64) -> Buf[T = Int64, N = String]",
        "(Int64) -> Buf[T = Int64, N = Bool]",
        value,
    );
}

// ── two arrows, two tuples ────────────────────────────────────────────────────────────

/// ANY PART OF AN ARROW tells it from another: the result, the parameter, one parameter of a
/// list, the parameter count, and the result of the arrow it returns. Each ran 30.
#[test]
fn a_requirement_at_another_arrow_is_no_cover() {
    let rows = [
        ("result", "(Int64) -> Int64", "(Int64) -> String", "lambda (x: Int64) -> \"s\""),
        ("param", "(Int64) -> Int64", "(String) -> Int64", "lambda (x: String) -> 1"),
        (
            "one_of_two",
            "(Int64, Int64) -> Int64",
            "(Int64, String) -> Int64",
            "lambda (x: Int64, y: String) -> 1",
        ),
        (
            "count",
            "(Int64) -> Int64",
            "(Int64, Int64) -> Int64",
            "lambda (x: Int64, y: Int64) -> 1",
        ),
        ("nullary", "() -> Int64", "() -> String", "lambda () -> \"s\""),
        (
            "returned_arrow",
            "(Int64) -> (Int64) -> Int64",
            "(Int64) -> (String) -> Int64",
            "lambda (x: Int64) -> lambda (y: String) -> 1",
        ),
    ];
    for (name, req, call, value) in rows {
        assert_no_cover(&format!("wi12nkg.arrow_{name}"), req, call, value);
    }
}

/// … and any part of a TUPLE: a component's type, positional or named, a label, the width,
/// and a value held by a component's type. Each ran 30. `named_width` is the pair the
/// subtype relation does relate — a tuple with a component more conforms to the narrower one
/// — and it is two types all the same: a provider at the narrower is not the wider's either,
/// with or without a `requires`.
#[test]
fn a_requirement_at_another_tuple_is_no_cover() {
    let rows = [
        ("positional", "(Int64, String)", "(Int64, Bool)", "(1, true)"),
        ("named", "(a: Int64, b: String)", "(a: Int64, b: Bool)", "(a: 1, b: true)"),
        ("label", "(a: Int64, b: Int64)", "(a: Int64, c: Int64)", "(a: 1, c: 2)"),
        ("width", "(Int64, Int64)", "(Int64, Int64, Int64)", "(1, 2, 3)"),
        ("named_width", "(a: Int64)", "(a: Int64, b: String)", "(a: 1, b: \"s\")"),
        (
            "held_value",
            "(Buf[T = Int64, N = 3], Int64)",
            "(Buf[T = Int64, N = 4], Int64)",
            "(buf(v: 1), 2)",
        ),
    ];
    for (name, req, call, value) in rows {
        assert_no_cover(&format!("wi12nkg.tuple_{name}"), req, call, value);
    }
}

/// ONE BRACKET DOWN — the arrow or the tuple an argument of an applied sort, where WI-825's
/// walk met it as a leaf and compared its head. Each ran 30.
#[test]
fn an_arrow_or_a_tuple_inside_an_application_is_compared_too() {
    let rows = [
        ("arrow", "Box[T = (Int64) -> Int64]", "Box[T = (Int64) -> String]", "box(n: 1)"),
        ("tuple", "Box[T = (Int64, String)]", "Box[T = (Int64, Bool)]", "box(n: 1)"),
        (
            "held_value",
            "Box[T = (Int64) -> Buf[T = Int64, N = 3]]",
            "Box[T = (Int64) -> Buf[T = Int64, N = 4]]",
            "box(n: 1)",
        ),
        ("list", "List[T = (Int64) -> Int64]", "List[T = (Int64) -> String]", "List.nil()"),
    ];
    for (name, req, call, value) in rows {
        assert_no_cover(&format!("wi12nkg.inside_{name}"), req, call, value);
    }
}

// ── the other places a requirement is held against a call ─────────────────────────────

const X: &str = "(Int64) -> Int64";
const Y: &str = "(String) -> Int64";
const AT_Y: &str = "lambda (x: String) -> 1";

/// Providers at `X` (30) and at `Y` (40).
fn at_x_and_y() -> String {
    format!("{}{}", provider("AtX", X, 30), provider("AtY", Y, 40))
}

/// TWO REQUIREMENTS OF ONE SPEC AT TWO ARROWS, and each call reads its own (§5.2's `OK` and
/// `OV`). Both calls read the first requirement's dictionary: 3030.
#[test]
fn two_requirements_at_two_arrows_are_each_read_by_their_own_call() {
    let body = format!(
        "{}\n  sort User\n    requires A1: Apply[F = {X}]\n    requires A2: Apply[F = {Y}]\n    \
         operation both(f: {X}, g: {Y}) -> Int64 = Apply.run(f) * 100 + Apply.run(g)\n  end\n",
        at_x_and_y()
    );
    assert_eq!(
        answers(
            "wi12nkg.two_requirements",
            &body,
            &format!("User.both(lambda (x: Int64) -> 1, {AT_Y})")
        ),
        3040
    );
}

/// ACROSS A CALL: `Caller` holds the requirement at `X`, `Callee` requires it at `Y`, and the
/// caller's dictionary is not the callee's. It was forwarded (30).
#[test]
fn a_callers_requirement_at_another_arrow_is_not_forwarded() {
    let body = format!(
        "{}\n  sort Callee\n    requires Apply[F = {Y}]\n    \
         operation inner(f: {Y}) -> Int64 = Apply.run(f)\n  end\n  \
         sort Caller\n    requires Apply[F = {X}]\n    \
         operation call(f: {Y}) -> Int64 = Callee.inner(f)\n  end\n",
        at_x_and_y()
    );
    assert_eq!(answers("wi12nkg.forward", &body, &format!("Caller.call({AT_Y})")), 40);
}

/// … and the caller's dictionary at the SAME arrow still is: two providers at `Y` (`AtY` 40,
/// `AtY2` 45), the bracket on `Caller.call` picks its requirement's supplier, and only that
/// dictionary handed on to `Callee` answers 45. Passes with the change backed out, by design.
#[test]
fn a_callers_requirement_at_the_same_arrow_is_forwarded() {
    let body = format!(
        "{}{}\n  sort Callee\n    requires Apply[F = {Y}]\n    \
         operation inner(f: {Y}) -> Int64 = Apply.run(f)\n  end\n  \
         sort Caller\n    requires Apply[F = {Y}]\n    \
         operation call(f: {Y}) -> Int64 = Callee.inner(f)\n  end\n",
        provider("AtY", Y, 40),
        provider("AtY2", Y, 45)
    );
    assert_eq!(
        answers(
            "wi12nkg.forward_same",
            &body,
            &format!("Caller.call[Apply = AtY2]({AT_Y})")
        ),
        45
    );
}

/// AN OPERATION'S OWN `requires` at another arrow licenses nothing. Ran 30.
#[test]
fn an_operations_own_requirement_at_another_arrow_is_no_cover() {
    let body = format!(
        "{}\n  operation via(f: {Y}) -> Int64 requires Apply[F = {X}] = Apply.run(f)\n",
        at_x_and_y()
    );
    assert_eq!(answers("wi12nkg.op_scoped", &body, &format!("via({AT_Y})")), 40);
}

/// A REQUIREMENT REACHED THROUGH A REQUIRED SORT (`User requires Mid`, `Mid requires Apply[F =
/// X]`): the call at `Y` was deferred into `Mid`'s dictionary and died when it ran.
#[test]
fn a_requirement_reached_through_a_required_sort_is_no_cover() {
    let body = format!(
        "{}\n  sort Mid\n    requires Apply[F = {X}]\n    operation mid() -> Int64 = 1\n  end\n  \
         sort MidImpl\n    provides Mid\n    operation mid() -> Int64 = 2\n  end\n  \
         sort User\n    requires Mid\n    operation via(f: {Y}) -> Int64 = Apply.run(f)\n  end\n",
        at_x_and_y()
    );
    assert_eq!(answers("wi12nkg.through_a_sort", &body, &format!("User.via({AT_Y})")), 40);
}

/// WHEREVER THE CALL IS WRITTEN in the body, and however the two types are named: a
/// condition, a `let`, a lambda's body, the operation imported, the requirement named, the two
/// arrows behind aliases. Each ran 30.
#[test]
fn the_call_is_no_cover_wherever_it_is_written() {
    let bodies = [
        ("condition", "if Apply.run(f) > 35 then 40 else 30".to_string()),
        ("let", "let g = f  Apply.run(g)".to_string()),
        ("lambda", format!("let h = lambda (g: {Y}) -> Apply.run(g)  h(f)")),
    ];
    for (name, body) in bodies {
        let src = format!("{}{}", at_x_and_y(), user("", X, Y, &body));
        assert_eq!(
            answers(&format!("wi12nkg.site_{name}"), &src, &format!("User.via({AT_Y})")),
            40,
            "the call written in a {name}"
        );
    }
    let imported = format!(
        "{}\n  sort User\n    import wi12nkg.site_import.Apply.run\n    \
         requires Apply[F = {X}]\n    operation via(f: {Y}) -> Int64 = run(f)\n  end\n",
        at_x_and_y()
    );
    assert_eq!(answers("wi12nkg.site_import", &imported, &format!("User.via({AT_Y})")), 40);
    let named = format!(
        "{}\n  sort User\n    requires A: Apply[F = {X}]\n    \
         operation via(f: {Y}) -> Int64 = Apply.run(f)\n  end\n",
        at_x_and_y()
    );
    assert_eq!(answers("wi12nkg.site_named", &named, &format!("User.via({AT_Y})")), 40);
    let aliased = format!(
        "{}\n  sort FnX = {X}\n  sort FnY = {Y}\n{}",
        at_x_and_y(),
        user("", "FnX", "FnY", "Apply.run(f)")
    );
    assert_eq!(answers("wi12nkg.site_alias", &aliased, &format!("User.via({AT_Y})")), 40);
}

// ── the controls: a requirement at the call's own type ────────────────────────────────

/// A REQUIREMENT AT THE CALL'S OWN TYPE STILL COVERS IT, and the call runs THROUGH it: two
/// providers at one type (`P1` 31, `P2` 32), so the body's `Apply.run` could not dispatch on
/// its own — the bracket on `User.via` picks the requirement's supplier, and only a deferral
/// to that requirement answers 32.
///
/// PASS WITH THE CHANGE BACKED OUT, by design — a head covers whatever stands beneath it. They
/// say the parts are compared as the language relates them: a type parameter of the sort is
/// one type on both sides, an arrow's parameters are a list read by position (so a requirement
/// written without labels covers a call whose arrow has them), and a tuple's labels are its
/// identity.
#[test]
fn a_requirement_at_the_calls_own_type_still_covers() {
    // (name, the providers' type, the sort's own declaration, the requirement's, the
    // parameter's, the call's brackets, the argument)
    let rows = [
        ("arrow", X, "", X, X, "", "lambda (x: Int64) -> x"),
        (
            "held_value",
            "(Int64) -> Buf[T = Int64, N = 4]",
            "",
            "(Int64) -> Buf[T = Int64, N = 4]",
            "(Int64) -> Buf[T = Int64, N = 4]",
            "",
            "lambda (x: Int64) -> buf(v: x)",
        ),
        ("param", X, "sort T = ?", "(T) -> Int64", "(T) -> Int64", "T = Int64, ", "lambda (x: Int64) -> x"),
        (
            "param_twice",
            "(Int64, Int64) -> Int64",
            "sort T = ?",
            "(T, T) -> T",
            "(T, T) -> T",
            "T = Int64, ",
            "lambda (x: Int64, y: Int64) -> x",
        ),
        (
            "labels",
            "(Int64, Int64) -> Int64",
            "",
            "(Int64, Int64) -> Int64",
            "(p: Int64, q: Int64) -> Int64",
            "",
            "lambda (x: Int64, y: Int64) -> x",
        ),
        ("tuple", "(Int64, String)", "", "(Int64, String)", "(Int64, String)", "", "(1, \"a\")"),
        (
            "tuple_param",
            "(Int64, String)",
            "sort T = ?",
            "(T, String)",
            "(T, String)",
            "T = Int64, ",
            "(1, \"a\")",
        ),
        (
            "tuple_named",
            "(a: Int64, b: String)",
            "",
            "(a: Int64, b: String)",
            "(a: Int64, b: String)",
            "",
            "(a: 1, b: \"a\")",
        ),
        (
            "inside",
            "List[T = (Int64) -> Int64]",
            "sort T = ?",
            "List[T = (T) -> Int64]",
            "List[T = (T) -> Int64]",
            "T = Int64, ",
            "List.nil()",
        ),
        (
            "arrow_of_arrow",
            "((Int64) -> Int64) -> Int64",
            "sort T = ?",
            "((T) -> Int64) -> T",
            "((T) -> Int64) -> T",
            "T = Int64, ",
            "lambda (g: (Int64) -> Int64) -> g(1)",
        ),
    ];
    for (name, at, decl, req, arg, brackets, value) in rows {
        let body = format!(
            "{}{}{}",
            provider("P1", at, 31),
            provider("P2", at, 32),
            user(decl, req, arg, "Apply.run(f)")
        );
        assert_eq!(
            answers(
                &format!("wi12nkg.covers_{name}"),
                &body,
                &format!("User.via[{brackets}Apply = P2]({value})")
            ),
            32,
            "`requires Apply[F = {req}]` covers the call at `{arg}`"
        );
    }
}

// ── a part nothing has determined ─────────────────────────────────────────────────────

/// A LAMBDA WRITTEN WITHOUT ITS PARAMETER'S TYPE is at `(?x) -> Int64`, and the part nothing
/// has determined says nothing: the call reads the requirement at `(Int64) -> Int64`, as it
/// did. Held to "an unsolved parameter is not `Int64`", the call matches no provider and no
/// requirement, and a program that ran is refused.
///
/// The second call is the one only the requirement can answer: two providers at one arrow,
/// and the bracket picks the supplier.
#[test]
fn a_lambda_without_its_parameters_type_reads_the_requirement() {
    let body = format!(
        "{}{}\n  sort User\n    requires Apply[F = {X}]\n    \
         operation use() -> Int64 = Apply.run(lambda x -> x + 1)\n  end\n",
        provider("AtX", X, 30),
        provider("AtBool", "(Bool) -> Int64", 40)
    );
    assert_eq!(answers("wi12nkg.open_part", &body, "User.use()"), 30);
    let two = format!(
        "{}{}\n  sort User\n    requires Apply[F = {X}]\n    \
         operation use() -> Int64 = Apply.run(lambda x -> x + 1)\n  end\n",
        provider("P1", X, 31),
        provider("P2", X, 32)
    );
    assert_eq!(answers("wi12nkg.open_part_selected", &two, "User.use[Apply = P2]()"), 32);
}

/// `Callee` requires `Apply` at `(T) -> Int64` over its own `T`; `Caller` holds it at `held`
/// and calls `Callee.inner` as `{call}`.
fn open_callee(held: &str, call: &str) -> String {
    format!(
        "{}{}\n  sort Callee\n    sort T = ?\n    requires Apply[F = (T) -> Int64]\n    \
         operation inner(f: (T) -> Int64) -> Int64 = Apply.run(f)\n  end\n  \
         sort Caller\n    requires Apply[F = {held}]\n    \
         operation call() -> Int64 = {call}\n  end\n",
        provider("AtX", X, 30),
        provider("AtTwo", "(Int64, Int64) -> Int64", 40)
    )
}

/// ACROSS A CALL THE OPEN PART IS NOT GUESSED: `Callee.inner(lambda x -> 1)` leaves the
/// callee's `T` to nothing, its requirement is at `(?x) -> Int64`, and a caller's dictionary
/// is handed on only where the two are the same type with nothing left unsaid — the rule every
/// other element is held to. The caller's requirement at `(Int64) -> Int64` could be the one,
/// and the refusal names it and says how to pin the element; both repairs it advises run. It
/// was forwarded by its head (30).
#[test]
fn an_open_part_is_not_forwarded_across_a_call() {
    let unpinned = program(
        "wi12nkg.open_forward",
        &format!(
            "{}\n  operation go() -> Int64 = Caller.call()",
            open_callee(X, "Callee.inner(lambda x -> 1)")
        ),
    );
    assert_refused_naming(
        &load_errors_of(&unpinned),
        &[
            "cannot be supplied",
            "covers only as a wildcard and is not forwarded",
            "pin the element at the call site",
        ],
        "a callee's requirement at `(?x) -> Int64` under a caller holding `(Int64) -> Int64`",
    );
    for (name, call) in [
        ("lambda", "Callee.inner(lambda (x: Int64) -> 1)"),
        ("bracket", "Callee.inner[T = Int64](lambda x -> 1)"),
    ] {
        assert_eq!(
            answers(&format!("wi12nkg.open_forward_{name}"), &open_callee(X, call), "Caller.call()"),
            30,
            "the element pinned by the {name}"
        );
    }
}

/// … and a requirement that could NOT be the one is not named as a near miss. The caller
/// holds `Apply` at an arrow of TWO parameters; the callee's is at an arrow of one. The call
/// was forwarded that dictionary and ran its provider (40). Refused, the message used to add
/// "`requires Apply[F = (Int64, Int64) -> Int64]` covers only as a wildcard — its element is a
/// different type parameter", which is the COARSE cover's verdict read alone, and false: no
/// parameter makes a two-parameter arrow a one-parameter one.
#[test]
fn a_requirement_of_another_shape_is_not_named_as_a_near_miss() {
    let src = program(
        "wi12nkg.open_other_shape",
        &format!(
            "{}\n  operation go() -> Int64 = Caller.call()",
            open_callee("(Int64, Int64) -> Int64", "Callee.inner(lambda x -> 1)")
        ),
    );
    let errs = load_errors_of(&src);
    assert_refused_naming(
        &errs,
        &["cannot be supplied", "wi12nkg.open_other_shape.Apply[F = "],
        "a callee's requirement at a one-parameter arrow under a caller holding a two-parameter one",
    );
    assert!(
        !errs.iter().any(|e| e.contains("covers only as a wildcard")),
        "a two-parameter arrow is no cover of a one-parameter one, as a wildcard or otherwise; \
         got {errs:#?}"
    );
}

// ── a call no requirement covers and no provider answers ──────────────────────────────

/// The refusal's own words, which a back-out removes.
const NO_PROVISION: &[&str] = &["a tuple or an arrow, and no provision of", "answers at it"];

/// A CALL AT AN ARROW OR A TUPLE NOTHING PROVIDES THE SPEC AT IS REFUSED WHERE IT IS WRITTEN.
/// A value of such a type has no sort whose member could answer when the call runs, so a
/// provision matched where the call is typed is all there is; with none, the call loaded and
/// died `OperationBodyMissing`. The repair the message names — a sort providing the spec at
/// that type — runs.
#[test]
fn a_call_at_an_arrow_or_a_tuple_nothing_provides_is_refused() {
    let rows = [
        ("arrow", X, Y, AT_Y),
        ("tuple", "(Int64, Int64)", "(Int64, String)", "(1, \"s\")"),
    ];
    for (name, provided, at, value) in rows {
        let call = format!("\n  operation use() -> Int64 = Apply.run({value})\n");
        let alone = format!("{}{call}", provider("AtX", provided, 30));
        assert_refused_naming(
            &load_errors_of(&program(&format!("wi12nkg.unprovided_{name}"), &alone)),
            NO_PROVISION,
            &format!("`Apply.run` at `{at}` beside a provider at `{provided}` alone"),
        );
        let repaired = format!("{alone}{}", provider("AtCall", at, 40));
        assert_eq!(
            answers(&format!("wi12nkg.unprovided_{name}_repaired"), &repaired, "use()"),
            40,
            "the same call with a sort providing `Apply` at `{at}`"
        );
    }
}

/// … AND SO IS ONE UNDER A REQUIREMENT AT ANOTHER ARROW, which is the call the rows above moved
/// off that requirement where no provider stands at its own type. It ran the requirement's
/// provider (30) on a callback of another type.
#[test]
fn a_call_a_requirement_at_another_arrow_does_not_cover_is_refused_with_no_provider() {
    let body = format!("{}{}", provider("AtX", X, 30), user("", X, Y, "Apply.run(f)"));
    assert_refused_naming(
        &load_errors_of(&program("wi12nkg.unprovided_under_requirement", &body)),
        NO_PROVISION,
        "a body call at `Y` under `requires Apply[F = X]`, and no provider at `Y`",
    );
}

/// A LAMBDA WRITTEN WITHOUT ITS PARAMETER'S TYPE, AND NO REQUIREMENT TO READ: the call is at
/// `(?x) -> Int64`, a provision is matched at the type as the call states it, and none is. It
/// loaded and died the same way, beside a provider at `(Int64) -> Int64` that answers once
/// the type is written — which is the repair the message names.
#[test]
fn a_lambda_without_its_parameters_type_and_no_requirement_is_refused() {
    let alone = |lambda: &str| {
        format!(
            "{}\n  operation use() -> Int64 = Apply.run({lambda})\n",
            provider("AtX", X, 30)
        )
    };
    assert_refused_naming(
        &load_errors_of(&program("wi12nkg.unprovided_open", &alone("lambda x -> 1"))),
        &[NO_PROVISION[0], "write the type of the lambda's parameter"],
        "`Apply.run(lambda x -> 1)` with no requirement in scope",
    );
    assert_eq!(
        answers("wi12nkg.unprovided_open_written", &alone("lambda (x: Int64) -> 1"), "use()"),
        30
    );
}

/// AN ARROW OVER A TYPE PARAMETER OF THE ENCLOSING SORT, and no `requires`: the provision is
/// each caller's to supply, and the refusal says to declare the requirement — not to write a
/// lambda's parameter, of which there is none. With it declared the call is the sort's own
/// requirement's and runs. It loaded and died as the others did.
#[test]
fn a_call_at_an_arrow_over_a_type_parameter_is_refused_naming_the_requires() {
    let generic = |requires: &str| {
        format!(
            "{}\n  sort User\n    sort T = ?{requires}\n    \
             operation via(f: (T) -> Int64) -> Int64 = Apply.run(f)\n  end\n",
            at_x_and_y()
        )
    };
    let errs = load_errors_of(&program("wi12nkg.unprovided_generic", &generic("")));
    assert_refused_naming(
        &errs,
        &[NO_PROVISION[0], "declare `requires wi12nkg.unprovided_generic.Apply[…]`"],
        "`Apply.run(f)` over `f: (T) -> Int64` in a sort that requires nothing",
    );
    assert!(
        !errs.iter().any(|e| e.contains("lambda's parameter")),
        "no lambda is written here; got {errs:#?}"
    );
    assert_eq!(
        answers(
            "wi12nkg.unprovided_generic_declared",
            &generic("\n    requires Apply[F = (T) -> Int64]"),
            &format!("User.via({AT_Y})")
        ),
        40
    );
}

/// A SPEC THAT RECEIVES ON `Self` IN ONE OPERATION AND ON A PARAMETER IN ANOTHER: the call of
/// the second is at its parameter, and a tuple there that nothing provides the spec at is
/// refused as any other. The rule the sort-carrier refusal has for a self-representing spec —
/// its parameter is an element, not the carrier — kept this one loading with nothing to run.
#[test]
fn a_parameter_received_operation_of_a_self_receiving_spec_is_refused_too() {
    let body = "\n  sort Mixed\n    sort C = ?\n    operation me(s: Self) -> Int64\n    \
                operation at(c: C) -> Int64\n  end\n  \
                operation use() -> Int64 = Mixed.at((1, 2))\n";
    assert_refused_naming(
        &load_errors_of(&program("wi12nkg.unprovided_mixed", body)),
        NO_PROVISION,
        "`Mixed.at((1, 2))` with no provider of `Mixed`",
    );
}

/// A CALL THE OPERATION'S OWN `requires` COVERS IS NOT REFUSED: `via[T]` requires `Apply` at
/// `(T) -> Int64` and calls it at that type, which matches no provider where the body is
/// typed and is supplied by each caller. Passes with the refusal backed out, and with it
/// asked ahead of the licence: the call is deferred to the requirement first.
#[test]
fn a_call_its_operations_own_requirement_covers_is_not_refused() {
    let body = format!(
        "{}\n  operation via[T](f: (T) -> Int64) -> Int64 requires Apply[F = (T) -> Int64] = \
         Apply.run(f)\n",
        at_x_and_y()
    );
    assert_eq!(answers("wi12nkg.licensed", &body, &format!("via[T = String]({AT_Y})")), 40);
    assert_eq!(answers("wi12nkg.licensed_inferred", &body, &format!("via({AT_Y})")), 40);
}
