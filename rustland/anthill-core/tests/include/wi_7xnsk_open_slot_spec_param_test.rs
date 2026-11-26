//! WI-20260929-7XNSK — a parameter of a spec several arguments name takes, in a slot one of
//! them leaves OPEN, what another says; so which provider a call reaches does not depend on
//! the order of its arguments.
//!
//! `peek2(s: State, t: State)` over providers `CA` at `Buf[T = Int64, N = Bool]` (answers
//! `s.v + 10`) and `CB` at `Buf[T = String, N = Bool]` (`s.v + 20`), with `mkb[E](xs: List[T
//! = E]) -> Buf[T = E, N = Bool]` and `y: Buf[T = Int64, N = Bool]`. `mkb([])`'s `T` is the
//! empty literal's element, an open slot admitted at every instance. The call's argument loop
//! bound `State` from the FIRST argument and only checked the second against it, so the goal
//! kept the slot open and every provider matched there. MEASURED on the parent commit:
//! `peek2(mkb([]), y)` was refused as ambiguous between `CA` and `CB` while `peek2(y,
//! mkb([]))` ran `CA` (11); beside `CB` alone the first order RAN `CB` (21), though `y` says
//! `T = Int64`. The value-in-type spelling (`N = 3`), a named or a receiver call, and the bare
//! open spelling (`Buf.empty()`, refused "nothing here fixes `T`") had the same split.
//!
//! An open slot takes the instance it meets — the parameter it is passed to (kernel-language
//! §5.4) — and a spec parameter's instance is what EVERY argument naming it says.
//! `fill_open_spec_params` writes the later arguments' types into the first one's open slots
//! before the loop binds; it widens nothing said, since a spec's parameter is a provision's
//! and is not joined. The same first-decides reading sat in an operation's own `[X]` at an
//! INVARIANT occurrence (`join_repeated_type_params`): occurrences that agree fixed `X` at
//! the first, open slot and all.
//!
//! Every row DRIVES the call: it runs to a value that names the provider reached, or the
//! refusal names the requirement at the instance the later argument says.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! Measured by backing each part out alone and running this file:
//!
//! 1. THE SPEC FILL (the `fill_open_spec_params` call in `check_apply_call`). 9 FAIL:
//!    [`the_ticket_call_reaches_the_provider_the_later_argument_says`] (ambiguous),
//!    [`beside_the_other_provider_alone_the_ticket_call_is_refused`] (runs 21),
//!    [`the_value_in_type_spelling_reaches_the_same_provider`] (ambiguous),
//!    [`the_value_in_type_spelling_beside_the_other_provider_is_refused`] (runs 21),
//!    [`a_named_call_in_either_order_reaches_the_same_provider`],
//!    [`a_receiver_call_reaches_the_same_provider`],
//!    [`the_bare_open_spelling_takes_the_later_argument`] ("nothing here fixes"),
//!    [`a_later_argument_that_disagrees_is_refused_as_a_mismatch`] (ambiguous), and
//!    [`a_spec_operation_with_a_body_runs_at_the_said_instance`].
//! 2. THE INVARIANT FILL (`join_repeated_type_params`'s invariant arm binding the first
//!    agreeing occurrence). 3 FAIL:
//!    [`an_operations_own_parameter_at_an_invariant_occurrence_takes_the_later_argument`]
//!    (ambiguous), [`beside_the_other_provider_the_invariant_route_is_refused`] (runs 21) and
//!    [`a_disagreeing_third_invariant_occurrence_is_refused_in_either_order`] (ambiguous).
//! 3. THE FILLED OCCURRENCE BOUND THOUGH A LATER ONE DISAGREES (`agree || filled`, found by
//!    `/code-review`). 1 FAILS: [`a_disagreeing_third_invariant_occurrence_is_refused_in_either_order`].
//!
//! PASS EITHER WAY, by design: every `…_other_order` control (the said argument first was
//! always read right), [`two_open_arguments_say_nothing`] (nothing to fill from: still
//! ambiguous), and [`a_named_value_keeps_its_own_unknown`] (`let w = mkb([])` closes the
//! slot at the name, §5.4, before any call meets it).

use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::Value;

/// `Buf[T, N]`, the spec `Store2`, `mkb`, the providers `providers`, then `body`; `N` is
/// spelled `n` throughout.
fn program(ns: &str, n: &str, providers: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Bool}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: Int64)
    operation empty() -> Self = buf(v: 1)
  end

  sort Cell
    sort T = ?
    entity cell(c: T)
  end

  sort Store2
    sort State = ?
    operation peek2(s: State, t: State) -> Int64
    operation peek3(s: State, t: State, u: State) -> Int64 = 0
  end

  operation mkb[E](xs: List[T = E]) -> Buf[T = E, N = {n}] = buf(v: 1)
{providers}
{body}
end
"#
    )
}

/// A provider `name` of `Store2` at `Buf[T = t, N = n]`; each operation answers `s.v +
/// offset`, so the answer names the provider that ran.
fn provider(name: &str, t: &str, n: &str, offset: i64) -> String {
    let at = format!("Buf[T = {t}, N = {n}]");
    format!(
        r#"
  sort {name}
    provides Store2[State = {at}]
    operation peek2(s: {at}, t: {at}) -> Int64 = s.v + {offset}
    operation peek3(s: {at}, t: {at}, u: {at}) -> Int64 = s.v + {offset}
  end
"#
    )
}

/// `CA` (`T = Int64`, +10) and `CB` (`T = String`, +20).
fn both(n: &str) -> String {
    format!("{}{}", provider("CA", "Int64", n, 10), provider("CB", "String", n, 20))
}

/// `CB` alone.
fn cb_alone(n: &str) -> String {
    provider("CB", "String", n, 20)
}

/// `use(y: Buf[T = Int64, N = n], z: Buf[T = String, N = n]) = call`, and `go()` calling it.
fn body(n: &str, call: &str) -> String {
    format!(
        "  operation use(y: Buf[T = Int64, N = {n}], z: Buf[T = String, N = {n}]) -> Int64 = {call}\n  \
         operation go() -> Int64 = use(buf(v: 1), buf(v: 1))"
    )
}

/// Load the program and run `ns.go()` to an `Int64`.
fn answers(ns: &str, n: &str, providers: &str, call: &str) -> i64 {
    let mut interp = interp_for(&program(ns, n, providers, &body(n, call)));
    let entry = format!("{ns}.go");
    match interp.call(&entry, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Int(v)) => v,
        other => panic!("`{entry}` must run to an Int64: {other:?}"),
    }
}

/// The load's refusals.
fn refusals(ns: &str, n: &str, providers: &str, call: &str) -> Vec<String> {
    load_errors_of(&program(ns, n, providers, &body(n, call)))
}

// ── the ticket's call ─────────────────────────────────────────────────────────────────

/// THE TICKET'S CALL: the open argument first, and `y` says `T = Int64`.
#[test]
fn the_ticket_call_reaches_the_provider_the_later_argument_says() {
    assert_eq!(answers("wi7xnsk.first", "Bool", &both("Bool"), "Store2.peek2(mkb([]), y)"), 11);
}

/// CONTROL: the said argument first — read right before the change.
#[test]
fn the_ticket_call_other_order() {
    assert_eq!(answers("wi7xnsk.second", "Bool", &both("Bool"), "Store2.peek2(y, mkb([]))"), 11);
}

/// BESIDE `CB` ALONE the call is refused at the instance `y` says — as the other order is —
/// where it ran `CB` (21).
#[test]
fn beside_the_other_provider_alone_the_ticket_call_is_refused() {
    for (ns, call) in [
        ("wi7xnsk.alone_first", "Store2.peek2(mkb([]), y)"),
        ("wi7xnsk.alone_second", "Store2.peek2(y, mkb([]))"),
    ] {
        let errs = refusals(ns, "Bool", &cb_alone("Bool"), call);
        assert_refused_naming(
            &errs,
            &["cannot be supplied", "State = ", "Buf[T = anthill.prelude.Int64, N = anthill.prelude.Bool]"],
            &format!("`{call}` beside `CB` alone"),
        );
    }
}

/// THE VALUE-IN-TYPE SPELLING (`N = 3`), whose binding rides an occurrence: the same verdicts.
#[test]
fn the_value_in_type_spelling_reaches_the_same_provider() {
    assert_eq!(answers("wi7xnsk.v_first", "3", &both("3"), "Store2.peek2(mkb([]), y)"), 11);
    assert_eq!(answers("wi7xnsk.v_second", "3", &both("3"), "Store2.peek2(y, mkb([]))"), 11);
}

#[test]
fn the_value_in_type_spelling_beside_the_other_provider_is_refused() {
    for (ns, call) in [
        ("wi7xnsk.v_alone_first", "Store2.peek2(mkb([]), y)"),
        ("wi7xnsk.v_alone_second", "Store2.peek2(y, mkb([]))"),
    ] {
        let errs = refusals(ns, "3", &cb_alone("3"), call);
        assert_refused_naming(
            &errs,
            &["cannot be supplied", "Buf[T = anthill.prelude.Int64, N = 3]"],
            &format!("`{call}` beside `CB` alone, `N = 3`"),
        );
    }
}

// ── the other spellings of the call ───────────────────────────────────────────────────

/// NAMED ARGUMENTS are met in WRITTEN order, so `s: mkb([])` first was the ticket's call.
#[test]
fn a_named_call_in_either_order_reaches_the_same_provider() {
    for (ns, call) in [
        ("wi7xnsk.named_first", "Store2.peek2(s: mkb([]), t: y)"),
        ("wi7xnsk.named_second", "Store2.peek2(t: y, s: mkb([]))"),
    ] {
        assert_eq!(answers(ns, "Bool", &both("Bool"), call), 11, "`{call}`");
    }
}

/// THE RECEIVER SPELLING is the open argument first.
#[test]
fn a_receiver_call_reaches_the_same_provider() {
    assert_eq!(answers("wi7xnsk.recv", "Bool", &both("Bool"), "mkb([]).peek2(y)"), 11);
}

/// THE BARE OPEN SPELLING: `Buf.empty()` fixes neither slot, and `y` says both. It was refused
/// "nothing here fixes `T` of `Buf`" in this order and ran `CA` in the other.
#[test]
fn the_bare_open_spelling_takes_the_later_argument() {
    assert_eq!(answers("wi7xnsk.bare_first", "Bool", &both("Bool"), "Store2.peek2(Buf.empty(), y)"), 11);
    assert_eq!(answers("wi7xnsk.bare_second", "Bool", &both("Bool"), "Store2.peek2(y, Buf.empty())"), 11);
}

/// A LATER ARGUMENT THAT DISAGREES: `y` fills the open slot and `z` (`T = String`) is refused
/// against it, as it is when `y` comes first — where the open goal was refused as ambiguous.
#[test]
fn a_later_argument_that_disagrees_is_refused_as_a_mismatch() {
    for (ns, call) in [
        ("wi7xnsk.three_open", "Store2.peek3(mkb([]), y, z)"),
        ("wi7xnsk.three_said", "Store2.peek3(y, mkb([]), z)"),
    ] {
        let errs = refusals(ns, "Bool", &both("Bool"), call);
        assert_refused_naming(
            &errs,
            &["peek3.u", "expected Buf[T = Int64, N = Bool], got Buf[T = String, N = Bool]"],
            &format!("`{call}`"),
        );
    }
}

/// A SPEC OPERATION WITH A BODY is dispatched as one without: `peek3` has a default, and each
/// provider's own runs.
#[test]
fn a_spec_operation_with_a_body_runs_at_the_said_instance() {
    assert_eq!(answers("wi7xnsk.default", "Bool", &both("Bool"), "Store2.peek3(mkb([]), y, y)"), 11);
}

/// NOTHING TO FILL FROM: both arguments open, so nothing says `T` and the call stays ambiguous.
#[test]
fn two_open_arguments_say_nothing() {
    let errs = refusals("wi7xnsk.both_open", "Bool", &both("Bool"), "Store2.peek2(mkb([]), mkb([]))");
    assert_refused_naming(&errs, &["ambiguous dispatch", "CA", "CB"], "two open arguments");
}

/// A NAME CLOSES THE SLOT (§5.4): `let w = mkb([])` is a `Buf[T = w.T, …]`, which `y` does not
/// fit — in this change's terms nothing is left open for `y` to say.
#[test]
fn a_named_value_keeps_its_own_unknown() {
    let errs = refusals(
        "wi7xnsk.named_value",
        "Bool",
        &both("Bool"),
        "(let w = mkb([])\n    Store2.peek2(w, y))",
    );
    assert_refused_naming(&errs, &["peek2.t", "expected Buf[T = w.T, N = Bool]"], "a named open value");
}

// ── an operation's own parameter at an invariant occurrence ───────────────────────────

/// `h[X]` takes `X` under `Cell`, which declares no variance — an INVARIANT occurrence — and
/// asks `Store2` at `X` for its body's call.
const H: &str = "  operation h[X](a: Cell[T = X], b: Cell[T = X]) -> Int64 requires Store2[State = X] = \
                 Store2.peek2(a.c, b.c)\n";

fn with_h(providers: String) -> String {
    format!("{providers}{H}")
}

/// The open `Cell` first: `X` was fixed at `Buf[T = ?T, …]` and the requirement was refused as
/// ambiguous.
#[test]
fn an_operations_own_parameter_at_an_invariant_occurrence_takes_the_later_argument() {
    assert_eq!(
        answers("wi7xnsk.inv_first", "Bool", &with_h(both("Bool")), "h(cell(c: mkb([])), cell(c: y))"),
        11
    );
}

#[test]
fn an_operations_own_parameter_at_an_invariant_occurrence_other_order() {
    assert_eq!(
        answers("wi7xnsk.inv_second", "Bool", &with_h(both("Bool")), "h(cell(c: y), cell(c: mkb([])))"),
        11
    );
}

/// … and beside `CB` alone it RAN `CB` (21).
#[test]
fn beside_the_other_provider_the_invariant_route_is_refused() {
    for (ns, call) in [
        ("wi7xnsk.inv_alone_first", "h(cell(c: mkb([])), cell(c: y))"),
        ("wi7xnsk.inv_alone_second", "h(cell(c: y), cell(c: mkb([])))"),
    ] {
        let errs = refusals(ns, "Bool", &with_h(cb_alone("Bool")), call);
        assert_refused_naming(
            &errs,
            &["h.requires", "Buf[T = anthill.prelude.Int64, N = anthill.prelude.Bool]"],
            &format!("`{call}` beside `CB` alone"),
        );
    }
}

/// THREE INVARIANT OCCURRENCES, THE LAST DISAGREEING: `y` fills the open one and `z` (`T =
/// String`) is refused against it in either order. Left to the site when the occurrences did
/// not all agree, the open one decided again, `z` fitted it, and the requirement was asked at
/// `Buf[T = ?T]` — ambiguous — with the open one first (review).
#[test]
fn a_disagreeing_third_invariant_occurrence_is_refused_in_either_order() {
    let h3 = "  operation h3[X](a: Cell[T = X], b: Cell[T = X], c: Cell[T = X]) -> Int64 \
              requires Store2[State = X] = Store2.peek2(a.c, b.c)\n";
    for (ns, call) in [
        ("wi7xnsk.inv3_open", "h3(cell(c: mkb([])), cell(c: y), cell(c: z))"),
        ("wi7xnsk.inv3_said", "h3(cell(c: y), cell(c: mkb([])), cell(c: z))"),
    ] {
        let errs = refusals(ns, "Bool", &format!("{}{h3}", both("Bool")), call);
        assert_refused_naming(
            &errs,
            &["h3.c", "Cell[T = Buf[T = Int64, N = Bool]]"],
            &format!("`{call}`"),
        );
        assert!(
            !errs.iter().any(|e| e.contains("ambiguous")),
            "`{call}` is refused at its third argument, not asked at an open slot: {errs:#?}"
        );
    }
}
