//! WI-20260929-9WXK2 — a value-in-type written as a NAME in a clause binding is the type a
//! signature writes.
//!
//! Over `operation size() -> Int64 = 3`, a signature's `s: Buf[T = Int64, N = size]` holds
//! the value `size`: a type position lowers the name of a value to its `denoted`
//! occurrence. A clause binding lowered every bare name to the sort reference `Ref(size)`,
//! so `provides Store[State = Buf[T = Int64, N = size]]` bound another type than the member
//! it is met by, and `subtype` relates a `denoted` only to a `denoted`. MEASURED before the
//! fix: a CORRECT member was refused "parameter 1 is `Buf[T = Int64, N = size]` where the
//! spec's is `Buf[T = Int64, N = size]`" — both sides printing alike — and so were an
//! operation bound by name, a spec alias fixing the binding, a nested `Modify[slot]` over a
//! zero-argument operation, a provision's condition, and a sort's `requires` (refused as
//! "`Buf` provides no `Store`"); a TOP-LEVEL `provides Sized[N = size]` loaded, and its
//! call failed at run time, "operation has no body". The literal twins (`N = 3`) load and
//! run since WI-20260924-F3FYJ.
//!
//! THE FIX: a clause binding at a type parameter reads a value's name as a type position
//! does (`Loader::names_a_value_in_a_type`, one answer for both). At an operation's slot the
//! name is the operation: `peek = bufPeek` binds the operation `bufPeek`, which is also the
//! name of a value. An OPERATION's own `requires` is lowered from the clause's term, and
//! reads a value's name at a type parameter the same way (`Loader::contract_value_binding`):
//! with only the provision's half of the fix, `operation via() -> Int64 requires Sized[N =
//! size] = 7` — which ran, both halves `Ref(size)` — was refused (MEASURED, found by review).
//!
//! Every correct row DRIVES what it claims — a call runs through the provision or the
//! requirement — and every control is refused naming the type it is at.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! THREE PARTS, each backed out present-but-wrong and run over this file's 17 rows:
//!
//! 1. THE VALUE NAME — a sort clause's binding is its `Ref` at every slot again. 14 FAIL,
//!    every row but the operation-requirement ones: the rows that run a call, and the
//!    controls — each still refused, but for the `fresh` member beside the changed one
//!    ([`assert_fresh_fits`]) or for the provider's members beside the requirement.
//! 2. THE SLOT — the top-level loop reads every key alike. As a type parameter, `peek =
//!    bufPeek` binds the value `bufPeek`, and the standard library itself no longer loads
//!    (`Delay provides DelayMonad` "backs no operation 'pure'"): ALL FAIL. As an
//!    operation's slot: 1 FAILS, [`a_top_level_binding_selects_its_provider`] — the one row
//!    whose value is the spec's own binding; every other row's is inside `State`.
//! 3. THE OPERATION'S `requires` — its bracket keeps the name's `Ref`. 3 FAIL: the three
//!    operation-requirement rows, the control at its message only (still refused, the
//!    requirement printed `N = wi9wxk2.opreq_bad.size`, a sort reference).
//!
//! PASS UNDER EVERY BACK-OUT, by design: none.

use crate::common::{assert_refused_naming, interp_for, try_load_kb_with};
use anthill_core::eval::Value;

/// `Buf[T, N]` — `N` the value-in-type argument — the spec `Store`, whose `State` the
/// provisions bind, and two zero-argument operations whose names are the values. `body`
/// follows.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Unit, Modify, Modifiable}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
    operation fresh(n: Int64) -> State
  end

  operation size() -> Int64 = 3
  operation other() -> Int64 = 4
{body}
end
"#
    )
}

/// A carrier `name` whose own members implement `Store` — `peek` taking `peek_ty` and
/// returning `s.v + bump`, `fresh` returning `fresh_ty` — provided through `provision`.
fn carrier_named(name: &str, provision: &str, peek_ty: &str, fresh_ty: &str, bump: i64) -> String {
    format!(
        r#"
  sort {name}
    {provision}
    operation peek(s: {peek_ty}) -> Int64 = s.v + {bump}
    operation fresh(n: Int64) -> {fresh_ty} = buf(v: n)
  end
"#
    )
}

fn carrier(provision: &str, peek_ty: &str, fresh_ty: &str) -> String {
    carrier_named("Carrier", provision, peek_ty, fresh_ty, 10)
}

const NAMED: &str = "Buf[T = Int64, N = size]";
const WRONG: &str = "Buf[T = Int64, N = other]";
const PROVIDES_NAMED: &str = "provides Store[State = Buf[T = Int64, N = size]]";

/// Load `program(ns, body)` with `go() = {go}` appended, call `ns.go()`, return its `Int64`.
fn answers(ns: &str, body: &str, go: &str) -> i64 {
    let src = program(ns, &format!("{body}\n  operation go() -> Int64 = {go}"));
    let mut interp = interp_for(&src);
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` must run to an Int64: {other:?}"),
    }
}

fn load_errors(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// What makes a control measure the binding and not only the member it changes: the
/// `fresh` member, at the provision's own type, is not refused beside it.
fn assert_fresh_fits(errs: &[String]) {
    assert!(
        !errs
            .iter()
            .any(|e| e.contains("member 'fresh' does not fit") || e.contains("Store.fresh")),
        "the `fresh` member is at the provision's own type; got: {errs:#?}"
    );
}

// ── the carrier's own members ─────────────────────────────────────────────────────────

/// THE TICKET'S PROGRAM: the members fit the provision at `N = size` — `peek` at the
/// parameter, `fresh` at the return — and the spec operation dispatches to the carrier.
#[test]
fn a_correct_member_loads_and_the_call_runs() {
    let body = carrier(PROVIDES_NAMED, NAMED, NAMED);
    assert_eq!(
        answers("wi9wxk2.member", &body, "Store.peek(buf(v: 7))"),
        17
    );
}

/// THE CONTROL: `N = other` is another type, refused naming both.
#[test]
fn a_member_at_another_name_is_refused() {
    let body = carrier(PROVIDES_NAMED, WRONG, NAMED);
    let errs = load_errors(&program("wi9wxk2.member_bad", &body));
    assert_refused_naming(
        &errs,
        &[
            "its own member 'peek' does not fit",
            "parameter 1 is `Buf[T = Int64, N = other]` where the spec's is \
             `Buf[T = Int64, N = size]`",
        ],
        "a member at another value's name",
    );
    assert_fresh_fits(&errs);
}

// ── an operation bound by name ────────────────────────────────────────────────────────

/// Operations bound BY NAME in the provision (`peek = bufPeek`): the key is the spec's
/// operation, so the name is the operation — while `N = size` beside it is the value.
fn bound_by_name(peek_ty: &str) -> String {
    format!(
        r#"
  operation bufPeek(s: {peek_ty}) -> Int64 = s.v + 20
  operation bufFresh(n: Int64) -> {NAMED} = buf(v: n)
  sort Carrier
    provides Store[State = {NAMED}, peek = bufPeek, fresh = bufFresh]
  end
"#
    )
}

#[test]
fn an_operation_bound_by_name_loads_and_the_call_runs() {
    assert_eq!(
        answers(
            "wi9wxk2.bound",
            &bound_by_name(NAMED),
            "Store.peek(buf(v: 7))"
        ),
        27
    );
}

#[test]
fn an_operation_bound_by_name_at_another_name_is_refused() {
    let errs = load_errors(&program("wi9wxk2.bound_bad", &bound_by_name(WRONG)));
    assert_refused_naming(
        &errs,
        &[
            "binds 'wi9wxk2.bound_bad.Store.peek' to a signature-incompatible operation",
            "has type `Buf[T = Int64, N = other]`, incompatible with the spec parameter type \
             `Buf[T = Int64, N = size]`",
        ],
        "an operation bound at another value's name",
    );
    assert_fresh_fits(&errs);
}

// ── a spec alias fixing the binding ───────────────────────────────────────────────────

fn through_alias(peek_ty: &str) -> String {
    format!(
        "  sort BufStore = Store[State = {NAMED}]\n{}",
        carrier("provides BufStore", peek_ty, NAMED)
    )
}

#[test]
fn a_spec_alias_fixing_the_binding_loads_and_the_call_runs() {
    assert_eq!(
        answers(
            "wi9wxk2.alias",
            &through_alias(NAMED),
            "Store.peek(buf(v: 7))"
        ),
        17
    );
}

#[test]
fn a_spec_alias_fixing_the_binding_refuses_a_member_at_another_name() {
    let errs = load_errors(&program("wi9wxk2.alias_bad", &through_alias(WRONG)));
    assert_refused_naming(
        &errs,
        &[
            "its own member 'peek' does not fit",
            "parameter 1 is `Buf[T = Int64, N = other]` where the spec's is \
             `Buf[T = Int64, N = size]`",
        ],
        "a member at another value's name, through the alias",
    );
    assert_fresh_fits(&errs);
}

// ── a nested `Modify` target ──────────────────────────────────────────────────────────

/// `Modify[slot]` as a type argument of the binding, over a zero-argument operation:
/// `slot` is a value there as in the member's signature.
fn modify_target(peek_target: &str) -> String {
    let at = |target: &str| format!("Buf[T = Int64, N = Modify[{target}]]");
    format!(
        r#"
  sort CounterState
    provides Modifiable[T = Self]
    entity counter
  end
  operation slot() -> CounterState = counter()
  operation slot2() -> CounterState = counter()
{}"#,
        carrier(
            &format!("provides Store[State = {}]", at("slot")),
            &at(peek_target),
            &at("slot")
        )
    )
}

#[test]
fn a_nested_modify_target_loads_and_the_call_runs() {
    assert_eq!(
        answers(
            "wi9wxk2.modify",
            &modify_target("slot"),
            "Store.peek(buf(v: 7))"
        ),
        17
    );
}

#[test]
fn a_nested_modify_target_refuses_a_member_at_another_name() {
    let errs = load_errors(&program("wi9wxk2.modify_bad", &modify_target("slot2")));
    assert_refused_naming(
        &errs,
        &[
            "its own member 'peek' does not fit",
            "parameter 1 is `Buf[T = Int64, N = Modify[T = slot2]]` where the spec's is \
             `Buf[T = Int64, N = Modify[T = slot]]`",
        ],
        "a member at another `Modify` target",
    );
    assert_fresh_fits(&errs);
}

// ── the top-level binding ─────────────────────────────────────────────────────────────

/// `provides Sized[N = size]` beside `provides Sized[N = other]`: the bracket selects the
/// provider at its value, each one. Before the fix both loaded and the call found none.
#[test]
fn a_top_level_binding_selects_its_provider() {
    let body = r#"
  sort Sized
    sort N = ?
    operation width() -> Int64
  end
  sort AtSize
    provides Sized[N = size]
    operation width() -> Int64 = 10
  end
  sort AtOther
    provides Sized[N = other]
    operation width() -> Int64 = 20
  end
"#;
    assert_eq!(
        answers(
            "wi9wxk2.top",
            body,
            "Sized[N = size].width() * 100 + Sized[N = other].width()"
        ),
        1020
    );
}

/// Two providers of `Store`, at `N = size` and at `N = other`: a call's argument type
/// selects each.
#[test]
fn a_call_selects_the_provider_at_its_name() {
    let body = format!(
        "{}{}
  operation viaSize(s: {NAMED}) -> Int64 = Store.peek(s)
  operation viaOther(s: {WRONG}) -> Int64 = Store.peek(s)",
        carrier_named("AtSize", PROVIDES_NAMED, NAMED, NAMED, 100),
        carrier_named(
            "AtOther",
            &format!("provides Store[State = {WRONG}]"),
            WRONG,
            WRONG,
            200
        ),
    );
    assert_eq!(
        answers(
            "wi9wxk2.select",
            &body,
            "viaSize(buf(v: 1)) * 1000 + viaOther(buf(v: 2))"
        ),
        101_202
    );
}

/// A qualified name is the same value.
#[test]
fn a_qualified_name_is_the_same_value() {
    let body = carrier(
        "provides Store[State = Buf[T = Int64, N = wi9wxk2.qualified.size]]",
        NAMED,
        NAMED,
    );
    assert_eq!(
        answers("wi9wxk2.qualified", &body, "Store.peek(buf(v: 7))"),
        17
    );
}

// ── a sort's `requires` and a provision's condition ───────────────────────────────────

/// The ticket's addendum (WI-20260929-WBHTM): a sort's `requires` at `N = size` covers its
/// own call, and with a provider there the call runs through the requirement.
fn requirement(provision: &str, peek_ty: &str) -> String {
    format!(
        r#"
  sort User
    requires Store[State = {NAMED}]
    operation via(s: {NAMED}) -> Int64 = Store.peek(s)
  end
{}"#,
        carrier(provision, peek_ty, peek_ty)
    )
}

#[test]
fn a_sort_requirement_at_a_name_is_supplied() {
    let body = requirement(PROVIDES_NAMED, NAMED);
    assert_eq!(answers("wi9wxk2.req", &body, "User.via(buf(v: 7))"), 17);
}

/// THE CONTROL: the one provider is at `N = other`, which does not supply `N = size`.
#[test]
fn a_sort_requirement_at_another_name_is_refused() {
    let body = requirement(&format!("provides Store[State = {WRONG}]"), WRONG);
    let src = program(
        "wi9wxk2.req_bad",
        &format!("{body}\n  operation go() -> Int64 = User.via(buf(v: 7))"),
    );
    let errs = load_errors(&src);
    assert_refused_naming(
        &errs,
        &[
            "requirement `wi9wxk2.req_bad.Store[State = wi9wxk2.req_bad.Buf[T = \
             anthill.prelude.Int64, N = size]]`",
            "cannot be supplied for call to `wi9wxk2.req_bad.User.via`",
        ],
        "a requirement at a value no provider is at",
    );
    assert!(
        !errs.iter().any(|e| e.contains("does not fit")),
        "the provider's own members fit its provision; got: {errs:#?}"
    );
}

/// A provision CONDITIONED on `Store` at `N = size`, met by the provider there.
#[test]
fn a_provision_condition_at_a_name_is_met() {
    let body = format!(
        r#"
  sort Tag
    sort X = ?
    operation tag(x: X) -> Int64
  end
{}
  sort Wrap
    sort A = ?
    entity wrap(a: A)
    provides Tag[X = Wrap[A = {NAMED}]] :- Store[State = {NAMED}]
    operation tag(x: Wrap[A = {NAMED}]) -> Int64 = 5
  end
"#,
        carrier(PROVIDES_NAMED, NAMED, NAMED)
    );
    assert_eq!(
        answers("wi9wxk2.cond", &body, "Tag.tag(wrap(a: buf(v: 1)))"),
        5
    );
}

// ── an operation's own `requires` ─────────────────────────────────────────────────────

/// The requirement is the clause's TERM, lowered by another path than a sort's clause.
fn op_requirement(provision: &str, peek_ty: &str) -> String {
    format!(
        r#"
  operation via(s: {NAMED}) -> Int64
    requires Store[State = {NAMED}]
  = Store.peek(s)
{}"#,
        carrier(provision, peek_ty, peek_ty)
    )
}

#[test]
fn an_operation_requirement_at_a_name_is_supplied() {
    let body = op_requirement(PROVIDES_NAMED, NAMED);
    assert_eq!(answers("wi9wxk2.opreq", &body, "via(buf(v: 7))"), 17);
}

/// THE CONTROL: the one provider is at `N = other`.
#[test]
fn an_operation_requirement_at_another_name_is_refused() {
    let body = op_requirement(&format!("provides Store[State = {WRONG}]"), WRONG);
    let src = program(
        "wi9wxk2.opreq_bad",
        &format!("{body}\n  operation go() -> Int64 = via(buf(v: 7))"),
    );
    let errs = load_errors(&src);
    assert_refused_naming(
        &errs,
        &[
            "requirement `wi9wxk2.opreq_bad.Store[State = wi9wxk2.opreq_bad.Buf[T = \
             anthill.prelude.Int64, N = size]]`",
            "cannot be supplied for call to `wi9wxk2.opreq_bad.via`",
        ],
        "an operation's requirement at a value no provider is at",
    );
}

/// The program the provision's half alone broke: a TOP-LEVEL value binding, required by an
/// operation whose body calls nothing of it. It ran before the fix and must run after.
#[test]
fn an_operation_requirement_of_a_top_level_binding_is_supplied() {
    let body = r#"
  sort Sized
    sort N = ?
    operation width() -> Int64
  end
  sort AtSize
    provides Sized[N = size]
    operation width() -> Int64 = 10
  end
  operation via() -> Int64
    requires Sized[N = size]
  = 7
"#;
    assert_eq!(answers("wi9wxk2.optop", body, "via()"), 7);
}
