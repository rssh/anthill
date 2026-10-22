//! WI-20261003-GR5EN — THE DECLARATION RULE THROUGH A PROVIDER, AT EVERY POSITION IT WALKS. A
//! member is compared with its spec by subtyping, its variables bound along the relation where
//! unification stops short (`bind_member_vars_along`). A carrier against a spec it provides
//! (`Box[T = Int64]` behind a member's `Describe[K = W]`) was bound by a second walk that read
//! the provision at the top of a position and through same-sort applications only, so a member
//! wider through a provider inside a tuple or an arrow was refused as taking less. S7YF5's
//! unifier reads an APPLIED carrier through its provision at any depth, which closed the
//! ticket's own two programs; a carrier with no parameters (a bare `Plain`, which the unifier
//! admits against `Describe[K = W]` binding nothing) and a tuple wider by width (where
//! unification gives up) stayed refused. The provider is now an arm of the relation's walk, the
//! carrier side chosen by the walk's direction, and the second walk is gone.
//!
//! A spec parameter the provision leaves out is the `?` written there, the caller's, and the
//! returns below behind a spec's open slot write the spec's own unwritten slot (`-> Describe`),
//! which is the member's to pick (`wi_gr5en_left_out_parameter_test` holds the rest).
//!
//! BACK-OUTS, measured on one build with each switch:
//! - THE PROVIDER ARM (`bind_member_vars_through_provision`) not called — 5 FAIL: the
//!   parameter rows whose carrier is `Plain` or whose tuple differs in width (the arm also
//!   replaces the removed walk, which bound `Plain` at the top), and
//!   [`a_written_receiver_meets_its_provision_through_a_provider`]. The returns behind the
//!   spec's own unwritten slot pass without it, as they did on the parent.
//! - The arm AND S7YF5's provider view in `unify_parameterized_view` — 8 FAIL: the ticket's two
//!   rows and the variable read by a later parameter as well; either alone binds an applied
//!   carrier.
//! - Pass either way by design: the refusals of a member narrower than its spec, of a provider
//!   at another instance and of a member fixing the caller's slot, and the controls a member is
//!   generic over the slot in.
use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// `Box` provides `Describe` at its own `T`.
const BOX: &str = r#"
  sort Box
    sort T = ?
    entity box(n: Int64, t: T)
    provides Describe[K = T]
    operation tag(b: Self) -> Int64 = b.n
    operation key(b: Self) -> T = b.t
  end"#;

/// `Plain` has no parameters: a reference to it is bare, never an application.
const PLAIN: &str = r#"
  sort Plain
    entity plain(n: Int64)
    provides Describe[K = Int64]
    operation tag(b: Self) -> Int64 = b.n
    operation key(b: Self) -> Int64 = b.n
  end"#;

/// `Car provides {provision}` with its member `{member}` behind `Sp.op(s: Self{spec}`.
fn program(
    name: &str,
    provider: &str,
    provision: &str,
    spec: &str,
    member: &str,
    go: &str,
) -> String {
    format!(
        r#"
namespace gr5en.{name}
  import anthill.prelude.{{Int64, String, List}}
  sort Describe
    sort K = ?
    operation tag(d: Self) -> Int64
    operation key(d: Self) -> K
  end{provider}
  sort Sp
    sort T = ?
    sort K = ?
    operation op(s: Self{spec}
  end
  sort Car
    entity car(n: Int64)
    provides {provision}
    operation {member}
  end
  operation go() -> Int64 = {go}
end
"#
    )
}

fn runs(name: &str, provider: &str, provision: &str, spec: &str, member: &str, go: &str) {
    let src = program(name, provider, provision, spec, member, go);
    assert_eq!(run_src(&src, &format!("gr5en.{name}.go")), Ok(42), "{name}");
}

fn refused(name: &str, provider: &str, provision: &str, spec: &str, member: &str, at: &str) {
    let src = program(name, provider, provision, spec, member, "0");
    assert_refused_naming(
        &load_errors(&src),
        &[&format!("its own member 'op' does not fit 'gr5en.{name}.Sp.op'"), at],
        name,
    );
}

// ── the ticket's programs: an applied carrier ──────────────────────────────────────────────

/// `x: (a: Describe, b: Int64)` behind `x: (a: Box[T = T], b: Int64)`. Refused on the ninth
/// pass's tree, ran on the eighth's (MEASURED by the ticket); runs since S7YF5.
#[test]
fn a_member_wider_through_a_provider_inside_a_tuple_fits() {
    runs(
        "tuple_wider",
        BOX,
        "Sp[T = Int64]",
        ", x: (a: Box[T = T], b: Int64)) -> Int64",
        "op(c: Car, x: (a: Describe, b: Int64)) -> Int64 = Describe.tag(x.a) + 1",
        "Sp.op(car(n: 1), (a: box(n: 41, t: 5), b: 0))",
    );
}

/// `f: (u: Int64) -> Describe` behind `f: (u: Int64) -> Box[T = T]`.
#[test]
fn a_member_wider_through_a_provider_in_an_arrows_result_fits() {
    runs(
        "arrow_wider",
        BOX,
        "Sp[T = Int64]",
        ", f: (u: Int64) -> Box[T = T]) -> Int64",
        "op(c: Car, f: (u: Int64) -> Describe) -> Int64 = Describe.tag(f(41)) + 1",
        "Sp.op(car(n: 1), lambda (u) -> box(n: u, t: 5))",
    );
}

/// The member's `W`, bound through the provider inside the tuple, is the `W` its later
/// parameter reads: `y: W` behind `y: String` is refused.
#[test]
fn a_variable_bound_through_a_provider_inside_a_tuple_is_read_by_a_later_parameter() {
    runs(
        "tuple_var",
        BOX,
        "Sp[T = Int64]",
        ", x: (a: Box[T = T], b: Int64), y: T) -> Int64",
        "op[W](c: Car, x: (a: Describe[K = W], b: Int64), y: W) -> Int64 = Describe.tag(x.a) + x.b",
        "Sp.op(car(n: 1), (a: box(n: 41, t: 5), b: 1), 7)",
    );
    refused(
        "tuple_var_bad",
        BOX,
        "Sp[T = Int64]",
        ", x: (a: Box[T = T], b: Int64), y: String) -> Int64",
        "op[W](c: Car, x: (a: Describe[K = W], b: Int64), y: W) -> Int64 = 1",
        "parameter 3",
    );
}

/// CONTROL: narrower through a provider (`(a: Box[T = Int64], b: Int64)` behind `(a: Describe,
/// b: Int64)`), and a provider the wrong way in an arrow's parameter. Refused either way.
#[test]
fn a_member_narrower_through_a_provider_is_refused() {
    refused(
        "tuple_narrower",
        BOX,
        "Sp[T = Int64]",
        ", x: (a: Describe, b: Int64)) -> Int64",
        "op(c: Car, x: (a: Box[T = Int64], b: Int64)) -> Int64 = 1",
        "parameter 2",
    );
    refused(
        "arrow_param_wrong",
        BOX,
        "Sp[T = Int64]",
        ", f: (u: Box[T = T]) -> Int64) -> Int64",
        "op(c: Car, f: (u: Describe) -> Int64) -> Int64 = 1",
        "parameter 2",
    );
}

// ── a carrier with no parameters ───────────────────────────────────────────────────────────

/// `x: (a: Describe[K = W], b: Int64)` behind `x: (a: Plain, b: Int64)`: the unifier admits the
/// bare `Plain` against `Describe[K = W]` and binds nothing, so `W` stayed open and the member
/// was refused — the ticket's regression, still open after S7YF5 (MEASURED on the parent).
#[test]
fn a_parameterless_provider_inside_a_tuple_fits() {
    runs(
        "plain_tuple",
        PLAIN,
        "Sp[T = Int64]",
        ", x: (a: Plain, b: Int64), y: Int64) -> Int64",
        "op[W](c: Car, x: (a: Describe[K = W], b: Int64), y: W) -> Int64 = Describe.tag(x.a) + x.b",
        "Sp.op(car(n: 1), (a: plain(n: 41), b: 1), 7)",
    );
    refused(
        "plain_tuple_bad",
        PLAIN,
        "Sp[T = Int64]",
        ", x: (a: Plain, b: Int64), y: String) -> Int64",
        "op[W](c: Car, x: (a: Describe[K = W], b: Int64), y: W) -> Int64 = 1",
        "parameter 3",
    );
}

/// … and at the top of a position, which the removed walk bound and the arm binds now.
#[test]
fn a_parameterless_provider_at_the_top_fits() {
    runs(
        "plain_top",
        PLAIN,
        "Sp[T = Int64]",
        ", x: Plain, y: Int64) -> Int64",
        "op[W](c: Car, x: Describe[K = W], y: W) -> Int64 = Describe.tag(x) + 1",
        "Sp.op(car(n: 1), plain(n: 41), 7)",
    );
}

/// A RETURN: the spec's own unwritten slot (`-> Describe`) is the member's to pick, so `->
/// Plain` fits — at the top and inside a tuple.
#[test]
fn a_parameterless_provider_returned_behind_the_specs_open_slot_fits() {
    runs(
        "plain_ret",
        PLAIN,
        "Sp[T = Int64]",
        ") -> Describe",
        "op(c: Car) -> Plain = plain(n: 42)",
        "Describe.tag(Sp.op(car(n: 1)))",
    );
    runs(
        "plain_ret_tuple",
        PLAIN,
        "Sp[T = Int64]",
        ") -> (a: Describe, b: Int64)",
        "op(c: Car) -> (a: Plain, b: Int64) = (a: plain(n: 41), b: 1)",
        "Describe.tag(Sp.op(car(n: 1)).a) + 1",
    );
}

/// CONTROL: a provider of ANOTHER instance of the spec's return (`K = String`). Refused either
/// way.
#[test]
fn a_parameterless_provider_of_another_instance_is_refused() {
    refused(
        "plain_ret_wrong",
        PLAIN,
        "Sp[T = Int64, K = String]",
        ") -> (a: Describe[K = K], b: Int64)",
        "op(c: Car) -> (a: Plain, b: Int64) = (a: plain(n: 41), b: 1)",
        "the member returns",
    );
}

// ── a tuple wider by width ─────────────────────────────────────────────────────────────────

/// Unification gives up on two tuples of different widths; the relation's walk aligns them and
/// now reaches the provider in the field: `x: (a: Describe[K = W])` behind `x: (a: Box[T = T],
/// b: Int64)`, with `Box` and with `Plain`. Refused on the parent.
#[test]
fn a_parameter_wider_by_width_and_through_a_provider_fits() {
    runs(
        "width",
        BOX,
        "Sp[T = Int64]",
        ", x: (a: Box[T = T], b: Int64), y: T) -> Int64",
        "op[W](c: Car, x: (a: Describe[K = W]), y: W) -> Int64 = Describe.tag(x.a) + 1",
        "Sp.op(car(n: 1), (a: box(n: 41, t: 5), b: 1), 7)",
    );
    runs(
        "plain_width",
        PLAIN,
        "Sp[T = Int64]",
        ", x: (a: Plain, b: Int64), y: Int64) -> Int64",
        "op[W](c: Car, x: (a: Describe[K = W]), y: W) -> Int64 = Describe.tag(x.a) + 1",
        "Sp.op(car(n: 1), (a: plain(n: 41), b: 1), 7)",
    );
    refused(
        "width_bad",
        BOX,
        "Sp[T = Int64]",
        ", x: (a: Box[T = T], b: Int64), y: String) -> Int64",
        "op[W](c: Car, x: (a: Describe[K = W]), y: W) -> Int64 = 1",
        "parameter",
    );
}

/// A return wider by width: `-> (a: Box[T = W], b: Int64)` behind `-> (a: Describe)`.
#[test]
fn a_return_wider_by_width_and_through_a_provider_fits() {
    runs(
        "ret_width",
        BOX,
        "Sp[T = Int64]",
        ", y: T) -> (a: Describe)",
        "op[W](c: Car, y: W) -> (a: Box[T = W], b: Int64) = (a: box(n: 42, t: y), b: 1)",
        "Describe.tag(Sp.op(car(n: 1), 7).a)",
    );
    runs(
        "plain_ret_width",
        PLAIN,
        "Sp[T = Int64]",
        ") -> (a: Describe)",
        "op(c: Car) -> (a: Plain, b: Int64) = (a: plain(n: 42), b: 1)",
        "Describe.tag(Sp.op(car(n: 1)).a)",
    );
    refused(
        "ret_width_wrong",
        BOX,
        "Sp[T = Int64, K = String]",
        ", y: T) -> (a: Describe[K = K])",
        "op[W](c: Car, y: W) -> (a: Box[T = W], b: Int64) = (a: box(n: 42, t: y), b: 1)",
        "the member returns",
    );
}

/// A CALLBACK's parameter, where the relation turns over and the carrier is on the member's
/// side: `f: (u: (a: Box[T = W], b: Int64)) -> Int64` behind `f: (u: (a: Describe[K = T])) ->
/// Int64`.
#[test]
fn a_callback_parameter_wider_by_width_and_through_a_provider_fits() {
    runs(
        "callback_width",
        BOX,
        "Sp[T = Int64]",
        ", f: (u: (a: Describe[K = T])) -> Int64, y: T) -> Int64",
        "op[W](c: Car, f: (u: (a: Box[T = W], b: Int64)) -> Int64, y: W) -> Int64 = \
         f((a: box(n: 41, t: y), b: 1)) + 1",
        "Sp.op(car(n: 1), lambda (u) -> Describe.tag(u.a), 7)",
    );
    refused(
        "callback_width_bad",
        BOX,
        "Sp[T = Int64]",
        ", f: (u: (a: Describe[K = T])) -> Int64, y: String) -> Int64",
        "op[W](c: Car, f: (u: (a: Box[T = W], b: Int64)) -> Int64, y: W) -> Int64 = 1",
        "parameter",
    );
}

// ── the caller's slot ──────────────────────────────────────────────────────────────────────

/// A SPEC PARAMETER THE PROVISION LEAVES OUT IS THE CALLER'S, at a callback's parameter as
/// anywhere: `f: (u: Box[T = Int64]) -> Int64` behind `f: (u: Describe[K = K]) -> Int64` fixes
/// it. Bound there by the relation's walk, as a member's own variable is, it loaded, and a call
/// passing a callback that reads a `String` key ran it on an `Int64` one (MEASURED: a run-time
/// type error). Refused on the parent, where no walk reached the pair.
#[test]
fn a_callback_fixing_the_callers_unbound_slot_through_a_provider_is_refused() {
    refused(
        "fixed_callback",
        BOX,
        "Sp[T = Int64]",
        ", f: (u: Describe[K = K]) -> Int64) -> Int64",
        "op(c: Car, f: (u: Box[T = Int64]) -> Int64) -> Int64 = f(box(n: 1, t: 41))",
        "parameter 2",
    );
    refused(
        "fixed_callback_plain",
        PLAIN,
        "Sp[T = Int64]",
        ", f: (u: Describe[K = K]) -> Int64) -> Int64",
        "op(c: Car, f: (u: Plain) -> Int64) -> Int64 = f(plain(n: 41))",
        "parameter 2",
    );
}

/// … AND UNDER A RETURNED FUNCTION'S PARAMETER, where the caller supplies the value: `-> (u: (a:
/// Box[T = Int64])) -> Int64` behind `-> (u: (a: Box[T = K], b: Int64)) -> Int64`, `K` left
/// out. Bound there by the relation's walk it loaded, and a caller handing the returned
/// function a `Box[T = String]` ran it on one (MEASURED: `type mismatch: expected Int64, got
/// String`). Refused on the parent, where no walk bound it.
#[test]
fn a_returned_functions_parameter_is_the_callers_slot() {
    refused(
        "returned_parameter",
        BOX,
        "Sp[T = Int64]",
        ") -> (u: (a: Box[T = K], b: Int64)) -> Int64",
        "op(c: Car) -> (u: (a: Box[T = Int64])) -> Int64 = lambda (u) -> Box.key(u.a) + 1",
        "the member returns",
    );
}

/// A WRITTEN RECEIVER MEETS ITS PROVISION THROUGH A PROVIDER TOO: `op[U](s: Sp[T = Describe[K =
/// U]], x: U)` at `Car provides Sp[T = Box[T = Int64]]`, `T` covariant, reaches `Car` with `U =
/// Int64` — the call reads it so — and `x: Int64` fits. With `U` left open the member was
/// compared at any `U` and refused as taking less (MEASURED on the parent). A call at another
/// `U` is refused at the call.
#[test]
fn a_written_receiver_meets_its_provision_through_a_provider() {
    let src = |name: &str, arg: &str| {
        format!(
            r#"
namespace gr5en.{name}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.reflect.typing.{{Covariant}}
  sort Describe
    sort K = ?
    operation tag(d: Self) -> Int64
  end{BOX}
  sort Sp
    sort T = ?
    fact Covariant(sort: Sp, param: T)
    operation op[U](s: Sp[T = Describe[K = U]], x: U) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Box[T = Int64]]
    operation op(c: Car, x: Int64) -> Int64 = x + 1
  end
  operation go() -> Int64 = Sp.op(car(n: 1), {arg})
end
"#
        )
    };
    assert_eq!(run_src(&src("receiver_meet", "41"), "gr5en.receiver_meet.go"), Ok(42));
    assert_refused_naming(
        &load_errors(&src("receiver_meet_bad", "\"s\"")),
        &["type mismatch in op.s (op-arg): expected Sp[T = Describe[K = String]], got Car"],
        "a spec call at another `U`",
    );
}

/// CONTROL: a member generic over the caller's slot, or one the provision binds, fits either way.
#[test]
fn a_member_generic_over_the_callers_unbound_slot_fits() {
    runs(
        "generic",
        BOX,
        "Sp[T = Int64]",
        ", x: Box[T = K]) -> Describe[K = K]",
        "op[W](c: Car, x: Box[T = W]) -> Box[T = W] = x",
        "Describe.key(Sp.op(car(n: 1), box(n: 1, t: 42)))",
    );
    runs(
        "bound_callback",
        PLAIN,
        "Sp[T = Int64]",
        ", f: (u: Describe[K = T]) -> Int64) -> Int64",
        "op(c: Car, f: (u: Plain) -> Int64) -> Int64 = f(plain(n: 41)) + 1",
        "Sp.op(car(n: 1), lambda (u) -> Describe.tag(u))",
    );
}
