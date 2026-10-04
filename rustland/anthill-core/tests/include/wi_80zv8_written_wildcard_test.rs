//! WI-20261001-80ZV8 — A `?` WRITTEN AT A SORT'S OWN SLOT IS A VARIABLE LIKE ANY OTHER
//! (proposal 070 §1.3; brought ahead of stage (e) by the user, 2026-10-04, "(a)").
//!
//! Inside `sort Car`, `Car[V = ?]` used to be a second spelling of `Self`: the `?` took the
//! sort's own parameter, "`?` and an omitted slot are one type", and the omitted slot was the
//! tie. Stage (d) made the omitted slot a load error and tells the author to write `Self` or
//! `Car[V = ?]` — so the second of those has to mean what it says: ANY `Car`. In a parameter
//! the caller picks it; in a return the operation does, and each call opens it; in a
//! provision the carrier provides the spec at every one.
//!
//! Each row RUNS or names its refusal.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED (2026-10-04, again after the review of this stage) on a temporary binary — this
//! file, `wi_80zv8_written_in_full_test`, `wi_80zv8_written_carrier_test`,
//! `wi_80zv8_written_receivers_test`, `wi_80zv8_self_test`, the four `wi_0rp29_*` suites,
//! `wi1076`, `wi1078`, the three `wi456_*`, `wi_wn9p8`, `wi_4zzkz`; 598 rows — each part
//! present but disabled:
//!
//! 1. THE TIE IS FOR A SLOT NOT WRITTEN (typing/elaborate.rs
//!    `rigidify_unwritten_sort_params`: the self half taken for a written `?` again).
//!    9 FAIL: five here — [`a_parameter_at_a_wildcard_takes_any_instance`],
//!    [`a_body_may_not_read_a_wildcard_parameter_as_this_instance`],
//!    [`a_return_at_a_wildcard_is_opened_at_the_call`],
//!    [`a_field_at_a_wildcard_holds_any_instance`],
//!    [`a_provision_at_a_wildcard_is_provided_at_every_instance`] (its member takes `o` at
//!    `?`) — and `wi1078 a_self_sort_return_at_a_variable_is_opened_…`, `wi_0rp29_call_binding
//!    a_projection_of_the_bound_parameter_is_an_instance_of_its_own`, `wi_0rp29_member_rule
//!    a_projection_over_any_provider_is_any_type`, `wi_80zv8_written_in_full
//!    an_alias_of_the_enclosing_sort_is_the_sort_it_stands_for` (its control at `R = ?`).
//! 2. A PROVISION'S OWN VARIABLES ARE OPENED IN THE CARRIER'S VIEW (typing/subtype.rs
//!    `ProvisionOpening::open_view` opening nothing). 5 FAIL:
//!    [`a_provision_at_a_wildcard_is_provided_at_every_instance`],
//!    [`a_variable_a_provision_writes_twice_is_one_variable`], the controls of
//!    [`a_body_may_not_pin_a_parameter_typed_by_a_projection`] and
//!    [`a_member_may_not_tie_a_projection_to_the_parameter_beside_it`], and
//!    `wi_0rp29_member_rule
//!    a_binding_naming_the_carrier_at_a_wildcard_is_an_independent_instance_control`.
//! 3. A SPEC PARAMETER A PROVISION LEAVES OUT IS OPEN (`provision_leaves_param_open`
//!    answering no). 2 FAIL: [`a_spec_parameter_a_provision_leaves_out_is_any_type`] and
//!    `wi_0rp29_member_rule a_wildcard_bound_to_a_member_variable_is_not_frozen`.
//! 4. A PROJECTION READS THE PROVISION'S VARIABLES OPENED (typing/projection.rs
//!    `provision_variables_opened` answering `None`). 4 FAIL: `wi_0rp29_call_binding
//!    a_projection_of_the_bound_parameter_is_an_instance_of_its_own`,
//!    [`a_body_may_not_pin_a_parameter_typed_by_a_projection`],
//!    [`a_body_packs_a_witness_into_a_return_at_a_wildcard`],
//!    [`a_member_may_not_tie_a_projection_to_the_parameter_beside_it`].
//! 5. THE DECLARATION RULE READS A `Self` RECEIVER AS UNWRITTEN (typing/signature.rs, the
//!    filter on the self-receiver's written arguments). 2 FAIL: `wi_0rp29_member_rule
//!    a_receiver_written_with_arguments_fixes_them_control` and
//!    `a_received_parameter_written_with_arguments_does_not_narrow_the_self_receiver`, each
//!    on the refusal's kind.
//! 6. THE RULE'S READER ANSWERS A PROJECTED PARAMETER AS AN INSTANCE OF ITS OWN
//!    (`ProjectionReader::instance_of`). On the spec's side alone, or on both: 2 FAIL,
//!    `wi_0rp29_call_binding
//!    a_projection_of_the_bound_parameter_is_an_instance_of_its_own_misfit` and
//!    [`a_member_may_not_tie_a_projection_to_the_parameter_beside_it`] (each tied member is
//!    admitted). On the member's side alone: 1 FAILS, `wi_0rp29_review9
//!    a_written_wildcard_only_the_return_reads_stays_open`.
//! 7. A PROJECTED PARAMETER'S OPEN SLOTS ARE ITS OWN IN THE BODY (typing/op_bodies.rs, the
//!    fill after the parameter-projection fixpoint). 1 FAILS:
//!    [`a_body_may_not_pin_a_parameter_typed_by_a_projection`].
//! 8. THE BODY PACKS A RETURN WRITTEN AT `?` (typing/op_bodies.rs, the declared return read
//!    through what the body bound). 5 FAIL:
//!    [`a_body_packs_a_witness_into_a_return_at_a_wildcard`],
//!    [`a_return_at_a_wildcard_is_opened_at_the_call`], `wi1078
//!    the_four_return_spellings_agree`, and — through the `get` member their fixture shares
//!    — [`a_body_may_not_pin_a_parameter_typed_by_a_projection`] and
//!    [`a_member_may_not_tie_a_projection_to_the_parameter_beside_it`].
//!
//! 9. A CONSTRUCTOR PATTERN OPENS WHAT ITS FIELDS LEAVE OPEN (typing/elaborate.rs
//!    `FieldOpening::open` returning the field as declared). 2 FAIL:
//!    [`a_binder_over_a_field_left_open_is_an_instance_of_its_own`] and
//!    [`a_variable_two_fields_share_is_one_for_both_binders`]. With the opening on but no
//!    rigid of the pattern's for a NAMED variable (`FieldOpening::of`), 1 FAILS: the second.
//! 10. A FIELD READ OPENS A NAMED VARIABLE (`open_existential_return` ignoring what the
//!    reduction brought in). 1 FAILS: [`a_field_read_opens_a_named_variable_too`].
//!    (Parts 9 and 10 measured on a binary of this file and `wi_80zv8_written_in_full_test`.)
//!
//! NOT MEASURED BY ANY ROW, and said so: that the provision's own variables are read off
//! its STORED bindings (`ProvisionOpening::of`) rather than taken to be every variable that
//! is no parameter of the carrier. No program was found that tells the two apart; that
//! function says why the first is the definition.
//!
//! [`a_provision_at_self_is_the_receivers_instance`] passes under every part, by design: it
//! is the other spelling the refusal offers, and what a wildcard must stay different from.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

// ── in an operation ─────────────────────────────────────────────────────────

/// `car` carries a function of its own `V`, so a body can only apply it to a value of THIS
/// instance.
fn car_program(ns: &str, member: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Car
    sort V = ?
    entity car(v: V, f: (x: V) -> Int64)
    {member}
  end
  operation takes_int(c: Car[V = Int64]) -> Int64 = 1
  operation takes_any[A](c: Car[V = A]) -> Int64 = 1
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 1, f: lambda (n: Int64) -> n)
    let y: Car[V = String] = car(v: "s", f: lambda (n: String) -> 0)
    {go}
end
"#
    )
}

/// A PARAMETER AT `?` TAKES ANY INSTANCE: `both(s: Self, o: Car[V = ?])` over a `Car` of
/// `Int64` and one of `String` runs. CONTROL — `o: Self` is this instance, and the second
/// `Car` is refused at its argument.
#[test]
fn a_parameter_at_a_wildcard_takes_any_instance() {
    let any = car_program(
        "wi80zv8q.p1",
        "operation both(s: Self, o: Car[V = ?]) -> Int64 = 5",
        "Car.both(x, y)",
    );
    assert_eq!(run_src(&any, "wi80zv8q.p1.go"), Ok(5));
    let this = car_program(
        "wi80zv8q.p2",
        "operation both(s: Self, o: Self) -> Int64 = 5",
        "Car.both(x, y)",
    );
    assert_refused_naming(
        &load_errors(&this),
        &["both.o (op-arg): expected Car[V = Int64], got Car[V = String]"],
        "a second instance where the parameter is `Self`",
    );
}

/// …AND ITS BODY MAY NOT TAKE IT FOR THIS INSTANCE: applying the receiver's function to
/// `o`'s value is refused, since `o`'s `V` is its own. CONTROL — with `o: Self` the same body
/// loads and runs.
#[test]
fn a_body_may_not_read_a_wildcard_parameter_as_this_instance() {
    let body = "match s case car(_, g) -> g(o.v)";
    let any = car_program(
        "wi80zv8q.b1",
        &format!("operation apply(s: Self, o: Car[V = ?]) -> Int64 = {body}"),
        "0",
    );
    assert_refused_naming(
        &load_errors(&any),
        &["g._1 (op-arg): expected ?V, got o.V"],
        "the receiver's function applied to another instance's value",
    );
    let this = car_program(
        "wi80zv8q.b2",
        &format!("operation apply(s: Self, o: Self) -> Int64 = {body}"),
        "Car.apply(x, x) + 41",
    );
    assert_eq!(run_src(&this, "wi80zv8q.b2.go"), Ok(42));
}

/// A RETURN AT `?` IS A TYPE THE OPERATION PICKS: its body returns a `Car` of `String` over
/// a receiver of `Int64`, and the result, opened at each call, is no `Car[V = Int64]` to a
/// consumer that asks for one — while one that takes any `Car` runs. The body was refused,
/// `some.return (op-return): expected Car[V = ?_], got Car[V = String]` (MEASURED), and this
/// row passed with a body-less `some` that never had to return anything. CONTROL — `-> Self`
/// is the receiver's instance and the same consumer takes it.
#[test]
fn a_return_at_a_wildcard_is_opened_at_the_call() {
    let some = "operation some(s: Self) -> Car[V = ?] = car(v: \"s\", f: lambda (n: String) -> 0)";
    let any = car_program("wi80zv8q.r1", some, "takes_int(Car.some(x))");
    assert_refused_naming(
        &load_errors(&any),
        &["takes_int.c (op-arg): expected Car[V = Int64], got Car[V = ?V]"],
        "a result whose `V` the operation picked",
    );
    let taken = car_program("wi80zv8q.r3", some, "takes_any(Car.some(x)) + 41");
    assert_eq!(run_src(&taken, "wi80zv8q.r3.go"), Ok(42));
    let this = car_program(
        "wi80zv8q.r2",
        "operation same(s: Self) -> Self = s",
        "takes_int(Car.same(x))",
    );
    assert_eq!(run_src(&this, "wi80zv8q.r2.go"), Ok(1));
}

// ── in an entity field ──────────────────────────────────────────────────────

/// A FIELD AT `?` HOLDS ANY INSTANCE: a `node` in a `Box` of `Int64` may hold a `Box` of
/// `String`. CONTROL — a field typed `Self` is this instance's, and the same value is
/// refused there.
#[test]
fn a_field_at_a_wildcard_holds_any_instance() {
    let program = |ns: &str, ctor: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Box
    sort T = ?
    entity leaf(v: T)
    entity node(next: Box[T = ?])
    entity same(next: Self)
  end
  operation depth(b: Box[T = Int64]) -> Int64 =
    match b
      case leaf(_) -> 0
      case node(_) -> 1
      case same(_) -> 2
  operation make() -> Box[T = Int64] = {ctor}(next: leaf(v: "s"))
  operation go() -> Int64 = depth(make())
end
"#
        )
    };
    assert_eq!(run_src(&program("wi80zv8q.f1", "node"), "wi80zv8q.f1.go"), Ok(1));
    assert_refused_naming(
        &load_errors(&program("wi80zv8q.f2", "same")),
        &["expected Box[T = Int64], got Box[T = String]"],
        "a `Box` of `String` in a field of this instance",
    );
}

// ── in a provision ──────────────────────────────────────────────────────────

/// `Sp.both(s: Self, o: T)` at `Car provides Sp[T = {binding}]`, the member taking `o` as
/// `member_o`; `go` calls it over a `Car` of `Int64` and `second`.
fn provision_program(ns: &str, binding: &str, member_o: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Sp
    sort T = ?
    operation both(s: Self, o: T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = {binding}]
    operation both(s: Self, o: {member_o}) -> Int64 = 41
  end
  sort Other
    entity other(n: Int64)
  end
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 1)
    Sp.both(x, {second}) + 1
end
"#
    )
}

/// A PROVISION AT `?` IS PROVIDED AT EVERY INSTANCE: `Car provides Sp[T = Car[V = ?]]` makes
/// a `Car` of `Int64` an `Sp` whose `T` is any `Car`, so a spec that types its receiver
/// `Self` takes a `Car` of `String` beside it. It was refused, `both.s (op-arg): expected
/// Sp[T = Car[V = String]], got Car[V = Int64]` — and so was ONE instance passed twice
/// (MEASURED): the bare receiver the tie read as this instance never asked the subtype
/// relation about the binding. What is no `Car` is still refused.
#[test]
fn a_provision_at_a_wildcard_is_provided_at_every_instance() {
    for (ns, second) in [("wi80zv8q.v1", "car(v: \"s\")"), ("wi80zv8q.v2", "x")] {
        let src = provision_program(ns, "Car[V = ?]", "Car[V = ?]", second);
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42), "{second}");
    }
    let src = provision_program("wi80zv8q.v3", "Car[V = ?]", "Car[V = ?]", "other(n: 3)");
    assert_refused_naming(
        &load_errors(&src),
        &["both.s (op-arg): expected Sp[T = Other], got Car[V = Int64]"],
        "an argument that is no `Car`",
    );
}

/// …AND AT `Self` IT IS THE RECEIVER'S INSTANCE: one instance runs, a second is refused.
#[test]
fn a_provision_at_self_is_the_receivers_instance() {
    let one = provision_program("wi80zv8q.s1", "Self", "Self", "x");
    assert_eq!(run_src(&one, "wi80zv8q.s1.go"), Ok(42));
    let two = provision_program("wi80zv8q.s2", "Self", "Self", "car(v: \"s\")");
    assert_refused_naming(
        &load_errors(&two),
        &["expected Car[V = Int64], got Car[V = String]"],
        "a second instance behind a binding of `Self`",
    );
}

/// A NAMED VARIABLE WRITTEN TWICE IN ONE PROVISION IS ONE VARIABLE: `Rel[A = Car[V = ?x], B
/// = Car[V = ?x]]` is provided at every `x`, the same in both places — so a `Car` is a `Rel`
/// of two `Car`s of `Int64`, and no `Rel` of one of `Int64` and one of `String`.
#[test]
fn a_variable_a_provision_writes_twice_is_one_variable() {
    let program = |ns: &str, b: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Rel
    sort A = ?
    sort B = ?
    operation weigh(r: Self) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Rel[A = Car[V = ?x], B = Car[V = ?x]]
    operation weigh(r: Self) -> Int64 = 42
  end
  operation use(r: Rel[A = Car[V = Int64], B = Car[V = {b}]]) -> Int64 = Rel.weigh(r)
  operation go() -> Int64 = use(car(v: true))
end
"#
        )
    };
    assert_eq!(run_src(&program("wi80zv8q.n1", "Int64"), "wi80zv8q.n1.go"), Ok(42));
    assert_refused_naming(
        &load_errors(&program("wi80zv8q.n2", "String")),
        &["use.r (op-arg): expected Rel[A = Car[V = Int64], B = Car[V = String]]"],
        "one variable asked to be two types",
    );
}

/// A SPEC PARAMETER THE PROVISION LEAVES OUT IS ANY TYPE, as a `?` written there would be:
/// `Car provides Sp` is an `Sp[T = X]` for every `X`. The spec's `Self` receiver asks, and
/// was answered no — `op.s (op-arg): expected Sp[T = Int64], got Car[V = Int64]` (MEASURED).
#[test]
fn a_spec_parameter_a_provision_leaves_out_is_any_type() {
    let src = r#"
namespace wi80zv8q.out
  import anthill.prelude.{Int64, List, Option}
  import anthill.prelude.Option.{some}
  sort Sp
    sort T = ?
    operation op(s: Self, a: Option[T = T], b: List[T = T]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp
    operation op[M](s: Self, a: Option[T = M], b: List[T = M]) -> Int64 = List.length(b)
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    Sp.op(c, some("x"), ["a", "b", "c"])
end
"#;
    assert_eq!(run_src(src, "wi80zv8q.out.go"), Ok(3));
}

// ── a projection of a wildcard binding ──────────────────────────────────────

/// `Sp` over a carrier whose provision binds `T` to `binding`, the member `pick` written as
/// `member`; `go` is the body of the driver over a `Car` of `Int64`.
fn projected_program(ns: &str, binding: &str, members: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool}}
  sort Other
    sort W = ?
    entity other(w: W)
  end
  sort Sp
    sort T = ?
    operation pick(s: Self, o: s.T) -> Int64
    operation both(s: Self, a: T, b: s.T) -> Int64
    operation get(s: Self) -> s.T
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = {binding}]
    {members}
  end
  operation takes_int(c: Other[W = Int64]) -> Int64 = 41
  operation takes_any[A](c: Other[W = A]) -> Int64 = 41
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 1)
    {go}
end
"#
    )
}

/// The members a row does not look at, so that the provision is whole.
const PICK: &str = "operation pick(s: Self, o: s.T) -> Int64 = 41";
const BOTH: &str = "operation both[P, Q](s: Self, a: Other[W = P], b: Other[W = Q]) -> Int64 = 41";
const GET: &str = "operation get(s: Self) -> s.T = other(w: 1)";

/// A PARAMETER TYPED BY A PROJECTION IS THE CALLER'S TO FIX, so its body may not take it for
/// one instance: `pick(s: Self, o: s.T) = takes_int(o)` is refused, at the bare binding (`T
/// = Other`, whose half of this predates the ticket) and at the wildcard one alike. Left as
/// the projection read it, each loaded and `Sp.pick(x, other(w: "s"))` ran `takes_int` on a
/// `String` one (MEASURED, found by /code-review). CONTROL — the same parameter passed on to
/// an operation that takes any instance, to the spec's own call and back out through `->
/// s.T` runs.
#[test]
fn a_body_may_not_pin_a_parameter_typed_by_a_projection() {
    for (ns, binding) in [("wi80zv8q.j1", "Other"), ("wi80zv8q.j2", "Other[W = ?]")] {
        let pins = format!(
            "operation pick(s: Self, o: s.T) -> Int64 = takes_int(o)\n    {BOTH}\n    {GET}"
        );
        assert_refused_naming(
            &load_errors(&projected_program(ns, binding, &pins, "0")),
            &["takes_int.c (op-arg): expected Other[W = Int64], got Other[W = o.W]"],
            binding,
        );
        let passes = format!(
            "operation pick(s: Self, o: s.T) -> Int64 = takes_any(o)\n    \
             operation both[P, Q](s: Self, a: Other[W = P], b: Other[W = Q]) -> Int64 = \
             Sp.pick(s, b)\n    {GET}"
        );
        let go = "Sp.pick(x, other(w: \"s\")) + Sp.both(x, other(w: 1), other(w: true)) - 40";
        let ns = format!("{ns}c");
        assert_eq!(
            run_src(&projected_program(&ns, binding, &passes, go), &format!("{ns}.go")),
            Ok(42),
            "{binding}"
        );
    }
}

/// EACH PROJECTION OF A WILDCARD BINDING IS AN INSTANCE OF ITS OWN, so a member may not tie
/// one to the parameter beside it: behind `both(s: Self, a: T, b: s.T)` a member typing `a`
/// and `b` by one `W` is refused, and one typing them apart runs over three instances. The
/// rule opened only the variables NO parameter reads, so the `?` that `a: T` reads stood for
/// `b: s.T` too, the tying member was admitted and `Sp.both(x, other(w: "s"), other(w:
/// true))` loaded against a body typed as if the two were one (MEASURED, found by
/// /code-review).
#[test]
fn a_member_may_not_tie_a_projection_to_the_parameter_beside_it() {
    let tied = format!(
        "{PICK}\n    operation both[W](s: Self, a: Other[W = W], b: Other[W = W]) -> Int64 = \
         41\n    {GET}"
    );
    assert_refused_naming(
        &load_errors(&projected_program("wi80zv8q.t1", "Other[W = ?]", &tied, "0")),
        &[
            "its own member 'both' does not fit",
            "parameter 3 (`b: Other[W = ?W]`) takes less than the spec's",
        ],
        "a member tying `a` and `b`",
    );
    let apart = format!("{PICK}\n    {BOTH}\n    {GET}");
    let go = "Sp.both(x, other(w: \"s\"), other(w: true)) + 1";
    assert_eq!(
        run_src(
            &projected_program("wi80zv8q.t2", "Other[W = ?]", &apart, go),
            "wi80zv8q.t2.go"
        ),
        Ok(42)
    );
}

/// THE BODY PICKS A RETURN WRITTEN AT `?`: behind `get(s: Self) -> s.T` at `T = Other[W =
/// ?]`, a member returning through the projection or through the written wildcard packs
/// whichever `Other` it likes, and the caller takes the result for none in particular. The
/// body's return was compared structurally against the declared `?` and refused, `expected
/// Other[W = ?_], got Other[W = String]` (MEASURED) — so the spelling the refusal offers for
/// "any" could be declared and never returned. CONTROL — a consumer asking for one instance
/// is refused at the call, whatever the member packed.
#[test]
fn a_body_packs_a_witness_into_a_return_at_a_wildcard() {
    for (ns, ret) in [("wi80zv8q.k1", "s.T"), ("wi80zv8q.k2", "Other[W = ?]")] {
        let members = format!(
            "{PICK}\n    {BOTH}\n    operation get(s: Self) -> {ret} = other(w: \"s\")"
        );
        let runs = projected_program(ns, "Other[W = ?]", &members, "takes_any(Sp.get(x)) + 1");
        assert_eq!(run_src(&runs, &format!("{ns}.go")), Ok(42), "{ret}");
        let ns = format!("{ns}c");
        let pinned = projected_program(&ns, "Other[W = ?]", &members, "takes_int(Sp.get(x))");
        assert_refused_naming(
            &load_errors(&pinned),
            &["takes_int.c (op-arg): expected Other[W = Int64], got Other[W = ?W]"],
            ret,
        );
    }
}

// ── taken out of a field ────────────────────────────────────────────────────

/// `Box` with a field at `?` and one at `Self`, a holder of a bare `Box` of another sort, and
/// two fields that share a named variable; `ops` are the operations under test.
fn field_program(ns: &str, ops: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Box
    sort T = ?
    entity leaf(v: T)
    entity node(next: Box[T = ?])
    entity same(next: Self)
  end
  sort Holder
    entity hold(item: Box)
  end
  sort Two
    entity two(a: Box[T = ?x], b: Box[T = ?x])
  end
  operation takes_int(b: Box[T = Int64]) -> Int64 = 41
  operation takes_any[A](b: Box[T = A]) -> Int64 = 41
  operation agree[A](p: Box[T = A], q: Box[T = A]) -> Int64 = 41
  {ops}
  operation go() -> Int64 = {go}
end
"#
    )
}

/// A PATTERN BINDER OVER A FIELD LEFT OPEN IS AN INSTANCE OF ITS OWN: what a `node` holds
/// is any `Box`, so the binder that takes it out is one the arm may not take for a `Box` of
/// `Int64` — whether the field wrote `?` or left a foreign sort's slot out. The binder kept
/// the declaration's own variable, which the first use bound: `case node(n) -> takes_int(n)`
/// loaded and ran `takes_int` on a `Box` of `String` (MEASURED; the bare half predates the
/// ticket). CONTROLS — the same binder handed to an operation that takes any `Box` runs,
/// and a field typed `Self` is this instance's, so its binder is taken for one.
#[test]
fn a_binder_over_a_field_left_open_is_an_instance_of_its_own() {
    let peel = |arm: &str| {
        format!(
            "operation peel(b: Box[T = Int64]) -> Int64 =\n    match b\n      case leaf(_) -> \
             0\n      case node(n) -> {arm}\n      case same(m) -> takes_int(m)"
        )
    };
    // The unknown is named by the binder that holds it, as a parameter's is.
    assert_refused_naming(
        &load_errors(&field_program("wi80zv8q.g1", &peel("takes_int(n)"), "0")),
        &["takes_int.b (op-arg): expected Box[T = Int64], got Box[T = n.T]"],
        "a binder over `next: Box[T = ?]`",
    );
    let held = "operation peel(h: Holder) -> Int64 =\n    match h\n      case hold(b) -> takes_int(b)";
    assert_refused_naming(
        &load_errors(&field_program("wi80zv8q.g2", held, "0")),
        &["takes_int.b (op-arg): expected Box[T = Int64], got Box[T = b.T]"],
        "a binder over a bare `item: Box`",
    );
    let any = field_program(
        "wi80zv8q.g3",
        &peel("takes_any(n)"),
        "peel(node(next: leaf(v: \"s\"))) + peel(same(next: leaf(v: 1))) - 40",
    );
    assert_eq!(run_src(&any, "wi80zv8q.g3.go"), Ok(42));
}

/// A VARIABLE TWO FIELDS SHARE IS ONE UNKNOWN FOR BOTH BINDERS OF A PATTERN: `two(a: Box[T
/// = ?x], b: Box[T = ?x])` holds two boxes of one element type, whatever it is — built from
/// two that agree, taken apart as two that agree, and neither taken for a `Box` of `Int64`.
/// The binders kept the declaration's `?x` itself: `agree(p, q)` was refused, `expected a
/// type for 'A', got unconstrained`, and `takes_int(p)` loaded (MEASURED).
#[test]
fn a_variable_two_fields_share_is_one_for_both_binders() {
    let both = |arm: &str| {
        format!("operation both(t: Two) -> Int64 =\n    match t\n      case two(p, q) -> {arm}")
    };
    let agree = field_program(
        "wi80zv8q.h1",
        &both("agree(p, q)"),
        "both(two(a: leaf(v: \"s\"), b: leaf(v: \"t\"))) + 1",
    );
    assert_eq!(run_src(&agree, "wi80zv8q.h1.go"), Ok(42));
    assert_refused_naming(
        &load_errors(&field_program("wi80zv8q.h2", &both("takes_int(p)"), "0")),
        &["takes_int.b (op-arg): expected Box[T = Int64], got Box[T = ?x]"],
        "one of the two binders taken for a `Box` of `Int64`",
    );
    let apart = field_program(
        "wi80zv8q.h3",
        &both("agree(p, q)"),
        "both(two(a: leaf(v: 1), b: leaf(v: \"s\")))",
    );
    assert_refused_naming(
        &load_errors(&apart),
        &["two.b (entity-field): expected Box[T = Int64], got Box[T = String]"],
        "a `two` built from boxes that do not agree",
    );
}

/// A FIELD READ OPENS A NAMED VARIABLE TOO. `t.a` over `a: Box[T = ?x]` is the holder's
/// unknown, as a read of a field written at `?` already was; left as the declaration's
/// variable, `takes_int(t.a)` loaded (MEASURED). CONTROL — the same read handed to an
/// operation that takes any `Box` runs.
#[test]
fn a_field_read_opens_a_named_variable_too() {
    let read = |call: &str| format!("operation read(t: Two) -> Int64 = {call}(t.a)");
    assert_refused_naming(
        &load_errors(&field_program("wi80zv8q.i1", &read("takes_int"), "0")),
        &["takes_int.b (op-arg): expected Box[T = Int64], got Box[T = ?x]"],
        "a read of `a: Box[T = ?x]`",
    );
    let any = field_program(
        "wi80zv8q.i2",
        &read("takes_any"),
        "read(two(a: leaf(v: \"s\"), b: leaf(v: \"t\"))) + 1",
    );
    assert_eq!(run_src(&any, "wi80zv8q.i2.go"), Ok(42));
}

// ── a binding that is not ground, on the carrier-parameter path ─────────────

/// `Rel.mix(a: A, b: B)` — the receiver typed by the spec's CARRIER PARAMETER — at `Car
/// provides Rel[A = Self, B = {binding}]`; `go` calls it over a `Car` of `Int64` and `second`.
fn carrier_param_program(ns: &str, binding: &str, member_b: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool, Pair}}
  import anthill.prelude.Pair.{{pair}}
  sort Other
    sort W = ?
    entity other(w: W)
  end
  sort Rel
    sort A = ?
    sort B = ?
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Rel[A = Self, B = {binding}]
    operation mix{member_b} -> Int64 = 41
  end
  operation generic[X](c: Car[V = X], x: X) -> Int64 = Rel.mix(c, {second})
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    Rel.mix(c, {second}) + 1
end
"#
    )
}

/// A WILDCARD BINDING HOLDS ITS ARGUMENT TO THE SORT IT NAMES. Behind `B = Other[W = ?]` the
/// parameter `b: B` is an `Other` — any one — and an `Int64` is none. The binding, not
/// ground by its own `?`, was skipped with the ones a receiver really leaves open; `B`
/// stayed unbound, the ARGUMENT bound it, and nothing compared the two: `Rel.mix(c, 5)`
/// loaded (MEASURED). The self-receiver path never had the hole — its receiver is checked
/// against `Sp[T = …]` after the argument has said `T`. CONTROL — an `Other` of any element
/// type runs.
#[test]
fn a_wildcard_binding_holds_its_argument_to_the_sort_it_names() {
    let member = "[M](a: Self, b: Other[W = M])";
    for (ns, second, got) in [
        ("wi80zv8q.w1", "5", "Int64"),
        ("wi80zv8q.w2", "car(v: \"s\")", "Car[V = String]"),
    ] {
        let src = carrier_param_program(ns, "Other[W = ?]", member, second);
        assert_refused_naming(
            &load_errors(&src),
            &[&format!("mix.b (op-arg): expected Other[W = ?_], got {got}")],
            second,
        );
    }
    for (ns, second) in [("wi80zv8q.w3", "other(w: \"s\")"), ("wi80zv8q.w4", "other(w: x)")] {
        // `x` is the generic operation's own parameter; `go` has none, so it passes a literal.
        let second_in_go = if second.contains("x)") { "other(w: true)" } else { second };
        let src = carrier_param_program(ns, "Other[W = ?]", member, second)
            .replace(&format!("Rel.mix(c, {second}) + 1"), &format!("Rel.mix(c, {second_in_go}) + 1"));
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42), "{second}");
    }
    // …and the `?` is fresh at each call: one body, two calls, two instances. Bound as the
    // provision's own variable, the first call would have said what the second may pass.
    let twice = carrier_param_program("wi80zv8q.w5", "Other[W = ?]", member, "other(w: 1)").replace(
        "Rel.mix(c, other(w: 1)) + 1",
        "Rel.mix(c, other(w: \"s\")) + Rel.mix(c, other(w: true)) - 40",
    );
    assert_eq!(run_src(&twice, "wi80zv8q.w5.go"), Ok(42));
}

/// A BINDING RESTING ON THE CALLER'S OWN TYPE PARAMETER IS KNOWN, AND IS BOUND. Behind `B =
/// Pair[A = Int64, B = V]`, a receiver `c: Car[V = X]` — `X` the calling operation's
/// parameter — makes `b` a `Pair[A = Int64, B = X]`: as determined as it will ever be. The
/// test at the binding was "holds no variable of any kind", which reads a rigid as still
/// open, so the binding was skipped and `Rel.mix(c, 5)` loaded inside a generic operation
/// (MEASURED; older than this ticket — the same two readings WI-1059 separated at the
/// argument check). CONTROL — the pair the binding asks for runs.
#[test]
fn a_binding_resting_on_the_callers_own_parameter_is_bound() {
    let binding = "Pair[A = Int64, B = V]";
    let member = "(a: Self, b: Pair[A = Int64, B = V])";
    let refused = carrier_param_program("wi80zv8q.x1", binding, member, "5")
        .replace("Rel.mix(c, 5) + 1", "generic(c, 2)");
    assert_refused_naming(
        &load_errors(&refused),
        &["mix.b (op-arg): expected Pair[A = Int64, B = ?X], got Int64"],
        "an `Int64` where the binding is a pair over the caller's parameter",
    );
    let runs = carrier_param_program("wi80zv8q.x2", binding, member, "pair(1, x)")
        .replace("Rel.mix(c, pair(1, x)) + 1", "generic(c, 2) + 1");
    assert_eq!(run_src(&runs, "wi80zv8q.x2.go"), Ok(42));
}

/// WHAT THE RECEIVER LEAVES OPEN IS A FRESH VARIABLE OF THE CALL, AND THE BINDING IS MADE
/// (user, 2026-10-04: "now we open variables, so it should be fresh variables"). Behind
/// `Element = Pair[A = K, B = V]`, a receiver that writes neither `K` nor `V` — a nullary
/// producer's result — or one whose `V` is not inferred yet (`ml(k: 1, v: [])`) still makes
/// `x: Element` a PAIR, and the argument says the rest. The binding used to be skipped
/// wherever it was not fully known, "so that the declaration's variable would not reach a
/// call's types"; the argument then bound `Element` itself and was compared with nothing —
/// `Coll.has(MapLike.mk(), 5)` loaded (MEASURED). CONTROLS — the pair each receiver admits
/// runs, and the one it does not is refused on the slot the receiver did write.
#[test]
fn a_binding_the_receiver_leaves_open_is_bound_at_the_calls_own_variables() {
    let program = |ns: &str, go: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool, Pair, List}}
  import anthill.prelude.Pair.{{pair}}
  sort Coll
    sort C = ?
    sort Element = ?
    operation has(c: C, x: Element) -> Int64
  end
  sort MapLike
    sort K = ?
    sort V = ?
    entity ml(k: K, v: V)
    entity empty
    provides Coll[C = Self, Element = Pair[A = K, B = V]]
    operation has(c: Self, x: Pair[A = K, B = V]) -> Int64 = 21
    operation mk() -> Self = empty
  end
  operation go() -> Int64 = {go}
end
"#
        )
    };
    for (ns, go, names) in [
        ("wi80zv8q.y1", "Coll.has(MapLike.mk(), 5)", vec!["has.x (op-arg): expected Pair[A = ?", "got Int64"]),
        (
            "wi80zv8q.y2",
            "Coll.has(ml(k: 1, v: []), 5)",
            vec!["has.x (op-arg): expected Pair[A = Int64, B = List[T = ", "got Int64"],
        ),
        (
            "wi80zv8q.y3",
            "Coll.has(ml(k: 1, v: []), pair(\"x\", [2]))",
            vec!["has.x (op-arg): expected Pair[A = Int64, B = List[T = ", "got Pair[A = String"],
        ),
    ] {
        assert_refused_naming(&load_errors(&program(ns, go)), &names, go);
    }
    for (ns, go) in [
        ("wi80zv8q.y4", "Coll.has(MapLike.mk(), pair(1, \"s\")) * 2"),
        ("wi80zv8q.y5", "Coll.has(ml(k: 1, v: []), pair(1, [2])) * 2"),
    ] {
        assert_eq!(run_src(&program(ns, go), &format!("{ns}.go")), Ok(42), "{go}");
    }
}
