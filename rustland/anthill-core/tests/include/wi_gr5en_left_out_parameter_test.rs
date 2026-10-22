//! A SPEC PARAMETER A `provides` CLAUSE LEAVES OUT IS THE `?` WRITTEN THERE — `provides Sp[T =
//! V]` is `provides Sp[T = V, K = ?]` — the spec's carrier parameter excepted, which names the
//! provider (decided with the user during WI-20261003-GR5EN). And a call through the spec is at
//! one instance, `Sp[T = V, K = ?k]`: `?k` is one variable of the call, inferred there, which
//! every reading of `K` in the call is — `k: K` and `s.K` alike — and one rigid type in the
//! member, which may not pick it. So a member takes every `K` the provision answers a call at:
//! `op[W](t: Int64, x: W)`, or `x: ?W`, and not `x: Car`.
//!
//! On the parent the two spellings disagreed: the declaration check compared nothing at a
//! left-out `K`, so a member fixing it loaded and a call at another `K` ran it on the wrong type
//! (MEASURED: `field_access: receiver is not an entity (got String)`), where the written `K = ?`
//! was refused; and a call reading `s.K` refused a left-out `K` ("type 'Car' has no member
//! 'K'") while it read a written one afresh at each read, so `Sp.put(c, 40, "x")` behind `put(s:
//! Self, k: s.K, j: s.K)` ran and `put[W](c: Self, k: W, j: W)` was refused.
//!
//! Every row runs both spellings and asserts one verdict for them.
//!
//! BACK-OUTS, measured on one build with each switch:
//! - THE LEFT-OUT PARAMETER WRITTEN AS `?` in the declaration check's σ (`write_left_out_params`)
//!   not called — 5 FAIL: every row whose member fixes the slot, the left-out spelling loading.
//! - THE CALL'S ONE SLOT (`call_slot_member`) not read — 3 FAIL:
//!   [`a_projected_slot_is_one_type_per_call`], [`a_returned_slot_is_the_calls`] and
//!   [`a_lambda_through_a_projected_slot_is_typed_at_the_call`].
//! - THE PROVISION'S ONE VARIABLE READ ONCE in the declaration check (`instance_of` opening it per
//!   read, and a projection of it not counted as a parameter's read) — 3 FAIL: the same three.
//! - THE LEFT-OUT PARAMETER LENT AS `?` by the call's readings of a provision — off a receiver
//!   declared at the carrier, 1 FAILS: [`a_receiver_declared_at_the_carrier_reads_a_left_out_parameter`];
//!   off one declared by the spec, 1 FAILS: [`a_lambda_through_a_projected_slot_is_typed_at_the_call`].
//! - THE CARRIER EXCEPTION READ AS THE SOLE PARAMETER TOO (`spec_carrier_param_or_sole`) — 1
//!   FAILS: [`a_sole_parameter_left_out_is_the_written_question_mark`].
//! - Pass either way by design: a provision that binds `K` to a type, and one whose binding holds
//!   a `?` inside (`K = List[T = ?]`), which reads as before.
use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// The two spellings of one provision.
const SPELLINGS: [(&str, &str); 2] = [("left_out", ""), ("written", ", K = ?")];

/// `Car[V]` providing `Sp[T = {t}{written}]`, with the spec's operation `{spec}` and the member
/// `{member}`; `go` runs `{go}` with `c: Car[V = String]` in scope.
fn program(ns: &str, t: &str, written: &str, spec: &str, member: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Sp
    sort T = ?
    sort K = ?
    operation {spec}
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = {t}{written}]
    operation {member}
  end
  operation go() -> Int64 =
    let c: Car[V = String] = car(v: "s")
    {go}
end
"#
    )
}

/// Both spellings, `T` bound to `t`, run `go` to `expected`.
fn runs_both(name: &str, t: &str, spec: &str, member: &str, go: &str, expected: i64) {
    for (spelling, written) in SPELLINGS {
        let ns = format!("gr5enlo.{name}_{spelling}");
        let src = program(&ns, t, written, spec, member, go);
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(expected), "{name}, {spelling}");
    }
}

/// Both spellings, `T` bound to `t`, are refused, naming `tokens`.
fn refused_both(name: &str, t: &str, spec: &str, member: &str, go: &str, tokens: &[&str]) {
    for (spelling, written) in SPELLINGS {
        let ns = format!("gr5enlo.{name}_{spelling}");
        let src = program(&ns, t, written, spec, member, go);
        assert_refused_naming(&load_errors(&src), tokens, &format!("{name}, {spelling}"));
    }
}

// ── the member is held to every `K` ────────────────────────────────────────────────────────

/// A MEMBER FIXING A LEFT-OUT PARAMETER TAKES LESS. `op(t: Int64, x: Car[V = List[T = Int64]])`
/// behind `op(t: T, x: K)`: a call at `K = String`, which the provision answers, reaches it.
#[test]
fn a_member_fixing_a_left_out_parameter_is_refused() {
    refused_both(
        "fixed",
        "Int64",
        "op(t: T, x: K) -> Int64",
        "op(t: Int64, x: Car[V = List[T = Int64]]) -> Int64 = t",
        "0",
        &["parameter 2 (`x: Car[V = List[T = Int64]]`) takes less than the spec's"],
    );
}

/// … AND A MEMBER GENERIC OVER IT FITS, its parameter named or written `?W`, and runs at any `K`.
#[test]
fn a_member_generic_over_a_left_out_parameter_fits() {
    for member in [
        "op[W](t: Int64, x: W) -> Int64 = t + 1",
        "op(t: Int64, x: ?W) -> Int64 = t + 1",
    ] {
        runs_both("generic", "Int64", "op(t: T, x: K) -> Int64", member, "Sp.op(41, \"s\")", 42);
    }
}

// ── one slot per call ──────────────────────────────────────────────────────────────────────

/// `put(s: Self, k: s.K, j: s.K)` behind a member generic over one `W`.
const PUT: &str = "put(s: Self, k: s.K, j: s.K) -> Int64";

/// ONE `K` PER CALL, READ BY A PROJECTION AS BY THE PARAMETER: the member taking one `W` for
/// both fits, the call reads one `?k` — so it runs at `Int64` and is refused handing it an
/// `Int64` and a `String` — and two calls in one body each have their own.
#[test]
fn a_projected_slot_is_one_type_per_call() {
    let member = "put[W](c: Self, k: W, j: W) -> Int64 = 21";
    runs_both("one_slot", "V", PUT, member, "Sp.put(c, 40, 2) + Sp.put(c, 40, 2)", 42);
    runs_both("two_calls", "V", PUT, member, "Sp.put(c, 40, 2) + Sp.put(c, \"a\", \"b\")", 42);
    refused_both(
        "one_slot_bad",
        "V",
        PUT,
        member,
        "Sp.put(c, 40, \"x\")",
        &["type mismatch in put.j (op-arg): expected Int64, got String"],
    );
}

/// … AND A MEMBER FIXING THE PROJECTED SLOT TAKES LESS.
#[test]
fn a_member_fixing_a_projected_slot_is_refused() {
    refused_both(
        "one_slot_fixed",
        "V",
        PUT,
        "put(c: Self, k: Int64, j: Int64) -> Int64 = k + j",
        "0",
        &["parameter 2 (`k: Int64`) takes less than the spec's"],
    );
}

/// THE RETURN READS THE CALL'S SLOT TOO: `get(s: Self, k: s.K) -> s.K` returns what `k` was
/// given, a caller asking another type of it is refused, and a member fixing it takes less.
#[test]
fn a_returned_slot_is_the_calls() {
    let spec = "get(s: Self, k: s.K) -> s.K";
    let member = "get[W](c: Self, k: W) -> W = k";
    runs_both("ret", "V", spec, member, "Sp.get(c, 41) + 1", 42);
    refused_both(
        "ret_bad",
        "V",
        spec,
        member,
        "let x: String = Sp.get(c, 41)\n    0",
        &["type mismatch in x.annotation (let-binding): expected String, got Int64"],
    );
    refused_both(
        "ret_fixed",
        "V",
        spec,
        "get(c: Self, k: Int64) -> Int64 = k",
        "0",
        &["parameter 2 (`k: Int64`) takes less than the spec's"],
    );
}

/// A SLOT ONLY THE RETURN READS is the caller's as well: the member's `-> List[T = Int64]` fixes
/// a `K` a caller may ask for as a `String` list.
#[test]
fn a_member_fixing_a_slot_only_the_return_reads_is_refused() {
    refused_both(
        "ret_only",
        "V",
        "mk(s: Self) -> List[T = K]",
        "mk(c: Self) -> List[T = Int64] = [1]",
        "0",
        &["the member returns `List[T = Int64]`, which is not a subtype of the spec's"],
    );
}

/// A RECEIVER DECLARED AT THE CARRIER reads the sort's own provisions by agreement, and a
/// left-out parameter lends its `?` there as a written one does: `probe(c: Car[V = String], k:
/// c.K)` loads. It was refused "type 'Car' has no member 'K'" where the written `K = ?` loaded.
#[test]
fn a_receiver_declared_at_the_carrier_reads_a_left_out_parameter() {
    runs_both(
        "unowned",
        "V",
        "put(s: Self, k: s.K) -> Int64",
        "put[W](c: Self, k: W) -> Int64 = 41\n    operation probe(c: Car[V = String], k: c.K) -> Int64 = 1",
        "Car.probe(c, 7) + 41",
        42,
    );
}

/// A LAMBDA TYPED THROUGH THE SLOT is hinted with a variable the call then ties to its one `K`:
/// `lambda (u) -> u + 1` behind `f: (u: s.K) -> Int64` runs, and one reading `u` as a `String`
/// is refused at the call, where `k` says `Int64`. Hinted with the neutral `s.K` where `K` was
/// left out, the first was refused (MEASURED).
#[test]
fn a_lambda_through_a_projected_slot_is_typed_at_the_call() {
    let spec = "put(s: Self, f: (u: s.K) -> Int64, k: s.K) -> Int64";
    let member = "put[W](c: Self, f: (u: W) -> Int64, k: W) -> Int64 = f(k)";
    runs_both("lambda", "V", spec, member, "Sp.put(c, lambda (u) -> u + 1, 41)", 42);
    refused_both(
        "lambda_bad",
        "V",
        spec,
        member,
        "Sp.put(c, lambda (u) -> String.length(u), 41)",
        &["type mismatch in put.k (op-arg): expected String, got Int64"],
    );
}

/// A SOLE PARAMETER NO OPERATION RECEIVES ON is no carrier, and left out it is the `?` too:
/// `provides Tagged` over `tag(n: Int64) -> T` holds `Car`'s `tag(n: Int64) -> Int64` to every
/// `T`. Read as the carrier, it was compared nowhere, and `let s: String = Tagged.tag(1)` ran the
/// member (MEASURED: `type mismatch: expected String, got Int64`).
#[test]
fn a_sole_parameter_left_out_is_the_written_question_mark() {
    for (spelling, written) in [("left_out", ""), ("written", "[T = ?]")] {
        let src = format!(
            r#"
namespace gr5enlo.sole_{spelling}
  import anthill.prelude.{{Int64, String, List}}
  sort Tagged
    sort T = ?
    operation tag(n: Int64) -> T
  end
  sort Car
    entity car(n: Int64)
    provides Tagged{written}
    operation tag(n: Int64) -> Int64 = n
  end
  operation go() -> Int64 =
    let s: String = Tagged.tag(1)
    String.length(s)
end
"#
        );
        assert_refused_naming(
            &load_errors(&src),
            &["the member returns `Int64`, which is not a subtype of the spec's"],
            spelling,
        );
    }
}

// ── controls ───────────────────────────────────────────────────────────────────────────────

/// CONTROL: a provision that binds `K` to a type reads it as that type at every read. Either way
/// by design.
#[test]
fn a_bound_slot_reads_its_binding_control() {
    let ns = "gr5enlo.bound";
    let src = |go: &str| {
        program(
            ns,
            "V",
            ", K = Int64",
            PUT,
            "put(c: Self, k: Int64, j: Int64) -> Int64 = k + j",
            go,
        )
    };
    assert_eq!(run_src(&src("Sp.put(c, 40, 2)"), &format!("{ns}.go")), Ok(42));
    assert_refused_naming(
        &load_errors(&src("Sp.put(c, 40, \"x\")")),
        &["type mismatch in put.j (op-arg): expected Int64, got String"],
        "a bound slot",
    );
}

/// CONTROL: a binding that holds a `?` inside (`K = List[T = ?]`) is read as before, a list of
/// its own at each read — the decision is about a whole parameter left to the call. Either way by
/// design.
#[test]
fn a_binding_holding_a_variable_inside_reads_as_before_control() {
    let ns = "gr5enlo.nested";
    let src = program(
        ns,
        "V",
        ", K = List[T = ?]",
        PUT,
        "put[W, X](c: Self, k: List[T = W], j: List[T = X]) -> Int64 = 42",
        "Sp.put(c, [1], [\"a\"])",
    );
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42));
}
