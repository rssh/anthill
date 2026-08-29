//! WI-20260829-9TGP7 — a BRANCHING expression (`match` / `if`) whose expected type is an
//! UNBOUND INFERENCE VARIABLE was refused outright.
//!
//! THE SHAPE. `xs.map(lambda r -> match r case row(x, f) -> x)` →
//! `type mismatch in match.rule (rule): expected ?Dst, got Int64`. `map[Dst, EffP]`'s
//! result parameter is free at the call, so the callback's body is visited with `?Dst` as
//! its top-down hint. Most body forms IGNORE that hint — a field dot returns `Int64` and
//! `Dst` is bound above, when the lambda's arrow unifies with the declared
//! `(x: Element) -> Dst`. `compute_branch_join_type` is one of the few that ENFORCES it,
//! and it enforced it with [`types_compatible`], which has no arm for a bare variable at
//! all: `type_dispatch_name_view` answers `None` for a variable head (deliberately,
//! WI-1079 — the structural arms are not where a variable is decided), so the subtype
//! relation fell to its `_ => false` and read an UNCONSTRAINED expectation as a MISMATCH.
//!
//! NOT THE CALLBACK BINDER, and that is what separates this from WI-20260828-N2FHM one
//! operation over. `Element` grounds fine — `map / field dot` was green throughout — and
//! `?Dst` failed anyway. The two are independent, which is the open question
//! WI-20260829-9TGP7 asked and `typer_capability_matrix_test`'s sweep answered.
//!
//! NOT ABOUT `map` EITHER, though every red cell named it — and the reason is MEASURED,
//! by printing every `compute_branch_join_type` call's expectation and its head. Over the
//! four programs, the only rows that differ between them are:
//!
//!   xs.map(0, lambda r -> match …)         expected `?Dst`  as FLEXVAR   ← the defect
//!   xs.foldLeft(0, lambda (acc, r) -> …)   expected `Int64` as SortRef
//!   pick[Q9](x, y, b) = if b then x else y expected `?Q9`   as SKOLEM, branches ?Q9/?Q9
//!   bad[Q9](x, b)     = if b then x else 1 expected `?Q9`   as SKOLEM, branches ?Q9/Int64
//!
//! So `foldLeft`'s callback body is never checked against `Acc` at all: the seed `0`
//! grounds it to `Int64` BEFORE the callback is visited, which is why a result parameter
//! is not the discriminator (and `filter`'s callback returns a ground `Bool` for the same
//! reason). `map` is simply the combinator whose result parameter is still free at the
//! point the callback body is visited.
//!
//! AND THE LAST TWO ROWS ARE THE `Skolem` BOUNDARY, measured rather than assumed. A
//! declared type parameter arrives as a `Skolem`, not a `FlexVar` (`rigidify_op_type_-
//! params`, WI-392: an operation's own `[T]` is rigidified for its body check). The
//! conformance loop therefore still RUNS for it — `?Q9` vs `?Q9` passes on the interned-
//! term identity `types_compatible` opens with, and `?Q9` vs `Int64` is refused, which is
//! the correct answer for a parameter the CALLER picks. Excluding `Skolem` from
//! `expected_is_unconstraining` is what keeps that refusal;
//! `a_rigid_expectation_still_refuses` is its row.
//!
//! THE SECOND HALF NOTHING HAD ASKED ABOUT: `if` is the other construct routed through
//! `compute_branch_join_type`, and `xs.map(lambda r -> if r.flag then 1 else 2)` failed
//! identically. The capability matrix carried no `if` body form; it does now.
//!
//! WHAT FAILS WHEN THE FIX IS BACKED OUT (measured, by narrowing
//! `expected_is_unconstraining` to `TypeVar` alone — a `false`-returning stub would
//! neutralize the `type_var` half too, which is not this change):
//!
//!   * 4 of the 6 tests here: `a_match_arm_grounds_a_free_result_parameter`,
//!     `an_if_body_grounds_a_free_result_parameter`,
//!     `branch_types_that_clash_are_still_refused` (its arm-clash message is in front of
//!     the `?Dst` refusal) and `the_branch_join_reaches_the_result_type`. The two that
//!     hold are `a_field_dot_body_is_the_control` and `a_rigid_expectation_still_refuses`
//!     — BY DESIGN, one because a field dot never enforces the hint, one because a
//!     `Skolem` is a REAL bound this change deliberately leaves enforced;
//!   * `typer_capability_matrix_test::sweep_map` — and the failure names exactly the 6
//!     cells, `{dot, unqualified, qualified}` x `{match destructure, if}`. Every other
//!     host's sweep, and `a_label_parameterized_receiver_changes_no_verdict`, hold;
//!   * `guardians_test::an_agent_can_inline_the_body_projection`, alone among that file's
//!     36 tests.
//!
//! THE CONTROL WAS WRONG ONCE AND THE BACK-OUT IS WHAT CAUGHT IT: the field-dot control
//! first lived in [`SRC`] beside the two arms, so a back-out that stopped the file loading
//! failed it too. It has its own program now ([`CONTROL_SRC`]) — a control sharing a
//! fixture with the arms is a second arm.

use crate::common::{interp_for, list_ints, try_load_kb_with};

/// One two-field entity, one list of them, and the two BRANCHING projections under test —
/// the field-dot control has its own program, see [`CONTROL_SRC`]. The
/// operations return a `List`, so `collect` materializes `map`'s lazy `MappedStream` —
/// consuming it EAGERLY is WI-20260829-N01PY's subject and not this one, so every
/// spelling here goes through `collect` and none of them asks that question.
const SRC: &str = r#"
namespace wi9tgp7
  import anthill.prelude.{List, Int64, Bool, Iterable, FiniteCollection}
  import anthill.prelude.Iterable.{map}
  import anthill.prelude.FiniteCollection.{collect}
  sort Row
    import anthill.prelude.{Int64, Bool}
    entity row(a: Int64, flag: Bool)
  end
  import wi9tgp7.Row.{row}

  operation rows() -> List[T = Row] = [row(a: 1, flag: true), row(a: 2, flag: false)]

  -- THE REGRESSION: a match arm's type must reach `map`'s free `Dst`.
  operation viaMatch() -> List[T = Int64] =
    collect(rows().map(lambda r -> match r case row(x, f) -> x))

  -- The other branching construct, through the same checked-mode path.
  operation viaIf() -> List[T = Int64] =
    collect(rows().map(lambda r -> if r.flag then 10 else 20))

end
"#;

/// THE CONTROL'S OWN PROGRAM, and it must not share [`SRC`] — which the first cut did, and
/// the back-out measured the mistake: with `viaMatch` in the same file NOTHING loads, so
/// the control failed too and would have "measured" the change while asking a question the
/// change cannot answer. A control that shares a fixture with the arms is a second arm.
const CONTROL_SRC: &str = r#"
namespace wi9tgp7ctl
  import anthill.prelude.{List, Int64, Bool, Iterable, FiniteCollection}
  import anthill.prelude.Iterable.{map}
  import anthill.prelude.FiniteCollection.{collect}
  sort Row
    import anthill.prelude.{Int64, Bool}
    entity row(a: Int64, flag: Bool)
  end
  import wi9tgp7ctl.Row.{row}
  operation rows() -> List[T = Row] = [row(a: 1, flag: true), row(a: 2, flag: false)]
  operation viaFieldDot() -> List[T = Int64] =
    collect(rows().map(lambda r -> r.a))
end
"#;

fn drive_in(src: &str, op: &str) -> Vec<i64> {
    // A FRESH interpreter per call — a reused one returns a bogus `Internal` after any
    // trapped call, which reads as an unrelated second failure.
    let mut interp = interp_for(src);
    let v = interp
        .call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"));
    list_ints(&v)
}

fn drive(op: &str) -> Vec<i64> {
    drive_in(SRC, op)
}

/// THE TICKET. Not "it loads" — the arm's VALUE must come out, which is the only thing
/// that says `Dst` bound to what the arm actually returns rather than to some wildcard
/// the refusal was replaced by.
#[test]
fn a_match_arm_grounds_a_free_result_parameter() {
    assert_eq!(
        drive("wi9tgp7.viaMatch"),
        vec![1, 2],
        "the match arm projects `a`, so `Dst` is Int64 and the mapped list is the `a`s",
    );
}

/// The half no table had asked about. `if` and `match` share
/// `compute_branch_join_type`'s checked mode, so one fix closes both — and one
/// regression would reopen both.
#[test]
fn an_if_body_grounds_a_free_result_parameter() {
    assert_eq!(drive("wi9tgp7.viaIf"), vec![10, 20]);
}

/// CONTROL — PASSES EITHER WAY BY DESIGN. A field dot returns its type and ignores the
/// expected hint entirely, so it never reached the refusal. Its presence is what says the
/// callback BINDER was never the problem: `r` is typed well enough to project from,
/// before and after.
#[test]
fn a_field_dot_body_is_the_control() {
    assert_eq!(drive_in(CONTROL_SRC, "wi9tgp7ctl.viaFieldDot"), vec![1, 2]);
}

/// THE FIX MUST NOT HAVE DELETED THE CHECK. Branch types that genuinely have no common
/// supertype are still a type error under a FREE result parameter — the arm that reports
/// it (`(clash, Some(exp))`) was UNREACHABLE before, because the per-branch loop refused
/// every branch first, so this row is new behaviour rather than a preserved one.
#[test]
fn branch_types_that_clash_are_still_refused() {
    let src = r#"
namespace wi9tgp7clash
  import anthill.prelude.{List, Int64, Bool, Iterable}
  import anthill.prelude.Iterable.{map}
  sort Row
    import anthill.prelude.{Int64, Bool}
    entity row(a: Int64, flag: Bool)
  end
  import wi9tgp7clash.Row.{row}
  operation cell(xs: List[T = Row]) -> Int64 =
    let s = xs.map(lambda r -> if r.flag then 1 else r)
    42
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_else(|| {
        panic!("`if b then 1 else r` has no common supertype and must be refused")
    });
    assert!(
        errs.iter().any(|e| e.contains("expected Int64") && e.contains("got Row")),
        "expected the branch clash, reported against the branch that breaks the join; \
         got: {errs:#?}",
    );
}

/// THE OTHER VARIABLE FORM IS A REAL BOUND, and this is the row that says the fix
/// distinguishes them. A declared type parameter / a rigidified binder unifies with
/// nothing but itself, so a branch that does not match it must still be refused —
/// `expected_is_unconstraining` names `TypeVar` and `FlexVar` and deliberately omits
/// `Skolem`.
///
/// PASSES EITHER WAY BY DESIGN. It is here to pin the boundary, not to measure the change:
/// the loop refuses it either way, because `Skolem` is not in the predicate. What would
/// fail is a repair that made every variable expectation a wildcard — which is the obvious
/// shape of this fix and the wrong one. Measured: the expectation here is `?Q9` classified
/// as `TypeHead::Skolem`, against branches `?Q9` and `Int64`.
#[test]
fn a_rigid_expectation_still_refuses() {
    let src = r#"
namespace wi9tgp7rigid
  import anthill.prelude.{Bool, Int64}
  operation bad[T](x: T, b: Bool) -> T = if b then x else 1
  -- CONTROL for the control: both branches at the rigid parameter still load, so the row
  -- above is about the Int64 and not about a Skolem expectation refusing everything.
  operation pick[T](x: T, y: T, b: Bool) -> T = if b then x else y
end
"#;
    let errs = try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("`Int64` is not `T`, and a caller picks `T`"));
    assert!(
        errs.iter().any(|e| e.contains("if.rule") && e.contains("got Int64")),
        "expected the rigid type parameter to refuse the Int64 branch; got: {errs:#?}",
    );
    // EXACTLY ONE, and this is what makes `pick` a control rather than decoration (found
    // by /code-review). The `any` above is satisfied by `bad`'s error alone, so a change
    // that made a `Skolem` expectation refuse EVERY branch — `pick` included — would add a
    // second error, leave the `any` matching, and keep this test green while the sentence
    // it exists to assert had become false. Measured: 1 error today.
    assert_eq!(
        errs.len(),
        1,
        "`pick` must load: a Skolem expectation bounds its branches, it does not refuse          them all. got: {errs:#?}",
    );
}

/// A BRANCHING EXPRESSION UNDER A FREE PARAMETER MUST KEEP ITS PRECISE TYPE, not collapse
/// to the variable it was checked against. `compute_branch_join_type`'s `(no clash,
/// Some(exp))` arm returns `exp` when the join does not conform to it — which for a bare
/// `?Dst` is always, since `types_compatible` has no variable arm — so without the second
/// half of the fix `Dst` would bind to a still-free variable and the mapped element type
/// would be lost.
///
/// Measured through a DELIBERATE mismatch, because the inferred type is not otherwise
/// observable from a test: the diagnostic must name `MappedStream[T = Int64, …]`. A
/// `T = ?Dst` there would be the collapse.
#[test]
fn the_branch_join_reaches_the_result_type() {
    let src = r#"
namespace wi9tgp7precise
  import anthill.prelude.{List, Int64, Bool, Iterable}
  import anthill.prelude.Iterable.{map}
  sort Row
    import anthill.prelude.{Int64, Bool}
    entity row(a: Int64, flag: Bool)
  end
  import wi9tgp7precise.Row.{row}
  operation cell(xs: List[T = Row]) -> Int64 =
    xs.map(lambda r -> match r case row(x, f) -> x)
end
"#;
    let errs = try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("a MappedStream is not an Int64"));
    assert!(
        errs.iter().any(|e| e.contains("MappedStream[T = Int64")),
        "the match arm's Int64 must reach the call's result type; got: {errs:#?}",
    );
}
