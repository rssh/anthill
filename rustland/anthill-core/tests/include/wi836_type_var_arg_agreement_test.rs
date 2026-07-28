//! WI-836 — two arguments that SHARE one type variable are checked against each
//! other.
//!
//! Measured on the parent commit: `same[X](a: List[T = X], b: List[T = X])`
//! applied to a `List[Int64]` and a `List[String]` LOADED CLEAN. Every generic
//! multi-argument operation silently accepted heterogeneous calls.
//!
//! ONE LOCUS, and it is a WALK DEPTH. `validate_arg_against_param` (the WI-385
//! argument/field conformance check, shared by the operation-call, function-value
//! and entity-constructor sites) resolves both sides through σ with `walk_view`,
//! which follows only the HEAD var / sort-alias chain — it stops at a `Term::Fn`.
//! So a type variable NESTED inside a sort application survived the walk, the
//! groundness gate read the param as still-polymorphic, and the check SKIPPED.
//! The two spellings that hit it are the two this file pins: an OP type param
//! (`List[T = X]`) and a sort's OWN params WRITTEN OUT (`Box[T = T, O = O]`).
//!
//! WHY IT HID — the three neighbouring checks all fire, so the area looked
//! covered, and each is a control below:
//!   * a param typed with a BARE variable (`a: X, b: X`) IS caught — the variable
//!     is the head, so the shallow walk resolves it;
//!   * the RETURN position IS caught — it resolves DEEPLY
//!     (`resolve_type_deep_value`), which is exactly the difference;
//!   * an argument list constraining `X` nowhere IS loud
//!     (`UnconstrainedTypeParam`).
//! Binding happened and conformance happened; only the re-check of a LATER
//! argument against the ALREADY-BOUND variable was missing. Proposal 058 §4.7
//! read a RETURN-position probe as evidence that the ARGUMENT position was
//! checked; §5.3's `SortedSet` driver rests on the argument one.
//!
//! NOT fixed by consulting the arg-unify loops' verdict instead: those discard
//! `unify_types`' boolean deliberately (WI-367/WI-379 depend on a failed unify
//! against an already-pinned slot being a silent no-op), so the conformance site
//! is the one that must decide it.

use crate::common::{interp_for, try_load_kb_with};

/// Assert the program is refused at LOAD by a diagnostic containing every needle.
/// The single "must not load" spelling in this file — asserting on the MESSAGE and
/// not merely on the refusal matters here, because the defect was a check that
/// reported NOTHING and a count-only assertion would pass on a fix that rejected
/// the program for an unrelated reason.
fn assert_refused_with(src: &str, needles: &[&str], why: &str) {
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("must NOT load: {why}"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| needles.iter().all(|n| e.contains(n))),
        "{why}; got: {errs:?}",
    );
}

/// The conflict shape: refused naming BOTH conflicting bindings.
fn assert_refused_naming(src: &str, expected: &str, got: &str) {
    let wanted = format!("expected {expected}, got {got}");
    assert_refused_with(
        src,
        &["type mismatch", &wanted],
        &format!("rejection must be a type mismatch reading `{wanted}`"),
    );
}

fn eval_int(src: &str, op: &str) -> i64 {
    // A FRESH interpreter per case: after any trapped call, reusing one makes
    // every later call return a bogus `Internal(...)` that reads as a second bug.
    match interp_for(src).call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// The op-level type param, in the two forms the ticket measured separately —
/// the bracket INFERRED from the arguments and the bracket SEEDED explicitly.
/// Both are asserted because a fix that only re-checked what inference had bound
/// would leave the seeded form open, and the ticket measured them as behaving
/// identically (both clean) before.
const SAME_PRELUDE: &str = r#"
  import anthill.prelude.{List, Int64, String}
  import anthill.prelude.List.{nil}
  operation li() -> List[T = Int64] = nil()
  operation ls() -> List[T = String] = nil()
  operation same[X](a: List[T = X], b: List[T = X]) -> Int64 = 1
"#;

/// THE HEADLINE. `X` is pinned to `Int64` by the FIRST argument; the second is a
/// `List[String]` and nothing objected.
#[test]
fn two_arguments_sharing_an_op_type_param_must_agree() {
    assert_refused_naming(
        &format!(
            "namespace test.wi836.infer\n{SAME_PRELUDE}\
             \n  operation go() -> Int64 = same(li(), ls())\nend\n"
        ),
        "List[T = Int64]",
        "List[T = String]",
    );
}

/// The same program with the 042 bracket written out. This is not an
/// inference-only gap — with `X` pinned by the caller the second argument still
/// went unchecked.
#[test]
fn an_explicitly_seeded_bracket_does_not_exempt_the_later_argument() {
    assert_refused_naming(
        &format!(
            "namespace test.wi836.seeded\n{SAME_PRELUDE}\
             \n  operation go() -> Int64 = same[X = Int64](li(), ls())\nend\n"
        ),
        "List[T = Int64]",
        "List[T = String]",
    );
}

/// A sort declaring `sort T = ?` and `sort O = ?`, its `union`'s parameter type
/// supplied by the caller. This is the shape proposal 058 §5.3's `SortedSet` driver
/// needs: a `union` of two sets ordered by DIFFERENT comparators must be a type
/// error, and `O` is where the comparator rides.
///
/// Parameterized on the param spelling rather than copied per case, so that the ONE
/// varying token is the visible difference between this ticket's shape
/// (`Box[T = T, O = O]`, written out) and control (d)'s (`Box`, bare) — which is
/// control (d)'s entire point.
fn box_sort(union_param: &str) -> String {
    format!(
        r#"
  import anthill.prelude.{{Int64}}
  sort Q
    entity q
  end
  sort R
    entity r
  end
  sort Box
    sort T = ?
    sort O = ?
    entity box(v: T)
    operation union(a: {union_param}, b: {union_param}) -> {union_param} = a
  end
  operation mkq() -> Box[T = Int64, O = Q] = Box.box(1)
  operation mkr() -> Box[T = Int64, O = R] = Box.box(1)
"#
    )
}

/// The written-out spelling, which is this ticket's.
fn box_written() -> String {
    box_sort("Box[T = T, O = O]")
}

#[test]
fn two_arguments_sharing_a_written_sort_param_must_agree() {
    assert_refused_naming(
        &format!(
            "namespace test.wi836.sortparam\n{}\
             \n  operation go() -> Box[T = Int64, O = Q] = Box.union(mkq(), mkr())\nend\n",
            box_written()
        ),
        "Box[T = Int64, O = Q]",
        "Box[T = Int64, O = R]",
    );
}

/// The ENTITY-FIELD channel of the same check — `validate_arg_against_param` is
/// shared by the constructor site, so the two-field shape has the identical hole
/// and must close with it. Asserted separately because sharing a helper is not
/// evidence that both callers reach the changed line.
///
/// The fields must be written with `Pair2`'s OWN params (`Box[T = T, O = O]`), not
/// with concrete types: a field typed `Box[T = Int64, O = Q]` carries no variable,
/// so the shallow walk already read it as ground and the mismatch was ALREADY
/// caught — that spelling would assert nothing about this ticket.
#[test]
fn two_entity_fields_sharing_a_written_sort_param_must_agree() {
    assert_refused_naming(
        &format!(
            "namespace test.wi836.field\n{}\
             \n  sort Pair2\
             \n    sort T = ?\
             \n    sort O = ?\
             \n    entity both(l: Box[T = T, O = O], r: Box[T = T, O = O])\
             \n  end\
             \n  operation go() -> Pair2[T = Int64, O = Q] = Pair2.both(mkq(), mkr())\nend\n",
            box_written()
        ),
        "Box[T = Int64, O = Q]",
        "Box[T = Int64, O = R]",
    );
}

/// The FUNCTION-VALUE channel — the third caller family of the shared checker
/// (`check_apply_iter`'s Path 2, applying a function VALUE rather than a named
/// operation) — is pinned only in its VARIABLE-FREE form, which WI-792 already
/// covered. Stated rather than left as a silent omission, because the entity-field
/// case above argues that sharing a helper is not evidence both callers reach the
/// changed line, and that argument applies here too.
///
/// MEASURED, not assumed: a variable-bearing slot at this path has no surface
/// witness. The slot types come from the applied VALUE's arrow, whose type
/// variables are either already concrete (this test) or an enclosing operation's /
/// sort's parameters — rigidified in the body (the WI-392 skolems), so the
/// application's own σ never binds them and the gate correctly defers.
/// `let f = same` does not reach the path either: a `let`-bound operation
/// reference is refused earlier with `expected known operation or arrow-typed
/// value`. If that changes, this becomes a real witness and should be written.
#[test]
fn a_function_value_application_still_checks_its_slots() {
    assert_refused_naming(
        r#"
namespace test.wi836.fnvalue
  import anthill.prelude.{List, Int64, String}
  import anthill.prelude.List.{nil}
  operation li() -> List[T = Int64] = nil()
  operation ls() -> List[T = String] = nil()
  operation same(a: List[T = Int64], b: List[T = Int64]) -> Int64 = 1
  operation take(f: (a: List[T = Int64], b: List[T = Int64]) -> Int64) -> Int64
    = f(li(), ls())
  operation go() -> Int64 = take(same)
end
"#,
        "List[T = Int64]",
        "List[T = String]",
    );
}

/// POSITIVE CONTROL, and the one that keeps the fix from being "refuse every
/// generic multi-argument call": AGREEING arguments still load — and EVALUATE, in
/// both the inferred and the seeded form. Driven rather than load-asserted
/// because the whole defect class here is invisible at load.
#[test]
fn agreeing_arguments_still_apply() {
    let src = r#"
namespace test.wi836.ok
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{nil, cons}
  operation li() -> List[T = Int64] = cons(1, nil())
  operation lj() -> List[T = Int64] = cons(2, nil())
  operation same[X](a: List[T = X], b: List[T = X]) -> Int64 = 7
  operation drive() -> Int64 = same(li(), lj())
  operation drive_seeded() -> Int64 = same[X = Int64](li(), lj())
end
"#;
    for op in ["drive", "drive_seeded"] {
        assert_eq!(eval_int(src, &format!("test.wi836.ok.{op}")), 7, "{op}");
    }
}

/// POSITIVE CONTROL for the sort-level shape: `union` at ONE instance still
/// loads and evaluates. The deep walk resolves the written `Box[T = T, O = O]`
/// against σ, so a fix that resolved it WRONG would break this, not merely fail
/// to reject the case above.
#[test]
fn a_sort_param_call_at_one_instance_still_applies() {
    let src = format!(
        "namespace test.wi836.sortok\n{}\
         \n  operation drive() -> Int64 = Box.union(mkq(), mkq()).v\nend\n",
        box_written()
    );
    assert_eq!(eval_int(&src, "test.wi836.sortok.drive"), 1);
}

/// CONTROL (a) — a variable-FREE param mismatch was ALREADY caught, and still is.
/// It shares the diagnostic this ticket now reaches, so it pins that the fix did
/// not move the existing message.
#[test]
fn a_variable_free_param_mismatch_is_still_caught() {
    assert_refused_naming(
        &format!(
            "namespace test.wi836.ctla\n{}\
             \n  operation takeR(b: Box[T = Int64, O = R]) -> Int64 = 1\
             \n  operation go() -> Int64 = takeR(mkq())\nend\n",
            box_written()
        ),
        "Box[T = Int64, O = R]",
        "Box[T = Int64, O = Q]",
    );
}

/// CONTROL (b) — the RETURN position. The variable DOES bind from argument 1 and
/// the return IS checked against it; that is why the argument hole hid, and it is
/// the exact probe proposal 058 §4.7 cited. The diagnostic must stay at
/// `go.return`, not migrate to an argument.
#[test]
fn the_return_position_still_reports_the_bound_variable() {
    let src = r#"
namespace test.wi836.ctlb
  import anthill.prelude.{List, Int64, String}
  import anthill.prelude.List.{nil}
  operation li() -> List[T = Int64] = nil()
  operation idbox[X](a: List[T = X]) -> List[T = X] = a
  operation go() -> List[T = String] = idbox(li())
end
"#;
    assert_refused_with(
        src,
        &["go.return", "expected List[T = String], got List[T = Int64]"],
        "the return-position check must still own this",
    );
}

/// CONTROL (c) — an argument list that constrains `X` NOWHERE stays loud, and
/// stays the `UnconstrainedTypeParam` message rather than degrading into a
/// mismatch against some accidentally-resolved type.
#[test]
fn an_unconstrained_type_param_is_still_its_own_diagnostic() {
    let src = r#"
namespace test.wi836.ctlc
  import anthill.prelude.{Int64}
  operation pick[X](n: Int64) -> Int64 = n
  operation go() -> Int64 = pick(1)
end
"#;
    assert_refused_with(
        src,
        &["expected a type for 'X', got unconstrained"],
        "unconstrained must keep its own diagnostic",
    );
}

/// KNOWN GAP, pinned so it is visible rather than assumed closed — and inverted
/// when it closes, the way WI-792 inverted WI-791's.
///
/// Two ARROW-typed arguments sharing one type variable are still NOT checked
/// against each other: this loads clean, `f` pinning `X := Int64` and `g` handing
/// over a `(String) -> Int64`. The deep walk is deliberately NOT applied when
/// either side is callable — see `validate_arg_against_param` — because making a
/// callback read as ground routes it from the component-wise arrow checkers to
/// the whole-type `types_compatible`, which REFUSES the `Function[A = tuple]`
/// against a 2-parameter eta arrow that WI-775/WI-792 settled must be accepted
/// (measured: 5 cases across wi424/wi784/wi787 flipped to refused). Closing this
/// means teaching `arrow_compatible_view` the `Function`-states-no-arity rule,
/// which is a change to who OWNS arrow conformance, not a walk depth.
#[test]
fn known_gap_two_callback_arguments_sharing_a_type_var_are_not_checked() {
    let src = r#"
namespace test.wi836.gap
  import anthill.prelude.{Int64, String}
  operation fi(x: Int64) -> Int64 = x
  operation fs(x: String) -> Int64 = 1
  operation both[X](f: (x: X) -> Int64, g: (x: X) -> Int64) -> Int64 = 1
  operation go() -> Int64 = both(fi, fs)
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "KNOWN GAP: heterogeneous callback arguments still load — invert this when closed",
    );
}

/// CONTROL (d) — the BARE sort-ref spelling of the same conflict is owned by
/// WI-374's member tie (`enforce_member_tie`), which runs BEFORE this check and
/// reads σ's recorded contradictions. It stays that diagnostic: the written-out
/// spelling reached this ticket's hole precisely because a nested conflict never
/// attempts a rebind, so it records no contradiction for the member tie to see.
/// Pinned so the two checks are not later collapsed on the assumption that either
/// one covers both spellings.
#[test]
fn the_bare_sort_ref_spelling_stays_with_the_member_tie() {
    // The SAME program as `two_arguments_sharing_a_written_sort_param_must_agree`,
    // differing in exactly one token — `Box` where that one writes
    // `Box[T = T, O = O]` — so the spelling is the whole variable under test.
    assert_refused_with(
        &format!(
            "namespace test.wi836.ctld\n{}\
             \n  operation go() -> Box[T = Int64, O = Q] = Box.union(mkq(), mkr())\nend\n",
            box_sort("Box")
        ),
        &["op-type-params", "consistent bindings for the sort's shared type parameter"],
        "the bare spelling stays WI-374's member tie",
    );
}
