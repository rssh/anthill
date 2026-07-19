//! WI-764 — a WRITTEN `Relation[T = .., E = ..]` return annotation conforms against the
//! rule citation it describes.
//!
//! The symptom was reported as a binding-ORDER problem: the two sides rendered the same
//! bindings, the declared side always as `E, T` and the citation side always as `T, E`,
//! whichever order the annotation was written in. Instrumenting the comparison showed the
//! order is a FINGERPRINT, not the cause — the two producers key the same slot with
//! DIFFERENT symbols:
//!
//! * a relation VALUE from a rule citation (`assemble_relation_type` →
//!   `sort_type_params_as_pairs`) keys `T` with the sort's CANONICAL param symbol
//!   `anthill.prelude.Relation.T`;
//! * a WRITTEN signature type keys it with a BARE last-segment `T`.
//!
//! `parameterized_compatible_view` matched expected bindings against actual ones by raw
//! SYMBOL IDENTITY, so neither slot was ever found; same-base means no provider fallback,
//! so it rejected. The render order differed for the same reason: `make_entity_term`'s
//! canonicalizer sorts named args by symbol INDEX, and the two symbol sets intern in
//! opposite relative order.
//!
//! That is WI-726's bug exactly, in the sibling direction — WI-726 fixed the UNIFY twin
//! (`unify_parameterized_view`) with a same-base-gated `same_label` match and left the
//! SUBTYPE twin on raw identity. Both now share one `binding_for_param`.
//!
//! NOTE for anyone adding a case here: assert on the EXPECTED side of a mismatch, not the
//! ACTUAL side. The actual/citation side renders identically for a right and a wrong
//! annotation alike, so a test that greps it goes green in exactly the broken state this
//! ticket fixes. Two earlier drafts of the negative controls below did precisely that.

use crate::common::try_load_kb_with;

fn load_errs(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

/// The relation every case below cites: schema `(name: String, age: Int64)`.
const REL: &str = r#"
  import anthill.prelude.{String, Int64, Relation, Error}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
"#;

// ── The ticket's acceptance: BOTH binding orders ──────────────────────────────────

/// The annotation written `E` first. Before the fix this failed with `expected
/// Relation[E = .., T = ..], got Relation[T = .., E = ..]` — two renders of the same type.
#[test]
fn wi764_annotated_relation_return_conforms_written_e_first() {
    let src = format!(
        r#"
namespace test.wi764et
{REL}
  operation src() -> Relation[E = {{Error}}, T = (name: String, age: Int64)] = person_row
end
"#
    );
    let errs = load_errs(&src);
    assert!(
        errs.is_empty(),
        "an explicit `Relation[E = .., T = ..]` return must conform against the rule citation \
         it describes; got: {errs:?}",
    );
}

/// The same annotation written `T` first. Pinned as its own case because the ORIGINAL
/// report read as an ordering defect — and the point is that the surface order never
/// mattered: both orders failed identically before, and both must pass now.
#[test]
fn wi764_annotated_relation_return_conforms_written_t_first() {
    let src = format!(
        r#"
namespace test.wi764te
{REL}
  operation src() -> Relation[T = (name: String, age: Int64), E = {{Error}}] = person_row
end
"#
    );
    let errs = load_errs(&src);
    assert!(
        errs.is_empty(),
        "the same annotation written `T` first must conform too — surface order is not the \
         variable; got: {errs:?}",
    );
}

// ── Non-vacuity: matching by LABEL must not mean matching ANYTHING ────────────────

/// NEGATIVE CONTROL — a guard against FUTURE over-acceptance, not a test of this fix.
///
/// Stated plainly because an earlier draft claimed otherwise: this test passes with the
/// conformance fix reverted too (pre-fix, Relation conformance rejected *everything*, so
/// every `rejects_*` assertion held for the wrong reason). What discriminates the fix are
/// the two `conforms_*` tests above; what this one pins is the other half of the pair —
/// that finding a binding by LABEL rather than by symbol identity still CHECKS its value.
/// A conformance that had instead started SKIPPING the `T` slot (the failure mode WI-726
/// fixed on the unify side, where a missed binding is width-IGNORED rather than rejected)
/// would accept this silently. It must not: `name` is a `String`, not an `Int64`.
///
/// Asserted on the EXPECTED side (`name: Int64`) — see the module note; the actual side
/// renders identically whether the annotation is right or wrong, so it discriminates
/// nothing at all.
#[test]
fn wi764_annotated_relation_return_rejects_a_wrong_schema() {
    let src = format!(
        r#"
namespace test.wi764wrongt
{REL}
  operation src() -> Relation[E = {{Error}}, T = (name: Int64, age: Int64)] = person_row
end
"#
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("expected Relation") && e.contains("(name: Int64, age: Int64)")),
        "a `T` claiming `name: Int64` must be rejected, and the mismatch must name the \
         REJECTED claim — otherwise the label match is skipping the slot rather than \
         checking it; got: {errs:?}",
    );
}

/// The same non-vacuity check with a column the relation does not have: the slot is found,
/// compared, and refused on its CONTENTS rather than on arity.
#[test]
fn wi764_annotated_relation_return_rejects_an_unknown_column() {
    let src = format!(
        r#"
namespace test.wi764wrongcol
{REL}
  operation src() -> Relation[E = {{Error}}, T = (name: String, height: Int64)] = person_row
end
"#
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("expected Relation") && e.contains("height")),
        "a `T` naming a column the relation does not have must be rejected, and the \
         mismatch must name it; got: {errs:?}",
    );
}

/// A param bound TWICE is refused at load — the malformation that made the label match
/// unsound before it was guarded.
///
/// MEASURED, not hypothesised: with the conformance fix in and no duplicate guard,
/// `Relation[T = <right>, T = <wrong>]` loaded with ZERO errors while the SAME two bindings
/// in the opposite order rejected. `binding_for_param` resolves a repeated key first-wins,
/// so a stale correct binding above a new wrong one satisfied the check and the wrong one
/// was never compared — an annotation claiming a schema the typer never verified, decided
/// by writing order. `check_sort_type_args` admitted the duplicate because it only asked
/// whether each key is DECLARED, never whether it appears once.
///
/// Both orders are pinned: the guard is at the load gate, so neither can reach conformance.
#[test]
fn wi764_a_type_parameter_bound_twice_is_refused() {
    for (case, binding) in [
        ("right_then_wrong", "T = (name: String, age: Int64), T = (name: Int64, age: Int64)"),
        ("wrong_then_right", "T = (name: Int64, age: Int64), T = (name: String, age: Int64)"),
    ] {
        let src = format!(
            r#"
namespace test.wi764dup{case}
{REL}
  operation src() -> Relation[{binding}, E = {{Error}}] = person_row
end
"#
        );
        let errs = load_errs(&src);
        assert!(
            errs.iter().any(|e| e.contains("more than once")),
            "`Relation[{binding}]` binds `T` twice and must be refused at load, in EITHER \
             order — first-wins silently accepts whichever copy is written first; got: {errs:?}",
        );
    }
}

/// A PARTIAL annotation must not bind one slot twice.
///
/// `unroll_annotation_with_inferred` merges what the annotation writes with what the value
/// infers, and matched the two by raw identity — but the annotation writes a BARE `E` while
/// the value carries the canonical `anthill.prelude.Relation.E`. The miss took the "not
/// present, append it" arm, so `let r : Relation[E = {Error}] = person_row` built
/// `Relation[T = .., E = .., E = ..]` from ordinary source. Measured before being fixed: the
/// duplicate was visible in the render of any mismatch mentioning that type.
///
/// Pinned via a deliberate mismatch, because the merged type is otherwise internal: the
/// `-> Int64` return is wrong, and the diagnostic prints what `r` actually is. Counting `E`
/// occurrences is the assertion — a single `contains` would pass either way.
#[test]
fn wi764_a_partial_annotation_does_not_duplicate_a_slot() {
    let src = format!(
        r#"
namespace test.wi764partial
{REL}
  operation use_it() -> Int64 =
    let r : Relation[E = {{Error}}] = person_row
    r
end
"#
    );
    let errs = load_errs(&src);
    let rendered = errs.iter().find(|e| e.contains("got Relation[")).unwrap_or_else(|| {
        panic!("expected the `-> Int64` mismatch to render `r`'s type; got: {errs:?}")
    });
    assert_eq!(
        rendered.matches("E = ").count(),
        1,
        "the merged type must bind `E` exactly once — the annotation's bare `E` and the \
         value's canonical `Relation.E` name ONE slot; got: {rendered}",
    );
}

// ── What the fix unblocks — and what it does NOT ──────────────────────────────────

/// The shape WI-764 was filed FROM: a distribute-dot projection taken directly off a CALL
/// RESULT, with no intervening `let`. It could not be written at all while an annotated
/// `Relation` return did not conform, because the call being projected needs that return.
///
/// It now types, and the projection is REAL rather than incidentally accepted: the columns
/// are projected in the OPPOSITE order to the source schema, so the declared
/// `(age: Int64, name: String)` conforms only if the projection actually re-keyed the
/// schema — a fall-through to ordinary tuple typing (a tuple of two independent
/// single-column relations) does not produce this type.
///
/// FALSIFIED PREDICTION, recorded so the next reader does not re-derive it. WI-732's
/// hardening commit (9be1f834) called its new unresolvable-receiver branch "unreachable by
/// measurement, and therefore untested" and named THIS ticket as the blocker — the
/// reasoning being that a projection off a call result would reach it once the annotation
/// conformed. It does not: that branch fires only when `projection_receiver_type` cannot
/// resolve the receiver, and a call result resolves fine, which is why this LOADS instead
/// of raising. Unblocking WI-764 did not make it reachable. (Measured for THIS shape only —
/// no claim is made about others.) The second assertion is the tripwire: if that diagnostic
/// ever does fire here, the branch has finally acquired a test and WI-732's comment is stale.
#[test]
fn wi764_projection_off_a_call_result_types_and_reorders() {
    let src = format!(
        r#"
namespace test.wi764proj
{REL}
  operation src() -> Relation[T = (name: String, age: Int64), E = {{Error}}] = person_row
  operation proj() -> Relation[T = (age: Int64, name: String), E = {{Error}}] = src().(age, name)
end
"#
    );
    let errs = load_errs(&src);
    assert!(
        !errs.iter().any(|e| e.contains("receiver's type cannot be resolved here")),
        "WI-732's unresolvable-receiver diagnostic must not fire for a call-result receiver \
         (it resolves); got: {errs:?}",
    );
    assert!(
        errs.is_empty(),
        "a distribute-dot projection directly off a call result must type, and must project \
         the re-keyed schema; got: {errs:?}",
    );
}
