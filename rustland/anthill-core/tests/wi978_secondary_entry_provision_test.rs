//! WI-978 — a spec claim written in a SECONDARY ENTRY (proposal 059: a
//! `namespace X` block at the address of a sort `X`) must carry the same
//! load-time backing obligation it carries one level out.
//!
//! THE TICKET'S HYPOTHESIS IS REFUTED, and the correction is the point of this
//! file. It read the defect as the obligation scan not *visiting* a secondary
//! entry ("the scan walks `Item::SortWithBody` items; a secondary entry's items
//! arrive under `Item::Namespace`"). The scan walks neither — it walks the
//! `SortProvidesInfo` FACTS in the loaded KB (`check_provider_operations`). It
//! is not skipped for that placement: measured, the obligation already fired for
//! a `sort X` and an `enum X` main entry.
//!
//! What was skipped was the EMITTER, and the discriminator was DECLARATION
//! ORDER, not placement. `maybe_emit_fact_provides_info` branched on
//! `kind_of(domain)` — `primary_kind()`, the FIRST category added to the symbol
//! — while a secondary entry's symbol carries a SET of them (WI-956/WI-926):
//!
//! | main entry beside `namespace X`  | primary   | `has_kind(Sort)` |
//! |----------------------------------|-----------|------------------|
//! | `sort X … end`                   | Sort      | true             |
//! | `enum X … end`                   | Sort      | true             |
//! | `entity X(…)`  (§6.3)            | **Entity**| true             |
//!
//! So a `fact Spec[X]` in a secondary entry to a §6.3 free-standing entity
//! matched neither the `Sort` arm nor the `Namespace` arm and fell out of the
//! old `_ => return`: NO `SortProvidesInfo` was emitted at all. That answers the
//! ticket's "FIRST thing to pin" — the provision did not merely miss the check,
//! it did not exist, so every reader missed it, dispatch included. Writing the
//! same `namespace X` block BEFORE the entity made the primary kind `Namespace`
//! and the whole obligation came back; see [`order_alone_decided_it`].
//!
//! THE FIX: ask `has_kind(domain, Sort)` — "does this scope name a type" — which
//! is order-insensitive and is the reading 059 itself prescribes.
//!
//! WHAT THIS DOES **NOT** FIX, measured while pinning the above and split out as
//! WI-1008: with the provision now recorded, a generic caller reaching the
//! carrier through `requires Show[T = T]` STILL dies `OperationBodyMissing` when
//! the backing operation is declared in the secondary entry — and it does so
//! whether the claim sits in the entry or one level out, while the same caller
//! answers `111` with the operation in the sort body. So the OP's placement is
//! that discriminator, not the claim's; it is a dispatch-side defect in another
//! subsystem, and folding it in would have meant deciding between widening
//! dispatch and narrowing `op_backed`. This file therefore asserts what the
//! LOADER records, not what the requires route can run.
//!
//! A SECOND POPULATION, found by making the old `_ => return` loud rather than
//! by reasoning about it: a `fact Spec[X]` at a FILE'S TOP LEVEL, outside any
//! `namespace`. Its domain is the synthetic `_global` root scope, which carries
//! no category at all — so `Namespace` was as false for it as `Sort` was, and it
//! emitted no provision either, while the identical text one `namespace` in did.
//! Hence the fix's else is "everything else", not `has_kind(…, Namespace)`. It is
//! pinned by `parse_test::load_polynom_with_ring_requirement`, which loads two
//! top-level `fact Spec[…]` claims and fails loudly against a three-arm spelling;
//! not re-pinned here, so this file stays about the secondary entry.
//!
//! WHICH HALF FAILS WHEN THE FIX IS BACKED OUT — MEASURED, by reverting the
//! branch and re-running, not predicted. Both matrix halves report EVERY bad
//! row rather than panicking on the first, which is what makes the list below
//! exact: in each half exactly ONE of the four rows fails, the same one.
//!
//!   * [`backing_absent_is_refused`] — `entity` carrier, claim IN THE SECONDARY
//!     ENTRY: loads clean with nothing backing it. The other three rows —
//!     `entity`/one-level-out and both `sort` rows — pass either way, BY
//!     DESIGN. They are the control: three of the four cells are indifferent to
//!     the change, so the failure is attributable to the emitter's branch and
//!     not to the fixture, the spec, or the diagnostic.
//!   * [`backing_present_is_accepted_and_recorded`] — the same single row,
//!     recording `[]`. It still LOADS CLEAN, so reading only the verdict would
//!     have called it a pass; the provision count is what tells "checked and
//!     accepted" from "never recorded, so never checked".
//!   * [`both_placements_report_identically`] — fails.
//!   * [`order_alone_decided_it`] — the `entity`-first row only; the
//!     `namespace`-first row is the control and passes either way.
//!   * [`plain_namespace_provision_still_derives_its_carrier`] — passes either
//!     way. It pins the arm the fix must NOT have widened.

mod common;

use anthill_core::kb::KnowledgeBase;

/// One spec with one unbackable operation, shared by every fixture.
const SPEC: &str = r#"
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
"#;

/// The two main-entry spellings that differ in `primary_kind`. `enum` behaves as
/// `sort` does (both are `primary=Sort`) and is covered by the `sort` row.
const ENTITY: &str = "entity Rec(n: Int64)";
const SORT: &str = "sort Rec\n    entity rec(n: Int64)\n  end";

/// `Rec` claims `Show`, with the claim either inside the secondary entry or one
/// level out, and with the backing member either present or absent.
fn fixture(ns: &str, main_entry: &str, claim_in_entry: bool, backed: bool) -> String {
    let claim = "fact Show[T = Rec]";
    let (inner_claim, outer_claim) = if claim_in_entry { (claim, "") } else { ("", claim) };
    // The backing member stays in the secondary entry in every row, so the only
    // thing that varies across a row PAIR is where the CLAIM sits.
    let member = if backed { "operation show(x: Rec) -> Int64 = 111" } else { "" };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
{SPEC}
  {main_entry}
  namespace Rec
    {member}
    {inner_claim}
  end
  {outer_claim}
end
"#
    )
}

/// THE ACCEPTANCE MATRIX, HALF ONE — backing ABSENT: every row refused, naming
/// the carrier, the spec and the op. Its partner below is
/// [`backing_present_is_accepted_and_recorded`], and the PAIR is the control: a
/// test asserting only the refusal would pass on an implementation that refuses
/// every provision.
///
/// The two halves are separate tests rather than one loop so that backing the
/// fix out reports BOTH failure modes. In one test the first `panic!` hides the
/// rest, and the second half's mode — loads clean, records nothing — is the one
/// a reader would otherwise never see.
#[test]
fn backing_absent_is_refused() {
    let mut bad = Vec::new();
    for (spelling, main_entry) in [("entity", ENTITY), ("sort", SORT)] {
        for (i, claim_in_entry) in [true, false].into_iter().enumerate() {
            let placement = if claim_in_entry { "in the secondary entry" } else { "one level out" };
            let ns = format!("wi978.u{spelling}{i}");
            let src = fixture(&ns, main_entry, claim_in_entry, false);
            let want = format!("'{ns}.Rec' provides '{ns}.Show' but backs no operation '{ns}.Show.show'");
            match common::try_load_kb_with(&src) {
                Err(errs) if errs.join("\n").contains(&want) => {}
                Err(errs) => bad.push(format!(
                    "{spelling} carrier, claim {placement}: refused, but not with the \
                     unbacked-provider diagnostic — got {}",
                    errs.join(" | ")
                )),
                Ok(_) => bad.push(format!(
                    "{spelling} carrier, claim {placement}: LOADED CLEAN with nothing \
                     backing '{ns}.Show.show'"
                )),
            }
        }
    }
    // Every row reported, so backing the fix out names the discriminating rows
    // rather than only the first one reached.
    assert!(bad.is_empty(), "unbacked rows that were not refused:\n  {}", bad.join("\n  "));
}

/// THE ACCEPTANCE MATRIX, HALF TWO — backing PRESENT: every row accepted, AND
/// the provision is ON RECORD.
///
/// Counting the provisions is the whole point of this half. Pre-fix the two
/// `entity` rows LOADED CLEAN, so a test that read only the verdict would have
/// passed on them — clean because nothing was emitted, not because anything was
/// checked. The count is what tells those two apart.
#[test]
fn backing_present_is_accepted_and_recorded() {
    let mut bad = Vec::new();
    for (spelling, main_entry) in [("entity", ENTITY), ("sort", SORT)] {
        for (i, claim_in_entry) in [true, false].into_iter().enumerate() {
            let placement = if claim_in_entry { "in the secondary entry" } else { "one level out" };
            let ns = format!("wi978.b{spelling}{i}");
            let src = fixture(&ns, main_entry, claim_in_entry, true);
            // `load_kb_with` panics on a load error, so "accepted" is asserted by
            // getting here at all; the recorded provision is the other half.
            let kb = common::load_kb_with(&src);
            let got = provision_carriers(&kb, &ns);
            if got != vec![format!("{ns}.Rec")] {
                bad.push(format!(
                    "{spelling} carrier, claim {placement}: expected one provision for \
                     {ns}.Rec, recorded {got:?}"
                ));
            }
        }
    }
    assert!(bad.is_empty(), "backed rows recording the wrong provisions:\n  {}", bad.join("\n  "));
}

/// The two placements must give the SAME message, not merely both refuse — the
/// ticket asks for "the same message it gives one level out".
#[test]
fn both_placements_report_identically() {
    let inside = common::try_load_kb_with(&fixture("wi978.same", ENTITY, true, false))
        .err()
        .expect("claim in the secondary entry, unbacked: refused");
    let outside = common::try_load_kb_with(&fixture("wi978.same", ENTITY, false, false))
        .err()
        .expect("claim one level out, unbacked: refused");
    assert_eq!(
        inside, outside,
        "the same claim, the same carrier, the same missing backing — only the \
         placement differs, so the diagnostics must be identical"
    );
}

/// THE DISCRIMINATOR WAS ORDER, not placement. The same two declarations, in
/// both orders: pre-fix, `namespace Rec` first refused (primary kind
/// `Namespace`, carrier derived from the bindings) and `entity Rec` first loaded
/// clean (primary kind `Entity`, no arm matched). Post-fix both refuse, because
/// `has_kind` cannot see which declaration came first.
#[test]
fn order_alone_decided_it() {
    let entity_first = r#"
namespace wi978.o.ef
  import anthill.prelude.{Int64}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  entity Rec(n: Int64)
  namespace Rec
    fact Show[T = Rec]
  end
end
"#;
    let ns_first = r#"
namespace wi978.o.nf
  import anthill.prelude.{Int64}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  namespace Rec
    fact Show[T = Rec]
  end
  entity Rec(n: Int64)
end
"#;
    for (label, src, ns) in [
        // Fails when the fix is backed out.
        ("entity first", entity_first, "wi978.o.ef"),
        // Passes either way, by design: the control.
        ("namespace first", ns_first, "wi978.o.nf"),
    ] {
        let errs = common::try_load_kb_with(src)
            .err()
            .unwrap_or_else(|| panic!("{label}: an unbacked claim must be refused whichever declaration is written first"));
        assert!(
            errs.join("\n").contains(&format!("'{ns}.Rec' provides '{ns}.Show'")),
            "{label}: expected the unbacked-provider diagnostic; got:\n{}",
            errs.join("\n")
        );
    }
}

/// THE ARM THE FIX MUST NOT HAVE WIDENED. A claim in a PLAIN namespace — one
/// with no type at its address, `has_kind(Sort) == false` — still derives its
/// carrier from the bindings rather than filing the provision under the
/// namespace itself. Passes either way by design; it is here because
/// `kind_of == Sort` → `has_kind(Sort)` widens the first arm, and this is the
/// population that must stay in the second.
#[test]
fn plain_namespace_provision_still_derives_its_carrier() {
    let src = r#"
namespace wi978.plain
  import anthill.prelude.{Int64}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort Rec
    entity rec(n: Int64)
    operation show(x: Rec) -> Int64 = 111
  end
  namespace Holder
    operation unrelated(x: Int64) -> Int64 = x
  end
  fact Show[T = Rec]
end
"#;
    let kb = common::load_kb_with(src);
    assert_eq!(
        provision_carriers(&kb, "wi978.plain"),
        vec!["wi978.plain.Rec".to_string()],
        "a namespace-level claim files under the carrier its bindings name, never \
         under the enclosing namespace"
    );
}

// ── helpers ─────────────────────────────────────────────────────────────

/// The carrier of every provision the loader recorded under `ns` — i.e. what
/// every downstream reader (the backing obligation, coherence, dispatch)
/// consults. Filters `common::sort_provisions`, which is the shared walk over
/// `SortProvidesInfo` its own doc asks new readers to call.
///
/// Reading the KB rather than the load verdict is deliberate: pre-fix the backed
/// rows LOADED CLEAN, and only the empty provision list distinguishes "checked
/// and accepted" from "never recorded, so never checked".
fn provision_carriers(kb: &KnowledgeBase, ns: &str) -> Vec<String> {
    let prefix = format!("{ns}.");
    let mut out: Vec<String> = common::sort_provisions(kb)
        .into_iter()
        .map(|(carrier, _spec)| carrier)
        .filter(|c| c.starts_with(&prefix))
        .collect();
    out.sort();
    out
}
