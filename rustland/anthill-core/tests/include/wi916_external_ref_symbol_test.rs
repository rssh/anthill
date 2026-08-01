//! WI-916 — A MOUNTED NAME IS RESOLVED ONCE, AT THE MOUNT.
//!
//! `register_extent_owner` resolves an owner's `owned()` name to a `Symbol` and keys the
//! mount on it. An external `FactRef` used to carry the NAME instead, so every
//! `retract_persistent` / `update_persistent` re-ran the `_global` ladder on a string the
//! mount had already resolved — two independent readings of one name, with a whole load
//! able to happen in between.
//!
//! DRIVEN before the fix (this fixture, `panic!`-printed): mount `Widget916.w916a` under
//! one wildcard import, insert a row, then load a second import that contests the head.
//!
//!     read    = Ok(1)          <- Symbol-keyed off the mount: unaffected
//!     insert  = Ok             <- routed by the ROW's head symbol: unaffected
//!     retract = Err(Backend("persistent retract: ambiguous owner `Widget916.w916a`:
//!                            candidates [\"wi916.alpha.Widget916\", \"wi916.beta.Widget916\"]"))
//!     update  = Err(Backend("persistent update: ambiguous owner `Widget916.w916a`: …"))
//!
//! That asymmetry is the whole finding: the extent stayed mounted, readable and writable,
//! and its rows became permanently unretractable — because the only two operations that
//! re-asked the NAME question got a different answer than the mount had. A
//! name-resolution failure, reported as a backend one, about a name the caller never
//! wrote. (The `Ambiguous` half of that pair dates from WI-907, which recorded here that
//! unifying it was this ticket's.)
//!
//! THE FIX IS A DELETION: `FactRefInner::External` carries the resolved `Symbol`, so the
//! mutation seams look their owner up instead of re-deriving it, and both string errors
//! are gone rather than typed. A source cannot stamp the owner wrongly either — it hands
//! back a `SourceRow`, which has nowhere to name one, and the KB attaches the functor it
//! ROUTED the call through.
//!
//! WHAT EACH TEST IS FOR. The first two pin the two mutation seams across the contesting
//! load. The third is a CONTROL, green on BOTH sides — it pins the two halves that never
//! broke, so a green first test cannot be the mount having quietly stopped working. The
//! fourth pins the one failure the seam can still have, which is not about names.
//!
//! WHERE THE NAME QUESTION STILL LIVES: at the mount, once, typed — `mount_extent` on a
//! contested path is `ExtentRegError::AmbiguousName`
//! (`wi917_ambiguous_dotted_head_test::an_ambiguous_dotted_host_name_is_refused_as_ambiguous_not_absent`).
//!
//! STDLIB LOADS: four, one per `#[test]` — the fourth loads one for the PRODUCING KB and
//! pairs it with a bare `KnowledgeBase::new()`.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::extent::{BodiedRulePolicy, ExtentError, StoredRow};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

use crate::common::{load_kb_with, mount_extent};

/// Two namespaces declaring the same sort name, so a scope that sees both resolves the
/// HEAD of `Widget916.w916a` ambiguously. The entity `w916a` is alpha's alone — with one
/// import the path names exactly one functor and mounts.
const DECLS: &str = r#"
namespace wi916.alpha
  sort Widget916
    entity w916a(id: anthill.prelude.Int64)
  end
end

namespace wi916.beta
  sort Widget916
    entity w916b(id: anthill.prelude.Int64)
  end
end
"#;

/// The mount's `owned()` name: a DOTTED path whose head is what a second import contests.
/// (A short name would do as well; the dotted spelling is the one a host actually writes
/// for an entity, and it is WI-917's subject, so the two suites share a shape.)
const MOUNT_NAME: &str = "Widget916.w916a";

/// A KB with `DECLS` and ONE top-level wildcard import, an empty in-memory extent mounted
/// on [`MOUNT_NAME`] (`common::mount_extent`, the shared mount idiom; it keys on `id`, so
/// the fixture entity carries that field), and one row inserted THROUGH the mount.
/// Returns the KB, the mounted functor, the `id` field, and the row's reference.
fn mounted_with_one_row() -> (KnowledgeBase, Symbol, Symbol, StoredRow) {
    let mut kb = load_kb_with(&format!("{DECLS}\nimport wi916.alpha.*\n"));
    let functor = kb
        .try_resolve_symbol("wi916.alpha.Widget916.w916a")
        .expect("the entity loaded");
    let id_field = kb.intern("id");
    mount_extent(&mut kb, MOUNT_NAME)
        .expect("one import leaves the path unambiguous, so it mounts");
    let stored = kb
        .assert_persistent(row(functor, id_field, 1), None)
        .expect("the mounted owner accepts an insert");
    (kb, functor, id_field, stored)
}

/// `w916a(id: <n>)` as a raw `Value::Entity` — the shape the source stores.
fn row(functor: Symbol, id_field: Symbol, id: i64) -> Value {
    Value::Entity { functor, pos: [].into(), named: [(id_field, Value::Int(id))].into() }
}

/// Load a SECOND top-level wildcard import into the live KB, contesting `Widget916` at
/// `_global` — the load that used to happen "between" the mount and the mutation. A
/// top-level import is KB-wide (WI-853), and nothing here references the contested name,
/// so this loads clean and the ambiguity is live but unreported.
fn contest_the_mount_name(kb: &mut KnowledgeBase) {
    let parsed = parse::parse("import wi916.beta.*\n").expect("parse the second import");
    load::load(kb, &parsed, &NullResolver).expect("a top-level import alone loads clean");
}

/// How many rows the mounted extent holds.
fn row_count(kb: &KnowledgeBase, functor: Symbol) -> usize {
    kb.read_facts(functor, &[], BodiedRulePolicy::Refuse)
        .expect("the mount is enumerable")
        .len()
}

/// THE DEFECT, retract half. The reference names a row of a mount that is still there;
/// what changed is only what its NAME would resolve to now, which the retract has no
/// business asking.
#[test]
fn a_load_that_contests_the_mount_name_still_retracts_its_rows() {
    let (mut kb, functor, _, stored) = mounted_with_one_row();

    contest_the_mount_name(&mut kb);

    let retracted = kb
        .retract_persistent(&stored.reference)
        .expect("the owner is the symbol the mount resolved, so it is found without a \
                 second reading of the name — pre-fix: Err(Backend(\"ambiguous owner\"))");
    assert!(retracted, "the row was live, so the source reports it removed");
    assert_eq!(row_count(&kb, functor), 0, "and it is gone from the extent");
}

/// THE DEFECT, update half — the same re-resolution, and one thing more: the REPLACEMENT
/// reference must come back under the same owner, or the next mutation on it strands the
/// row exactly as this ticket's did.
#[test]
fn a_load_that_contests_the_mount_name_still_updates_its_rows() {
    let (mut kb, functor, id_field, stored) = mounted_with_one_row();

    contest_the_mount_name(&mut kb);

    let replacement = kb
        .update_persistent(&stored.reference, row(functor, id_field, 2), None)
        .expect("no name is re-read — pre-fix: Err(Backend(\"ambiguous owner\"))")
        .expect("the row is live");
    assert_eq!(row_count(&kb, functor), 1, "updated in place, not duplicated");
    assert!(
        kb.retract_persistent(&replacement.reference)
            .expect("the replacement rides the same owner"),
        "the reference an update hands back must be as usable as the one it replaces",
    );
}

/// CONTROL, green on BOTH sides of the fix: the contesting load leaves the READ and the
/// INSERT untouched, because both are keyed on a `Symbol` (the mount, and the row's own
/// head) rather than on the name. Without this the tests above would also pass if the
/// mount had simply stopped working — and it is this asymmetry that made the ticket a
/// defect rather than a policy: an extent you can read and write but never retract from.
#[test]
fn the_contesting_load_never_touched_the_symbol_keyed_halves() {
    let (mut kb, functor, id_field, _) = mounted_with_one_row();

    contest_the_mount_name(&mut kb);

    assert_eq!(row_count(&kb, functor), 1, "the mounted extent still reads");
    kb.assert_persistent(row(functor, id_field, 2), None)
        .expect("and still routes an insert to its owner");
    assert_eq!(row_count(&kb, functor), 2);
}

/// The one failure the mutation seam can still have, and it is not about names: a
/// reference is only valid in the KB that produced it. Within a KB this is unreachable —
/// the stamp is the routed owner and a mount is never removed — so the loud refusal
/// exists for exactly this misuse. It reports the owner as a `Symbol`, not as a name:
/// THIS KB's table is the wrong book to look a foreign symbol up in.
#[test]
fn a_reference_from_another_knowledge_base_is_refused_loudly() {
    let (_producer, functor, _, stored) = mounted_with_one_row();
    let mut other = KnowledgeBase::new();

    let err = other
        .retract_persistent(&stored.reference)
        .expect_err("nothing is mounted here, so there is no owner to retract from");

    match err {
        ExtentError::UnmountedOwner { op, owner } => {
            assert_eq!(op, "persistent retract", "the failing operation is named");
            assert_eq!(owner, functor, "and the owner is carried through verbatim");
        }
        other => panic!("a foreign reference must be refused as UnmountedOwner; got {other:?}"),
    }
}
