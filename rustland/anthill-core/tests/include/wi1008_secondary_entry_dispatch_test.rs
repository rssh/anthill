//! WI-1008 — an operation declared in a SECONDARY ENTRY (proposal 059: a
//! `namespace X` block at the address of a sort `X`) must be reachable by the
//! requires-dictionary DISPATCH route, not merely accepted by the load-time
//! backing check.
//!
//! THE DEFECT, measured before the fix on the three fixtures below: the program
//! loaded clean and DIED. `op_backed` (typing.rs, `check_provider_operations`)
//! found the secondary entry's `show` and accepted the claim; the runtime
//! dictionary route did not, and reported the SPEC op as missing a body —
//! `EvalError::OperationBodyMissing { name: "…Show.show" }`. That is the WI-818
//! failure mode, in the placement 059 R2 makes the whole point of the mechanism.
//!
//! WHICH SIDE WAS WRONG — the ticket left this open between (a) widening dispatch
//! and (b) narrowing `op_backed`. (a), because 059 R2 is explicit: what a secondary
//! entry declares "enters `X`'s scope … and may back `X`'s `provides`/`fact Spec[X]`
//! claims", and it "is the only route to a member of a type whose declaration one
//! does not own". (b) would have made the mechanism unable to supply members for a
//! foreign carrier, which is most of why one writes a secondary entry.
//!
//! THE DISCRIMINATOR, measured rather than reasoned: `SortInfo(name: Rec).operations`
//! was `["Rec.show"]` for the sort-body placement and `[]` for the secondary entry,
//! and everything that dispatches reads that field. `build_sort_ops_table` fills
//! `sort_ops` from it, and with the carrier's own entry missing its pass 2
//! substitutes the SPEC's body-less declaration — so `sort_ops_lookup(Rec, show)`
//! answered `Show.show`, which is exactly the op the error named. Two other records
//! answered CORRECTLY for both placements (`MemberInfo(kind: Operation, parent: Rec)`
//! and `OperationInfo` + `declaring_scope_symbol`), so `SortInfo` was the odd one
//! out, not a second opinion. The fix completes that record post-load
//! (`merge_secondary_entry_operations`) instead of teaching one reader to look
//! elsewhere; its doc owns the reasoning and the reader count.
//!
//! WHY THE DIRECT CALL ALWAYS WORKED, and why that is the point rather than a
//! curiosity: `Rec.show(rec(n: 7))` answered `111` in EVERY fixture, before the fix
//! included. Dot dispatch resolves through the symbol table, where one written name
//! is one symbol (WI-926) — and `op_backed`'s `{carrier_qn}.{op_short}` candidate IS
//! that same symbol, which is why the load accepted a claim the run could not honour.
//! Accepted by ADDRESS, unreachable by RECORD. [`direct_call_is_unchanged`] keeps the
//! address side pinned so a future narrowing of the record cannot quietly take it.
//!
//! WHICH TESTS FAIL WHEN THE FIX IS BACKED OUT — MEASURED, by removing the
//! `merge_secondary_entry_operations` call from `resolve_instantiations` and
//! re-running, not predicted. SIX of the nine fail, three pass either way. Every
//! failing dispatch row reports the SAME error, `EvalError::OperationBodyMissing`
//! naming `test.wi1008.Show.show` — rendered "operation has no body: … — this is a
//! typer-guaranteed invariant violation (should be unreachable)", which is the
//! program loading clean and then dying:
//!
//!   * [`op_in_secondary_entry_dispatches`] — FAILS. The capability.
//!   * [`claim_in_secondary_entry_dispatches`] — FAILS, identically. So the CLAIM's
//!     placement is not the discriminator; the OP's is.
//!   * [`free_standing_entity_carrier_dispatches`] — FAILS. WI-978's carrier shape,
//!     which is where this was found.
//!   * [`placement_is_not_declaration_order`] — FAILS in ALL THREE rows (entry
//!     before main, and both cross-file orders). The matrix reports every row rather
//!     than panicking on the first, which is what makes "all three" a measurement
//!     instead of an inference from the one row that happened to run.
//!   * [`sort_info_lists_the_secondary_entrys_operation`] — FAILS at the record
//!     itself: `operations` is `[]`, and `sort_ops_lookup(Rec, show)` answers
//!     `test.wi1008.Show.show` — the same name the four rows above die on.
//!   * [`rerunning_the_pass_rewrites_nothing`] — FAILS, but on its embedded CONTROL
//!     rather than on its subject. Its subject, idempotence, is orthogonal to the fix
//!     and would hold vacuously with the pass gone; the control asserts the fixture is
//!     the triggering one, so a no-op second run means something. Deliberate: the
//!     alternative is a test that passes whether or not the pass exists.
//!
//! PASS EITHER WAY, BY DESIGN — the three that make the five above attributable:
//!
//!   * [`op_in_sort_body_dispatches`] — the both-sides CONTROL. Fixture (1),
//!     unchanged. It shares the spec, the caller, the driver and the value with
//!     every failing row and differs only in where the op sits, which is what
//!     attributes the failures to PLACEMENT rather than to the fixture.
//!   * [`unbacked_claim_is_still_refused`] — the GUARD. A widening's only real
//!     control is that it did not widen past its target: this row would go green if
//!     completing the record had also made the load-time obligation vacuous.
//!   * [`direct_call_is_unchanged`] — pins the route that was never broken, in all
//!     four fixtures.

use anthill_core::eval::{self, Interpreter, Value};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::Term;

/// One spec with one operation, shared by every fixture.
const SPEC: &str = r#"
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
"#;

/// The GENERIC caller — the whole point. `useIt` knows nothing of `Rec`; it reaches
/// the carrier's `show` through the requirement dictionary its `requires` builds.
/// A test that called `Rec.show` directly would pass in every fixture (see the head
/// note) and measure nothing.
const CALLER: &str = r#"
  sort Caller
    sort T = ?
    requires Show[T = T]
    operation useIt(x: T) -> Int64 = show(x)
  end
"#;

/// The value the backing operation answers, distinct from any default so a wrong
/// dispatch cannot coincide with a right one.
const ANSWER: i64 = 111;

/// Load, then DRIVE — resolve the operation and assert the value it returns. A
/// fixture that only loaded would have passed throughout the defect: all three
/// loaded clean, which is precisely what made this a run-time death.
fn eval_int(src: &str, op: &str) -> Result<i64, String> {
    eval_int_files(&[src], op)
}

/// [`eval_int`] over several files — the cross-file half of "placement is not
/// order" (059: a secondary entry is legal in another file).
fn eval_int_files(srcs: &[&str], op: &str) -> Result<i64, String> {
    let kb = crate::common::try_load_kb_with_files(srcs)
        .unwrap_or_else(|errs| panic!("fixture must load clean; got {errs:#?}"));
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    match interp.call(op, &[]) {
        Ok(Value::Int(n)) => Ok(n),
        Ok(other) => Err(format!("expected Int, got {}", other.type_name())),
        Err(e) => Err(format!("{e}")),
    }
}

/// THE ONE PROGRAM SKELETON every fixture below is built from: the same spec, the same
/// generic caller, the same two drivers, the same answer — `carrier` and its
/// constructor are the ONLY things that vary.
///
/// This is the head note's attribution argument made STRUCTURAL rather than
/// hand-maintained. That argument is that the control differs from the failing rows in
/// exactly one respect, where the op sits; written as six near-identical literals, one
/// stray edit to a header or an import would weaken the control silently, with nothing
/// failing to say so. Here a difference has to be passed in to exist.
fn fixture(carrier: &str, ctor: &str) -> String {
    format!(
        r#"
namespace test.wi1008
  import anthill.prelude.{{Int64}}
{SPEC}
{carrier}
{CALLER}
  operation driveGeneric() -> Int64 = Caller.useIt({ctor})
  operation driveDirect() -> Int64 = Rec.show({ctor})
end
"#
    )
}

/// FIXTURE (1) — op in the SORT BODY, claim in the sort body. The CONTROL.
fn sort_body_fixture() -> String {
    fixture(
        &format!(
            "  sort Rec\n    entity rec(n: Int64)\n    \
             operation show(x: Rec) -> Int64 = {ANSWER}\n    provides Show[T = Rec]\n  end"
        ),
        "rec(n: 7)",
    )
}

/// FIXTURE (2) — op in the SECONDARY ENTRY, claim ONE LEVEL OUT.
fn secondary_entry_fixture() -> String {
    fixture(
        &format!(
            "  sort Rec\n    entity rec(n: Int64)\n  end\n  \
             namespace Rec\n    operation show(x: Rec) -> Int64 = {ANSWER}\n  end\n  \
             fact Show[T = Rec]"
        ),
        "rec(n: 7)",
    )
}

/// FIXTURE (3) — op AND claim both in the secondary entry.
///
/// THE CLAIM IS SPELLED `provides`, NOT `fact` (WI-1000 / 059 R3). Inside a
/// secondary entry the `fact Spec[X]` spelling is refused and the `provides` one is
/// allowed — not because the claim is unwelcome but because a `fact` there cannot be
/// told from an ordinary fact over a parameterized data sort, while `provides` is a
/// declaration the grammar recognises. The two mean the same thing (058 §4 proposes
/// retiring the `fact` spelling outright), so this is a re-spelling of the fixture
/// and not a change of what it asks: the claim is still in the entry, which is the
/// whole variable this row holds against fixture (2).
fn claim_in_entry_fixture() -> String {
    fixture(
        &format!(
            "  sort Rec\n    entity rec(n: Int64)\n  end\n  \
             namespace Rec\n    operation show(x: Rec) -> Int64 = {ANSWER}\n    \
             provides Show[T = Rec]\n  end"
        ),
        "rec(n: 7)",
    )
}

/// FIXTURE (4) — a §6.3 FREE-STANDING ENTITY as the main entry. WI-978's carrier, the
/// shape this was found on, and the one whose `SortInfo` comes from a different call
/// site (`emit_sort_info(functor, true, "entity", …)`, whose operations list is
/// unconditionally empty).
fn free_standing_entity_fixture() -> String {
    fixture(
        &format!(
            "  entity Rec(n: Int64)\n  \
             namespace Rec\n    operation show(x: Rec) -> Int64 = {ANSWER}\n  end\n  \
             fact Show[T = Rec]"
        ),
        "Rec(n: 7)",
    )
}

// ── The capability: the generic caller reaches a secondary entry's member ────

/// THE CONTROL, and fixture (1) unchanged. Passes with the fix backed out.
#[test]
fn op_in_sort_body_dispatches() {
    assert_eq!(eval_int(&sort_body_fixture(), "test.wi1008.driveGeneric"), Ok(ANSWER));
}

/// THE CAPABILITY. Fails `OperationBodyMissing { name: "…Show.show" }` without the fix.
#[test]
fn op_in_secondary_entry_dispatches() {
    assert_eq!(eval_int(&secondary_entry_fixture(), "test.wi1008.driveGeneric"), Ok(ANSWER));
}

/// The CLAIM moved inside the entry as well — the ticket's fixture (3). It fails and
/// passes in lockstep with fixture (2), which is what shows the claim's placement is
/// not the discriminator.
#[test]
fn claim_in_secondary_entry_dispatches() {
    assert_eq!(eval_int(&claim_in_entry_fixture(), "test.wi1008.driveGeneric"), Ok(ANSWER));
}

/// The §6.3 carrier — WI-978's shape, whose `SortInfo` comes from the other emitter.
#[test]
fn free_standing_entity_carrier_dispatches() {
    assert_eq!(eval_int(&free_standing_entity_fixture(), "test.wi1008.driveGeneric"), Ok(ANSWER));
}

/// 059: "'Main' and 'secondary' name roles, not order" — a secondary entry may be
/// written first, and in another file. All three rows must answer alike; a fix that
/// read the entries in load order would pass the first and fail the rest.
#[test]
fn placement_is_not_declaration_order() {
    // Same file, secondary entry written BEFORE the main entry. Same skeleton as every
    // fixture above — only the carrier block's internal order differs from (2)'s.
    let entry_first = fixture(
        &format!(
            "  namespace Rec\n    operation show(x: Rec) -> Int64 = {ANSWER}\n  end\n  \
             sort Rec\n    entity rec(n: Int64)\n  end\n  fact Show[T = Rec]"
        ),
        "rec(n: 7)",
    );
    // Two files, in both orders: the carrier's main entry and claim here, its secondary
    // entry in `entry_file` below.
    let main_file = fixture(
        "  sort Rec\n    entity rec(n: Int64)\n  end\n  fact Show[T = Rec]",
        "rec(n: 7)",
    );
    let entry_file = format!(
        r#"
namespace test.wi1008
  import anthill.prelude.{{Int64}}
  namespace Rec
    operation show(x: Rec) -> Int64 = {ANSWER}
  end
end
"#
    );
    // EVERY row is reported, not just the first — a matrix that panics on row 1
    // cannot say whether the rest agree, which is exactly what this test is for.
    let rows: Vec<(&str, Vec<&str>)> = vec![
        ("entry before main, same file", vec![entry_first.as_str()]),
        ("two files, main listed first", vec![main_file.as_str(), entry_file.as_str()]),
        ("two files, entry listed first", vec![entry_file.as_str(), main_file.as_str()]),
    ];
    let bad: Vec<String> = rows
        .into_iter()
        .filter_map(|(order, files)| {
            match eval_int_files(&files, "test.wi1008.driveGeneric") {
                Ok(ANSWER) => None,
                other => Some(format!("{order}: {other:?}")),
            }
        })
        .collect();
    assert!(
        bad.is_empty(),
        "placement must not depend on declaration order; these rows disagreed: {bad:#?}"
    );
}

// ── The record, and the guard ────────────────────────────────────────────────

/// The op symbols `SortInfo(name: sort).operations` lists, by qualified name.
fn sort_info_operations(kb: &KnowledgeBase, sort_qn: &str) -> Vec<String> {
    let sort_sym = kb.try_resolve_symbol(sort_qn).unwrap_or_else(|| panic!("no sort {sort_qn}"));
    let si = kb.try_resolve_symbol("anthill.reflect.SortInfo").expect("SortInfo");
    for rid in kb.rules_by_functor(si) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        // `get_named_arg` is the crate's own field reader (`kb::typing`); `head_sym` has
        // no public equivalent — `KnowledgeBase::head_functor` is `pub(crate)`.
        let field = |n| anthill_core::kb::typing::get_named_arg(kb, &named, n);
        let head_sym = |t| match kb.get_term(t) {
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            Term::Fn { functor, .. } => Some(*functor),
            _ => None,
        };
        if field("name").and_then(head_sym) != Some(sort_sym) {
            continue;
        }
        let Some(ops) = field("operations") else { continue };
        return anthill_core::kb::typing::list_to_vec(kb, ops)
            .into_iter()
            .filter_map(head_sym)
            .map(|s| kb.qualified_name_of(s).to_string())
            .collect();
    }
    panic!("no SortInfo fact for {sort_qn}");
}

/// THE FIX'S ACTUAL CLAIM — that the RECORD is complete, not that one reader was
/// taught a second lookup. Asserted at both ends: the `SortInfo` field the six
/// readers scan, and the `sort_ops` table `build_sort_ops_table` derives from it.
///
/// Without the fix, `operations` is `[]` and `sort_ops_lookup` answers
/// `test.wi1008.Show.show` — the body-less SPEC declaration substituted by pass 2,
/// which is verbatim the name the `OperationBodyMissing` error carried. Asserting
/// the table too is what ties this record to that error rather than leaving the
/// connection to the prose above.
#[test]
fn sort_info_lists_the_secondary_entrys_operation() {
    let mut kb = crate::common::load_kb_with(&secondary_entry_fixture());
    assert_eq!(
        sort_info_operations(&kb, "test.wi1008.Rec"),
        vec!["test.wi1008.Rec.show".to_string()],
        "a secondary entry's operation is a member of the sort (059 R2)"
    );

    let rec = kb.try_resolve_symbol("test.wi1008.Rec").expect("Rec");
    let show = kb.intern("show");
    let target = kb.sort_ops_lookup(rec, show).map(|s| kb.qualified_name_of(s).to_string());
    assert_eq!(
        target.as_deref(),
        Some("test.wi1008.Rec.show"),
        "the dispatch table must route Rec's `show` to the CARRIER's op, not to the \
         body-less spec declaration"
    );
}

/// THE GUARD, and the only real control on a widening: completing the record must not
/// have made the load-time backing obligation vacuous. The same carrier, the same
/// claim, an EMPTY secondary entry — nothing backs `show` anywhere, and the load must
/// still say so. Passes with the fix backed out, by design; it fails only if a future
/// change lets an unbacked claim through.
#[test]
fn unbacked_claim_is_still_refused() {
    let src = format!(
        r#"
namespace test.wi1008
  import anthill.prelude.{{Int64}}
{SPEC}
  sort Rec
    entity rec(n: Int64)
  end
  namespace Rec
  end
  fact Show[T = Rec]
end
"#
    );
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&src),
        &["'test.wi1008.Rec' provides 'test.wi1008.Show' but backs no operation"],
    );
}

/// THE PASS MUST BE IDEMPOTENT, because `load_incremental` relies on it: its doc
/// states that re-running `resolve_instantiations` over an already-finalized KB must
/// not retract or re-assert stdlib facts, and this pass now runs inside it.
///
/// `incremental_load_test::resolve_instantiations_is_idempotent` cannot cover that.
/// It snapshots `SortRequiresInfo` over the STDLIB — a corpus with no secondary entry,
/// where this pass rewrites nothing — so it is blind to the new writer twice over:
/// wrong relation, and a fixture that never triggers it. This is the same shape on a
/// fixture that DOES trigger it, asserting the RuleIds as well as the heads: a
/// re-assert that produced an identical head would still churn ids, and it is the id
/// that a stale index would be holding.
#[test]
fn rerunning_the_pass_rewrites_nothing() {
    let mut kb = crate::common::load_kb_with(&secondary_entry_fixture());
    let si = kb.try_resolve_symbol("anthill.reflect.SortInfo").expect("SortInfo");
    let snapshot = |kb: &KnowledgeBase| -> Vec<(anthill_core::kb::RuleId, _)> {
        kb.rules_by_functor(si).iter().map(|rid| (*rid, kb.rule_head(*rid))).collect()
    };

    let before = snapshot(&kb);
    assert!(!before.is_empty(), "the fixture must define SortInfo facts");
    // The control that this fixture is the triggering one: the first load already
    // merged the member in, so a second pass having nothing to do is a real no-op
    // rather than a pass that never fired.
    assert_eq!(
        sort_info_operations(&kb, "test.wi1008.Rec"),
        vec!["test.wi1008.Rec.show".to_string()]
    );

    anthill_core::kb::load::resolve_instantiations(&mut kb);
    let after = snapshot(&kb);

    // Reported as the DIFFERING rows, not as two 180-element vectors: measured on a
    // deliberately non-idempotent pass, every head (`TermId`) stays identical and only
    // the `RuleId`s churn, so a whole-vector `assert_eq!` prints two near-identical
    // walls of text with the one distinguishing column buried. That the heads match is
    // also why this test compares ids at all — a head-only snapshot passes over the
    // very churn it exists to catch.
    let changed: Vec<String> = before
        .iter()
        .zip(after.iter())
        .filter(|(b, a)| b != a)
        .map(|(b, a)| format!("{b:?} -> {a:?}"))
        .collect();
    assert!(
        before.len() == after.len() && changed.is_empty(),
        "re-running the pass must not retract or re-assert; {} of {} SortInfo facts \
         churned (first few: {:?})",
        changed.len(),
        before.len(),
        &changed[..changed.len().min(3)]
    );
}

/// The route that was NEVER broken, pinned so a later narrowing of the record cannot
/// quietly take it with it. `Rec.show(rec(n: 7))` resolves through the symbol table
/// (one written name, one symbol — WI-926), which is why it answered in every fixture
/// throughout the defect, and why the load-time check accepted what the run could not
/// reach. Passes with the fix backed out, in all four fixtures, by design.
#[test]
fn direct_call_is_unchanged() {
    for (label, src) in [
        ("sort body", sort_body_fixture()),
        ("secondary entry", secondary_entry_fixture()),
        ("claim in entry", claim_in_entry_fixture()),
        ("free-standing entity", free_standing_entity_fixture()),
    ] {
        assert_eq!(
            eval_int(&src, "test.wi1008.driveDirect"),
            Ok(ANSWER),
            "the direct dot call must answer in every placement ({label})"
        );
    }
}
