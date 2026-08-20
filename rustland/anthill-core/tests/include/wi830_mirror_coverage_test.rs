//! WI-830 — A MIRROR COVERS THE FUNCTORS IT IS DECLARED TO COVER.
//!
//! `read_stored_facts` attaches a durability mirror to each resident row it returns, so
//! that the `FactRef` the caller later hands to `retract_persistent` / `update_persistent`
//! reaches the file (or table, or service) the row actually lives in. Which mirror that is
//! was answered by `ExtentRegistry::sole_mirror_key`: "the one mirror, if there is exactly
//! one; otherwise refuse". That stand-in had two consequences, and this file drives both.
//!
//! 1. WITH ONE MIRROR IT ANSWERED FOR FUNCTORS THE MIRROR DOES NOT HOLD. Every functor in
//!    the KB got the sole mirror attached, whether or not that store had ever heard of it.
//! 2. WITH TWO IT ANSWERED FOR NONE. `AmbiguousResidentMirror` — so a second backend could
//!    not be registered beside the file store at all, which is exactly the shape WI-437
//!    needs (a GitHub owner beside the tracker's file mirror).
//!
//! Coverage is DECLARED now: `register_mirror` takes the functor names the mirror durably
//! backs. It is a registration argument rather than a `Store` trait method because the
//! backend cannot answer it — anthill-todo's `workitems.anthill` is ONE file holding four
//! functors, and which four is the project's layout, not the file store's.
//!
//! WHAT FAILS WITHOUT THE CHANGE — MEASURED, by restoring `sole_mirror_key`'s answer
//! inside `mirror_for` and re-running:
//!   * `each_functor_retracts_through_its_own_mirror` — the load-bearing one. Two mirrors
//!     are registered, so the old answer is "ambiguous" and NEITHER row carries a mirror;
//!     both logs come back empty. It cannot be rescued by registering only one mirror
//!     either: one mirror would then absorb BOTH retracts, which is the assertion this
//!     test makes fail.
//!   * `an_uncovered_functor_gets_no_mirror` — the sole mirror is attached to `Gamma830`,
//!     which no store covers, so the retract reaches it and the log is non-empty where
//!     this asserts it is empty.
//!
//! WHAT PASSES EITHER WAY BY DESIGN:
//!   * `one_mirror_still_backs_its_own_functor` — the no-regression control. A single
//!     mirror covering the functor it holds behaves identically before and after; it is
//!     here to show the fix is about WHICH mirror, not about whether mirroring works.
//!   * `two_mirrors_may_not_claim_one_functor` — this one pins the REGISTRATION half, so
//!     the read-side scaffold above leaves it green. Against the true pre-change tree it
//!     does not compile at all: `register_mirror` took no coverage argument, so there was
//!     no second claim to refuse and no way to spell one.
//!
//! STDLIB LOADS: four, one per `#[test]`.

use std::cell::RefCell;
use std::rc::Rc;

use anthill_core::eval::{value_functor, Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::extent::BodiedRulePolicy;
use anthill_core::kb::{ClauseKind, KnowledgeBase, RuleId};
use anthill_core::persistence::{PersistenceError, Store};
use anthill_core::kb::term::TermId;

use crate::common::interp_for;

/// Three functors in one namespace. `Alpha830` and `Beta830` are each backed by their own
/// mirror; `Gamma830` is backed by none, which is the ordinary resident-only case and must
/// stay distinguishable from "backed by whichever mirror happens to be registered".
const SRC: &str = "namespace test.wi830\n  \
                   import anthill.reflect.{fact_monotonicity, non_monotone}\n  \
                   entity Alpha830\n  \
                   entity Beta830\n  \
                   entity Gamma830\n  \
                   entity Delta830\n  \
                   fact Alpha830()\n  \
                   fact Beta830()\n  \
                   fact Gamma830()\n  \
                   rule fact_monotonicity(Delta830) <=> non_monotone() [simp]\n\
                   end\n";

/// A mirror that records the calls it receives instead of writing anything. The log is the
/// observable: "which store was asked to drop this row" is precisely the routing question,
/// and reading it back through a shared handle needs no filesystem and no flush protocol.
struct RecordingStore {
    label: &'static str,
    log: Rc<RefCell<Vec<String>>>,
}

impl Store for RecordingStore {
    fn persist(
        &mut self,
        _kb: &KnowledgeBase,
        _fact: TermId,
        _clause_kind: ClauseKind,
        _domain: Symbol,
        _meta: Option<TermId>,
    ) -> Result<(), PersistenceError> {
        self.log.borrow_mut().push(format!("{}:persist", self.label));
        Ok(())
    }

    fn retract(&mut self, kb: &KnowledgeBase, id: RuleId) -> Result<bool, PersistenceError> {
        // Name the ROW, not just the call: a routing bug that sent both retracts to one
        // store would still produce two log lines, and only the functor tells them apart.
        let functor = value_functor(kb, kb.rule_head_value(id))
            .map(|s| kb.local_name_of(s).to_string())
            .unwrap_or_else(|| "<non-functor>".to_string());
        self.log
            .borrow_mut()
            .push(format!("{}:retract:{functor}", self.label));
        Ok(true)
    }

    fn flush(&mut self, _kb: &KnowledgeBase) -> Result<(), PersistenceError> {
        Ok(())
    }
}

/// The store VALUE a recorder registers under. It differs per label, so two mirrors get
/// distinct canonical keys — registering both under one key would replace rather than
/// coexist, which is a different test.
fn recorder_store_value(interp: &mut Interpreter, label: &str) -> Value {
    let functor = interp.kb_mut().intern("RecordingStore");
    let label_field = interp.kb_mut().intern("label");
    Value::Entity {
        functor,
        pos: vec![].into(),
        named: vec![(label_field, Value::Str(label.to_string()))].into(),
    }
}

/// Register a `RecordingStore` under a distinct store value, covering `covers`. Returns the
/// shared log.
fn register_recorder(
    interp: &mut Interpreter,
    label: &'static str,
    covers: &[&str],
) -> Rc<RefCell<Vec<String>>> {
    let log = Rc::new(RefCell::new(Vec::new()));
    let store_val = recorder_store_value(interp, label);
    let key = interp
        .store_canonical_key(&store_val)
        .expect("canonical key");
    interp
        .register_mirror(
            key,
            Box::new(RecordingStore {
                label,
                log: Rc::clone(&log),
            }),
            covers,
        )
        .expect("the covered names are declared in SRC");
    log
}

/// Read `qname`'s single stored row and retract it through the seam — the round trip whose
/// routing this file is about.
fn retract_the_row(interp: &mut Interpreter, qname: &str) {
    let sym = interp
        .kb_mut()
        .try_resolve_symbol(qname)
        .unwrap_or_else(|| panic!("resolve `{qname}`"));
    let rows = interp
        .kb()
        .read_stored_facts(sym, BodiedRulePolicy::Refuse)
        .unwrap_or_else(|e| panic!("read_stored_facts({qname}): {e}"));
    assert_eq!(rows.len(), 1, "{qname} has exactly one fact in SRC");
    interp
        .kb_mut()
        .retract_persistent(&rows[0].reference)
        .unwrap_or_else(|e| panic!("retract_persistent({qname}): {e}"));
}

/// THE LOAD-BEARING ONE. Two mirrors, each covering one functor; each retract must reach
/// its own store and only its own.
#[test]
fn each_functor_retracts_through_its_own_mirror() {
    let mut interp = interp_for(SRC);
    let alpha_log = register_recorder(&mut interp, "alpha", &["test.wi830.Alpha830"]);
    let beta_log = register_recorder(&mut interp, "beta", &["test.wi830.Beta830"]);

    retract_the_row(&mut interp, "test.wi830.Alpha830");
    retract_the_row(&mut interp, "test.wi830.Beta830");

    assert_eq!(
        alpha_log.borrow().as_slice(),
        ["alpha:retract:Alpha830"],
        "the Alpha row belongs to the alpha mirror, and nothing else does"
    );
    assert_eq!(
        beta_log.borrow().as_slice(),
        ["beta:retract:Beta830"],
        "the Beta row belongs to the beta mirror, and nothing else does"
    );
}

/// A functor no mirror covers is resident-only: its retract drops the in-memory row and
/// touches no durability. Pre-change the sole registered mirror absorbed it.
#[test]
fn an_uncovered_functor_gets_no_mirror() {
    let mut interp = interp_for(SRC);
    let alpha_log = register_recorder(&mut interp, "alpha", &["test.wi830.Alpha830"]);

    retract_the_row(&mut interp, "test.wi830.Gamma830");

    assert!(
        alpha_log.borrow().is_empty(),
        "Gamma830 is covered by no mirror, so the alpha store must not be asked to drop it; \
         got {:?}",
        alpha_log.borrow()
    );
    let gamma = interp
        .kb_mut()
        .try_resolve_symbol("test.wi830.Gamma830")
        .expect("resolve Gamma830");
    assert!(
        interp
            .kb()
            .read_stored_facts(gamma, BodiedRulePolicy::Refuse)
            .expect("read after retract")
            .is_empty(),
        "the resident row is gone either way — only the durability leg differs"
    );
}

/// A functor has ONE durable home, so a second mirror claiming it is refused at
/// registration, where both spellings are still in hand — not at the read, one call too
/// late to say who declared what.
#[test]
fn two_mirrors_may_not_claim_one_functor() {
    use anthill_core::kb::extent::ExtentRegError;

    let mut interp = interp_for(SRC);
    let _first = register_recorder(&mut interp, "alpha", &["test.wi830.Alpha830"]);

    // The second registration, spelled out rather than via the helper, because the helper
    // unwraps and this is the refusal.
    let functor = interp.kb_mut().intern("RecordingStore");
    let label_field = interp.kb_mut().intern("label");
    let store_val = Value::Entity {
        functor,
        pos: vec![].into(),
        named: vec![(label_field, Value::Str("beta".to_string()))].into(),
    };
    let key = interp
        .store_canonical_key(&store_val)
        .expect("canonical key");
    let outcome = interp.register_mirror(
        key,
        Box::new(RecordingStore {
            label: "beta",
            log: Rc::new(RefCell::new(Vec::new())),
        }),
        &["test.wi830.Alpha830"],
    );

    match outcome {
        Err(ExtentRegError::MirrorConflict { functor, .. }) => {
            assert_eq!(functor, "test.wi830.Alpha830", "the refusal names the claim");
        }
        other => panic!("expected MirrorConflict, got {other:?}"),
    }
}

/// A ROW REACHED TWO WAYS CARRIES ONE DURABILITY LEG.
///
/// `Store.persist` mints a reference with its mirror attached; `read_stored_facts` mints
/// one from declared coverage. If those disagree, the same row retracts durably through
/// the first reference and only in-memory through the second — the resident row goes, the
/// file row stays, and nothing says so. Found in review of the first cut of this change,
/// where `persist_mirrored` stamped its mirror onto any functor while the read side
/// stamped only covered ones.
///
/// The fix is that a successful persist RECORDS coverage, so the read side finds the same
/// mirror. Refusing an uncovered persist was the other candidate and was rejected:
/// `Store.persist` accepts a bare-interned head no declaration mentions (WI-920), so a
/// refusal would have broken a supported path to fix a bookkeeping fault.
///
/// Backed out, the retract below reaches no store and the log is empty.
#[test]
fn a_persisted_functor_is_covered_by_the_mirror_that_took_it() {
    let mut interp = interp_for(SRC);
    // Registered covering NOTHING — coverage will come from the write itself.
    let log = register_recorder(&mut interp, "alpha", &[]);

    let store_val = recorder_store_value(&mut interp, "alpha");
    let delta = interp
        .kb_mut()
        .try_resolve_symbol("test.wi830.Delta830")
        .expect("resolve Delta830");
    let row = Value::Entity {
        functor: delta,
        pos: vec![].into(),
        named: vec![].into(),
    };
    interp
        .call(
            "anthill.persistence.Store.persist",
            &[store_val, row, Value::Unit],
        )
        .expect("persist Delta830 through the alpha mirror");

    // Now reach the SAME row the other way and retract through that reference.
    retract_the_row(&mut interp, "test.wi830.Delta830");

    assert_eq!(
        log.borrow().as_slice(),
        ["alpha:persist", "alpha:retract:Delta830"],
        "the mirror that took the write is the one the read hands back, so the retract \
         reaches durability instead of dropping only the resident row"
    );
}

/// CONTROL — passes before and after by design. One mirror covering the one functor it
/// holds still backs it; the fix is about WHICH mirror answers, not about whether the
/// mirror leg works at all.
#[test]
fn one_mirror_still_backs_its_own_functor() {
    let mut interp = interp_for(SRC);
    let alpha_log = register_recorder(&mut interp, "alpha", &["test.wi830.Alpha830"]);

    retract_the_row(&mut interp, "test.wi830.Alpha830");

    assert_eq!(
        alpha_log.borrow().as_slice(),
        ["alpha:retract:Alpha830"],
        "the single covering mirror still receives its row's retract"
    );
}
