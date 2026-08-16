//! WI-830 — THE BINDING IS DECLARED IN ANTHILL, NOT SPELLED IN THE HOST.
//!
//! Sibling of `wi830_mirror_coverage_test`, which pins the registry half (a mirror covers
//! the functors it is declared to cover). This file pins the CONFIGURATION half: where
//! that declaration comes from.
//!
//! Until now, "which store holds which functors" existed only as Rust in the embedding
//! binary — anthill-todo built one `IndexedFileStore` at a fixed path and named its
//! functors in a literal array. A project could not say it, so a project could not change
//! it, which is the whole of what WI-437 (a GitHub-backed tracker) is blocked on.
//!
//! `fact ExtentBinding(store:, role:, covers:)` is that declaration (proposal 057
//! §"Configuration & bootstrap"), and `KnowledgeBase::extent_bindings` reads it back.
//!
//! WHAT THE SEAM DOES NOT DO — and the split is deliberate. `extent_bindings` returns the
//! store as the `Value` the project WROTE; it does not instantiate anything. A backend is
//! native code, so declarative configuration chooses AMONG the host's compiled-in
//! backends and cannot introduce new ones. The host matches the value against its own
//! factory. `binding_drives_a_real_registration` plays the host's part with a recording
//! store, so the decoded `covers` really does reach `register_mirror` and really does
//! route a retract — the full loop, minus the tracker's own path plumbing.
//!
//! WHAT FAILS WITHOUT THE CHANGE: all six. `ExtentBinding` / `ExtentRole` are declared by
//! this change in `stdlib/anthill/persistence/store.anthill`, and `extent_bindings` is the
//! reader it adds; against the prior tree every fixture fails its import and the method
//! does not exist. There is no partial-credit control here — the previous state of this
//! capability was its absence, so nothing in this file can pass both ways.
//!
//! A NOTE ON WHERE THE ROLE REFUSAL LIVES. `role: ExtentRole` is a declared field type, so
//! a project that writes a non-role is refused by the LOADER, at the site, before any of
//! this runs — `a_role_that_is_not_a_role_is_refused_at_load` pins that, and it is the
//! stronger guarantee (unrepresentable rather than checked). `ExtentBindingError`'s own
//! role variants stay for rows that never passed through the loader's field check.
//!
//! STDLIB LOADS: six, one per `#[test]`.

use std::cell::RefCell;
use std::rc::Rc;

use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::extent::{BodiedRulePolicy, ExtentBindingError, ExtentRole};
use anthill_core::kb::term::TermId;
use anthill_core::kb::{ClauseKind, KnowledgeBase, RuleId};
use anthill_core::persistence::{PersistenceError, Store};

use crate::common::interp_for;

/// A project declaring one mirror binding over two of its three functors. `Gamma831` is
/// deliberately outside `covers`: a binding names what it holds, and the rest of the KB is
/// not swept in.
const SRC: &str = r#"namespace test.wi830b
  import anthill.persistence.{ExtentBinding, FileStore}
  import anthill.persistence.ExtentRole.{mirror}
  entity Alpha831
  entity Beta831
  entity Gamma831
  fact Alpha831()
  fact Beta831()
  fact Gamma831()
  fact ExtentBinding(
    store: FileStore(root: "tracker", convention: flat()),
    role: mirror(),
    covers: [Alpha831, Beta831])
end
"#;

fn sym(interp: &mut Interpreter, qname: &str) -> Symbol {
    interp
        .kb_mut()
        .try_resolve_symbol(qname)
        .unwrap_or_else(|| panic!("resolve `{qname}`"))
}

/// A project source with `binding` spliced in as its sole `ExtentBinding` fact — the
/// malformed-declaration tests differ only in that one term.
fn src_with(binding: &str) -> String {
    format!(
        "namespace test.wi830b\n  \
         import anthill.persistence.{{ExtentBinding, FileStore}}\n  \
         import anthill.persistence.ExtentRole.{{mirror, owner}}\n  \
         entity Alpha831\n  \
         entity Beta831\n  \
         fact Alpha831()\n  \
         fact ExtentBinding({binding})\n\
         end\n"
    )
}

/// The store spec every binding below names, spelled once.
const STORE: &str = r#"store: FileStore(root: "tracker", convention: flat())"#;

// ── the decode ─────────────────────────────────────────────────

#[test]
fn a_declared_binding_reads_back_as_role_and_covered_functors() {
    let mut interp = interp_for(SRC);
    let alpha = sym(&mut interp, "test.wi830b.Alpha831");
    let beta = sym(&mut interp, "test.wi830b.Beta831");

    let bindings = interp.kb().extent_bindings().expect("the binding decodes");

    assert_eq!(bindings.len(), 1, "one ExtentBinding fact was declared");
    assert_eq!(bindings[0].role, ExtentRole::Mirror, "the declared role");
    assert_eq!(
        bindings[0].covers,
        vec![alpha, beta],
        "covers reads back as the functors named, in written order, and NOT Gamma831"
    );
}

/// The store field comes back as the project's own term, for the host's factory to match.
/// Asserting on its FUNCTOR is the part the seam is responsible for: it hands over what
/// was written rather than interpreting it.
#[test]
fn the_store_field_is_handed_over_unread() {
    let mut interp = interp_for(SRC);
    let file_store = sym(&mut interp, "anthill.persistence.filesystem.FileStore");

    let bindings = interp.kb().extent_bindings().expect("the binding decodes");
    let store_functor = anthill_core::eval::value_functor(interp.kb(), &bindings[0].store)
        .expect("the store field carries a functor");

    assert_eq!(
        store_functor, file_store,
        "the seam reports WHICH backend was declared and stops there"
    );
}

/// A KB with no binding facts has no bindings — not an error. The tracker's own KB looked
/// like this until its `project.anthill` gained one.
#[test]
fn no_binding_facts_is_an_empty_list_not_a_failure() {
    let interp = interp_for("namespace test.wi830c\n  entity Delta831\nend\n");
    assert!(interp
        .kb()
        .extent_bindings()
        .expect("no bindings is not a fault")
        .is_empty());
}

// ── the refusals ───────────────────────────────────────────────

/// A binding that covers nothing is a mistake, not an empty configuration: it registers a
/// backend that will never be consulted, and reads as "configured" from every side.
#[test]
fn a_binding_covering_nothing_is_refused() {
    let interp = interp_for(&src_with(&format!("{STORE}, role: mirror(), covers: []")));
    match interp.kb().extent_bindings() {
        Err(ExtentBindingError::EmptyCovers) => {}
        other => panic!("expected EmptyCovers, got {other:?}"),
    }
}

/// A `role` naming something that is not an `ExtentRole` never reaches the reader at all:
/// `role: ExtentRole` is a declared field type, so the loader's entity-field check refuses
/// it where it is WRITTEN. That is the stronger guarantee — illegal state unrepresentable
/// rather than checked — and it is why this pins the LOAD error and not
/// `ExtentBindingError::UnknownRole`.
///
/// The runtime variant is kept regardless, because it guards a row that did not come from
/// source text (a runtime `KB.assert` carries no field typing); it is simply not
/// reachable from a project file, which is the case this test is about.
#[test]
fn a_role_that_is_not_a_role_is_refused_at_load() {
    let errors = match crate::common::try_load_kb_with(&src_with(&format!(
        "{STORE}, role: Alpha831(), covers: [Alpha831]"
    ))) {
        Err(errors) => errors,
        Ok(_) => panic!("a role that is not an ExtentRole must not load"),
    };
    assert!(
        errors.iter().any(|e| e.contains("ExtentBinding.role")
            && e.contains("expected ExtentRole")
            && e.contains("Alpha831")),
        "the load refusal names the field, the expected sort and the offender; got {errors:?}"
    );
}

// ── the loop, with the host's part played ──────────────────────

/// A mirror that records what it is asked to drop — the observable for "did the DECLARED
/// coverage reach registration".
struct RecordingStore {
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
        Ok(())
    }

    fn retract(&mut self, kb: &KnowledgeBase, id: RuleId) -> Result<bool, PersistenceError> {
        let functor = anthill_core::eval::value_functor(kb, kb.rule_head_value(id))
            .map(|s| kb.local_name_of(s).to_string())
            .unwrap_or_else(|| "<non-functor>".to_string());
        self.log.borrow_mut().push(functor);
        Ok(true)
    }

    fn flush(&mut self, _kb: &KnowledgeBase) -> Result<(), PersistenceError> {
        Ok(())
    }
}

/// END TO END. Read the project's binding, play the host — instantiate a backend for the
/// declared store and register it under the declared role with the declared coverage —
/// then retract a covered row and an uncovered one. Only the covered retract reaches the
/// store, and it does so because a `.anthill` file said which functors it holds.
#[test]
fn binding_drives_a_real_registration() {
    let mut interp = interp_for(SRC);

    let bindings = interp.kb().extent_bindings().expect("the binding decodes");
    let binding = bindings.into_iter().next().expect("one binding");
    assert_eq!(binding.role, ExtentRole::Mirror, "the host branches on this");

    let log = Rc::new(RefCell::new(Vec::new()));
    let key = interp
        .store_canonical_key(&binding.store)
        .expect("canonical key of the declared store");
    // The host's factory would pick a backend by `binding.store`'s functor; here the
    // recorder stands in for whatever `FileStore` maps to.
    let covers: Vec<String> = binding
        .covers
        .iter()
        .map(|s| interp.kb().qualified_name_of(*s).to_string())
        .collect();
    let covers_ref: Vec<&str> = covers.iter().map(String::as_str).collect();
    interp
        .register_mirror(
            key,
            Box::new(RecordingStore {
                log: Rc::clone(&log),
            }),
            &covers_ref,
        )
        .expect("the covered names came from the KB, so they resolve");

    for qname in [
        "test.wi830b.Alpha831", // covered
        "test.wi830b.Gamma831", // not covered
    ] {
        let functor = sym(&mut interp, qname);
        let rows = interp
            .kb()
            .read_stored_facts(functor, BodiedRulePolicy::Refuse)
            .expect("read");
        interp
            .kb_mut()
            .retract_persistent(&rows[0].reference)
            .expect("retract");
    }

    assert_eq!(
        log.borrow().as_slice(),
        ["Alpha831"],
        "only the DECLARED functor's retract reached the store; Gamma831 was never bound"
    );
}
