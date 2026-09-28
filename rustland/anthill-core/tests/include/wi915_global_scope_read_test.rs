//! WI-915 — THE TOP-LEVEL SCOPE IS OWNED ONCE, SO ASKING WHAT A HOST NAME DENOTES IS A
//! READ. `KnowledgeBase::global_scope` used to re-intern the sentinel on every call,
//! which forced `&mut self` onto it and onto `resolve_name_in_global` (WI-908's entry
//! point for host names). `SymbolTable::new` now mints it once.
//!
//! CONTROL — back out to the `&mut self` signatures and this file stops COMPILING: both
//! calls below go through a shared `&KnowledgeBase`. The value assertions pass either
//! way by design; they keep the read honest (it still resolves, to the declared symbol).

use anthill_core::kb::KnowledgeBase;
use anthill_core::intern::ResolveResult;

#[test]
fn a_host_name_resolves_through_a_shared_borrow() {
    let owned = crate::common::load_kb_with("namespace wi915\n  sort S\n  end\nend\n");
    let kb: &KnowledgeBase = &owned;

    let declared = kb
        .try_resolve_symbol("wi915.S")
        .expect("`wi915.S` is declared");
    assert!(
        matches!(kb.resolve_name_in_global("wi915.S"), ResolveResult::Found(s) if s == declared),
        "the qualified host name must resolve at the top level to the declared sort",
    );
    assert!(matches!(kb.resolve_name_in_global("S"), ResolveResult::NotFound));

    // The top-level scope is the one the loader filed the namespace under.
    let ns = kb.try_resolve_symbol("wi915").expect("the namespace is declared");
    assert_eq!(kb.declaring_scope_symbol(ns), Some(kb.global_scope().owner()));
}
