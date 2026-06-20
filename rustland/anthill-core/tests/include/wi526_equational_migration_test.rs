//! WI-526 — radius-3 migration of `=` equational rule heads to `<=>`.
//!
//! These tests pin the OBSERVABLE invariant that matters: a migrated `<=>`
//! equation head must resolve to the canonical `anthill.kernel.unify`, NOT a
//! per-namespace `<ns>.unify` shadow minted by `scan_rule_goal` when `unify`
//! is not reachable in the file's scope. A shadow silently hides the equation
//! from `apply_eq_rules` (which selects under the canonical functor).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_stdlib() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

/// Sort scopes whose `<=>`-migrated equations must resolve to canonical
/// `anthill.kernel.unify` rather than a `<ns>.unify` shadow.
const MIGRATED_SCOPES: &[&str] = &[
    "anthill.prelude.Pair",
    "anthill.prelude.Eq",
    "anthill.prelude.Set",
    "anthill.prelude.String",
    "anthill.prelude.Map",
    "anthill.prelude.Int64",
    "anthill.prelude.Float",
    "anthill.prelude.List",
];

#[test]
fn migrated_equation_heads_resolve_to_canonical_unify_not_shadow() {
    let kb = load_stdlib();
    let mut shadows = Vec::new();
    for ns in MIGRATED_SCOPES {
        let shadow = format!("{ns}.unify");
        if kb.try_resolve_symbol(&shadow).is_some() {
            shadows.push(shadow);
        }
    }
    assert!(
        shadows.is_empty(),
        "the loader minted per-namespace `unify` shadows for these `<=>` equation \
         heads instead of resolving them to canonical `anthill.kernel.unify` — the \
         equations are silently hidden from `apply_eq_rules`:\n  {}",
        shadows.join("\n  "),
    );
}
