//! WI-040 — the kernel DESUGARING VOCAB (reflect `Expr` / `Pattern`
//! constructors, `field_access`, the literal carriers `ListLiteral` /
//! `SetLiteral` / `TupleLiteral`, reflection primitives) is RESERVED: a bare
//! reference resolves DIRECTLY to its qualified home, with no `_global` import.
//!
//! This guards the QUERY-pattern path specifically (`convert_query_term` ->
//! `resolve_name_in_kb_opt`). Removing the `_global` imports regressed it — a
//! bare reserved name in a query silently bare-interned and matched nothing —
//! and the `kernel_vocab_qualified` fallback restores it. The loader / op-body
//! paths are covered by the rest of the suite (they resolve the vocab directly
//! via `remap_name_str` and `ExprBuilderSyms` respectively).

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use std::collections::HashMap;

fn load_stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib loads clean");
    kb
}

/// The functor of `fact <pattern>` after the query-term conversion path.
fn query_pattern_functor_qn(kb: &mut KnowledgeBase, pattern: &str) -> String {
    let src = format!("fact {pattern}");
    let parsed = parse::parse(&src).expect("parse query pattern");
    let _ = load::scan_definitions(kb, &[&parsed]);
    let global_raw = kb.make_name_term("_global").raw();
    let mut var_map = HashMap::new();
    for item in &parsed.items {
        if let anthill_core::parse::ir::Item::Fact(f) = item {
            let t =
                load::convert_query_term(kb, &parsed.terms, &parsed.symbols, f.term, global_raw, &mut var_map);
            if let Term::Fn { functor, .. } = kb.get_term(t) {
                return kb.qualified_name_of(*functor).to_string();
            }
        }
    }
    panic!("query pattern `{pattern}` produced no Fn term");
}

/// A bare reflection primitive (`field_access`) in a query pattern — with no
/// import and no `_global` rescue — resolves to its reserved reflect home.
#[test]
fn query_pattern_bare_field_access_resolves_qualified() {
    let mut kb = load_stdlib_kb();
    let qn = query_pattern_functor_qn(&mut kb, "field_access(object: ?o, field: ?f)");
    assert_eq!(
        qn, "anthill.reflect.field_access",
        "bare reserved `field_access` in a query must resolve to its qualified \
         reflect home (WI-040 reserved-vocab fallback), not bare-intern; got {qn:?}"
    );
}

/// A bare literal carrier (`ListLiteral`) likewise resolves directly — the
/// carrier MUST carry its qualified name so consumers keyed on
/// `anthill.reflect.ListLiteral` still fire.
#[test]
fn query_pattern_bare_list_literal_resolves_qualified() {
    let mut kb = load_stdlib_kb();
    let qn = query_pattern_functor_qn(&mut kb, "ListLiteral(?x)");
    assert_eq!(
        qn, "anthill.reflect.ListLiteral",
        "bare reserved `ListLiteral` carrier in a query must resolve to its \
         qualified reflect home (WI-040), not bare-intern; got {qn:?}"
    );
}

// Precedence note: the reserved resolution is a FALLBACK — `kernel_vocab_qualified`
// is called only in the `_ => None` arm of `resolve_in_scope`'s match in
// `resolve_name_in_kb_opt` / `remap_name_str`, so it physically cannot fire when a
// name resolves in scope. A user-defined same-spelling name therefore always wins;
// the reserved set only catches the synthesized reference no scope defines. This is
// guaranteed by code structure (not asserted here — exercising a namespace's exact
// symbol-scope from a query harness is brittle; the resolver's scope precedence is
// covered by `wi476_scope_chain_test`).
