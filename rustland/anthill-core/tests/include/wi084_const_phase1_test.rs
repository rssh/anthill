//! WI-084 / proposal 039 — term-level named constants, **Phase 1** (grammar +
//! loader).
//!
//! Phase 1 scope: a `const NAME: T [= EXPR]` declaration parses, and the loader
//! defines a `SymbolKind::Const` symbol carrying the declared type, storing the
//! body (when present) in a per-symbol side-table. NO value source, folding,
//! purity gate, typing of a bare reference, or eval yet — those are later
//! phases. So these tests assert only the loader-visible facts:
//!
//! 1. A file with consts (bodied + bodyless, namespace + sort scope, with
//!    visibility prefixes, and const-expression composition) loads with no
//!    errors.
//! 2. Each const symbol exists with `SymbolKind::Const`.
//! 3. The declared type is recorded (`kb.const_type`).
//! 4. The body is stored for a bodied const and ABSENT for a bodyless one
//!    (`kb.const_body_node`).
//!
//! The parse/CST side is exercised in `tree-sitter-anthill/test/corpus/const.txt`.

use anthill_core::intern::SymbolKind;
use anthill_core::kb::typing::extract_sort_ref_sym;

const SRC: &str = r#"
namespace test.wi084
  import anthill.prelude.{Int64, Float}

  -- concrete, anthill-bodied
  const BROADCAST_CHANNEL: Int64 = -1
  -- host-supplied (no body)
  const CHANNEL_BROADCAST: Int64
  -- visibility prefixes
  public const D_MIN: Float = 1.0
  internal const D_MAX: Float = 20.0
  -- const-expression composition (references another const)
  const PI: Float = 3.14159
  const TWO_PI: Float = 2.0 * PI

  sort Emitter
    const BROADCAST: Int64 = -1
  end
end
"#;

fn kb() -> anthill_core::kb::KnowledgeBase {
    crate::common::try_load_kb_with(SRC).unwrap_or_else(|errs| {
        for e in &errs {
            eprintln!("{e}");
        }
        panic!("WI-084 Phase 1 source should load cleanly; {} errors", errs.len());
    })
}

/// Resolve a qualified name and assert it is a `Const` symbol.
fn assert_const_kind(kb: &anthill_core::kb::KnowledgeBase, qname: &str) -> anthill_core::intern::Symbol {
    let sym = kb
        .try_resolve_symbol(qname)
        .unwrap_or_else(|| panic!("const `{qname}` should resolve to a symbol"));
    assert_eq!(
        kb.kind_of(sym),
        Some(SymbolKind::Const),
        "`{qname}` should have SymbolKind::Const"
    );
    sym
}

#[test]
fn const_declarations_load_cleanly() {
    // Step 1: the whole file (every const form) loads without errors. This also
    // proves sort-body routing — `sort Emitter { const BROADCAST ... }` goes
    // through `load_items` like a namespace-level const.
    let _ = kb();
}

#[test]
fn bodied_const_has_kind_type_and_stored_body() {
    let kb = kb();
    let sym = assert_const_kind(&kb, "test.wi084.BROADCAST_CHANNEL");
    assert!(
        kb.const_type(sym).is_some(),
        "a bodied const must record its declared type"
    );
    assert!(
        kb.const_body_node(sym).is_some(),
        "a bodied const must store its body node"
    );
}

#[test]
fn bodyless_const_has_kind_and_type_but_no_body() {
    let kb = kb();
    let sym = assert_const_kind(&kb, "test.wi084.CHANNEL_BROADCAST");
    assert!(
        kb.const_type(sym).is_some(),
        "a bodyless (host-supplied) const still records its declared type"
    );
    assert!(
        kb.const_body_node(sym).is_none(),
        "a bodyless const must NOT store a body node"
    );
}

#[test]
fn visibility_prefixed_consts_are_const_symbols() {
    let kb = kb();
    // `public` / `internal` prefixes parse and load as ordinary consts.
    assert_const_kind(&kb, "test.wi084.D_MIN");
    assert_const_kind(&kb, "test.wi084.D_MAX");
}

#[test]
fn const_expression_composition_stores_a_body() {
    let kb = kb();
    // `const TWO_PI: Float = 2.0 * PI` — references another const. Phase 1 only
    // STORES the body (no folding); the reference need not yet be evaluated.
    let pi = assert_const_kind(&kb, "test.wi084.PI");
    assert!(kb.const_body_node(pi).is_some());
    let two_pi = assert_const_kind(&kb, "test.wi084.TWO_PI");
    assert!(
        kb.const_body_node(two_pi).is_some(),
        "a composed const stores its (still-symbolic) body"
    );
}

#[test]
fn declared_type_is_the_right_sort() {
    // Content check (not just `is_some`): the stored declared type must be the
    // sort the source actually wrote — `Int64` for BROADCAST_CHANNEL, `Float`
    // for D_MIN — so a regression that records the wrong/placeholder type is
    // caught. `const_type` is a carrier-agnostic `Value`; `extract_sort_ref_sym`
    // reads the underlying sort symbol via the `TermView` abstraction.
    let kb = kb();
    let int64 = kb
        .try_resolve_symbol("anthill.prelude.Int64")
        .expect("Int64 resolves");
    let float = kb
        .try_resolve_symbol("anthill.prelude.Float")
        .expect("Float resolves");

    let bc = assert_const_kind(&kb, "test.wi084.BROADCAST_CHANNEL");
    let bc_ty = kb.const_type(bc).expect("bodied const records a type");
    assert_eq!(
        extract_sort_ref_sym(&kb, bc_ty),
        Some(int64),
        "BROADCAST_CHANNEL's declared type should be Int64"
    );

    let dmin = assert_const_kind(&kb, "test.wi084.D_MIN");
    let dmin_ty = kb.const_type(dmin).expect("const records a type");
    assert_eq!(
        extract_sort_ref_sym(&kb, dmin_ty),
        Some(float),
        "D_MIN's declared type should be Float"
    );
}

#[test]
fn const_inside_sort_body_is_loaded() {
    let kb = kb();
    // A const declared inside a `sort` body is loaded with the same machinery.
    let sym = assert_const_kind(&kb, "test.wi084.Emitter.BROADCAST");
    assert!(kb.const_type(sym).is_some());
    assert!(kb.const_body_node(sym).is_some());
}
