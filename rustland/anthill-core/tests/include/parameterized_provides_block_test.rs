//! A PARAMETERIZED standalone `provides` block loads.
//!
//! `provides Stack[T = Int64] language rust … end` is the form the grammar's own
//! doc comment documents (`tree-sitter-anthill/grammar.js`), and nothing in the
//! repo — no stdlib file, no fixture, no test — exercised it. That gap let the
//! sort/domain-as-`Symbol` change ship a loader ABORT for it: the block's spec
//! lowers to a SortView APPLICATION (`SortView(Stack, T = Int64)`), not a bare
//! name, and the new domain derivation unwrapped it as one.
//!
//! Two things are pinned here, and they pull in opposite directions:
//!
//!   * the DOMAIN of the block's inner clauses is the BASE sort (`Stack`) — a
//!     clause belongs to the sort, not to one instantiation of it;
//!   * the SCOPE is the full applied term, so `Stack[T = Int64]` and
//!     `Stack[T = String]` stay distinct identities.
//!
//! The unparameterized block is kept beside it as the control: it took the same
//! code path before and after, so if IT breaks the cause is not the spec shape.

use anthill_core::kb::KnowledgeBase;

use crate::common::try_load_kb_with;

/// Load `source` over the full stdlib, returning the load errors as strings.
/// The stdlib is REQUIRED, not incidental: the `Implementation` fact this block
/// emits names `anthill.realization.CarrierBinding`, so a prelude-only KB aborts
/// in `resolve_symbol` before reaching anything under test.
/// Deliberately NOT `load_kb_with` (which panics on error): the point of these
/// tests is what the loader DOES with the input, so a failure must be readable.
fn load_errors(source: &str) -> Vec<String> {
    try_load_kb_with(source).err().unwrap_or_default()
}

const PARAMETERIZED: &str = r#"
namespace test.pb
  sort Stack
    entity mk(x: Int64)
  end

  provides Stack[T = Int64]
    language rust
    artifact "src/stack.rs"
  end
end
"#;

const UNPARAMETERIZED: &str = r#"
namespace test.pb
  sort Stack
    entity mk(x: Int64)
  end

  provides Stack
    language rust
    artifact "src/stack.rs"
  end
end
"#;

#[test]
fn parameterized_provides_block_loads() {
    // Before the fix this did not FAIL — it panicked the process, so there was no
    // error list to assert on at all.
    assert!(
        load_errors(PARAMETERIZED).is_empty(),
        "parameterized provides block should load: {:?}",
        load_errors(PARAMETERIZED)
    );
}

#[test]
fn unparameterized_provides_block_loads() {
    assert!(
        load_errors(UNPARAMETERIZED).is_empty(),
        "unparameterized provides block should load: {:?}",
        load_errors(UNPARAMETERIZED)
    );
}

/// The `Implementation` fact is emitted for a non-`anthill` language, and its
/// domain is the BASE sort — the same domain the unparameterized block yields.
/// This is the assertion that would have caught the abort as a *wrong answer*
/// rather than as a crash: if the domain were derived from the applied term it
/// would differ between the two blocks.
#[test]
fn both_spec_shapes_file_the_implementation_fact_under_the_base_sort() {
    let domain_of = |source: &str| -> Vec<String> {
        let mut kb: KnowledgeBase = crate::common::load_kb_with(source);
        let impl_sort = kb.intern("anthill.realization.Implementation");
        // Filtered to this file's namespace: the Rust host bindings loaded
        // alongside emit their own `Implementation` facts (Int64, String, …).
        kb.by_sort(impl_sort)
            .iter()
            .map(|&rid| kb.qualified_name_of(kb.rule_domain(rid)).to_string())
            .filter(|d| d.starts_with("test.pb"))
            .collect()
    };
    let param = domain_of(PARAMETERIZED);
    assert_eq!(param.len(), 1, "expected one Implementation fact, got {param:?}");
    assert_eq!(param, domain_of(UNPARAMETERIZED), "domain must not depend on the spec shape");
    assert!(param[0].ends_with("Stack"), "domain should be the base sort, got {param:?}");
}
