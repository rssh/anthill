//! WI-987 — THE SYNTHETIC TOP-LEVEL SCOPE IS NAMED BY A SPELLING NO DECLARATION CAN
//! TAKE.
//!
//! A scope is minted from a SYMBOL (`ScopeId`, WI-984), and the top-level one's symbol
//! comes from interning a fixed name. That name used to be `_global`, which
//! `_identifier_token` (`[a-zA-Z_][a-zA-Z0-9_-]*`) admits — so `namespace _global`
//! declared a SECOND scope: `SymbolTable::define` writes `by_qualified_name("_global")`
//! and never consults the intern map, so the two never merged. Both then rendered
//! `_global` through `qualified_name_of`, which is what every scope diagnostic prints.
//! Nothing refused the declaration; nothing could tell the two scopes apart by name.
//!
//! The fix is the one `intern::ABSOLUTE_PATH_MARKER` already makes for `..`: a spelling
//! built from characters the identifier token does not admit, so the collision is
//! UNREPRESENTABLE rather than checked for. That is why this file asserts an ordinary
//! load rather than a diagnostic — there is no error case to drive.
//!
//! CONTROL, MEASURED — put `intern::GLOBAL_SCOPE_NAME` back to `"_global"` and BOTH
//! cases here fail: the first on the rendering inequality (the declaration still makes
//! its own scope, which is the point — two distinct scopes, one name), the second
//! because `_global` then parses as a namespace name. Two other sites read the constant
//! and move with it rather than discriminating: `load.rs`'s `walk_scopes` unit test and
//! `wi920_resident_write_domain_test`.
//!
//! Scaland carries the twin, `anthill.kb.GlobalScopeSentinelTest`, against its own
//! grammar. Neither tree reads the other's constant, so both are asserted.

use anthill_core::intern::GLOBAL_SCOPE_NAME;
use anthill_core::parse;

/// `namespace _global` is now an ORDINARY namespace — it loads, holds its own members,
/// and is NOT the scope the loader files top-level declarations into.
#[test]
fn a_declared_global_is_a_scope_of_its_own_and_renders_as_one() {
    let mut kb = crate::common::load_kb_with(
        "namespace _global\n  sort S\n    operation f(x: S) -> S\n  end\nend\n",
    );

    let declared = kb
        .try_resolve_symbol("_global")
        .expect("`namespace _global` must define a symbol of its own");
    // A scope IS its owner symbol (WI-984), so distinct owners are distinct scopes.
    assert_ne!(
        declared,
        kb.global_scope().owner(),
        "a declared `_global` must not own the loader's top-level scope",
    );
    // BOTH scopes are live, not just distinct: the sort inside the declaration is filed
    // under the DECLARED one. This is what made the shared rendering a hazard rather
    // than a curiosity — a name resolves against one of the two and not the other.
    let member = kb
        .try_resolve_symbol("_global.S")
        .expect("the declared `_global` holds its own members");
    assert_eq!(kb.declaring_scope_symbol(member), Some(declared));

    // THE POINT, and the discriminator: two live scopes must not RENDER alike. Asserted
    // as an inequality and not as two equalities against the constant — under the
    // control a pair of equalities BOTH HOLD (measured: this case reported green over
    // exactly the defect it exists for, until it was written this way).
    let global_owner = kb.global_scope().owner();
    assert_eq!(kb.qualified_name_of(declared), "_global");
    assert_ne!(
        kb.qualified_name_of(declared),
        kb.qualified_name_of(global_owner),
        "a diagnostic naming a scope could not say which of the two it meant",
    );
}

/// The sentinel is unspellable, so no `define` can ever reach that qualified name —
/// which is the whole of why the fix carries no check.
#[test]
fn the_sentinel_is_not_an_identifier() {
    let src = format!("namespace {GLOBAL_SCOPE_NAME}\nend\n");
    assert!(
        parse::parse(&src).is_err(),
        "the top-level scope's name must not parse as a namespace name",
    );

    // The LITERAL, pinned once. The spelling is also written out where this test cannot
    // reach it: four docs that show it to a user (`kernel-language.md` §2.3 and §8.6,
    // `cli-design.md`, proposals 001.1 and 044), the `--mode domain` help and refusal
    // hint, and scaland's own `GLOBAL_SCOPE_NAME`, which no Rust test links against.
    // Changing the constant alone leaves all of them describing a name the
    // implementation no longer uses, so the change has to come through this line.
    assert_eq!(GLOBAL_SCOPE_NAME, "<global>");
}
