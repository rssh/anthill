//! WI-448 — a `line_comment` immediately preceding an operation must NOT re-scope
//! that operation's trailing `requires` clause.
//!
//! BUG: both `requires_clause` (the operation's trailing clause, op-scoped, takes a
//! `rule_body`) and `requires_declaration` (a standalone sort/namespace declaration,
//! enclosing-scoped, takes a `_type`) begin with the `requires` token. The GLR
//! conflict `[$.operation_declaration]` explores both; their costs are otherwise
//! equal, and a comment preceding the operation tipped the tie toward the standalone
//! `requires_declaration` — silently re-scoping the clause's names (op-type-params and
//! other op-locals) to the ENCLOSING namespace, where they are unresolved. The return
//! type was unaffected (only the trailing clause), and the file still "checked green"
//! because `UnresolvedName` is non-blocking — a silent mis-scope (violates
//! loud-error-over-silent-skip).
//!
//! FIX (grammar): `prec.dynamic` on `requires_clause` biases the GLR conflict toward
//! the op-clause parse, matching the comment-free behavior regardless of comments.
//!
//! These tests load with NO stdlib (the snippets define their own `Eq`) so the only
//! diagnostics are from the snippet itself. `load_all` returns ALL errors (blocking or
//! not) in its `Err`, so the otherwise-non-blocking `UnresolvedName` is observable here.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Load ONLY `src` (no stdlib) and return every load error as a string.
fn load_errors_no_stdlib(src: &str) -> Vec<String> {
    let parsed = parse::parse(src).expect("parse");
    let refs = vec![&parsed];
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// The minimal repro from the ticket, parameterized on a leading `lead` line (a comment,
/// a blank line, or nothing). `f`'s op-type-param `T` is used in its `requires` clause.
fn src_with_lead(lead: &str) -> String {
    format!(
        r#"namespace m
  sort Eq
    sort T = ?
  end
{lead}  operation f[T](x: T) -> T requires Eq[T = T]
end
"#
    )
}

/// THE BUG: a `-- doc` comment immediately before the operation must not push the
/// `requires` clause's `T` out to the namespace scope. Before the fix this emitted
/// `unresolved name 'T' in scope 'm'`.
#[test]
fn comment_before_op_does_not_rescope_requires_clause() {
    let errs = load_errors_no_stdlib(&src_with_lead("  -- doc\n"));
    assert!(
        !errs.iter().any(|e| e.contains("unresolved name 'T'")),
        "a comment before the op must not re-scope its requires clause's op-type-param \
         T to the namespace; got: {errs:?}"
    );
}

/// EQUIVALENCE: the commented form must behave EXACTLY like the comment-free form —
/// both resolve the op-type-param `T` in the requires clause (op scope), no unresolved
/// name. (Comment-free was already correct; this pins that the comment changes nothing.)
#[test]
fn requires_clause_resolves_identically_with_and_without_lead() {
    for lead in ["", "  -- doc\n", "\n", "  -- a\n  -- b\n"] {
        let errs = load_errors_no_stdlib(&src_with_lead(lead));
        assert!(
            !errs.iter().any(|e| e.contains("unresolved name 'T'")),
            "lead {lead:?} must not re-scope the requires clause; got: {errs:?}"
        );
    }
}

/// The fix must not consume a GENUINE sort-level `requires_declaration` that does NOT
/// follow an operation — `requires Eq[T = T]` placed before the operations stays a
/// sort-scoped declaration and resolves `T` (the sort's own member) cleanly, even with
/// a preceding comment.
#[test]
fn sort_level_requires_before_ops_still_resolves() {
    let src = r#"namespace m
  sort Eq
    sort T = ?
  end
  sort S
    sort T = ?
    -- doc
    requires Eq[T = T]
    operation f(x: T) -> T
  end
end
"#;
    let errs = load_errors_no_stdlib(src);
    assert!(
        !errs.iter().any(|e| e.contains("unresolved name 'T'")),
        "a sort-level requires before the ops must resolve its member T in the sort \
         scope; got: {errs:?}"
    );
}
