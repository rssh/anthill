//! WI-374 — bare/partial sort-application expansion (kernel-language §8.1),
//! site-scoped per the 2026-06-12 design dialogue: context is used to unroll
//! definitions BEFORE the unify boundary (the loader knows a signature's
//! enclosing sort; the typing site knows an annotation's scope), so
//! `unify_types` stays a pure term relation.
//!
//! This file covers the LET-ANNOTATION site (user-confirmed P3 fix): a bare or
//! partial parametric-sort annotation is rewritten to KEEP the value's
//! inferred parameters instead of erasing them.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra sources → load-error strings (empty Vec on clean load).
fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// P3 — a BARE `Stream` annotation over a fully-inferred
/// `Stream[T = Int64, E = {}]` value keeps the inferred params, so the
/// downstream `count(s)` (which needs `Elem`) typechecks pure. Before WI-374
/// the annotation erased them: "expected a type for 'Elem', got unconstrained".
#[test]
fn bare_annotation_keeps_inferred_params() {
    let src = r#"
namespace test.wi374.bare_ann
  import anthill.prelude.{Int64, List, Stream, nil, cons}

  operation driver() -> Int64 =
    let s : Stream = anthill.prelude.List.iterator(cons(head: 1, tail: nil))
    anthill.prelude.Stream.count(s)
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "bare annotation must keep inferred params: {errs:#?}");
}

/// A PARTIAL annotation keeps its written binding and takes the rest from the
/// value: `Stream[T = Int64]` keeps `T` written, takes `E = {}` inferred —
/// `count(s)` still typechecks pure.
#[test]
fn partial_annotation_keeps_written_and_inferred() {
    let src = r#"
namespace test.wi374.partial_ann
  import anthill.prelude.{Int64, List, Stream, nil, cons}

  operation driver() -> Int64 =
    let s : Stream[T = Int64] = anthill.prelude.List.iterator(cons(head: 1, tail: nil))
    anthill.prelude.Stream.count(s)
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "partial annotation must keep written + inferred: {errs:#?}");
}

/// The annotation stays AUTHORITATIVE where written: a contradicting written
/// binding is still a mismatch (the WI-379 conformance check, unchanged).
#[test]
fn wrong_written_binding_still_rejected() {
    let src = r#"
namespace test.wi374.wrong_ann
  import anthill.prelude.{Int64, String, List, Stream, nil, cons}

  operation driver() -> Int64 =
    let s : Stream[T = String] = anthill.prelude.List.iterator(cons(head: 1, tail: nil))
    anthill.prelude.Stream.count(s)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "a contradicting written annotation binding must still be rejected"
    );
}

/// MEMBER TIE, ENFORCED (user-decided 2026-06-12, Q2): two bare self-sort
/// refs in a MEMBER signature share the sort's own param (§3 bullet 1 —
/// `append(xs: List, ys: List)` ties through `List.T`), and the tie is now a
/// real check: conflicting element types are REJECTED. Before WI-374 the
/// contradiction was recorded but never consulted (silent first-binding-wins).
#[test]
fn member_tie_conflicting_elements_rejected() {
    let src = r#"
namespace test.wi374.tie_reject
  import anthill.prelude.{Int64, String, List, nil, cons, append}

  operation driver() -> List =
    append(cons(head: 1, tail: nil), cons(head: "x", tail: nil))
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "append over conflicting element types must be rejected (member tie, enforced)"
    );
}

/// The enforced tie accepts CONSISTENT elements unchanged.
#[test]
fn member_tie_same_elements_accepted() {
    let src = r#"
namespace test.wi374.tie_accept
  import anthill.prelude.{Int64, List, nil, cons, append}

  operation driver() -> List =
    append(cons(head: 1, tail: nil), cons(head: 2, tail: nil))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "same-element append must stay accepted: {errs:#?}");
}

/// §3 bullet 2 — two bare refs of a FOREIGN sort in one signature are
/// INDEPENDENT: a top-level (non-member) op with two bare `List` params
/// accepts different element types. The enforcement above is gated to the
/// callee's OWN sort's params, so this stays accepted. (The foreign refs
/// still share canonical vars internally — normalizing them to
/// per-occurrence vars is the remaining WI-374 scope.)
#[test]
fn foreign_two_bare_params_stay_independent() {
    let src = r#"
namespace test.wi374.foreign_indep
  import anthill.prelude.{Int64, String, List, nil, cons}

  operation twoLists(a: List, b: List) -> Int64 = 42

  operation driver() -> Int64 =
    twoLists(cons(head: 1, tail: nil), cons(head: "x", tail: nil))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "foreign bare refs are independent (§3 bullet 2): {errs:#?}");
}

/// Type-not-provenance boundary (§5): expansion supplies VARIABLES, never
/// values. A producer that erases its params (bare `-> Stream` return) cannot
/// have them reconstructed by an annotation — the downstream consumer still
/// fails (unchanged, honest behavior).
#[test]
fn bare_value_stays_unusable() {
    let src = r#"
namespace test.wi374.bare_value
  import anthill.prelude.{Int64, List, Stream, nil, cons}

  sort Src
    entity mkSrc
    operation produce(s: Src) -> Stream = anthill.prelude.List.iterator(cons(head: 1, tail: nil))
  end

  operation driver() -> Int64 =
    let s : Stream = produce(mkSrc)
    anthill.prelude.Stream.count(s)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "an erased producer return must stay rejected (no reconstruction)"
    );
}
