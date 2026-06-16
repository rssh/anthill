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
    let s : Stream = anthill.prelude.Iterable.iterator(cons(head: 1, tail: nil))
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
    let s : Stream[T = Int64] = anthill.prelude.Iterable.iterator(cons(head: 1, tail: nil))
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
    let s : Stream[T = String] = anthill.prelude.Iterable.iterator(cons(head: 1, tail: nil))
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

/// Review-fix regression: REFINEMENT is not violation. A bare `List` element
/// against a `List[T = Int64]` element of the SAME sort param differs at the
/// raw-bind level (distinct TermIds) but unifies — the tie check must re-test
/// through the real relation, not TermId equality.
#[test]
fn member_tie_refinement_accepted() {
    let src = r#"
namespace test.wi374.tie_refine
  import anthill.prelude.{Int64, List, Option, nil, cons, append, some, none}

  operation listy() -> List =
    append(cons(head: nil, tail: nil), cons(head: cons(head: 1, tail: nil), tail: nil))

  operation opty() -> List =
    append(cons(head: none, tail: nil), cons(head: some(1), tail: nil))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "bare-vs-parameterized same-sort bindings unify (refinement): {errs:#?}");
}

/// Review-fix regression: a same-sort SIBLING member call at a DIFFERENT
/// instance keeps its acceptance — the conflict against the body's WI-424
/// seeded rigid is exempt from the tie check (enforcing the rigid tie is a
/// separate, undecided question).
#[test]
fn sibling_member_call_at_different_instance_accepted() {
    let src = r#"
namespace test.wi374.sibling
  import anthill.prelude.{Int64}

  sort Box
    sort T = ?
    entity mk(v: T)
    operation helper(b2: Box) -> Int64 = 42
    operation use(b: Box) -> Int64 = helper(mk(v: 1))
  end
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "sibling member call at a fresh instance must stay accepted: {errs:#?}");
}

/// Review-fix regression: a TOP-LEVEL op in the SAME namespace as the sort is
/// still FOREIGN — `impl_parent_of_op` yields the namespace symbol for it, and
/// the tie gate must not treat namespace containment as sort membership.
#[test]
fn same_namespace_top_level_op_stays_foreign() {
    let src = r#"
namespace test.wi374.ns_foreign
  import anthill.prelude.{Int64, String}

  sort Box
    sort T = ?
    entity mk(v: T)
  end

  operation twoBoxes(a: Box, b: Box) -> Int64 = 42

  operation driver() -> Int64 = twoBoxes(mk(v: 1), mk(v: "x"))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "same-namespace top-level op is foreign (§3 bullet 2): {errs:#?}");
}

/// Review-fix regression: an EARLIER benign foreign conflict must not mask a
/// member-tie violation in the same call — details are recorded per var and
/// all of them are scanned.
#[test]
fn masked_member_violation_still_rejected() {
    let src = r#"
namespace test.wi374.masking
  import anthill.prelude.{Int64, String, List, nil, cons}

  sort Box
    sort T = ?
    entity mk(v: T)
    operation combine(x: List, y: List, a: Box, b: Box) -> Int64 = 42
  end

  operation driver() -> Int64 =
    combine(
      cons(head: 1, tail: nil),
      cons(head: "s", tail: nil),
      mk(v: 1),
      mk(v: "z"))
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "the Box.T violation must be caught even when a foreign List.T conflict records first"
    );
}

/// Review-fix regression: the let-annotation rewrite must NOT cost the match
/// checks their scrutinee sort — a parameterized scrutinee type resolves its
/// constructor set and exhaustiveness through the base sort.
#[test]
fn annotated_let_match_exhaustiveness_kept() {
    let src = r#"
namespace test.wi374.exhaustive
  import anthill.prelude.{Int64, Option, some, none}

  operation f() -> Int64 =
    let o : Option = some(5)
    match o
      case some(x) -> x
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "non-exhaustive match on an annotated let scrutinee must still be reported"
    );
}

/// ANCHOR (pre-existing gap, not a WI-374 regression): a written WILDCARD
/// binding (`Stream[T = ?]`) should pin nothing — the value's inferred binding
/// should replace it. The merge handles this (the `TypeVar` arm in
/// `unroll_annotation_with_inferred`), but the PRE-EXISTING WI-379 let
/// conformance check rejects the value against the `?`-carrying annotation
/// first ("expected Stream[T = ?_], got Stream[E = {}, T = Int64]") — the
/// written-`?` slot reads as an incompatible head in `types_compatible`.
/// Un-ignore when that conformance gap is fixed.
#[test]
#[ignore = "pre-existing: types_compatible rejects a written `?` binding slot (see header)"]
fn wildcard_annotation_keeps_inferred() {
    let src = r#"
namespace test.wi374.wildcard_ann
  import anthill.prelude.{Int64, List, Stream, nil, cons}

  operation driver() -> Int64 =
    let s : Stream[T = ?] = anthill.prelude.Iterable.iterator(cons(head: 1, tail: nil))
    anthill.prelude.Stream.count(s)
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "a written wildcard must take the inferred binding: {errs:#?}");
}

/// CONSTRUCTOR tie, enforced (same §3-bullet-1 decision, field peer): two
/// fields typed at the sort's own param must agree — `pair2(1, "x")` with
/// `entity pair2(a: T, b: T)` was silently accepted (the contradiction was
/// recorded but never consulted; the built type carried `T = Int64` with a
/// String inside).
#[test]
fn ctor_member_tie_conflicting_fields_rejected() {
    let src = r#"
namespace test.wi374.ctor_tie
  import anthill.prelude.{Int64, String}

  sort Box
    sort T = ?
    entity pair2(a: T, b: T)
  end

  operation driver() -> Box = pair2(a: 1, b: "x")
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "conflicting bindings of the sort's T across constructor fields must be rejected"
    );
}

/// …and a bare self-sort FIELD (`cons`'s `tail: List`) ties the same way:
/// consing an Int64 head onto a String-element tail is rejected.
#[test]
fn ctor_member_tie_self_sort_field_rejected() {
    let src = r#"
namespace test.wi374.ctor_tail
  import anthill.prelude.{Int64, String, List, nil, cons}

  operation driver() -> List =
    cons(head: 1, tail: cons(head: "x", tail: nil))
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "cons(Int64 head, String-element tail) must be rejected (field tie, enforced)"
    );
}

/// Consistent constructor fields stay accepted, and bare-vs-parameterized
/// same-sort field bindings are refinement (re-unified), not violation.
#[test]
fn ctor_member_tie_consistent_and_refinement_accepted() {
    let src = r#"
namespace test.wi374.ctor_ok
  import anthill.prelude.{Int64, List, nil, cons}

  sort Box
    sort T = ?
    entity pair2(a: T, b: T)
  end

  operation consistent() -> Box = pair2(a: 1, b: 2)

  operation refine() -> Box =
    pair2(a: nil, b: cons(head: 1, tail: nil))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "consistent / refining constructor fields must stay accepted: {errs:#?}");
}

/// Review-fix regression (round 3): enforcement must be ORDER-INDEPENDENT on
/// one var — a benign first conflict (a WI-384 `?_` wildcard pair from the
/// arity-keeping constructor build) must not mask a later genuine violation
/// on the SAME var. `mkA(a: 2)` carries `B = ?_`; both argument orders of the
/// Int64-vs-String `B` conflict must reject.
#[test]
fn member_tie_wildcard_first_still_rejected() {
    let benign_first = r#"
namespace test.wi374.order1
  import anthill.prelude.{Int64, String}

  sort Pair2
    sort A = ?
    sort B = ?
    entity mkA(a: A)
    entity mkB(b: B)
    operation comb(x: Pair2, y: Pair2, z: Pair2) -> Int64 = 42
  end

  operation driver() -> Int64 = comb(mkB(b: 1), mkA(a: 2), mkB(b: "x"))
end
"#;
    let genuine_first = r#"
namespace test.wi374.order2
  import anthill.prelude.{Int64, String}

  sort Pair2
    sort A = ?
    sort B = ?
    entity mkA(a: A)
    entity mkB(b: B)
    operation comb(x: Pair2, y: Pair2, z: Pair2) -> Int64 = 42
  end

  operation driver() -> Int64 = comb(mkB(b: 1), mkB(b: "x"), mkA(a: 2))
end
"#;
    for (label, src) in [("benign-first", benign_first), ("genuine-first", genuine_first)] {
        let errs = load_errors(&[src]);
        assert!(
            !errs.is_empty(),
            "{label}: the Int64-vs-String conflict on Pair2.B must reject regardless of order"
        );
    }
}

/// Signature expansion end-to-end sanity: a FOREIGN op with a bare `List`
/// return loads, and its call site stays usable through an annotation. (The
/// return itself is deliberately NOT expanded — a bare return is erased, §5;
/// the annotation-as-bound-type is what carries the element here, the same
/// bare-vs-parameterized width acceptance as before WI-374.)
#[test]
fn foreign_bare_return_op_loads_and_narrows() {
    let src = r#"
namespace test.wi374.foreign_ret
  import anthill.prelude.{Int64, Option, List, nil, cons}
  import anthill.prelude.List.{nth}

  operation makeList() -> List = cons(head: 1, tail: nil)

  operation driver() -> Option[T = Int64] =
    let l : List[T = Int64] = makeList()
    nth(l, 0)
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "foreign bare-return op must load and narrow via annotation: {errs:#?}");
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
    operation produce(s: Src) -> Stream = anthill.prelude.Iterable.iterator(cons(head: 1, tail: nil))
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

