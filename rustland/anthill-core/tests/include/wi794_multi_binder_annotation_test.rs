//! WI-794: a MULTI-BINDER lambda's parameter annotations are never checked against the
//! callback parameter slot, so a contradicting annotation loads clean.
//!
//! KNOWN GAP — this file asserts the CURRENT WRONG behaviour on purpose, so the boundary
//! stays visible in the suite and fails loudly the moment it is closed. When WI-794
//! lands, replace `known_gap_multi_binder_annotation_is_unchecked` with a rejection
//! assertion; the one-binder control below is already positive and stays as-is.
//!
//! The discriminator is BINDER COUNT and nothing else — bisected, not assumed. Filed out
//! of WI-793, whose acceptance text claimed a contradicting binder annotation was "still
//! rejected"; measurement showed that holds only at arity 1. It is NOT about
//! path-dependent types (these programs have none), not about a decoupled effect row
//! (the one-binder contradiction is rejected with `@ {EffP}` and with a closed `@ {}`
//! alike), and not about an unbound accumulator type param (a one-binder callback with
//! `Acc` in the slot is rejected too). Adding a second binder to any refused shape makes
//! it load clean.
//!
//! Note this is a missing DIAGNOSTIC, not a wrong runtime value: the binder still types
//! from the context, which wins over the annotation (kernel-language.md §4.7). The
//! annotation is simply inert — accepted and ignored — which is why it stayed invisible.

use crate::common::try_load_kb_with;

/// THE CONTROL, and it is positive: at ONE binder the contradiction IS caught.
#[test]
fn one_binder_contradicting_annotation_is_rejected() {
    let src = r#"
namespace test.wi794.one
  import anthill.prelude.{Int64, String}

  operation apply1(f: (a: Int64) -> Int64) -> Int64 = f(1)

  operation drive() -> Int64 = apply1(lambda (a: String) -> 1)
end
"#;
    let errs = try_load_kb_with(src)
        .err()
        .expect("a String binder in an Int64 slot must be refused at arity 1");
    assert!(
        errs.iter().any(|e| e.contains("String")),
        "the diagnostic must name the contradicting annotation; got: {errs:?}",
    );
}

/// THE GAP. The same contradiction at TWO binders loads clean — including when BOTH
/// annotations contradict, which rules out "only the first slot is checked".
#[test]
fn known_gap_multi_binder_annotation_is_unchecked() {
    let one_wrong = r#"
namespace test.wi794.two
  import anthill.prelude.{Int64, String}

  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(1, 2)

  operation drive() -> Int64 = apply2(lambda (a: Int64, b: String) -> a)
end
"#;
    let both_wrong = r#"
namespace test.wi794.twoboth
  import anthill.prelude.{Int64, String}

  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(1, 2)

  operation drive() -> Int64 = apply2(lambda (a: String, b: String) -> 1)
end
"#;
    assert!(
        try_load_kb_with(one_wrong).is_ok(),
        "KNOWN GAP: a contradicting SECOND binder annotation is currently accepted. \
         If this now fails, WI-794 is closed — convert this test to a rejection assertion.",
    );
    assert!(
        try_load_kb_with(both_wrong).is_ok(),
        "KNOWN GAP: contradicting BOTH annotations is currently accepted too, so the \
         gap is the multi-binder channel as a whole, not an unchecked trailing slot.",
    );
}

/// An AGREEING multi-binder annotation must keep loading — whatever closes the gap must
/// reject only the contradiction, not annotations as such.
#[test]
fn multi_binder_annotation_that_agrees_still_loads() {
    let src = r#"
namespace test.wi794.agree
  import anthill.prelude.{Int64}

  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(3, 10)

  operation drive() -> Int64 = apply2(lambda (a: Int64, b: Int64) -> a - b)
end
"#;
    assert!(try_load_kb_with(src).is_ok(), "agreeing annotations must load");
}
