//! WI-345 — loader warnings channel.
//!
//! The loader gained a non-fatal diagnostics channel (`LoadWarning`),
//! surfaced via `LoadResult::warnings`, so lint-style passes can report
//! legal-but-suspicious constructs without failing the load. This file pins
//! the substrate: the type renders as an advisory, and a clean load threads
//! an (empty) `warnings` vec all the way out through `load_all`. WI-346 is
//! the first pass that actually emits into the channel.

use anthill_core::kb::load::{self, LoadError, LoadResult, LoadWarning, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

fn load_stdlib_result() -> Result<LoadResult, Vec<LoadError>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver)
}

#[test]
fn load_warning_other_renders_as_advisory() {
    let w = LoadWarning::Other {
        message: "operation `size` shadows `Iterable.size`".to_string(),
    };
    let s = format!("{w}");
    assert!(
        s.contains("warning:") && s.contains("size"),
        "a LoadWarning should render as an advisory line naming the issue; got: {s}"
    );
    // `format_with_source` is the span-aware twin of `Display`; the span-less
    // `Other` ignores the source text and renders the bare message.
    assert_eq!(w.format_with_source("any source text"), s);
}

#[test]
fn clean_stdlib_load_carries_no_warnings() {
    // End-to-end: the channel is wired through `load_all` → `LoadResult`. The
    // field threads out of the merged result and carries NOTHING — the stdlib
    // is warning-free, so every `anthill check` / `anthill query` is too.
    //
    // History of this count, because each step was a different kind of fix:
    //   * WI-585 Phase A, TRANSITIONAL: `size` / `foldLeft` / `foldRight` were
    //     re-homed onto `FiniteCollection` (which `requires Iterable`) while
    //     still living on `Iterable`, so WI-346 flagged five shadows. Phase C
    //     (WI-589) REMOVED them from `Iterable` — the source shape went away and
    //     three warnings with it.
    //   * WI-588 Phase B, PERMANENT: `map` / `filter` — `Iterable` KEEPS its lazy
    //     (maybe-infinite → `Stream`) pair while `FiniteCollection` adds finite
    //     (→ `FiniteCollection`) ones. Both coexist BY DESIGN, so no source edit
    //     could remove these two. WI-1048 fixed the LINT instead: the two are a
    //     deliberate refinement (different return type), not an accidental
    //     collision, and `requires_shadow_is_confusable` no longer flags them.
    //
    // WI-1048 BACKED OUT: this test fails with the two map/filter shadows. The
    // lint is NOT retired — `wi346_requires_shadow_test` and
    // `wi1048_requires_shadow_refinement_test::parametric_same_signature_shadow_still_warns`
    // are the same-signature cases that must, and do, still warn.
    let result = load_stdlib_result().expect("stdlib should load cleanly");
    let msgs: Vec<String> = result.warnings.iter().map(|w| w.to_string()).collect();
    assert!(
        msgs.is_empty(),
        "the stdlib must load with no warnings; got: {msgs:?}"
    );
}
