//! WI-345 — loader warnings channel.
//!
//! The loader gained a non-fatal diagnostics channel (`LoadWarning`),
//! surfaced via `LoadResult::warnings`, so lint-style passes can report
//! legal-but-suspicious constructs without failing the load. This file pins
//! the substrate: the type renders as an advisory, and a clean load threads
//! an (empty) `warnings` vec all the way out through `load_all`. WI-346 is
//! the first pass that actually emits into the channel.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError, LoadWarning, LoadResult};
use anthill_core::parse;

fn load_stdlib_result() -> Result<LoadResult, Vec<LoadError>> {
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
    load::load_all(&mut kb, &refs, &NullResolver)
}

#[test]
fn load_warning_other_renders_as_advisory() {
    let w = LoadWarning::Other { message: "operation `size` shadows `Iterable.size`".to_string() };
    let s = format!("{w}");
    assert!(s.contains("warning:") && s.contains("size"),
        "a LoadWarning should render as an advisory line naming the issue; got: {s}");
    // `format_with_source` is the span-aware twin of `Display`; the span-less
    // `Other` ignores the source text and renders the bare message.
    assert_eq!(w.format_with_source("any source text"), s);
}

#[test]
fn clean_stdlib_load_carries_empty_warnings() {
    // End-to-end: the channel is wired through `load_all` → `LoadResult`.
    // A clean stdlib load returns a result whose `warnings` vec exists and is
    // empty — no spurious advisories, and the field threads out of the merged
    // result. (Stays valid through WI-346: the stdlib has no requires-shadow.)
    let result = load_stdlib_result().expect("stdlib should load cleanly");
    assert!(result.warnings.is_empty(),
        "clean stdlib load should carry no warnings; got: {:?}",
        result.warnings.iter().map(|w| w.to_string()).collect::<Vec<_>>());
}
