//! WI-966 — no Rust source in the workspace discards the loader's verdict,
//! except in one helper whose NAME says it does.
//!
//! This is a mechanical guard, and it exists because the pattern it forbids has
//! come back three times. WI-887 found `let _ = load_all(..)` hiding a live load
//! error in `wi680_ite_lowering_test`; WI-959 found the same discard letting
//! `wi341_alpha_tests` pass over a half-loaded KB and removed the last one from
//! `anthill-core/src/`; WI-966 then measured 28 more sites across 22 files in
//! three crates, of which THREE fixtures were silently broken — an unresolved
//! `List` carried through 18 `toml_ser_test` tests, and two provider sorts whose
//! `provides` clauses were incoherent.
//!
//! A discarded `Err` is not a degraded diagnostic. It is no guard at all: the
//! test that follows asserts over a KB that never finished loading, and stays
//! green while doing it. So the rule is not "prefer strict" but "the verdict is
//! read, or the reader is named".
//!
//! CONTROL — this is the test that fails if WI-966 is backed out. Every other
//! test in the workspace passes with the discards restored, by design: that is
//! precisely the property that let them survive this long.

use std::path::{Path, PathBuf};

/// The single legitimate discard, by path: `load_kb_with_lenient`, for cpp-gen
/// fixtures whose REJECTED SHAPE is the subject (a kind error, a recursive
/// anonymous lambda). Its four callers each say so at the call site.
const ALLOWED: &[&str] = &["anthill-cpp-gen/tests/common/mod.rs"];

/// This file, skipped because it carries the forbidden shape as STRING LITERALS
/// — the corpus `the_recogniser_fires_on_the_pattern_and_not_on_prose` checks
/// the recogniser against. Quoting the pattern is how the recogniser is tested,
/// so it cannot also be how the scan fails.
const SELF: &str = "anthill-core/tests/include/wi966_loader_verdict_test.rs";

/// A line that takes a loader entry point's result and throws it away.
fn discards_a_loader_verdict(line: &str) -> bool {
    let t = line.trim();
    if t.starts_with("//") || t.starts_with("///") || t.starts_with("*") {
        return false; // a doc comment quoting the pattern is not the pattern
    }
    if !t.contains("let _ =") {
        return false;
    }
    [
        "load_all(",
        "load_incremental(",
        "load::load(",
        "scan_definitions(",
    ]
    .iter()
    .any(|entry| t.contains(entry))
}

fn rust_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            if p.file_name().is_some_and(|n| n == "target") {
                continue;
            }
            rust_sources(&p, out);
        } else if p.extension().is_some_and(|x| x == "rs") {
            out.push(p);
        }
    }
}

#[test]
fn no_source_discards_the_loaders_error() {
    let rustland = crate::common::workspace_root().join("rustland");
    let mut files = Vec::new();
    rust_sources(&rustland, &mut files);
    assert!(
        files.len() > 100,
        "expected to scan the whole rustland tree, saw only {} files — the walk is \
         broken and this guard would pass vacuously",
        files.len(),
    );

    let mut offenders = Vec::new();
    for path in &files {
        let rel = path
            .strip_prefix(&rustland)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        if ALLOWED.contains(&rel.as_str()) || rel == SELF {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        for (i, line) in text.lines().enumerate() {
            if discards_a_loader_verdict(line) {
                offenders.push(format!("{rel}:{}: {}", i + 1, line.trim()));
            }
        }
    }

    assert!(
        offenders.is_empty(),
        "these sites discard the loader's verdict, so whatever they assert next is \
         asserted over a KB that may never have finished loading. Read the `Err`: \
         `common::expect_loaded` to fail on it, `common::expect_load_errors` to pin \
         it when the fixture is dirty ON PURPOSE, or a named `*_lenient` helper (and \
         then add it to ALLOWED here).\n{}",
        offenders.join("\n"),
    );
}

/// The guard's own control: the recogniser must FIRE on the shape WI-966
/// removed and stay quiet on the shapes that legitimately survive. Without
/// this, a typo in `discards_a_loader_verdict` would make the test above pass
/// over a tree full of discards.
#[test]
fn the_recogniser_fires_on_the_pattern_and_not_on_prose() {
    for fires in [
        "    let _ = load::load_all(&mut kb, &refs, &NullResolver);",
        "let _ = load::load_incremental(&mut kb, &refs, &NullResolver);",
        "    let _ = load::load(&mut kb, &parsed, &NullResolver);",
        "    let _ = load::scan_definitions(&mut kb, &[&parsed]);",
    ] {
        assert!(discards_a_loader_verdict(fires), "must flag: {fires}");
    }
    for quiet in [
        "/// this crate's own test harness does `let _ = load_all(..)` and the CLI",
        "//    let _ = load::load_all(&mut kb, &refs, &NullResolver);",
        "    crate::common::expect_loaded(load::load_all(&mut kb, &refs, &NullResolver));",
        "    let _ = interp_for(SRC_CONCRETE);",
        "    let errs = load::scan_definitions(kb, &[&parsed]);",
    ] {
        assert!(!discards_a_loader_verdict(quiet), "must NOT flag: {quiet}");
    }
}
