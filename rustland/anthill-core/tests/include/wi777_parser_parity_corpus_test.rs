//! WI-777 — Rust and Scala read one shared parser-parity corpus.
//!
//! Rust is the kernel-language reference, so this half pins the corpus verdict against
//! rustland. Scaland's `ParserParityTest` reads the SAME paths and asserts the SAME
//! directory-derived verdict. A copied fixture would let the copies drift and recreate
//! the ticket while both suites stayed green; there is deliberately only one corpus.

use std::fs;
use std::path::{Path, PathBuf};

use anthill_core::parse;

fn corpus_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/parser-parity/wi777")
}

fn cases(verdict: &str) -> Vec<PathBuf> {
    let dir = corpus_root().join(verdict);
    let mut paths: Vec<_> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("cannot read shared parity corpus {}: {e}", dir.display()))
        .map(|entry| entry.expect("parity corpus entry must be readable").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "anthill"))
        .collect();
    paths.sort();
    assert!(
        !paths.is_empty(),
        "{verdict} parity corpus must not be empty"
    );
    paths
}

fn parse_path(path: &Path) -> Result<(), Vec<String>> {
    let source = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read parity case {}: {e}", path.display()));
    parse::parse(&source)
        .map(|_| ())
        .map_err(|errors| errors.into_iter().map(|e| e.message).collect())
}

#[test]
fn wi777_rust_parser_pins_the_shared_parity_corpus() {
    for path in cases("accept") {
        assert!(
            parse_path(&path).is_ok(),
            "reference parser rejected shared accept case {}: {:?}",
            path.display(),
            parse_path(&path),
        );
    }

    for path in cases("reject") {
        assert!(
            parse_path(&path).is_err(),
            "reference parser accepted shared reject case {}",
            path.display(),
        );
    }

    // CONTROL / BACK-OUT: rustland already passes this test by design; reverting the
    // Scaland production makes Scaland's peer fail on both one-component accept cases.
    // The two-field trailing-comma case and both negative cases pass either way and guard
    // the unchanged language around the fix.
}
