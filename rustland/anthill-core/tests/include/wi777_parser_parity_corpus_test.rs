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

    // CONTROL / BACK-OUT. The corpus is where a DIVERGENCE becomes visible, so each case
    // is named by the back-out that reddens it, and on which side:
    //   * WI-766, Scaland: reverting `tupleType`'s single-component arm fails the peer on
    //     both one-component TYPE accept cases. Rustland passes those either way — its
    //     half is the reference the corpus was written against.
    //   * WI-1131, BOTH sides, and they fail for DIFFERENT reasons — which is the point of
    //     having one corpus rather than two. All measured:
    //       - Rustland, `tuple_literal` restored to its two-arm form: fails
    //         `one_named_tuple_value{,_trailing_comma}`. It does NOT move
    //         `one_positional_tuple_value`, which stays rejected either way — by
    //         `missing `name`` at a zero-width span instead of the arity-one rule. This
    //         test reads only the VERDICT, so the message is pinned next door, in
    //         `wi1131_one_field_named_tuple_test`.
    //       - Scaland, `!")"` lookahead dropped from the element repetition: fails
    //         `one_named_tuple_value_trailing_comma` (`parse error: found ")\nend\n"`),
    //         and `two_positional_tuple_value_trailing_comma` with it — that second case
    //         IS the divergence this corpus caught. A literal trailing comma is something
    //         rustland has always accepted and Scaland never did, and nothing saw it,
    //         because the corpus's only trailing-comma case was a tuple TYPE.
    //       - Scaland, the `(x,)` refusal dropped: `one_positional_tuple_value` is
    //         ACCEPTED — silently, as grouping — and the reject half fails.
    //   * `one_positional_arrow`, `one_denoted_tuple_type`, `two_named_tuple_trailing_comma`
    //     and the two older reject cases pass under every back-out above, and guard the
    //     unchanged language around the fixes.
}
