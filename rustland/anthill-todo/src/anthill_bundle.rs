//! Embedded `.anthill` files for the bundle's main entry point.
//!
//! The bundle is the anthill-side of the rust+anthill realization: a
//! collection of `.anthill` files that are include_str!'d into the
//! binary, parsed at startup, and loaded into the KB alongside the
//! stdlib. The `anthill.todo.Main.main(args)` operation is the program
//! entry point — see `src/main.rs::run_anthill_bundle`.

use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

const BUNDLE_SOURCES: &[(&str, &str)] = &[
    ("anthill-todo/main", include_str!("../anthill/main.anthill")),
];

/// Parse all bundle sources. Returns (parsed files, fatal errors). A
/// non-empty errors vec means the bundle is malformed at compile time —
/// a build regression, not a user-facing condition.
pub fn parse_embedded_bundle() -> (Vec<ParsedFile>, Vec<String>) {
    let mut files = Vec::new();
    let mut errors = Vec::new();
    for &(name, source) in BUNDLE_SOURCES {
        match parse::parse(source) {
            Ok(parsed) => files.push(parsed),
            Err(parse_errors) => {
                for e in &parse_errors {
                    errors.push(format!("bundle {name}: {e}"));
                }
            }
        }
    }
    (files, errors)
}
