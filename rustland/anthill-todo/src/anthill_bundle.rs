//! Embedded `.anthill` bundle for the rust+anthill realization.

use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

const BUNDLE_SOURCES: &[(&str, &str)] = &[
    ("anthill-todo/store", include_str!("../anthill/store.anthill")),
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
