//! Embedded `.anthill` bundle for the rust+anthill realization.

use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

const BUNDLE_SOURCES: &[(&str, &str)] = &[
    // Version-stamp entities (TemplateInfo/StoreFormat) load first — they
    // define the `anthill.stage0` symbols the prescan resolves and that a
    // project's scaffolded stamps refer to (WI-434).
    ("anthill-todo/version", include_str!("../anthill/version.anthill")),
    // The canonical `anthill.stage0` domain (entity/enum defs) and the
    // `anthill.stage0.workflow` rules ship bundled so they are version-locked
    // with the logic that imports them (store/main below). Before WI-505 these
    // were loaded from each project's own domain.anthill/rules.anthill, which
    // silently broke a project whose copy predated a grammar or domain change
    // (a stale `export` clause cascaded into a wall of unresolved-import
    // errors). Bundling makes the definitions travel with the binary; the CLI
    // skips a project's own domain.anthill/rules.anthill at load so they are
    // never doubled.
    //
    // Canonical source = the repo-root tracker copy, reached the way main.rs
    // reaches its init templates (`../../../` = repo root). That keeps ONE
    // on-disk copy rather than minting a third: the same file is the binary's
    // domain, this project's own (skipped-at-load) tracker file, and the
    // anthill-core test fixture. Editing it rebuilds the binary — which is the
    // point (version-locking). A future cleanup could relocate the canonical
    // copy to `anthill/` beside version/store/main and repoint the fixtures,
    // decoupling the asset from the live tracker dir.
    ("anthill.stage0/domain", include_str!("../../../anthill-todo/domain.anthill")),
    ("anthill.stage0.workflow/rules", include_str!("../../../anthill-todo/rules.anthill")),
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
