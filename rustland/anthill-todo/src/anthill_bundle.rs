//! Embedded `.anthill` bundle for the rust+anthill realization.

use anthill_core::parse;
use anthill_core::parse::error::ParseError;
use anthill_core::parse::ir::ParsedFile;

const BUNDLE_SOURCES: &[(&str, &str)] = &[
    // Version-stamp entities (TemplateInfo/StoreFormat) load first — they
    // define the `anthill.stage0` symbols the prescan resolves and that a
    // project's scaffolded stamps refer to (WI-434).
    (
        "anthill-todo/version",
        include_str!("../anthill/version.anthill"),
    ),
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
    // Canonical source = these two files under `anthill/` beside version/store/
    // main (WI-684). This is the ONE on-disk copy: the bundle asset and the
    // anthill-core test fixtures point here, decoupled from the live tracker
    // dir. Editing them rebuilds the binary — which is the point (version-
    // locking). The repo's own `anthill-todo/` tracker no longer carries a
    // domain/rules copy; it dogfoods the bundle like any other project.
    (
        "anthill.stage0/domain",
        include_str!("../anthill/domain.anthill"),
    ),
    (
        "anthill.stage0.workflow/rules",
        include_str!("../anthill/rules.anthill"),
    ),
    // The mirror's domain and the `Forge` carrier's contract (WI-1117). Bundled
    // beside the domain and for the same reason (WI-505): a project's own copy
    // may predate the entity, and an unresolved import fails the whole load.
    // Loads AFTER the domain — `MirrorEntry` is a stage0 entity like `Tag`, and
    // the `document` namespace's mapping facts name it.
    (
        "anthill.stage0/coordination",
        include_str!("../anthill/coordination.anthill"),
    ),
    // The rust binding for the `Forge` carrier, SEPARATE from its declaration —
    // that file's header says why, and it is not tidiness: a binding block naming
    // a host function the runtime does not have is fatal for the whole program,
    // and anthill-core's own type-check fixtures load the declaration without
    // this binary behind it.
    (
        "anthill.stage0/coordination_rust",
        include_str!("../anthill/coordination_rust.anthill"),
    ),
    (
        "anthill-todo/store",
        include_str!("../anthill/store.anthill"),
    ),
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
                // WI-852: `line:col` in the embedded source — see
                // `anthill_stl::stdlib::parse_embedded`.
                errors.extend(
                    ParseError::all_located(&parse_errors, std::path::Path::new(name), source)
                        .into_iter()
                        .map(|located| format!("bundle {located}")),
                );
            }
        }
    }
    (files, errors)
}
