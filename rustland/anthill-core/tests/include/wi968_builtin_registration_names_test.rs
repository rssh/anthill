//! WI-968 — the FOUR builtin-registration names in [`EXPECTED_OWNER`] each have
//! exactly one definition, in the module that owns the registry it writes.
//!
//! `KnowledgeBase::register_builtin_tags` / `register_builtin_tag` write
//! `BuiltinTag`s at bootstrap; `eval::builtins::register_standard_builtins` /
//! `Interpreter::register_builtin` bind host Rust fns per fresh interpreter. Each
//! pair used to share the KB side's name.
//!
//! A TABLE, NOT A WORKSPACE RULE, and the distinction is the point: hundreds of
//! this workspace's fn names are defined more than once (`new`, `load_errors`,
//! `fmt`, …), all of them fine. Uniqueness is owed only where a bare occurrence
//! would be read as the wrong layer. A future twin pair earns a ROW here; it is
//! not already covered.
//!
//! WHY A SOURCE SCAN, AND NOT A BEHAVIOURAL TEST. There is no behaviour to drive —
//! the rename is behaviour-preserving, which is exactly the problem: a future
//! `KnowledgeBase::register_standard_builtins` would compile, pass the whole suite,
//! and reintroduce a READING failure. rustc cannot see it either (two inherent
//! impls on different types is no collision), and clippy has no cross-item
//! duplicate-name lint, so a scan is the only mechanism there is.
//!
//! `pub(crate)` carries the larger half of the load and the scan the remainder:
//! integration tests are separate crates, so a test can no longer NAME the KB pair
//! at all — a bare `register_standard_builtins` under `tests/` is the eval side by
//! compiler enforcement. What is left for the scan is a third same-named item
//! added inside `anthill-core/src`.
//!
//! SCANS RUST ONLY. `scaland` carries the same rename for parity but has no
//! interpreter, hence no twin to guard; a Scala evaluator would need its own.
//!
//! CONTROL: back either rename out and this test names both definition sites of
//! the re-collided name. Nothing else in the suite fails either way — no other
//! test distinguishes the old names from the new ones.

use std::collections::BTreeMap;
use std::path::PathBuf;

/// The four registration names and the file each must be defined in — the whole
/// claim this test holds. A name may be a prefix of another (`register_builtin` of
/// `register_builtin_tag`); [`definition_sites`] keeps them apart.
const EXPECTED_OWNER: [(&str, &str); 4] = [
    ("register_standard_builtins", "eval/builtins.rs"),
    ("register_builtin", "eval/mod.rs"),
    ("register_builtin_tags", "kb/mod.rs"),
    ("register_builtin_tag", "kb/mod.rs"),
];

/// Every hand-written `.rs` file in the workspace: under each crate directory in
/// `rustland/`, every subdirectory plus the crate root's own files (`build.rs`).
/// PRUNING `target`, not allowlisting `src`/`tests` — an allowlist is a silent
/// skip, and a `fn register_builtin(` added under `examples/`, `benches/`, or in a
/// `build.rs` would leave the assertions below reporting "exactly one" and green.
///
/// `target` is pruned at every level and the prune is CHECKED below, not assumed:
/// it holds well over a hundred `.rs` files that are not ours to name —
/// build-script `out/` products, vendored crates' generated sources — and a `fn`
/// in any of them would be reported as a collision this repo cannot fix.
fn workspace_rust_sources() -> Vec<PathBuf> {
    let rustland = crate::common::workspace_root().join("rustland");
    let mut files = Vec::new();
    for krate in read_dir_paths(&rustland) {
        if !krate.is_dir() || is_target(&krate) {
            continue;
        }
        for path in read_dir_paths(&krate) {
            if path.is_dir() {
                if is_target(&path) {
                    continue;
                }
                files.extend(
                    anthill_core::fs_util::collect_files(&path, &["rs"])
                        .unwrap_or_else(|e| panic!("collect {}: {e}", path.display())),
                );
            } else if path.extension().is_some_and(|e| e == "rs") {
                files.push(path);
            }
        }
    }
    assert!(
        files.len() > 100,
        "the scan found only {} .rs files under {} — it is not reading the workspace, \
         so every assertion below would pass vacuously",
        files.len(),
        rustland.display()
    );
    if let Some(leaked) = files.iter().find(|p| p.components().any(|c| c.as_os_str() == "target")) {
        panic!("the `target` prune leaked: {} is generated code", leaked.display());
    }
    files
}

fn read_dir_paths(dir: &std::path::Path) -> Vec<PathBuf> {
    std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()))
        .map(|e| e.expect("readable dir entry").path())
        .collect()
}

fn is_target(path: &std::path::Path) -> bool {
    path.file_name().is_some_and(|n| n == "target")
}

/// For each name, its definition sites as `path:line`. One walk, one read per file,
/// all names checked together — the four needles are tested against the same buffer.
///
/// A name must be followed by `(` or `<` (a generic parameter list —
/// `Interpreter::register_builtin` is `fn register_builtin<F>(…)`), which is what
/// keeps `register_builtin` from matching `register_builtin_tag`. Whole-line
/// comments are skipped; a trailing `// fn foo(` is not, and would be reported.
///
/// TEXTUAL, with no notion of a string literal: `anthill-rust-gen/src/bundle.rs`
/// holds the emitted bundle's `main.rs` as a `format!` template, so a `fn <name>(`
/// added to THAT would be reported as a definition site. Left as-is — it errs
/// toward a loud false alarm naming the exact line, never toward a silent pass.
fn definition_sites(names: &[&str]) -> BTreeMap<String, Vec<String>> {
    let needles: Vec<(String, String)> =
        names.iter().map(|n| ((*n).to_string(), format!("fn {n}"))).collect();
    let mut sites: BTreeMap<String, Vec<String>> =
        names.iter().map(|n| ((*n).to_string(), Vec::new())).collect();
    for path in workspace_rust_sources() {
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
        for (name, needle) in &needles {
            // One whole-buffer scan rejects the files that cannot match, in place of
            // a per-line `find` over each. A SUPERSET filter — `fn register_builtin`
            // passes a file holding only `fn register_builtin_tag`, which the loop
            // below then rejects on the following character — so it drops no hit.
            if !text.contains(needle) {
                continue;
            }
            for (i, line) in text.lines().enumerate() {
                let code = line.trim_start();
                if code.starts_with("//") || code.starts_with('*') {
                    continue;
                }
                let Some(after) = code.find(needle).map(|at| &code[at + needle.len()..]) else {
                    continue;
                };
                if after.starts_with('(') || after.starts_with('<') {
                    sites.get_mut(name).expect("name is a key").push(format!("{}:{}", path.display(), i + 1));
                }
            }
        }
    }
    sites
}

/// One assertion over all four names, so a regression names EVERY violation rather
/// than the first — backing out both renames is one edit and produces two.
#[test]
fn each_builtin_registration_name_has_exactly_one_definition() {
    let names: Vec<&str> = EXPECTED_OWNER.iter().map(|(n, _)| *n).collect();
    let sites = definition_sites(&names);
    let mut violations = Vec::new();
    for (name, owner) in EXPECTED_OWNER {
        let found = &sites[name];
        if found.is_empty() {
            violations.push(format!(
                "`{name}` names no function at all — expected one in {owner}. It was \
                 deleted or renamed, and the collision this test guards is unguarded."
            ));
        } else if found.len() > 1 {
            violations.push(format!(
                "`{name}` must name exactly ONE function — the eval-side ones are free \
                 functions and can be imported bare, so a second definition makes every \
                 bare call site ambiguous. Found {}: {found:?}",
                found.len()
            ));
        } else if !found[0].contains(owner) {
            violations.push(format!(
                "`{name}` belongs in {owner}; found it at {}",
                found[0]
            ));
        }
    }
    assert!(violations.is_empty(), "WI-968:\n{}", violations.join("\n"));
}
