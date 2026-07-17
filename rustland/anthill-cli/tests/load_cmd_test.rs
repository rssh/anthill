//! WI-744 — `anthill load`'s data-file path: loud about OUR broken data, silent
//! about files that were never ours.
//!
//! Two bugs met here. `collect_data_files` recursively claims every `.toml`/
//! `.json` under a path, and the load arm printed `warning: <file>: <err>` and
//! carried on — so a genuinely broken data file left the KB quietly missing facts
//! the user had supplied (a confident wrong answer), while an ordinary
//! `Cargo.toml` produced a warning nobody could act on. Making the arm loud
//! without fixing the claim turned the second into a hard failure of `anthill
//! load` on any project with a `Cargo.toml`. The fix is the `meta`+`data`
//! envelope sniff (`term_ser::load_data_file`): ours-and-broken is an error,
//! not-ours is not our business.
//!
//! Not covered: the unreadable-*directory* arm of `collect_files_recursive` (an
//! error too). Provoking it needs a chmod-000 directory, which is a no-op for a
//! root test runner and would be flaky in CI.

mod common;

use common::{anthill, fixtures_dir, Output};

/// `anthill load <fixtures/load/{rel}>` — `rel` may name a directory or a file.
fn load(rel: &str) -> Output {
    let path = fixtures_dir("load").join(rel);
    anthill(&["load", path.to_str().unwrap()])
}

/// The control for `broken_data_file_blocks_the_load`, and an exact one: it loads
/// the SAME `prog.anthill` that test does, naming the FILE rather than its
/// directory. Data files are globbed only out of directories, so the sibling
/// `broken.toml` is not picked up — which pins the failure there on the `.toml`
/// and nothing else. (A second copy of the source in its own directory would
/// drift out of sync and quietly stop controlling.)
#[test]
fn the_source_alone_loads() {
    let out = load("broken-data/prog.anthill");
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(out.stdout.contains("loaded:"),
            "expected a `loaded:` summary; got stdout:\n{}", out.stdout);
}

/// Data that IS ours — it carries the `meta`+`data` envelope — and is broken must
/// BLOCK. Before WI-744 this printed `warning: …` then `loaded: N facts`, exit 0,
/// leaving the KB missing the facts the file was supposed to supply.
#[test]
fn broken_data_file_blocks_the_load() {
    let out = load("broken-data");
    assert_eq!(out.code, 1, "broken data must block; stderr:\n{}", out.stderr);
    assert!(!out.stdout.contains("loaded:"),
            "the load must not report success; got stdout:\n{}", out.stdout);
    assert!(out.stderr.contains("error:")
            && out.stderr.contains("broken.toml")
            && out.stderr.contains("unknown entity"),
            "expected a loud `error:` naming the file and the fault; got stderr:\n{}", out.stderr);
    // Line-wise, and anchored on the file rather than on a `warning: /`
    // path-shape proxy: unrelated advisories share this stderr (the stdlib's
    // requires-shadow pair), and WI-745 is about to put `path:line:col` on the
    // advisory channel too, so any proxy for "looks like a path" would fire on
    // them. What must not exist is a WARNING LINE about THIS file.
    assert!(!out.stderr.lines().any(|l| l.starts_with("warning:") && l.contains("broken.toml")),
            "the data-file failure must not be demoted to a warning:\n{}", out.stderr);
}

/// Files that were never ours must be ignored outright — not loaded, not warned
/// about, not fatal. The fixture holds four shapes, each of which the loud arm
/// turned into a hard failure at some point in WI-744's development:
///   - `Cargo.toml`         — valid TOML, no envelope → `missing meta`
///   - `.vscode/settings.json` — JSONC comments, not strict JSON → `format error`
///   - `config.toml`        — has `[meta]`/`[data]` but no `meta.entity` string
///   - `manifest.json`      — has a nested `meta` object but no `meta.entity`
/// The last two are why the sniff keys on `meta.entity: String` rather than a
/// bare `meta` key: keying on the key claimed them and errored.
#[test]
fn foreign_data_files_are_not_our_business() {
    let out = load("foreign-files");
    assert_eq!(out.code, 0,
               "a foreign .toml/.json must not fail the load; stderr:\n{}", out.stderr);
    assert!(out.stdout.contains("loaded:"),
            "expected a `loaded:` summary; got stdout:\n{}", out.stdout);
    for foreign in ["Cargo.toml", "settings.json", "config.toml", "manifest.json"] {
        assert!(!out.stderr.contains(foreign),
                "foreign file `{foreign}` must not be mentioned; got stderr:\n{}", out.stderr);
    }
}
