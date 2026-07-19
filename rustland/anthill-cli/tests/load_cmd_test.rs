//! WI-744 / WI-746 — `anthill load`'s data-file path: data is OPT-IN, and every
//! fault in a file the user opted into is loud.
//!
//! WI-744 found two bugs meeting here. `collect_data_files` recursively claimed
//! every `.toml`/`.json` under a path, and the load arm printed
//! `warning: <file>: <err>` and carried on — so a broken data file left the KB
//! quietly missing facts the user had supplied (a confident wrong answer), while
//! an ordinary `Cargo.toml` produced a warning nobody could act on. Making the
//! arm loud without fixing the claim turned the second into a hard failure of
//! `anthill load` on any project with a `Cargo.toml`. WI-744's stopgap was a
//! `meta`+`data` envelope SNIFF: ours-and-broken is an error, not-ours is not our
//! business.
//!
//! WI-746 removed the need to sniff. Data files are now named by CONVENTION —
//! `<dir>/anthill.toml` / `<dir>/anthill.json`, non-recursive — and nothing else
//! on disk is read as data. That flips the two cases the sniff had to swallow: a
//! declared file that will not parse, and one missing its envelope, are faults to
//! report rather than evidence that the file was never ours. Those are
//! `unparseable_data_file_blocks_the_load` and
//! `envelope_less_data_file_blocks_the_load` below — the tests WI-744 could not
//! write.
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

/// `anthill query --path <fixtures/load/{rel}> <pattern>`.
fn query(rel: &str, pattern: &str) -> Output {
    let path = fixtures_dir("load").join(rel);
    anthill(&["query", "--path", path.to_str().unwrap(), pattern])
}

/// Assert the load failed loudly, blaming `file` for `fault`, with no trace of
/// the warn-and-continue demotion WI-744 killed.
fn assert_blocks(out: &Output, file: &str, fault: &str) {
    assert_eq!(out.code, 1, "the load must block; stderr:\n{}", out.stderr);
    assert!(!out.stdout.contains("loaded:"),
            "the load must not report success; got stdout:\n{}", out.stdout);
    assert!(out.has_diagnostic("error:", file) && out.stderr.contains(fault),
            "expected a loud `error:` naming {file} and reporting `{fault}`; got stderr:\n{}",
            out.stderr);
    // Line-wise, and anchored on the file rather than on a `warning: /`
    // path-shape proxy: unrelated advisories share this stderr (the stdlib's
    // requires-shadow pair), and WI-745 put `path:line:col` on the advisory
    // channel too, so any proxy for "looks like a path" would fire on them. What
    // must not exist is a WARNING LINE about THIS file.
    assert!(!out.has_diagnostic("warning:", file),
            "the data-file failure must not be demoted to a warning:\n{}", out.stderr);
}

/// Assert the load succeeded and said nothing about any of `unread`.
fn assert_clean(out: &Output, unread: &[&str]) {
    assert_eq!(out.code, 0, "the load must succeed; stderr:\n{}", out.stderr);
    assert!(out.stdout.contains("loaded:"),
            "expected a `loaded:` summary; got stdout:\n{}", out.stdout);
    for file in unread {
        assert!(!out.stderr.contains(file),
                "`{file}` must not be mentioned; got stderr:\n{}", out.stderr);
    }
}

/// The happy path — and the only test here that exercises it. Every other test in
/// this file pins a REFUSAL (the load blocks, or the file is not read), so without
/// this one a regression that found the data file and then dropped its facts on
/// the floor would pass the whole suite.
///
/// Queried back rather than counted: `loaded: N facts` would also rise if the
/// facts landed malformed, whereas a matching answer proves they are in the KB
/// with their fields intact.
#[test]
fn declared_data_reaches_the_kb() {
    let out = query("good-data", "data.good.Person(name: ?n, age: ?a)");
    assert_eq!(out.code, 0, "the query must succeed; stderr:\n{}", out.stderr);
    for expected in ["\"abe\"", "42", "\"bea\"", "37"] {
        assert!(out.stdout.contains(expected),
                "expected {expected} among the answers; got stdout:\n{}", out.stdout);
    }
    assert!(out.has_stdout_line("2 solution(s)"),
            "expected exactly the 2 facts from anthill.toml; got stdout:\n{}", out.stdout);
}

/// When a directory declares data in BOTH conventional formats, both load. Each
/// is equally a declaration, so reading one and ignoring the other would be the
/// silent skip relocated rather than closed.
///
/// Pinned because it is the kind of behavior that flips by accident — a `break`
/// added to the extension loop, or a switch to first-match, would quietly halve
/// someone's data. If it is ever to become an error ("ambiguous data"), that
/// should be a decision this test is updated to record, not a drift.
#[test]
fn both_conventional_formats_load() {
    let out = query("both-formats", "data.both.Person(name: ?n, age: ?a)");
    assert_eq!(out.code, 0, "the query must succeed; stderr:\n{}", out.stderr);
    for expected in ["from-toml", "from-json"] {
        assert!(out.stdout.contains(expected),
                "expected `{expected}` among the answers; got stdout:\n{}", out.stdout);
    }
}

/// A declared data file that cannot be READ must block — the third fault in the
/// same family as `unparseable` and `envelope_less`, and the one the first cut of
/// WI-746 got wrong.
///
/// The collector probed candidates with `is_file()`, which answers false for a
/// directory wearing the name, for a dangling symlink, and for any stat failure —
/// so a declared-but-unreachable data file vanished with no diagnostic and the
/// load reported success, facts missing. That was a regression as well as a bug:
/// the extension-walk it replaced collected such a path and let `read_to_string`
/// fail loudly. Only `NotFound` may count as absent.
///
/// The fixture uses a DIRECTORY named `anthill.toml` because git cannot portably
/// store a dangling symlink; both cases ride the same two lines.
#[test]
fn unreadable_data_file_blocks_the_load() {
    assert_blocks(&load("dir-named-data"), "anthill.toml", "read error");
}

/// The control for `broken_data_file_blocks_the_load`, and an exact one: it loads
/// the SAME `prog.anthill` that test does, naming the FILE rather than its
/// directory. The convention keys on a DIRECTORY argument, so naming the source
/// picks up no data — which pins that test's failure on the `anthill.toml` and
/// nothing else. (A second copy of the source in its own directory would drift
/// out of sync and quietly stop controlling.)
#[test]
fn the_source_alone_loads() {
    assert_clean(&load("broken-data/prog.anthill"), &["anthill.toml"]);
}

/// Declared data that the deserializer rejects must BLOCK. Before WI-744 this
/// printed `warning: …` then `loaded: N facts`, exit 0, leaving the KB missing
/// the facts the file was supposed to supply.
#[test]
fn broken_data_file_blocks_the_load() {
    assert_blocks(&load("broken-data"), "anthill.toml", "unknown entity");
}

/// A declared data file that will not PARSE must block — the first residual
/// WI-744 could not close.
///
/// Under discovery this was skipped without a word, and necessarily so: the
/// envelope test needs a parsed value, so an unparseable file offered no evidence
/// it was ever addressed to us, making it indistinguishable from a JSONC
/// `tsconfig.json` the tool had merely found. Erroring was tried and killed
/// `anthill load` for every VS Code user. The conventional NAME is the evidence
/// that was missing: a file at `anthill.toml` was put there to be loaded.
#[test]
fn unparseable_data_file_blocks_the_load() {
    // The TOML parser's own wording for the unclosed table header is not ours to
    // pin; that it reaches the user as an `error:` about this file is.
    assert_blocks(&load("unparseable-data"), "anthill.toml", "format error");
}

/// A declared data file missing its `meta.entity` envelope must block — the
/// second residual. WI-744's sniff read the absent envelope as "not ours" and
/// skipped it, because under discovery that is exactly what a config file looks
/// like.
///
/// Read this against `foreign_data_files_are_not_our_business`: the fixture's
/// data-bearing lines are IDENTICAL to `foreign-files/config.toml`, which that
/// test requires to be ignored. Same bytes, opposite verdicts, and the only thing
/// that differs is the file's NAME — which is the ticket's claim made executable.
/// Sniffing could never have told these apart; it had only the content to go on.
#[test]
fn envelope_less_data_file_blocks_the_load() {
    assert_blocks(&load("envelope-less-data"), "anthill.toml", "meta.entity must be a string");
}

/// Files that were never ours must be ignored outright — not loaded, not warned
/// about, not fatal. The fixture holds four shapes, each of which the loud arm
/// turned into a hard failure at some point in WI-744's development:
///   - `Cargo.toml`            — valid TOML, no envelope → `missing meta`
///   - `.vscode/settings.json` — JSONC comments, not strict JSON → `format error`
///   - `config.toml`           — has `[meta]`/`[data]` but no `meta.entity` string
///   - `manifest.json`         — has a nested `meta` object but no `meta.entity`
///
/// WI-746 changed WHY they are ignored, and the test is worth keeping for the new
/// reason: they are no longer *sniffed and dismissed*, they are never read at
/// all, because none of them is named `anthill.toml`. The last two used to
/// justify keying the sniff on `meta.entity: String` rather than a bare `meta`
/// key; they now stand as ordinary foreign files, which is what they always were.
#[test]
fn foreign_data_files_are_not_our_business() {
    assert_clean(&load("foreign-files"),
                 &["Cargo.toml", "settings.json", "config.toml", "manifest.json"]);
}

/// The convention is `<dir>/anthill.toml` for a directory NAMED on the command
/// line — not "any `anthill.toml` anywhere beneath it". `nested-data/sub/` holds
/// one bearing the conventional name and carrying the `broken-data` fault, so if
/// the recursive walk ever returns this load stops being clean and starts
/// failing — a regression this catches loudly rather than passing on silently.
#[test]
fn the_lookup_is_not_recursive() {
    assert_clean(&load("nested-data"), &["anthill.toml"]);
}
