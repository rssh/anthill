//! WI-852 — a parse error names its file and position, like a load error does.
//!
//! WI-745 gave blocking LOAD errors a `path:line:col` rendering, because a raw
//! byte offset "named nothing once N files merged into one KB". PARSE errors
//! were left on `ParseError`'s `Display`, which is that byte offset — so which
//! STAGE found a fault decided whether the author got a clickable location or a
//! number to count to, a distinction they cannot predict. It widens as
//! converter-stage refusals multiply: WI-805, WI-808, WI-809 and WI-850 are all
//! reported as parse errors.
//!
//! These tests pin the RENDERED STRING, not the exit code — the defect was
//! entirely in the rendering, so a test that only asserts "it failed" passes
//! against the bug.
//!
//! `stage_does_not_change_the_rendering` is the one that states the ticket's
//! claim directly: the same fixture through `check`, `load`, `run` and `codegen
//! rust` must produce the identical location. Per-command tests would each pass
//! while the family drifted.

use crate::common::{anthill, fixtures_dir, Output};
use std::path::{Path, PathBuf};

fn fixture(name: &str) -> PathBuf {
    fixtures_dir("wi852").join(name)
}

/// The one diagnostic line starting `error: <path>:` — panics with the whole
/// stderr if there is none, so a failure shows what was printed instead.
fn located_error<'a>(out: &'a Output, path: &Path) -> &'a str {
    let prefix = format!("error: {}:", path.display());
    out.diagnostics("error:")
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| {
            panic!(
                "no `error: {}:…` line; stderr:\n{}",
                path.display(),
                out.stderr
            )
        })
}

/// Every `error:` line naming `path` carries a `line:col` after it.
///
/// Stated POSITIVELY on purpose. The first version of this control asserted the
/// absence of the literal `"parse error at"` — and once `ParseError`'s sourceless
/// `Display` was deleted, no code path in the workspace could emit that string,
/// so the control could not fail. It would have missed any *other* sourceless
/// rendering (`{e:?}`, a raw `span.start`). This one fails the moment a
/// diagnostic names the file without saying where in it.
fn assert_every_mention_is_located(out: &Output, path: &Path) {
    let prefix = format!("error: {}", path.display());
    for line in out.diagnostics("error:").filter(|l| l.starts_with(&prefix)) {
        let rest = &line[prefix.len()..];
        let located = rest
            .strip_prefix(':')
            .map(|r| {
                let mut parts = r.splitn(3, ':');
                let line_no = parts.next().unwrap_or("");
                let col = parts.next().unwrap_or("");
                !line_no.is_empty()
                    && line_no.chars().all(|c| c.is_ascii_digit())
                    && !col.is_empty()
                    && col.chars().all(|c| c.is_ascii_digit())
            })
            .unwrap_or(false);
        assert!(
            located,
            "diagnostic names the file but not a position:\n{line}"
        );
    }
}

/// A converter-stage refusal (WI-850's type-parameter default) is the case the
/// ticket was found on: the message named the file and the operation, then
/// pointed at bytes 86..95.
#[test]
fn a_converter_diagnostic_renders_path_line_col() {
    let path = fixture("type-param-default.anthill");
    let out = anthill(&["check", path.to_str().unwrap()]);

    assert_eq!(out.code, 1, "the check must block; stderr:\n{}", out.stderr);
    let line = located_error(&out, &path);
    assert!(
        line.starts_with(&format!("error: {}:3:17: ", path.display())),
        "expected the location of `T` in `operation foo[T = Int64]` (line 3, col 17); got:\n{line}"
    );
    assert!(
        line.contains("type parameter `T` carries a default"),
        "the location must not cost the diagnostic; got:\n{line}"
    );
    assert_every_mention_is_located(&out, &path);
}

/// The other half of the parse stage: a genuine syntax fault, whose span comes
/// from tree-sitter rather than from the converter.
#[test]
fn a_syntax_error_renders_path_line_col() {
    let path = fixture("missing-name.anthill");
    let out = anthill(&["check", path.to_str().unwrap()]);

    assert_eq!(out.code, 1, "the check must block; stderr:\n{}", out.stderr);
    let line = located_error(&out, &path);
    assert_eq!(
        line,
        format!("error: {}:3:15: missing `identifier`", path.display()),
        "expected the location of the absent field name in `entity mk(: Int64)`"
    );
    assert_every_mention_is_located(&out, &path);
}

/// WI-852's actual claim. One fixture, four commands, one location — the four
/// CLI printers cannot drift apart, and neither can a parse error from a load
/// error (both render through `span::render_located`).
#[test]
fn stage_does_not_change_the_rendering() {
    let path = fixture("type-param-default.anthill");
    let p = path.to_str().unwrap();
    let expected = format!("error: {}:3:17: ", path.display());

    // `--dry-run` writes nothing, so `--output-dir` keeps its default and no
    // directory is created.
    for args in [
        vec!["check", p],
        vec!["load", p],
        vec!["run", p],
        vec!["codegen", "rust", "--dry-run", p],
    ] {
        let out = anthill(&args);
        let line = located_error(&out, &path);
        assert!(
            line.starts_with(&expected),
            "`anthill {}` located it differently:\n{line}",
            args.join(" ")
        );
        assert_every_mention_is_located(&out, &path);
    }
}

/// `--query-file` reads a real file, so its faults get the same `path:line:col`
/// every other parse error gets — the site used to print `parse error: {e}`,
/// naming neither.
#[test]
fn a_query_file_parse_error_names_the_file() {
    let kb = fixture("good.anthill");
    let q = fixture("bad-query.anthill");
    let out = anthill(&[
        "query",
        "--path",
        kb.to_str().unwrap(),
        "--query-file",
        q.to_str().unwrap(),
    ]);

    assert_eq!(out.code, 1, "the query must block; stderr:\n{}", out.stderr);
    let line = located_error(&out, &q);
    assert!(
        line.starts_with(&format!("error: {}:3:8: ", q.display())),
        "expected the location of `(` in the query file's third line; got:\n{line}"
    );
    assert_every_mention_is_located(&out, &q);
}

/// `collect_queries` used to parse a source it SYNTHESIZED — one `import` line
/// per `-i` flag, then the file — so an unshifted span reported the file's
/// faults one line too low per flag, and WI-852 shifted each span back across a
/// recorded boundary. WI-853 removed the join instead: the flags are parsed as
/// sources of their own and the file is parsed ALONE, so the file's spans are
/// its own and no shift exists to get wrong.
///
/// The claim outlives the mechanism, so the test does: the reported line is the
/// same with flags as without. It now holds by construction rather than by
/// arithmetic, which is the point — it fails if a future change re-prepends
/// anything to the author's text.
#[test]
fn prepended_import_lines_do_not_shift_the_file_location() {
    let kb = fixture("good.anthill");
    let q = fixture("bad-query.anthill");
    let out = anthill(&[
        "query",
        "--path",
        kb.to_str().unwrap(),
        "-i",
        "wi852.good",
        "-i",
        "wi852.good",
        "--query-file",
        q.to_str().unwrap(),
    ]);

    assert_eq!(out.code, 1, "the query must block; stderr:\n{}", out.stderr);
    let line = located_error(&out, &q);
    assert!(
        line.starts_with(&format!("error: {}:3:8: ", q.display())),
        "two prepended `import` lines shifted the file's reported location; got:\n{line}"
    );
    assert_every_mention_is_located(&out, &q);
}

/// The merged-node case: when the file's first token cannot begin a top-level
/// item, tree-sitter recovery swallowed the synthesized `import` lines and the
/// file into ONE `ERROR` node starting at byte 0 — and attributing that node by
/// where it STARTED blamed `--import` and dropped the file's location entirely,
/// the exact failure WI-852 existed to remove, reintroduced by the fix for it.
/// The overlap rule that repaired it is gone with the join (WI-853): a flag and
/// the file are different sources, so no node can span both.
///
/// Still driven, because "cannot happen by construction" is a claim about the
/// current construction. `bad-query.anthill` cannot stand in for it: its first
/// token (`fact`) is a valid top-level start, so recovery never merges there.
#[test]
fn a_span_merged_across_the_prefix_is_located_in_the_file() {
    let kb = fixture("good.anthill");
    let q = fixture("leading-junk-query.anthill");
    let out = anthill(&[
        "query",
        "--path",
        kb.to_str().unwrap(),
        "-i",
        "wi852.good",
        "--query-file",
        q.to_str().unwrap(),
    ]);

    assert_eq!(out.code, 1, "the query must block; stderr:\n{}", out.stderr);
    let line = located_error(&out, &q);
    assert!(
        line.starts_with(&format!("error: {}:1:1: ", q.display())),
        "a fault reaching the file's text must be located IN the file, at the \
         first byte the merged span covers there; got:\n{line}"
    );
    assert_every_mention_is_located(&out, &q);
}

/// An inline `--pattern` is not a file: it is one argument the author just
/// typed, and every line around it (`import` lines, the `fact` keyword) is
/// synthesized. A `line:col` would point into text they never wrote — the same
/// "location naming nothing" this ticket removes — so the origin IS the flag.
#[test]
fn an_inline_pattern_names_the_flag() {
    let kb = fixture("good.anthill");
    let out = anthill(&["query", "--path", kb.to_str().unwrap(), "mk(x:"]);

    assert_eq!(out.code, 1, "the query must block; stderr:\n{}", out.stderr);
    assert!(
        out.diagnostics("error:")
            .any(|l| l == "error: --pattern: syntax error near `(x:`"),
        "expected the fault blamed on `--pattern`; stderr:\n{}",
        out.stderr
    );
}

// DELETED by WI-853: `a_malformed_import_flag_names_which_flag`. It pinned the
// RANGE naming ("--import (one of `a`, `b`)") that the join forced — one
// recovery node could cover several `import` lines, so the flag at its start was
// the wrong answer and every covered flag had to be named. Each flag is now its
// own source, so a span covers exactly one and the range has no case to serve.
// The claim it protected — the good flag is never blamed for the bad one's fault
// — is asserted more strictly by `a_malformed_flag_names_only_itself` in
// `wi853_query_import_test.rs`.

/// The single-flag case, which is now every case — the flag is named exactly.
#[test]
fn a_lone_malformed_import_flag_is_named_exactly() {
    let kb = fixture("good.anthill");
    let out = anthill(&[
        "query",
        "--path",
        kb.to_str().unwrap(),
        "-i",
        "not a name!!",
        "mk(x: 1)",
    ]);

    assert_eq!(out.code, 1, "the query must block; stderr:\n{}", out.stderr);
    assert!(
        out.diagnostics("error:")
            .all(|l| l.starts_with("error: --import `not a name!!`: ")),
        "expected the one flag named; stderr:\n{}",
        out.stderr
    );
}
