//! The GitHub export target, over the `gh` CLI.
//!
//! THROUGH `gh`, NOT THROUGH THE API, and that is the whole reason there is no
//! token handling here: `gh` already holds the user's credentials, so this
//! inherits whatever auth the checkout already has and stores none of its own.
//! A machine with no `gh`, or a `gh` with no auth, fails LOUDLY at the first
//! call — there is no degraded path, because a mirror that silently did not
//! publish is worse than one that says it could not.
//!
//! THE HANDLE IS THE ISSUE NUMBER, as a string. `gh issue create` prints a URL
//! and `gh issue list` reports numbers, so one of the two has to be normalized
//! or an ADOPTED entry and a CREATED one would carry different spellings of the
//! same entry and never compare equal. The number is the spelling both can
//! produce, and `gh issue edit` accepts it.
//!
//! WHAT IS TESTED HERE AND WHAT IS NOT. The `gh` calls themselves need a network
//! and an account, so no test in this repo runs them — that is exactly why the
//! fake exists. What IS tested is everything either side of the process
//! boundary: the argv each operation builds, and the parse of each output shape.
//! Those are where the bugs live, and both are pure functions for that reason.

use std::process::Command;

use super::{Comment, Entry, ForgeBackend};

pub(crate) struct Gh {
    pub repo: String,
}

impl ForgeBackend for Gh {
    /// The REPO, so two GitHub repos are two targets. Without it an item
    /// exported to one repo would read as already-exported when the project's
    /// mirror is repointed at another, and export would try to update an entry
    /// that lives somewhere else.
    fn target_name(&self) -> String {
        format!("github:{}", self.repo)
    }

    fn create_entry(&self, title: &str, body: &str) -> Result<String, String> {
        let out = self.run(&create_argv(&self.repo, title, body))?;
        entry_from_created(&out)
    }

    fn update_entry(&self, entry: &str, title: &str, body: &str) -> Result<(), String> {
        self.run(&update_argv(&self.repo, entry, title, body))?;
        Ok(())
    }

    fn list_entries(&self) -> Result<Vec<Entry>, String> {
        parse_list(&self.run(&list_argv(&self.repo))?)
    }

    fn entry_comments(&self, entry: &str) -> Result<Vec<Comment>, String> {
        parse_comments(&self.run(&comments_argv(&self.repo, entry))?)
    }
}

impl Gh {
    /// Run `gh` and answer its stdout. A non-zero exit carries `gh`'s own stderr
    /// through verbatim: it is the only thing that knows whether the failure was
    /// auth, network, a missing repo or a rate limit, and paraphrasing it would
    /// lose the one detail that decides what to do next.
    fn run(&self, argv: &[String]) -> Result<String, String> {
        let out = Command::new("gh").args(argv).output().map_err(|e| {
            format!(
                "running `gh {}`: {e}. The GitHub mirror publishes through the `gh` CLI, \
                 which is where this checkout's credentials already are — install it, or \
                 run with `--offline` / `ANTHILL_TODO_MIRROR=off`.",
                argv.join(" ")
            )
        })?;
        if !out.status.success() {
            return Err(format!(
                "`gh {}` failed ({}): {}",
                argv.join(" "),
                out.status,
                String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    }
}

// ── The argv each operation builds ───────────────────────────────

fn create_argv(repo: &str, title: &str, body: &str) -> Vec<String> {
    owned(&[
        "issue", "create", "--repo", repo, "--title", title, "--body", body,
    ])
}

fn update_argv(repo: &str, entry: &str, title: &str, body: &str) -> Vec<String> {
    owned(&[
        "issue", "edit", entry, "--repo", repo, "--title", title, "--body", body,
    ])
}

/// EVERY entry, open and closed. An export must find a closed entry too, or a
/// verified item's entry would be adopted twice — created again beside the one
/// already there.
fn list_argv(repo: &str) -> Vec<String> {
    owned(&[
        "issue",
        "list",
        "--repo",
        repo,
        "--state",
        "all",
        "--limit",
        LIST_LIMIT,
        "--json",
        "number,title",
        "--template",
        LIST_TEMPLATE,
    ])
}

fn comments_argv(repo: &str, entry: &str) -> Vec<String> {
    owned(&[
        "issue",
        "view",
        entry,
        "--repo",
        repo,
        "--json",
        "comments",
        "--template",
        COMMENTS_TEMPLATE,
    ])
}

fn owned(args: &[&str]) -> Vec<String> {
    args.iter().map(|s| (*s).to_string()).collect()
}

/// `gh`'s own default is 30, which would silently list a fraction of a real
/// tracker — and a fraction is worse than a failure here, because a missing
/// entry reads as "not exported yet" and gets duplicated.
const LIST_LIMIT: &str = "1000";

/// One line per issue: `<number>\t<title>`. The number never carries a tab, so
/// splitting ONCE from the left leaves the whole title on the right, however it
/// is spelled.
const LIST_TEMPLATE: &str = "{{range .}}{{.number}}\t{{.title}}\n{{end}}";

/// One record per comment: a `<author>\t<createdAt>\t<byte length>` line, then
/// exactly that many bytes of body.
///
/// LENGTH-PREFIXED RATHER THAN DELIMITED, because a comment body is arbitrary
/// text a stranger wrote: any sentinel line could appear inside one, and a
/// collision would silently split one comment into two — ingesting a fragment as
/// if somebody had said it. A byte count cannot collide with anything.
const COMMENTS_TEMPLATE: &str =
    "{{range .comments}}{{.author.login}}\t{{.createdAt}}\t{{len .body}}\n{{.body}}{{end}}";

// ── The parse of each output shape ───────────────────────────────

/// `gh issue create` prints the new issue's URL; the handle is its last segment.
fn entry_from_created(stdout: &str) -> Result<String, String> {
    let url = stdout
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .ok_or_else(|| "`gh issue create` printed nothing — no issue URL to read".to_string())?;
    let number = url.rsplit('/').next().unwrap_or_default();
    if number.is_empty() || !number.chars().all(|c| c.is_ascii_digit()) {
        return Err(format!(
            "`gh issue create` printed `{url}`, whose last path segment is not an issue \
             number — the handle every later `export` addresses this entry by would be wrong"
        ));
    }
    Ok(number.to_string())
}

fn parse_list(stdout: &str) -> Result<Vec<Entry>, String> {
    let mut out = Vec::new();
    for line in stdout.lines().filter(|l| !l.trim().is_empty()) {
        let (entry, title) = line.split_once('\t').ok_or_else(|| {
            format!("`gh issue list` printed `{line}`, which carries no `<number>\\t<title>`")
        })?;
        out.push(Entry {
            entry: entry.trim().to_string(),
            title: title.to_string(),
        });
    }
    Ok(out)
}

fn parse_comments(stdout: &str) -> Result<Vec<Comment>, String> {
    let bytes = stdout.as_bytes();
    let mut at = 0usize;
    let mut out = Vec::new();
    while at < bytes.len() {
        let Some(nl) = stdout[at..].find('\n') else {
            // Trailing whitespace after the last body is `gh`'s, not a record.
            if stdout[at..].trim().is_empty() {
                break;
            }
            return Err(format!(
                "`gh issue view --json comments` ends with `{}`, which is not a \
                 `<author>\\t<at>\\t<length>` header line",
                &stdout[at..]
            ));
        };
        let header = &stdout[at..at + nl];
        at += nl + 1;
        if header.trim().is_empty() {
            continue;
        }
        let mut parts = header.split('\t');
        let (Some(author), Some(when), Some(len), None) =
            (parts.next(), parts.next(), parts.next(), parts.next())
        else {
            return Err(format!(
                "`gh issue view --json comments` printed the header `{header}`, which is \
                 not exactly `<author>\\t<createdAt>\\t<length>`"
            ));
        };
        let len: usize = len.trim().parse().map_err(|_| {
            format!("`{len}` is not a byte length, so the comment body has no end")
        })?;
        if at + len > bytes.len() {
            return Err(format!(
                "a comment declares {len} bytes of body and only {} follow — the output is \
                 truncated, and reading it would ingest a fragment as if it were the comment",
                bytes.len() - at
            ));
        }
        let body = std::str::from_utf8(&bytes[at..at + len])
            .map_err(|_| "a comment body's declared length cuts a character in half".to_string())?;
        at += len;
        out.push(Comment {
            author: author.to_string(),
            at: when.to_string(),
            body: body.to_string(),
        });
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The handle is the NUMBER, whatever `gh issue create` printed around it.
    /// Adoption reads numbers out of `gh issue list`, so a URL stored here would
    /// never compare equal to the entry it names.
    #[test]
    fn the_handle_is_the_issue_number_not_the_url() {
        assert_eq!(
            entry_from_created("https://github.com/rssh/anthill/issues/42\n").expect("parse"),
            "42"
        );
    }

    /// Anything but a number is a refusal. `gh` prints warnings to stdout in
    /// some configurations, and taking the last path segment of one would store
    /// a handle every later `export` then fails to address.
    #[test]
    fn a_created_line_that_is_not_a_url_is_refused() {
        let err = entry_from_created("Welcome to GitHub CLI!\n").expect_err("must refuse");
        assert!(err.contains("issue number"), "says what is wrong: {err}");
    }

    /// A title carrying a tab still reads back whole: the split is ONCE, from
    /// the left, and a work item's description is arbitrary prose.
    #[test]
    fn a_listed_title_may_carry_a_tab() {
        let got = parse_list("7\tWI-1: a\tb\n8\tWI-2: c\n").expect("parse");
        assert_eq!(got.len(), 2);
        assert_eq!(got[0].entry, "7");
        assert_eq!(got[0].title, "WI-1: a\tb");
        assert_eq!(got[1].title, "WI-2: c");
    }

    /// The body is taken by BYTE COUNT, so a comment containing what looks like
    /// another record's header is one comment, not two. A delimiter-based reader
    /// splits this into two and ingests a fragment.
    #[test]
    fn a_comment_body_that_looks_like_a_header_is_still_one_comment() {
        let body = "octocat\t2026-01-01T00:00:00Z\t3\nnot a record";
        let out = format!("hubot\t2026-08-20T10:00:00Z\t{}\n{body}", body.len());

        let got = parse_comments(&out).expect("parse");
        assert_eq!(got.len(), 1, "one record, not two");
        assert_eq!(got[0].author, "hubot");
        assert_eq!(got[0].body, body);
    }

    /// Two real records read back in order, with a multi-line body between them.
    #[test]
    fn two_comments_read_back_in_order() {
        let out = "a\t2026-01-01T00:00:00Z\t11\nline1\nline2b\t2026-01-02T00:00:00Z\t2\nhi";
        let got = parse_comments(out).expect("parse");
        assert_eq!(got.len(), 2);
        assert_eq!(got[0].author, "a");
        assert_eq!(got[0].body, "line1\nline2");
        assert_eq!(got[1].author, "b");
        assert_eq!(got[1].body, "hi");
    }

    /// A truncated body is a refusal rather than a short comment: ingesting a
    /// fragment records words nobody wrote in that order.
    #[test]
    fn a_truncated_comment_body_is_refused() {
        let err = parse_comments("a\t2026-01-01T00:00:00Z\t99\nshort").expect_err("must refuse");
        assert!(err.contains("truncated"), "says what is wrong: {err}");
    }

    /// Every entry, open AND closed. A verified item's issue is closed, and
    /// missing it from the listing makes adoption create a second one beside it.
    #[test]
    fn the_listing_asks_for_closed_entries_too() {
        let argv = list_argv("rssh/anthill");
        let at = argv.iter().position(|a| a == "--state").expect("--state");
        assert_eq!(argv[at + 1], "all");
    }

    /// The repo reaches every call. Without `--repo` `gh` reads the CWD's git
    /// remote, so a command run from another checkout would publish somewhere
    /// the project never named.
    #[test]
    fn every_call_names_the_repo() {
        for argv in [
            create_argv("o/r", "t", "b"),
            update_argv("o/r", "1", "t", "b"),
            list_argv("o/r"),
            comments_argv("o/r", "1"),
        ] {
            let at = argv
                .iter()
                .position(|a| a == "--repo")
                .unwrap_or_else(|| panic!("no --repo in {argv:?}"));
            assert_eq!(argv[at + 1], "o/r");
        }
    }
}
