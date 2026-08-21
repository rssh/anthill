//! The fake export target: a directory of files standing in for a forge.
//!
//! NOT A TEST TRICK — the second implementation of a first-class seam, and what
//! makes `export` and `import` drivable with no network and no account. §8.3
//! justified a fake that could force §6.1's lost-race interleavings
//! deterministically and let tests search whole schedule spaces under `Branch`.
//! There is no race left (WI-1121 made allocation local and pure), so there is
//! no schedule space, and this is deliberately no larger than export and import
//! need.
//!
//! ON DISK, AND WHY IT IS ON DISK RATHER THAN IN MEMORY. Each entry is
//! `<dir>/<n>.entry`, its comments `<dir>/<n>.comments`. The state has to
//! survive between two runs of the CLI, because the property an idempotence test
//! measures is exactly what the SECOND run does — an in-memory list would start
//! empty on the second `export` and every run would look like the first.
//!
//! THE COMMENT FILE IS HAND-WRITABLE, and that is its job: `import` has no way
//! to produce a comment (nothing in the tree generates one — that is what makes
//! ingestion sound, §7.3), so a test drives it by writing the file a target
//! would have.

use std::fs;
use std::path::PathBuf;

use super::{Comment, Entry, ForgeBackend};

pub(crate) struct Fake {
    /// Where the entries actually live, resolved against the config directory.
    pub dir: PathBuf,
    /// The directory AS WRITTEN in the `Mirror` fact, which is what names the
    /// target. The resolved path would put this machine's `/private/tmp/...` into
    /// every item's `- mirrors:` line, so a link written on one checkout would
    /// not be recognized on another — and the `MirrorEntry` rows are committed
    /// to the repository.
    pub declared: String,
}

/// Between a record's headers and its body.
const BODY_MARK: &str = "--";
/// Between two comment records.
const RECORD_MARK: &str = "====";
/// Holds the next handle to hand out. Not an `.entry`, so the listing ignores it.
const HANDLE_COUNTER: &str = "next";

impl ForgeBackend for Fake {
    /// The DIRECTORY AS WRITTEN, so two fakes in one project are two targets —
    /// the same property `GithubForge`'s repo gives it, and written the same way:
    /// what the configuration says, not what this machine resolved it to.
    fn target_name(&self) -> String {
        format!("fake:{}", self.declared)
    }

    fn create_entry(&self, title: &str, body: &str) -> Result<String, String> {
        fs::create_dir_all(&self.dir)
            .map_err(|e| format!("creating the fake target's directory: {e}"))?;
        // FROM A COUNTER, not from what is on disk. §8.3's contract item (5) is
        // that entries PERSIST once created, so a real target never re-issues a
        // handle — and a fake that derived the next number from the highest file
        // present would hand a deleted entry's number to the next one, silently
        // re-pointing some item's `MirrorEntry` at somebody else's entry. The
        // fake exists to stand in for the real thing, so it keeps the property.
        let entry = self.take_handle()?;
        self.write_entry(&entry, title, body)?;
        Ok(entry)
    }

    fn update_entry(&self, entry: &str, title: &str, body: &str) -> Result<(), String> {
        if !self.entry_path(entry).exists() {
            return Err(format!(
                "the fake target has no entry `{entry}` to update — the link says it was \
                 exported, and it is not there"
            ));
        }
        self.write_entry(entry, title, body)
    }

    fn list_entries(&self) -> Result<Vec<Entry>, String> {
        if !self.dir.exists() {
            return Ok(Vec::new());
        }
        let mut out = Vec::new();
        for found in fs::read_dir(&self.dir)
            .map_err(|e| format!("reading the fake target's directory: {e}"))?
        {
            let path = found
                .map_err(|e| format!("reading the fake target's directory: {e}"))?
                .path();
            if path.extension().and_then(|e| e.to_str()) != Some("entry") {
                continue;
            }
            let Some(entry) = path.file_stem().and_then(|s| s.to_str()) else {
                continue;
            };
            let text = fs::read_to_string(&path)
                .map_err(|e| format!("reading {}: {e}", path.display()))?;
            let (headers, _) = split_record(&text);
            out.push(Entry {
                entry: entry.to_string(),
                title: header(&headers, "title").unwrap_or_default(),
            });
        }
        // NEWEST FIRST, like the listing §8.3's contract item (2) describes.
        // Sorted by NUMBER, not by the string: `10` sorts before `9`
        // lexically, and a test that exports ten items would see the wrong order.
        out.sort_by_key(|e| std::cmp::Reverse(e.entry.parse::<u64>().unwrap_or(0)));
        Ok(out)
    }

    fn entry_comments(&self, entry: &str) -> Result<Vec<Comment>, String> {
        let path = self.dir.join(format!("{entry}.comments"));
        if !path.exists() {
            return Ok(Vec::new());
        }
        let text =
            fs::read_to_string(&path).map_err(|e| format!("reading {}: {e}", path.display()))?;
        let mut out = Vec::new();
        for (i, record) in text.split(&format!("\n{RECORD_MARK}\n")).enumerate() {
            if record.trim().is_empty() {
                continue;
            }
            let (headers, body) = split_record(record);
            // LOUD, not skipped: a comment whose author or timestamp is missing
            // cannot be deduped — `(author, at)` IS the ingest key — so ingesting
            // it would re-add the same feedback on every run.
            let (Some(author), Some(at)) = (header(&headers, "author"), header(&headers, "at"))
            else {
                return Err(format!(
                    "{}: comment {} carries no `author:`/`at:` header pair, and that pair \
                     is what ingestion dedups on",
                    path.display(),
                    i + 1
                ));
            };
            out.push(Comment {
                author,
                at,
                body: body.trim_end_matches('\n').to_string(),
            });
        }
        Ok(out)
    }
}

impl Fake {
    fn entry_path(&self, entry: &str) -> PathBuf {
        self.dir.join(format!("{entry}.entry"))
    }

    /// The next handle, advancing the counter. A missing counter file starts at
    /// 1, so a directory a test hand-populated still works.
    fn take_handle(&self) -> Result<String, String> {
        let path = self.dir.join(HANDLE_COUNTER);
        let next: u64 = match fs::read_to_string(&path) {
            Ok(text) => text
                .trim()
                .parse()
                .map_err(|_| format!("{}: `{}` is not a handle", path.display(), text.trim()))?,
            Err(_) => self
                .list_entries()?
                .iter()
                .filter_map(|e| e.entry.parse::<u64>().ok())
                .max()
                .unwrap_or(0)
                + 1,
        };
        fs::write(&path, (next + 1).to_string())
            .map_err(|e| format!("writing {}: {e}", path.display()))?;
        Ok(next.to_string())
    }

    fn write_entry(&self, entry: &str, title: &str, body: &str) -> Result<(), String> {
        fs::create_dir_all(&self.dir)
            .map_err(|e| format!("creating the fake target's directory: {e}"))?;
        let path = self.entry_path(entry);
        fs::write(&path, format!("title: {title}\n{BODY_MARK}\n{body}\n"))
            .map_err(|e| format!("writing {}: {e}", path.display()))
    }
}

/// A record's header block and its body, split at the first `--` line. A record
/// with no `--` is all headers and an empty body.
fn split_record(text: &str) -> (Vec<String>, String) {
    let mut headers = Vec::new();
    let mut lines = text.trim_start_matches('\n').lines();
    for line in lines.by_ref() {
        if line.trim() == BODY_MARK {
            break;
        }
        headers.push(line.to_string());
    }
    (headers, lines.collect::<Vec<_>>().join("\n"))
}

fn header(headers: &[String], name: &str) -> Option<String> {
    headers
        .iter()
        .find_map(|l| l.strip_prefix(&format!("{name}:")))
        .map(|v| v.trim().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A comment file as a test hand-writes it reads back as its records — the
    /// only way `import` can be driven, since nothing in the tree makes comments.
    #[test]
    fn a_hand_written_comment_file_reads_back_as_records() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let fake = Fake {
            dir: tmp.path().to_path_buf(),
            declared: "mirror".to_string(),
        };
        fs::write(
            tmp.path().join("7.comments"),
            "author: octocat\nat: 2026-08-20T10:00:00Z\n--\nfirst line\nsecond line\n\
             \n====\nauthor: hubot\nat: 2026-08-20T11:00:00Z\n--\njust one\n",
        )
        .expect("write comments");

        let got = fake.entry_comments("7").expect("read comments");
        assert_eq!(got.len(), 2, "two records, split on the `====` line");
        assert_eq!(got[0].author, "octocat");
        assert_eq!(got[0].at, "2026-08-20T10:00:00Z");
        assert_eq!(
            got[0].body, "first line\nsecond line",
            "the body is every line after `--`, newlines and all"
        );
        assert_eq!(got[1].author, "hubot");
        assert_eq!(got[1].body, "just one");
    }

    /// A record missing the dedup key is REFUSED, not ingested with a blank
    /// author: `(author, at)` is what makes ingestion idempotent, so a record
    /// without it would re-add the same feedback on every `import`.
    #[test]
    fn a_comment_with_no_author_is_refused() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let fake = Fake {
            dir: tmp.path().to_path_buf(),
            declared: "mirror".to_string(),
        };
        fs::write(tmp.path().join("3.comments"), "at: 2026-08-20T10:00:00Z\n--\nbody\n")
            .expect("write comments");

        let err = fake.entry_comments("3").expect_err("must refuse");
        assert!(err.contains("dedups on"), "says why it matters: {err}");
    }

    /// A handle is never reused. Deleting entry 2 of 2 and creating another must
    /// not hand out `2` again — an item's `MirrorEntry` still names it, and the
    /// reused handle would silently re-point that item at somebody else's entry.
    #[test]
    fn a_deleted_handle_is_not_handed_out_again() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let fake = Fake {
            dir: tmp.path().to_path_buf(),
            declared: "mirror".to_string(),
        };
        assert_eq!(fake.create_entry("one", "b").expect("create"), "1");
        assert_eq!(fake.create_entry("two", "b").expect("create"), "2");
        fs::remove_file(tmp.path().join("2.entry")).expect("delete entry 2");

        assert_eq!(
            fake.create_entry("three", "b").expect("create"),
            "3",
            "one past the HIGHEST that exists, not the file count"
        );
    }

    /// `update_entry` on a handle the target does not hold is a refusal. The link
    /// said the item was exported; silently creating a new entry would leave the
    /// tracker pointing at one entry and the reader looking at another.
    #[test]
    fn updating_an_absent_entry_is_refused() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let fake = Fake {
            dir: tmp.path().to_path_buf(),
            declared: "mirror".to_string(),
        };
        let err = fake
            .update_entry("42", "t", "b")
            .expect_err("must refuse an absent entry");
        assert!(err.contains("42"), "names the handle: {err}");
    }
}
