//! WI-VDXAM — `fsck --renumber`, the REPAIR half of design §6.6.
//!
//! Design: `rustland/anthill-todo/docs/design/backend-github-coordination.md` §6.5,
//! §6.6. WI-1121 shipped the DETECTION: two unsynced writers can mint ids whose
//! `<time>-<hash>` identity prefixes agree, `LayoutFault::IdCollision` names that and
//! BLOCKS. What ships here is the repair, and the load-bearing property is not that it
//! works but that TWO CHECKOUTS RESOLVING THE SAME COLLISION WITHOUT TALKING PRODUCE
//! THE SAME TREE — a repair the two sides disagree about turns one collision into a
//! second and worse divergence.
//!
//! WHAT FAILS WITHOUT THE CHANGE. Every test in this file. `--renumber` is not a flag
//! any earlier build accepts, so each one exits non-zero at option parsing.
//!
//! WHAT PASSES EITHER WAY BY DESIGN. Nothing here. `a_collision_blocks_every_command`
//! comes closest — WI-1121 already made a collision blocking — but it also asserts the
//! remedy the message names, and before this change that line said `--fix`, which
//! repairs nothing here and reports the same error again.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn run_in(proj: &Path, args: &[&str]) -> std::process::Output {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    Command::new(BIN)
        .args(&full)
        .output()
        .expect("run anthill-todo")
}

fn ok(proj: &Path, args: &[&str]) -> String {
    let out = run_in(proj, args);
    assert!(
        out.status.success(),
        "{args:?} failed\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

const ITEM_PER_FILE_BINDING: &str = r#"fact Project(
  name: "per-file",
  language: "rust",
  build: "cargo",
  tools: ["cargo-test"])

fact anthill.persistence.ExtentBinding(
  store: anthill.persistence.filesystem.ItemPerFileStore(
    root: ".",
    status_field: "last_status_change.status",
    id_field: "id",
    ref_field: "workitem"),
  role: anthill.persistence.ExtentRole.mirror(),
  covers: [WorkItem, Feedback, Tag, StoreFormat])
"#;

/// The shared identity prefix every fixture below collides on. Hand-written, because
/// a single writer CANNOT mint one: `mint_id` looks before it writes and advances its
/// attempt counter (§6.5). The whole subject of §6.6 is the state only two unsynced
/// writers reach, so a fixture for it is written by hand or not at all.
const PREFIX: &str = "WI-20260817-K7M2Q";

/// One item document, spelled out. `created` and `status_agent` are the two inputs the
/// loser-order reads besides the description, so each fixture states them.
fn item_doc(id: &str, created: &str, agent: &str, description: &str, extra: &str) -> String {
    format!(
        "## Attributes\n\n- id: {id}\n- created: {created}\n\n- status: Open\n\
         - status_agent: {agent}\n\n- acceptance: cargo-test\n{extra}\n\
         ## Description\n\n{description}\n"
    )
}

/// A project on the per-file layout holding exactly the item files given, each as
/// `(id, created, agent, description, extra attribute lines)`.
fn colliding_project(tmp: &tempfile::TempDir, items: &[(&str, &str, &str, &str, &str)]) -> PathBuf {
    let proj = setup_project(tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        ITEM_PER_FILE_BINDING,
    )
    .expect("write project config");
    fs::remove_file(proj.join("anthill-todo/workitems.anthill")).expect("no shared file");
    let open = proj.join("anthill-todo/open");
    fs::create_dir_all(&open).expect("mkdir open");
    for (id, created, agent, description, extra) in items {
        fs::write(
            open.join(format!("{id}.anthill.md")),
            item_doc(id, created, agent, description, extra),
        )
        .expect("write item");
    }
    proj
}

/// THE STANDARD FIXTURE: two real items whose ids share `PREFIX` and whose slugs — so
/// whose FILENAMES — differ, which is why git merges the two cleanly and nothing below
/// the tracker can notice. `beta` was created an hour later, so `beta` is the loser.
///
/// HERE THE `created` ORDER AND THE PATH ORDER AGREE, so these tests measure the repair
/// and not the rule that picks its target. The rule has its own controls:
/// `later_created_loses_even_when_it_sorts_first` and
/// `an_equal_created_is_broken_on_the_author`, where the two orders are made to
/// disagree.
fn two_colliding(tmp: &tempfile::TempDir) -> (PathBuf, String, String) {
    let winner = format!("{PREFIX}-alpha-thing");
    let loser = format!("{PREFIX}-beta-thing");
    let proj = colliding_project(
        tmp,
        &[
            (&winner, "2026-08-17T09:00:00Z", "alice", "alpha thing", ""),
            (&loser, "2026-08-17T10:00:00Z", "bob", "beta thing", ""),
        ],
    );
    (proj, winner, loser)
}

fn open_dir(proj: &Path) -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(proj.join("anthill-todo/open"))
        .expect("read open/")
        .map(|e| e.expect("entry").file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    names
}

/// The one id in `open/` that is neither of the two given — the id the repair minted.
fn minted_id(proj: &Path, known: &[&str]) -> String {
    let found: Vec<String> = open_dir(proj)
        .into_iter()
        .map(|n| n.trim_end_matches(".anthill.md").to_string())
        .filter(|id| !known.contains(&id.as_str()))
        .collect();
    assert_eq!(found.len(), 1, "exactly one id was minted: {found:?}");
    found.into_iter().next().expect("length checked")
}

// ── The fault, and the remedy it names ─────────────────────────

/// A collision blocks every command, and the message names the verb that repairs IT.
///
/// THE REMEDY IS THE ASSERTION. The fault itself is WI-1121's; what is new is that the
/// gate no longer sends its reader to `--fix`, which moves a file to the path its fact
/// names and so does exactly nothing here — then reports the same error again.
#[test]
fn a_collision_blocks_every_command_and_names_renumber() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (proj, winner, loser) = two_colliding(&tmp);

    let blocked = run_in(&proj, &["list"]);
    assert!(!blocked.status.success(), "a collision is not worked around");
    let err = String::from_utf8_lossy(&blocked.stderr);
    assert!(err.contains(PREFIX), "the fault names the prefix: {err}");
    assert!(err.contains(&winner) && err.contains(&loser), "and both files: {err}");
    assert!(
        err.contains("fsck --renumber"),
        "and the verb that repairs it: {err}"
    );
    assert!(
        !err.contains("fsck --fix"),
        "which is NOT the one that moves a file: {err}"
    );
}

// ── The repair ─────────────────────────────────────────────────

/// The whole gesture, end to end: the later-created item is re-minted, its file
/// travels with its id, and the tracker is usable again.
#[test]
fn renumber_re_mints_the_later_item_and_moves_its_file() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (proj, winner, loser) = two_colliding(&tmp);

    let out = ok(&proj, &["fsck", "--renumber"]);
    assert!(out.contains(&format!("renumbered {loser} -> ")), "{out}");

    let minted = minted_id(&proj, &[&winner]);
    assert_ne!(minted, loser, "the id changed");
    assert!(minted.ends_with("-beta-thing"), "the slug is kept: {minted}");
    assert!(
        minted.starts_with("WI-20260817-"),
        "and so is the day partition, which `created` decides: {minted}"
    );
    assert_eq!(
        open_dir(&proj),
        vec![
            format!("{minted}.anthill.md"),
            format!("{winner}.anthill.md"),
        ],
        "the loser's file is at the new id and the winner's is untouched"
    );

    let doc = fs::read_to_string(
        proj.join("anthill-todo/open")
            .join(format!("{minted}.anthill.md")),
    )
    .expect("the renumbered file");
    assert!(doc.contains(&format!("- id: {minted}\n")), "{doc}");
    assert!(doc.contains("beta thing"), "its description came through: {doc}");

    // Read back by the NEXT process: without this the repair is write-only.
    let listed = ok(&proj, &["list"]);
    assert!(listed.contains(&minted) && listed.contains(&winner), "{listed}");
}

/// Every inbound `depends_on` moves with the id. A renumber that changed the id and
/// left the edges behind would turn one collision into a tree of dangling references —
/// which `list` renders as a blocked item waiting on nothing.
#[test]
fn every_inbound_depends_on_is_rewritten() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let winner = format!("{PREFIX}-alpha-thing");
    let loser = format!("{PREFIX}-beta-thing");
    let dependent = "WI-20260817-ZZZZZ-third";
    let proj = colliding_project(
        &tmp,
        &[
            (&winner, "2026-08-17T09:00:00Z", "alice", "alpha thing", ""),
            (&loser, "2026-08-17T10:00:00Z", "bob", "beta thing", ""),
            (
                dependent,
                "2026-08-17T11:00:00Z",
                "alice",
                "third thing",
                &format!("\n- depends_on: {loser}\n"),
            ),
        ],
    );

    let out = ok(&proj, &["fsck", "--renumber"]);
    assert!(out.contains("rewrote `depends_on` in 1 item(s)"), "{out}");

    let minted = minted_id(&proj, &[&winner, dependent]);
    let third = fs::read_to_string(
        proj.join("anthill-todo/open")
            .join(format!("{dependent}.anthill.md")),
    )
    .expect("the dependent's file");
    assert!(third.contains(&format!("- depends_on: {minted}")), "{third}");
    assert!(!third.contains(&loser), "and the retired id is gone: {third}");

    // The edge is a live edge, not just a matching string.
    let listed = ok(&proj, &["list"]);
    assert!(
        listed.contains(&format!("depends: {minted}")),
        "the graph reads the rewritten edge: {listed}"
    );
}

/// The loser's satellites travel with it: they live in its file, and their
/// `workitem:` names the id that just changed.
///
/// THE CONTROL IS `show` AND `list --tag`, not the file's bytes. A tag and a feedback
/// entry are written INSIDE the item's document (§5.3), so "the text is still there"
/// would pass for a repair that moved the bytes and left every row naming an id no file
/// holds — an orphan at the next startup. Resolving them through the new id is what
/// proves the reference moved.
#[test]
fn satellites_travel_with_the_renumbered_item() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let winner = format!("{PREFIX}-alpha-thing");
    let loser = format!("{PREFIX}-beta-thing");
    let proj = colliding_project(
        &tmp,
        &[
            (&winner, "2026-08-17T09:00:00Z", "alice", "alpha thing", ""),
            (
                &loser,
                "2026-08-17T10:00:00Z",
                "bob",
                "beta thing",
                "\n- tags: wi437, backend\n",
            ),
        ],
    );
    // The feedback chapter, appended through the CLI so its shape is the store's own.
    // It cannot run while the tree collides, so it is written by hand, exactly as a
    // merge would have left it.
    let path = proj
        .join("anthill-todo/open")
        .join(format!("{loser}.anthill.md"));
    let mut doc = fs::read_to_string(&path).unwrap();
    doc.push_str("\n## Changes\n\n### 2026-08-17T12:00:00Z — feedback — user\n\na note that must travel\n");
    fs::write(&path, doc).unwrap();

    let out = ok(&proj, &["fsck", "--renumber"]);
    assert!(out.contains("re-pointed 3 satellite row(s)"), "two tags and one feedback: {out}");

    let minted = minted_id(&proj, &[&winner]);
    let shown = ok(&proj, &["show", &minted]);
    assert!(shown.contains("backend, wi437"), "the tags resolve under the new id: {shown}");
    assert!(shown.contains("a note that must travel"), "and so does the feedback: {shown}");

    let tagged = ok(&proj, &["list", "--tag", "wi437"]);
    assert!(tagged.contains(&minted), "{tagged}");
    assert!(!tagged.contains(&loser), "and nothing answers to the retired id: {tagged}");

    // And nothing was stranded: a satellite left naming the old id is an orphan, which
    // `fsck` reports.
    let checked = ok(&proj, &["fsck"]);
    assert!(checked.contains("layout ok"), "{checked}");
}

/// PROSE IS REPORTED, NOT REWRITTEN. Both sides of a collision were minted into one
/// day partition, so a `WI-…` in a description or a feedback entry may perfectly well
/// mean the item that KEPT the id — and nothing distinguishes the two readings. The
/// honest answer is the location and the reason.
#[test]
fn prose_mentions_are_reported_and_left_alone() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let winner = format!("{PREFIX}-alpha-thing");
    let loser = format!("{PREFIX}-beta-thing");
    let talker = "WI-20260817-ZZZZZ-third";
    let proj = colliding_project(
        &tmp,
        &[
            (&winner, "2026-08-17T09:00:00Z", "alice", "alpha thing", ""),
            (&loser, "2026-08-17T10:00:00Z", "bob", "beta thing", ""),
            (
                talker,
                "2026-08-17T11:00:00Z",
                "alice",
                &format!("third thing, which discusses {loser} in prose"),
                "",
            ),
        ],
    );

    let out = ok(&proj, &["fsck", "--renumber"]);
    assert!(out.contains("prose mention(s)"), "{out}");
    assert!(
        out.contains(&format!("{talker}.anthill.md:")),
        "with the file and the line: {out}"
    );
    assert!(
        out.contains("were NOT rewritten"),
        "and it says it did not touch them: {out}"
    );

    let third = fs::read_to_string(
        proj.join("anthill-todo/open")
            .join(format!("{talker}.anthill.md")),
    )
    .unwrap();
    assert!(
        third.contains(&format!("discusses {loser} in prose")),
        "the sentence is byte-for-byte what it was: {third}"
    );
}

// ── Convergence: the property the whole design rests on ────────

/// THE TEST THAT MATTERS. Two checkouts that have not synced hold the same merged
/// tree; each repairs it alone; the two trees must come out BYTE-IDENTICAL, so that
/// git merges the two independent fixes with no conflict because both sides made the
/// same change.
///
/// The second checkout is made to differ in everything a repair must NOT read: the
/// files are written in the opposite order, and their modification times are set
/// decades apart. Only the CONTENT of the rows is the same.
#[test]
fn two_checkouts_repairing_independently_produce_identical_trees() {
    let one = tempfile::tempdir().expect("tempdir");
    let two = tempfile::tempdir().expect("tempdir");
    let winner = format!("{PREFIX}-alpha-thing");
    let loser = format!("{PREFIX}-beta-thing");
    let items: [(&str, &str, &str, &str, &str); 2] = [
        (&winner, "2026-08-17T09:00:00Z", "alice", "alpha thing", ""),
        (&loser, "2026-08-17T10:00:00Z", "bob", "beta thing", ""),
    ];
    let mut reversed = items;
    reversed.reverse();
    let a = colliding_project(&one, &items);
    let b = colliding_project(&two, &reversed);

    // Different mtimes, decades apart, on the file that a "whichever is older" rule
    // would pick — the second thing §6.6's control names after file order.
    let old = std::time::SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(1_000_000);
    fs::File::options()
        .write(true)
        .open(
            b.join("anthill-todo/open")
                .join(format!("{winner}.anthill.md")),
        )
        .expect("open for set_modified")
        .set_modified(old)
        .expect("set mtime");

    ok(&a, &["fsck", "--renumber"]);
    ok(&b, &["fsck", "--renumber"]);

    let names_a = open_dir(&a);
    assert_eq!(names_a, open_dir(&b), "the same files, under the same ids");
    for name in &names_a {
        let ta = fs::read_to_string(a.join("anthill-todo/open").join(name)).unwrap();
        let tb = fs::read_to_string(b.join("anthill-todo/open").join(name)).unwrap();
        assert_eq!(ta, tb, "{name} came out byte-identical");
    }
}

/// THE CONTROL FOR THE ORDER. `created` decides, not the order the files are walked
/// in — and here the two disagree: `zulu thing` was created FIRST and sorts LAST, so a
/// repair that renumbered "the second file it met" would pick the wrong side.
///
/// WHAT FAILS WHEN THE ORDER IS BACKED OUT: this test alone. Every other test in this
/// file passes under a "later path loses" rule, because their fixtures are written so
/// that the two agree.
#[test]
fn later_created_loses_even_when_it_sorts_first() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let early_but_last = format!("{PREFIX}-zulu-thing");
    let late_but_first = format!("{PREFIX}-alpha-thing");
    let proj = colliding_project(
        &tmp,
        &[
            (&early_but_last, "2026-08-17T09:00:00Z", "alice", "zulu thing", ""),
            (&late_but_first, "2026-08-17T10:00:00Z", "bob", "alpha thing", ""),
        ],
    );

    let out = ok(&proj, &["fsck", "--renumber"]);
    assert!(
        out.contains(&format!("renumbered {late_but_first} -> ")),
        "the LATER-created item lost, though its file sorts first: {out}"
    );
    assert!(
        open_dir(&proj).contains(&format!("{early_but_last}.anthill.md")),
        "and the earlier one kept its id: {:?}",
        open_dir(&proj)
    );
}

/// Equal `created` is broken on the author, and that is what makes the order TOTAL
/// rather than usually-total: a merged tree can perfectly well hold two items filed in
/// the same second, and a rule that stopped at `created` would leave the two checkouts
/// to pick by whatever came next.
///
/// THE AUTHOR ORDER AND THE DESCRIPTION ORDER DISAGREE HERE, deliberately. `zoe` filed
/// `alpha thing` and `adam` filed `beta thing`, so a repair that never read the author
/// — the field a work item does NOT obviously carry (§6.7: it records no filer, only
/// the agent of its last status change) — would fall through to the description and
/// renumber the other side. It is also the only test here whose answer differs from
/// "the file that sorts last loses".
#[test]
fn an_equal_created_is_broken_on_the_author() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let by_zoe = format!("{PREFIX}-alpha-thing");
    let by_adam = format!("{PREFIX}-beta-thing");
    let proj = colliding_project(
        &tmp,
        &[
            (&by_adam, "2026-08-17T09:00:00Z", "adam", "beta thing", ""),
            (&by_zoe, "2026-08-17T09:00:00Z", "zoe", "alpha thing", ""),
        ],
    );

    let out = ok(&proj, &["fsck", "--renumber"]);
    assert!(
        out.contains(&format!("renumbered {by_zoe} -> ")),
        "`adam` sorts before `zoe`, so zoe's is the side that moves — though its \
         description sorts first and would have won on the next key: {out}"
    );
}

// ── The override ───────────────────────────────────────────────

/// `--renumber <id>` forces THAT id to be the one that moves — for when the other has
/// already escaped into commit messages, where nothing here can follow it.
#[test]
fn renumber_with_an_id_forces_which_side_loses() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (proj, would_win, would_lose) = two_colliding(&tmp);

    let out = ok(&proj, &["fsck", "--renumber", &would_win]);
    assert!(
        out.contains(&format!("renumbered {would_win} -> ")),
        "the named side lost, against the order: {out}"
    );
    let names = open_dir(&proj);
    assert!(
        names.contains(&format!("{would_lose}.anthill.md")),
        "and the side the order would have moved kept its id: {names:?}"
    );
}

/// An id that is not one side of a collision is a refusal, not a no-op. Renumbering it
/// would change an identity nothing asked to change.
#[test]
fn renumber_refuses_an_id_that_is_not_colliding() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (proj, _, _) = two_colliding(&tmp);

    let out = run_in(&proj, &["fsck", "--renumber", "WI-20260817-ZZZZZ-nothing"]);
    assert!(!out.status.success(), "{out:?}");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("not one side of an id collision"), "{err}");
}

// ── The quiet cases ────────────────────────────────────────────

/// A tree with nothing to repair says so. A repair that prints nothing is
/// indistinguishable from one that did not run.
#[test]
fn renumber_on_a_clean_tree_says_there_is_nothing_to_do() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = colliding_project(
        &tmp,
        &[(
            "WI-20260817-AAAAA-lonely",
            "2026-08-17T09:00:00Z",
            "alice",
            "lonely thing",
            "",
        )],
    );
    let out = ok(&proj, &["fsck", "--renumber"]);
    assert!(out.contains("no id collisions"), "{out}");
    assert!(out.contains("layout ok"), "{out}");
}

/// Grandfathered `WI-NNN` ids carry no identity prefix, so they cannot collide and are
/// never re-minted. §6.5: the two id shapes coexist permanently, and renumbering
/// `WI-1114` would break 4,700 references to buy nothing.
#[test]
fn legacy_ids_are_never_renumbered() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = colliding_project(
        &tmp,
        &[
            ("WI-001", "2026-08-17T09:00:00Z", "alice", "first", ""),
            ("WI-002", "2026-08-17T09:00:00Z", "alice", "second", ""),
        ],
    );
    let out = ok(&proj, &["fsck", "--renumber"]);
    assert!(out.contains("no id collisions"), "{out}");
    assert_eq!(
        open_dir(&proj),
        vec!["WI-001.anthill.md", "WI-002.anthill.md"],
        "both kept their ids"
    );
}

/// A DUPLICATE ID STOPS THE REPAIR, and it is the sharp case rather than a
/// tidiness check: two files carrying ONE id would be re-minted to two different
/// ids under one key, and whichever landed second would move onto the other's file.
/// The remedy is the opposite one and nobody but the user can pick it (§10).
#[test]
fn renumber_refuses_while_a_duplicate_id_stands() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let winner = format!("{PREFIX}-alpha-thing");
    let loser = format!("{PREFIX}-beta-thing");
    let proj = colliding_project(
        &tmp,
        &[
            (&winner, "2026-08-17T09:00:00Z", "alice", "alpha thing", ""),
            (&loser, "2026-08-17T10:00:00Z", "bob", "beta thing", ""),
        ],
    );
    // A second file claiming the winner's id — the debris an interrupted move
    // leaves, and the one thing `fsck` refuses to pick between.
    let claimed = proj.join("anthill-todo/claimed");
    fs::create_dir_all(&claimed).expect("mkdir claimed");
    fs::write(
        claimed.join(format!("{winner}.anthill.md")),
        item_doc(&winner, "2026-08-17T09:00:00Z", "alice", "alpha thing", ""),
    )
    .expect("write the duplicate");

    let out = run_in(&proj, &["fsck", "--renumber"]);
    assert!(!out.status.success(), "{out:?}");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("Resolve that first"), "{err}");
    assert!(
        open_dir(&proj).contains(&format!("{loser}.anthill.md")),
        "and nothing was renumbered: {:?}",
        open_dir(&proj)
    );
}

// ── What has to be settled first, and what is not a deadlock ───

/// THE TWO REPAIRS COMPOSE IN ONE RUN. `--fix` moves the misplaced file, and
/// `--renumber` then finds a tree whose only remaining fault is the collision.
///
/// WHAT FAILED BEFORE THE FIX (found in review): `repair_paths` refused outright
/// while ANY collision stood, so the combined form died inside `--fix` and never
/// reached the renumber — and the report told its reader to run `--fix` first,
/// which is the command that had just refused. Two colliding ids name two
/// DIFFERENT destinations, so a collision makes no path repair ambiguous and had
/// no business blocking one.
#[test]
fn fix_and_renumber_repair_a_tree_holding_both_faults_in_one_run() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (proj, winner, loser) = two_colliding(&tmp);

    // Displace the loser, the way an interrupted `claim` would: the bytes say
    // `Open`, the directory says `claimed`.
    let claimed = proj.join("anthill-todo/claimed");
    fs::create_dir_all(&claimed).expect("mkdir claimed");
    fs::rename(
        proj.join("anthill-todo/open").join(format!("{loser}.anthill.md")),
        claimed.join(format!("{loser}.anthill.md")),
    )
    .expect("displace");

    let out = ok(&proj, &["fsck", "--fix", "--renumber"]);
    assert!(out.contains("moved"), "the file was put back: {out}");
    assert!(out.contains(&format!("renumbered {loser} -> ")), "{out}");
    assert!(out.contains("layout ok"), "and nothing is left over: {out}");

    let minted = minted_id(&proj, &[&winner]);
    assert_eq!(
        open_dir(&proj),
        vec![
            format!("{minted}.anthill.md"),
            format!("{winner}.anthill.md"),
        ],
    );
    assert!(
        !claimed.join(format!("{loser}.anthill.md")).exists(),
        "and the displaced copy is gone"
    );
}

/// `--renumber` ALONE refuses while a misplaced file stands, and names the verb
/// that moves it. It does not half-repair.
///
/// WHAT FAILED BEFORE THE FIX (found in review): it renumbered, moved the file as
/// a side effect of the update — and then reported the `PathDisagreement` recorded
/// at load, naming a path and an id that no longer existed, exiting non-zero on a
/// repair that had worked.
#[test]
fn renumber_refuses_while_a_misplaced_file_stands() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (proj, _, loser) = two_colliding(&tmp);
    let claimed = proj.join("anthill-todo/claimed");
    fs::create_dir_all(&claimed).expect("mkdir claimed");
    fs::rename(
        proj.join("anthill-todo/open").join(format!("{loser}.anthill.md")),
        claimed.join(format!("{loser}.anthill.md")),
    )
    .expect("displace");

    let out = run_in(&proj, &["fsck", "--renumber"]);
    assert!(!out.status.success(), "{out:?}");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("Resolve that first"), "{err}");
    assert!(err.contains("fsck --fix"), "naming the verb that does it: {err}");
    assert!(
        claimed.join(format!("{loser}.anthill.md")).exists(),
        "and nothing moved"
    );
}

/// AN UNDATED COLLIDING ITEM IS REFUSED, NOT SILENTLY MADE THE WINNER.
///
/// WHAT FAILED BEFORE THE FIX (found in review): an absent `created` read back as
/// the empty string, which sorts before every real timestamp — so the rule "later
/// `created` loses" handed the collision to the item with no date at all, and
/// renumbered the well-formed one.
///
/// AND `--fix --renumber` GETS THROUGH IT IN ONE RUN, which is the second half of
/// the assertion: `--fix` dates the item from its file, and the renumber SEES that
/// dated row. Before the store kept a row addressable across an update-flush, it
/// did not — the row vanished from the store's index, its collision group dropped
/// to one, and the repair reported nothing to do while `fsck` went on reporting
/// the collision.
#[test]
fn an_undated_colliding_item_is_refused_and_then_dated_by_fix() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let winner = format!("{PREFIX}-alpha-thing");
    let undated = format!("{PREFIX}-beta-thing");
    let proj = colliding_project(
        &tmp,
        &[(&winner, "2026-08-17T09:00:00Z", "alice", "alpha thing", "")],
    );
    // Written by hand without the field, which is how an item file acquires one:
    // `created` is not the sort of thing a person remembers.
    fs::write(
        proj.join("anthill-todo/open").join(format!("{undated}.anthill.md")),
        "## Attributes\n\n- id: {ID}\n\n- status: Open\n- status_agent: bob\n\n         - acceptance: cargo-test\n\n## Description\n\nbeta thing\n"
            .replace("{ID}", &undated),
    )
    .expect("write the undated item");

    let refused = run_in(&proj, &["fsck", "--renumber"]);
    assert!(!refused.status.success(), "{refused:?}");
    let err = String::from_utf8_lossy(&refused.stderr);
    assert!(err.contains(&undated), "it names the undated item: {err}");
    assert!(err.contains("carries no `created`"), "{err}");
    assert!(
        open_dir(&proj).contains(&format!("{winner}.anthill.md")),
        "and the well-formed item kept its id: {:?}",
        open_dir(&proj)
    );

    let out = ok(&proj, &["fsck", "--fix", "--renumber"]);
    assert!(out.contains(&format!("dated {undated}")), "{out}");
    assert!(
        out.contains(&format!("renumbered {undated} -> ")),
        "and the dated row was still there to renumber: {out}"
    );
    assert!(out.contains("layout ok"), "{out}");
}

/// A fault with no mechanical repair names no command — and `--fix` in particular,
/// because `repair_layout` SKIPS a blocking document fault by design: re-rendering
/// a file the reader had to drop a field from would make the loss permanent.
///
/// WHAT FAILED BEFORE THE FIX (found in review): the gate said "run `fsck --fix`",
/// and `fsck --fix` printed `no misplaced files` and the identical error.
#[test]
fn a_fault_no_command_repairs_names_no_command() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = colliding_project(
        &tmp,
        &[(
            "WI-20260817-AAAAA-one",
            "2026-08-17T09:00:00Z",
            "alice",
            "one",
            "",
        )],
    );
    // One attribute written twice: the reader cannot pick, and neither can a
    // re-render.
    let path = proj
        .join("anthill-todo/open/WI-20260817-AAAAA-one.anthill.md");
    let doubled = fs::read_to_string(&path)
        .unwrap()
        .replace(
            "- created: 2026-08-17T09:00:00Z\n",
            "- created: 2026-08-17T09:00:00Z\n- created: 2026-08-17T09:00:00Z\n",
        );
    fs::write(&path, doubled).unwrap();

    let blocked = run_in(&proj, &["list"]);
    assert!(!blocked.status.success(), "it blocks");
    let err = String::from_utf8_lossy(&blocked.stderr);
    assert!(err.contains("written twice"), "{err}");
    assert!(
        err.contains("needs a hand"),
        "and says so instead of naming a verb: {err}"
    );
    assert!(
        !err.contains("fsck --fix"),
        "which is NOT the verb, because it skips this fault: {err}"
    );
}

/// `--renumber` under the shared-file backend refuses, exactly as `--fix` does: there
/// are no two item FILES there for a collision to be between.
#[test]
fn renumber_under_the_shared_file_backend_refuses() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let out = run_in(&proj, &["fsck", "--renumber"]);
    assert!(!out.status.success(), "{out:?}");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("IndexedFileStore"), "{err}");
}

/// `fsck --help` names the new verb. It is in the bundle's registry so `--help` finds
/// it, and a repair nobody can discover is a repair nobody runs.
#[test]
fn the_usage_text_names_renumber() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (proj, _, _) = two_colliding(&tmp);
    let out = ok(&proj, &["fsck", "--help"]);
    assert!(out.contains("--renumber"), "{out}");
}
