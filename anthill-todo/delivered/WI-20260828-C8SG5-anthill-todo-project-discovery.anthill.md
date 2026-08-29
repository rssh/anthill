## Attributes

- id: WI-20260828-C8SG5-anthill-todo-project-discovery
- created: 2026-08-28T13:33:22Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-29T00:00:51Z

- acceptance: cargo-test

## Description

anthill-todo project discovery does not walk up the directory tree, and the item-per-file layout makes standing inside the tracker the normal case. From <proj>/anthill-todo/claimed/ — the directory a user is naturally in while editing a WI-....anthill.md — a bare `anthill-todo list` exits 1 with 'no anthill-todo project found in .../claimed', and the remedy it suggests (`anthill-todo init`) would nest a SECOND project inside the tracker. Before WI-1118 a project had no subdirectories, so cwd-inside-the-tracker was not a place anyone stood; now init scaffolds that shape for every new project. Walking up from cwd looking for PROJECT_MARKERS appears safe rather than a return of the WI-744 footgun — it is the marker test, not the search depth, that rejects rustland/anthill-todo/ (the crate) — but this touches a documented invariant with its own history (WI-744 tightened discovery, WI-748 fixed -d), so it wants its own ticket and its own tests rather than riding along. Found by code review of the init-scaffolds-item-per-file change.


### DELIVERED — the walk, and the split it exposed

`find_project_dir` now tries the cwd AND EVERY ANCESTOR, NEAREST FIRST, each at the two arms it always had: `<dir>/anthill-todo/` carries a marker, or `<dir>` carries one itself.

MEASURED, before and after, from this repo:
  * `anthill-todo/claimed/` (the ticket's case) — before: `error: no anthill-todo project found in …/claimed`, exit 1, advising an `init` that would have nested a second project. After: the repo's own listing.
  * `rustland/` (the WI-744 case) — before: the same exit-1 refusal. After: the tracker, reached one level ABOVE the CLI's own crate. The crate is not a candidate at any depth, because it carries neither marker; nothing about depth relaxes that test.

**THE WALK EXPOSED A SPLIT THAT WAS ALREADY THERE, and closing it is the larger half of this delivery.** `find_project_dir` proved a project by MARKER and returned the directory ABOVE it; a separate `scan_dir` then re-derived the scan root by NAME (`<dir>/anthill-todo`, if `is_dir()`). The two could disagree. REPRODUCED: a flat project at `<d>/workitems.anthill` beside a MARKER-LESS `<d>/anthill-todo/` (a crate, a scratch dir) resolved on the flat marker and then scanned the marker-less directory — `list` said "No work items found", exit 0, and `add` opened a SECOND store inside it, orphaning the rows discovery had just matched on. Pre-change one had to stand exactly on `<d>`; the walk made every descendant reach it. `find_project_dir` now returns the SCANNED DIRECTORY ITSELF and `scan_dir` is deleted, so the disagreement is unrepresentable. The explicit `-d` arm routes through the same two arms, so it cannot misroute either.

**THREE MORE DEFECTS THE WALK CREATED OR SHARPENED**, each found by /code-review and each reproduced before and after:
  * `Path::is_file()` collapses EACCES/EIO/ELOOP into `false` exactly like ENOENT. Under the walk that swallow stopped being harmless: "no marker here" means KEEP WALKING, so `chmod 000` on the project one is standing in silently handed `add` a DIFFERENT project higher up and wrote there. Marker probing is `fs::metadata` now, and anything but `NotFound` is a loud refusal naming the file.
  * The walk is UNBOUNDED and named nothing, so a mutating command could write into an unrelated ancestor tracker with `added: WI-…` as its only output. Every match ABOVE the cwd now prints the directory it chose. The level-0 path stays silent — WI-744 deleted a warning there because it annotated every normal invocation and distinguished nothing, which is not true of a project the cwd does not show.
  * `run_init` still permitted the nesting this ticket's own description cites: only the ADVICE was removed. It is not merely redundant — `collect_anthill_files` walks the tracker recursively, so a nested `project.anthill` becomes a SECOND `Project` fact in the OUTER project's KB and `add` at `<proj>` dies naming neither file. `init` now refuses when its target is INSIDE a tracker; the test is "inside a tracker", not "beneath a project", so `init` at `~/code/newthing` under a personal `~/anthill-todo/` still works.

A half-migrated project (both layouts present) now NAMES the flat file it is ignoring rather than dropping its rows in silence.

### Tests

`wic8sg5_discovery_walks_up_test` — 8 rows. CONTROL MEASURED by reverting `src/main.rs` and re-running: 7 fail, 1 passes either way.
  * Six fail on the BEHAVIOUR (exit 1, `no anthill-todo project found`), including the WRITE half — a `claim` from inside the item tree.
  * `no_project_anywhere_up_the_tree_is_a_loud_error` fails on its WORDING alone; its exit-code and "names what it could not find" halves hold either way and pin that widening the search neither succeeded by accident nor ran off the end of the tree.
  * `…_beside_a_flat_project_is_not_the_scan_root` fails at HEAD from the flat project's own directory, with no walking involved — it is the regression test for the marker/scan split, and what backs it out is re-splitting the two decisions.
  * `a_nested_project_wins_over_the_one_above_it` passes EITHER WAY by design: nearest-first is trivially satisfied by a search that never leaves the cwd. Its control is reversing the iteration, under which it is the only row here that fails — every other puts one project on the chain, so direction cannot be observed. It asserts the WRITE too: two projects on one chain, and `add` from the inner one must leave the outer tracker's count unchanged.

`assert_no_project_above` moved to `tests/common` and is called from both sites that need it — `cmd_version_test`'s `add --version` runs in a bare tempdir with no `-d`, and with `TMPDIR` redirected into a checkout it would FILE A REAL WORK ITEM before its exit-code assertion failed. `cmd_tests.rs` records that the test cwd (`rustland/anthill-todo`) now resolves to this repo's own tracker, so a future test spawning the binary with neither `-d` nor `current_dir` would read — and if mutating, WRITE — the real tracker during `cargo test`.

Suite: `scripts/test.sh -p anthill-todo` green — 12 + 257 passed, 0 failures. That is the complete blast radius: `find_project_dir` / `scan_root_at` / `is_project_dir` are private to `anthill-todo/src/main.rs`, and no crate depends on `anthill-todo`.

### NOT COVERED, stated rather than ticketed

THE `-d "$PWD"` PATH IS UNFIXED, and it is the one the skill documents. `skills/anthill-todo/SKILL.md` and the `SKILL_MD` literal both say "Always pass `-d` with the current working directory", and the explicit arm returns before the walk. From inside the tracker `-d "$PWD"` reports a lost `ExtentBinding` — advice that diagnoses the wrong thing; from `rustland/` it still resolves to the crate, WI-744's original footgun. The marker-based descent added here removes the misroute but not the arm's premise. Either drop `-d "$PWD"` from both skill copies now that bare invocation works, or decide the `-d` arm should refuse a directory locating no project at all — a user-facing policy change on a different arm, and the reason this is a sentence and not a silent edit.

A flat project high in the tree still makes `collect_anthill_files` walk its whole subtree (symlinks followed, no visited set). Pre-existing, in shared `fs_util`, and now reachable from any descendant rather than only from the project's own directory.

