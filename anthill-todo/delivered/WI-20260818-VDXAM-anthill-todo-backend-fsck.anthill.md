## Attributes

- id: WI-20260818-VDXAM-anthill-todo-backend-fsck
- created: 2026-08-18T10:23:40Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-21T14:17:53Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-1121

- tags: wi437

## Description

anthill-todo backend: `fsck --renumber` — the REPAIR half of design §6.6, whose detection shipped with WI-1121. Two unsynced writers can mint ids whose `<time>-<hash>` identity prefixes agree; `LayoutFault::IdCollision` now names that and BLOCKS, which is the half only the tracker can do (their slugs differ, so their filenames differ, so git merges the two files cleanly and nothing at the VCS or filesystem level can notice). What is NOT built is the repair, and it is deliberately its own ticket because it changes an IDENTITY rather than a location — a different blast radius from `--fix`, which only moves a file to match its fact.

WORK. (1) The verb: `fsck --renumber`, separate from `--fix` for the reason above. `--renumber <id>` overrides which side loses, for when one has already escaped into commit messages. (2) THE LOSER IS CHOSEN BY A DETERMINISTIC TOTAL ORDER, and this is the load-bearing requirement: both checkouts must reach the same answer without talking, or the repair turns one collision into a second, worse divergence. Later `created` loses; ties break on author, then on the full description. Re-minting is deterministic too (§6.5's attempt counter), so two checkouts resolving independently produce BYTE-IDENTICAL trees and git merges the two fixes with no conflict, because both sides made the same change. (3) What it rewrites: the loser's filename, its `id:` field, its satellites' `workitem:` fields (same file, so §5.1's relocation carries them), and every `depends_on` entry in the tree. (4) What it REFUSES to rewrite: prose. A `WI-…` in feedback text or a commit message may legitimately mean the winner, so those are REPORTED with locations — the same honest limit §6.4 states for provisional ids, now on a rare path instead of every offline add.

WHY IT CAN WAIT. The exposure is not a day's items but the handful created independently before a merge, and the measured re-hash rate is ~0 (78 active days, mean 9.9 items/day, busiest 35). Reached, the state is loud and blocking rather than silent, so nothing is lost while the repair does not exist — the user is told, and can renumber by hand. That is the whole reason detection shipped without it.

DRIVE THE CAPABILITY: two fixture trees holding items whose identity prefixes agree and whose descriptions differ; renumber; assert the loser's file, `id:`, satellites and every inbound `depends_on` moved together, that prose mentions are reported and NOT rewritten, and — the test that matters — that running the repair independently in two checkouts produces byte-identical trees. CONTROL: the deterministic-order test fails if the loser is chosen by anything a second checkout could disagree about (file order, timestamps read at repair time).

## Changes

### 2026-08-21T14:18:28Z — feedback — user

DELIVERED. `fsck --renumber [<id>]` ships; §6.6's repair half is complete and §6.8 records what building it settled.

THE ORDER: `created`, then the agent the row records (§6.7: a work item records no FILER, so the status agent is the author it has), then the description, then the full id — the last key is what makes it total rather than usually-total, because a hand-written minted-shaped id satisfies none of the digest argument. The re-mint enters §6.5's attempt counter at 1 and calls `slug`/`digestBase32` through the interpreter rather than re-deriving them.

THREE STORE CHANGES MADE IT POSSIBLE, each a defect in its own right. (1) The flush paired a retract with its persist by the PRIMARY KEY, which is exactly what a renumber changes — so the move read as a delete plus a create and the satellites and prose did not travel. It pairs on the RULE the write replaces now. (2) `IdCollision` was recorded while seeding, so the repair could not un-push the fault it had just fixed; it is derived from the current index, which also deleted `by_identity` and closed a case-folding gap between the detector and the mint. (3) The flush dropped an updated row from its index, so the store silently stopped holding a row it was holding.

FOUND BY REVIEW, ALL FIXED AND TESTED: `--fix` refused while any collision stood, which deadlocked the two verbs against each other and made the combined form impossible (a collision makes no path repair ambiguous — the two ids name two different destinations); an absent `created` read back as "" and so sorted FIRST, handing the collision to the undated item; `--renumber` alone half-repaired over a misplaced file and then reported a stale fault; and a blocking `DocumentFault` was routed to `--fix`, which skips it by design.

TESTS: 19 in `wivdxam_fsck_renumber_test.rs` (including two checkouts repairing independently to byte-identical trees, and controls where the `created` order and the path order disagree) plus 5 in `wi1114_item_per_file_store_test.rs`. cargo-test 5422/0; scaland-sbt-test 531/0.

