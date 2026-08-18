```anthill
fact WorkItem(id: "WI-20260818-VDXAM-anthill-todo-backend-fsck", created: "2026-08-18T10:23:40Z", acceptance: [ToolPasses(tool: "cargo-test"), ToolPasses(tool: "scaland-sbt-test")], depends_on: some(value: ["WI-1121"]), status: Open)

fact Tag(workitem: "WI-20260818-VDXAM-anthill-todo-backend-fsck", name: "wi437")
```

## description

anthill-todo backend: `fsck --renumber` — the REPAIR half of design §6.6, whose detection shipped with WI-1121. Two unsynced writers can mint ids whose `<time>-<hash>` identity prefixes agree; `LayoutFault::IdCollision` now names that and BLOCKS, which is the half only the tracker can do (their slugs differ, so their filenames differ, so git merges the two files cleanly and nothing at the VCS or filesystem level can notice). What is NOT built is the repair, and it is deliberately its own ticket because it changes an IDENTITY rather than a location — a different blast radius from `--fix`, which only moves a file to match its fact.

WORK. (1) The verb: `fsck --renumber`, separate from `--fix` for the reason above. `--renumber <id>` overrides which side loses, for when one has already escaped into commit messages. (2) THE LOSER IS CHOSEN BY A DETERMINISTIC TOTAL ORDER, and this is the load-bearing requirement: both checkouts must reach the same answer without talking, or the repair turns one collision into a second, worse divergence. Later `created` loses; ties break on author, then on the full description. Re-minting is deterministic too (§6.5's attempt counter), so two checkouts resolving independently produce BYTE-IDENTICAL trees and git merges the two fixes with no conflict, because both sides made the same change. (3) What it rewrites: the loser's filename, its `id:` field, its satellites' `workitem:` fields (same file, so §5.1's relocation carries them), and every `depends_on` entry in the tree. (4) What it REFUSES to rewrite: prose. A `WI-…` in feedback text or a commit message may legitimately mean the winner, so those are REPORTED with locations — the same honest limit §6.4 states for provisional ids, now on a rare path instead of every offline add.

WHY IT CAN WAIT. The exposure is not a day's items but the handful created independently before a merge, and the measured re-hash rate is ~0 (78 active days, mean 9.9 items/day, busiest 35). Reached, the state is loud and blocking rather than silent, so nothing is lost while the repair does not exist — the user is told, and can renumber by hand. That is the whole reason detection shipped without it.

DRIVE THE CAPABILITY: two fixture trees holding items whose identity prefixes agree and whose descriptions differ; renumber; assert the loser's file, `id:`, satellites and every inbound `depends_on` moved together, that prose mentions are reported and NOT rewritten, and — the test that matters — that running the repair independently in two checkouts produces byte-identical trees. CONTROL: the deterministic-order test fails if the loser is chosen by anything a second checkout could disagree about (file order, timestamps read at repair time).

