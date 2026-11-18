## Attributes

- id: WI-20261118-GWVNZ-the-discrimination-tree-s-skip
- created: 2026-11-18T04:09:38Z

- status: Open
- status_agent: user
- status_at: 2026-11-18T04:09:38Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE DISCRIMINATION TREE'S SKIP RECURSES ONCE PER SYMBOL OF A HEAD'S KEY PATH. SubstTree::skip_subtree_then_continue (kb/discrim.rs) calls itself for each child of a node it skips, so its native depth is the length of the longest flattened key path below the skipped node, each frame large at opt-level 0 (twelve arguments and a SmallSubst clone). MEASURED (WI-20261117-8J8NG, 2026-11-18): a guarded law whose guard calls rule nz[A](?b: A) :- EuclideanDomain[T = A], Additive[T = A], neq(?b, zero) — whose neq reads an inferred PartialEq that nothing routes — beside operation risky(a: Int64, b: Int64) -> Int64 effects { Boom :- neq((a * b) / b, a) } = a and c(x) = risky(x, 2), overflows a 2 MiB test thread at opt-level 0 while the guard is proved: in one load since 8J8NG routes a law's goals, and in two loads (the law and nz in an earlier sealed load) on main before it. 103 of the top 120 frames of the overflow are skip_subtree_then_continue; with a 1 GiB stack the load finishes, the guard undecided. TO DO: find which query skips so long a path (the unrouted find_dictionary read is the suspect), and make the skip iterative (an explicit stack of node/substitution pairs) or bounded. ACCEPTANCE: the fixture loads on a 2 MiB thread at opt-level 0 with the verdict it has with a large stack; a row for it; full workspace green via rustland/scripts/test.sh.

