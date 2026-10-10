## Attributes

- id: WI-20261009-S723J-scaland-close-a-composite-s
- created: 2026-10-09T18:53:29Z

- status: Open
- status_agent: user
- status_at: 2026-10-09T18:53:29Z

- acceptance: scaland-sbt-test

- tags: scaland

## Description

SCALAND: CLOSE A COMPOSITE'S EQUALITY AT THE LOAD THAT DEFINES IT, AND LOAD THE STDLIB FIRST — the Scala port of two rules rustland has and scaland does not.

WHAT. (1) kernel-language.md §8.3 (WI-20261006-SZKV7): a load may change nothing about the equality of a composite an EARLIER load defined — who supplies its `eq`, which provisions of `PartialEq` / `Eq` / `NonEq` name it, under what conditions — and doing so is a load error (`EqualityOfEarlierSort` in rustland, decided by comparing each composite's equality signature recorded when a load ends with the one recomputed at the next). scaland has no such check: measured 2026-10-09 by grep, nothing under `scaland/src` names it or an equality signature. (2) The stdlib is its own load in the product (the rustland ticket filed the same day): a program is a later load than the standard library, so rule (1) applies to every program.

WHY A TICKET OF ITS OWN. The first is a pass that is not there — the signature, its recording at every exit of a load, the refusal and its message — not a call site to move. Check first whether scaland's loader can be called a second time on a KB at all, and what its equality derivation does then: rustland's two-step switch found two differences before any rule was written (docs/design/test-infrastructure.md §4 A3), and scaland has never been run that way.

CONTROL. The rows of `wi_szkv7_later_equality_test` are the shapes to port: a witness `eq` for a base composite in a later load is refused; the same file loaded with the base is not; a later load that leaves equality alone loads; a sort with no constructors is outside the rule.

DONE WHEN: scaland refuses what rustland refuses for those shapes, its entry point loads the stdlib before the program, and `sbt testFull` is green.

