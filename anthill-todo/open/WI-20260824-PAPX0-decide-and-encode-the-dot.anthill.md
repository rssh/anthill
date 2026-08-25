## Attributes

- id: WI-20260824-PAPX0-decide-and-encode-the-dot
- created: 2026-08-24T05:05:04Z

- status: Open
- status_agent: user
- status_at: 2026-08-24T05:05:04Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260824-WAHB6-classify-a-nominal-type-once

- tags: proposal-055

## Description

DECIDE AND ENCODE THE DOT-RECEIVER SPLIT: SORT COMPANION VERSUS `Type`-VALUE MEMBER (proposal 055 umbrella A, step 4).

docs/design/055-implementation.md §4. A type-shaped receiver participates in two different mechanisms and they must not be separated by whichever lookup happens to run first:

  Map[K = String].empty()   -- sort companion / static lookup
  Cell[Int64].name          -- potentially a member of the `Type` VALUE

DELIVERABLE: preserve the distinction in the resolved receiver / projection node rather than re-deriving it downstream -- design §4 sketches `ResolvedReceiver::{Value, TypeValue, SortCompanion}`; the exact owner may differ, the invariant may not. Existing companion syntax and lookup remain authoritative. Where a surface can name BOTH a companion member and a `Type` member and no existing rule orders them, refuse the ambiguity naming BOTH routes (design §8) -- never a lookup-order fallback, and never a retry of a failed lookup as the other kind.

CODEBASE SITE: the `DotApply` work-frame in `typing.rs` and the `lowered_receiver` channel on `NodeKind::Expr` (`node_occurrence.rs`, WI-762) -- that channel already exists so a consumer that must SPLICE the receiver reads the lowered form instead of re-deriving it, which is the same discipline this ticket needs for the receiver's KIND. Check whether it is the right carrier before adding a second one; a receiver kind and a lowered receiver are two questions, so if it is reused the reason must be written at the site.

WHY ITS OWN TICKET: this is a DECISION, not the mechanics of steps 1--2. Settled inside the occurrence matrix it would get no control of its own, and an ambiguity refusal that nothing drives is indistinguishable from an ambiguity that never arises.

CONTROL: (1) a companion call that resolves today still resolves and reaches the same member; (2) a `Type`-member read on a type value is DRIVEN -- evaluate it and assert the value, not that it loads; (3) a surface that names both is refused with a diagnostic naming both routes, and the test asserts the distinguishing tokens of both, not merely that some diagnostic mentioning the sort was raised. State which rows fail on back-out and which pass either way.

ACCEPTANCE: full Rust workspace via rustland/scripts/test.sh.

