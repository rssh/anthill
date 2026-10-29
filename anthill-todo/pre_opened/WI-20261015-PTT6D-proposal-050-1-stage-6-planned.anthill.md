## Attributes

- id: WI-20261015-PTT6D-proposal-050-1-stage-6-planned
- created: 2026-10-15T13:48:25Z

- status: PreOpened
- status_agent: user
- status_at: 2026-10-15T13:48:31Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261015-169VS-proposal-050-1-stage-4-the, WI-20261029-627CM-a-body-is-held-to-the-guarded

- tags: proposal-050.1, typing

## Description

Proposal 050.1, stage 6 (planned, §8 C2): conditions at joins, for computing conditional rows — region membership carries the branch condition that made it.

PROGRAM (docs/proposals/050.1-memory-alias-and-maybe-connected.md §8 C): touch(p: Cell[V = Int64], b: Bool) -> Unit effects { Modify[p] :- eq(b, true) } = let y = if b then p else Cell.new(0), then Cell.set(y, 1). From stage 1 on, the write is charged Modify[p] unconditionally, so this declaration is refused, and the author declares Modify[p] — which a caller passing false then pays for a write it does not get.

EXPECTED: y lies in p's region under eq(b, true) and in a fresh one otherwise; the write charges Modify[p] :- eq(b, true), discharged by 048 at a caller passing a literal; a fact over p survives the write under not eq(b, true). Taken up when a body is first checked against a conditional Modify row — today only body-less operations in four test files declare one (wi067, wi347, wi478, wi4gbqv), and the stdlib none.

