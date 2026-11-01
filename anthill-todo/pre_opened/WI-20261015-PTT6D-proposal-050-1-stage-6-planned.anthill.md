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

## Changes

### 2026-11-01T10:08:20Z — feedback — claude

PREMISE CORRECTED (2026-11-01, measured). "From stage 1 on, the write is charged Modify[p] unconditionally, so this declaration is refused" did not hold when written: a declared guarded element admitted its label wherever the body incurred it (WI-818), so touch loaded. Since WI-20261029-627CM a body is held to its own guarded row at each call (kernel-language §5.5), and touch is refused as the premise says: touch.effects, "Modify[T = p] only where eq(b, true) holds ... the call of set incurs Modify[T = p] where nothing shows eq(b, true)" — the join charges p for every b. Row: wi_627cm_guarded_row_test::a_write_through_a_bound_name_is_held_as_the_parameters (ptt6d). Also: wi4gbqv was not body-less — its touch / swap had bodies that broke their own guarded rows; their fixtures were rewritten under 627CM.

