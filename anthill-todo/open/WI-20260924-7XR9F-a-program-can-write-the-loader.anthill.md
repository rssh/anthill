## Attributes

- id: WI-20260924-7XR9F-a-program-can-write-the-loader
- created: 2026-09-24T04:47:54Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T04:47:54Z

- acceptance: cargo-test

- tags: typing

## Description

A PROGRAM CAN WRITE THE LOADER'S REFLECT ROWS — facts and rules under `anthill.reflect`'s record relations load clean, and the reflect readers then report them as the program's own structure or refuse to answer.

MEASURED (2026-09-24, under WI-20260923-9R5HN): (1) `fact DescriptionInfo(target: Color, content: "forged", index: 7)` in a user namespace LOADS, and `KB.descriptions(kb(), some("Color"))` returns the forged row beside the real ones — a rule-body `<=>` over it answers 1. (2) `rule DescriptionInfo(target: ?t, content: "forged", index: 0) :- MemberInfo(name: ?t, kind: ?, parent: ?)` LOADS; the extent seam then refuses to read `DescriptionInfo` as facts, so every `KB.descriptions` call fails: the interpreter reports `EvalError::KbReadFailed` (a rule-body operand suspends with a warning — before 9R5HN the reader PANICKED the process), and the host bridge's `KbBridge::descriptions` still panics, its generated trait method having no error channel. The same holds for `SortInfo`, `OperationInfo`, `MemberInfo`, `FieldInfo` and the other rows the loader emits. The guardians work measured the forging half (a loaded candidate can hand-write any reflect row) and routed around it — its gate reads the layer delta through operations rather than facts (WI-5XBBQ) — so nothing refuses it.

USER DIRECTION (2026-09-24): user-added reflect rules should be REJECTED, and the rejection must NOT DENY REFACTORING — i.e. it is decided by PROVENANCE, not by spelling (the WI-1009 precedent): the loader's own emission stays legal, and so must a sanctioned future move of that emission into anthill-side rules (a reflect relation later DERIVED by stdlib rules instead of emitted by Rust). A blanket 'no clause may head a reflect functor' check would forbid exactly that refactoring.

TO DECIDE AT PICKUP: what marks a sanctioned producer (the relation's declaring namespace / the stdlib load, a declaration-level attribute on the relation, or the loader's emission path alone) and which relations are loader-owned (all of `anthill.reflect`'s record entities, or a declared set). Whether a scoped layer (`KB.loaded`) refuses a candidate's forged rows with `LoadFailed` — the gate then sees a load failure — and what that changes for the guardians pipeline.

ACCEPTANCE: a user-written fact AND a user-written bodied rule headed by a loader-owned reflect relation are load errors naming the relation and the rule; the loader's own emission still loads (the full closure loads clean); a sanctioned producer (whatever the pickup decides) is driven and loads; the two MEASURED rows above become load errors; the guardians suite passes with its forgery scenarios re-measured; cargo-test green via scripts/test.sh.

