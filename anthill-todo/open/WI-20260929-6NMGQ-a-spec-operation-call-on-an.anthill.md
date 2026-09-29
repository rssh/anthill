## Attributes

- id: WI-20260929-6NMGQ-a-spec-operation-call-on-an
- created: 2026-09-29T20:17:10Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T20:17:10Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SPEC-OPERATION CALL ON AN UNANNOTATED LAMBDA PARAMETER DEFERS TO THE ENCLOSING `requires` BEFORE THE PARAMETER IS SOLVED, AND RUNS THAT REQUIREMENT'S PROVIDER ON A VALUE OF ANOTHER SORT. `sort User { requires Store[State = Other]; operation go() -> Int64 = let f = lambda x -> Store.peek(x)  f(buf(v: 7)) }`, providers `Carrier` at `Buf[T = Int64]` (answers `s.v + 30`) and `OtherImpl` at `Other` (answers 99), called `User.go()`: runs `OtherImpl.peek` on the `Buf` (99). The annotated lambda `lambda (x: Buf[T = Int64]) -> Store.peek(x)` runs Carrier (37). MEASURED before and after WI-20260929-WBHTM, and not about value-in-type (the `Buf` here holds no value). MECHANISM: when `Store.peek(x)` is typed, `x`'s type is still an unbound variable, so `State` is open and the OPEN-T defer trigger (`find_requires_slot` / `entry_matches_subst`, an unbound spec param is "no constraint") classifies the call `DeferToRequirement` onto `requires Store[State = Other]`; the application `f(buf(v: 7))` pins `x` later, after the classification is fixed. FIX: re-check a deferral whose element was open once the lambda's parameter is solved (the WI-20260904-50B2K binder discharge is the nearest owner of "a binder's uses solve it later"), or refuse the call when the enclosing requirement's element is concrete and the call's is still open. FOUND by WI-20260929-WBHTM's /code-review. ACCEPTANCE: the unannotated lambda runs Carrier (37) as the annotated one does, or is refused at load — never runs `OtherImpl`; full workspace green via rustland/scripts/test.sh.

