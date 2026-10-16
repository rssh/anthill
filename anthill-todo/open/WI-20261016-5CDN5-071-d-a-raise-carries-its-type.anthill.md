## Attributes

- id: WI-20261016-5CDN5-071-d-a-raise-carries-its-type
- created: 2026-10-16T14:51:31Z

- status: Open
- status_agent: claude
- status_at: 2026-10-16T14:51:31Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261016-YM8HD-071-c-error-reify-requires

- tags: proposal-071

## Description

071 (d): A RAISE CARRIES ITS TYPE — `raise … requires TypeValue[T = T]`, AND THE BOUNDARY ADMITS BY FULL TYPE. Proposal 071 §1.3. Delivers WI-20260911-3MV2C.
THE CHANGE: `operation raise(error: T) -> Nothing effects Error[T] requires TypeValue[T = T]`; the raised error travels with that evidence, and the boundary calls `admits` with its `type_value()`. A monomorphic raise's evidence is static; a generic raiser states the clause (`raiseAt[P](p: P) requires TypeValue[T = P]`); a host raiser (`division_by_zero`, `match_failed`, `evaluation_failure`, …) supplies its payload sort's derived evidence. A raise at a tuple or arrow payload is refused at load (065 §2: no instance yet).
MEASURED (2026-10-16): `caughtS(n) -> Result[E = Boom[Reason = String], T = Int64] effects {Error[Boom[Reason = Int64]]} = Error.reify(lambda () -> both(n))`, inside an outer boundary, answers "inner" for `boom(5)` where "outer" is right — the runtime compares head sorts. Census: no `Error[(…)]` label outside tests; six in three test files (`wi_9wvt7_reify_rule_body_test`, `wi_9wvt7_error_reify_test`, `wi_n31xx_type_value_read_rule_test`), all fixtures of the tuple refusal, which move from the reify to the raise.
ACCEPTANCE (cargo-test via rustland/scripts/test.sh, scaland sbt testFull): 3MV2C's nested boundaries at `Box[V = Int64]` / `Box[V = String]` answer through the outer for a `Box[V = String]` raise and the inner for a `Box[V = Int64]` one, the two-distinct-sorts row passing either way; the "inner"/"outer" row above answers "outer"; `1 / 0` inside a reify at `DivisionByZero` still caught; a tuple raise refused at load naming the former.

