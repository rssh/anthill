## Attributes

- id: WI-20261116-3D05F-a-forall-precondition-is-not
- created: 2026-11-16T10:13:01Z

- status: Open
- status_agent: claude
- status_at: 2026-11-16T10:13:01Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `forall` PRECONDITION IS NOT CHECKED AT THE CALL. PROGRAM: operation needy(l: List[T = Int64]) -> Int64 requires (forall ?x in l: gt(?x, 0)) = 1, operation bad() -> Int64 = needy([1, 0]), operation good() -> Int64 = needy([1, 2]). MEASURED on 7c63d768: loads clean, and bad() runs to 1. A precondition without the quantifier, requires gt(x, 0) at needy(0), is refused 'unsatisfied precondition'. Found in WI-20261105-CBRD2 part 5g. WANTED: needy([1, 0]) refused at load as an unsatisfied precondition, needy([1, 2]) proved, and a call at a list whose elements the caller cannot see left to the caller's own requires, as other preconditions are. ACCEPTANCE: rows for the three; full workspace green via rustland/scripts/test.sh.

