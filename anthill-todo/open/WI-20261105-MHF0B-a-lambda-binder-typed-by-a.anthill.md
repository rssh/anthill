## Attributes

- id: WI-20261105-MHF0B-a-lambda-binder-typed-by-a
- created: 2026-11-05T09:48:59Z

- status: Open
- status_agent: user
- status_at: 2026-11-05T09:48:59Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

a lambda binder typed by a dispatch in its body only through the callee's own type variable never reaches the lambda's arrow, so a use at another type loads and stops at run time. MEASURED 2026-11-05 on bd5d1bd9 with WI-20260904-34J8Z applied (debug CLI), each in an operation declared -> Int64: let g = lambda x -> x * 10 then g("a") loads and stops "type mismatch: expected Int64, got String and Int64"; let g = lambda (a, b) -> a * 10 + b then g("a", 1) the same (g("a", true) is refused at b only: + b pins b, a * 10 does not pin a); let g = lambda ((a, b), c) -> a * 100 then g(("x", true), 3) the same at a nested binder. And let g = lambda ((a, b), c) -> (s: a + b, t: a) then let x: String = g((1, 2), 3).s loads: the sum is typed at the callee's T, not at a. WHY, read from the code and not yet driven: the dispatch resolves Multiplicative at Int64 inside its own call sigma, where ?a := ?T_mul and ?T_mul := Int64; report_call_solutions (kb/typing/forms.rs) reports a binding only when its value is walk-local, so ?a := ?T_mul is dropped, the walk's solved never learns ?a = Int64, the LambdaBody frame builds the arrow at ?a, and a use binds ?a to String in its own sigma. The gate's population 2 ("the range leaks where the domain does not") is the case; a value whose chain ends at a ground type in the call sigma is the candidate. Found while delivering WI-20260904-34J8Z (user, 2026-11-05: file it). ACCEPTANCE: the four programs refused at load, at the use; let g = lambda x -> x * 10 then g(2) answers 20; full workspace green via rustland/scripts/test.sh, families run.

