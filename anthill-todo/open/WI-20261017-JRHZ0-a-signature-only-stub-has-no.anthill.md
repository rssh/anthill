## Attributes

- id: WI-20261017-JRHZ0-a-signature-only-stub-has-no
- created: 2026-10-17T09:39:52Z

- status: Open
- status_agent: user
- status_at: 2026-10-17T09:39:52Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A SIGNATURE-ONLY STUB HAS NO HONEST BODY, SO M8QWJ'S FIXTURES USE SELF-RECURSION, WHICH HANGS IF CALLED -- WI-20260909-M8QWJ refuses a namespace (or data-sort) operation that nothing defines, and ~127 typing-test stubs were given `= f(x)` bodies to keep their signatures. A call of one loops for ever: tail recursion is O(1) frames and tests run with no step cap (MEASURED: `stub(x) = stub(x)` called from `anthill run` ran 60 s until killed), where the stub used to die 'operation has no body' at once. PROPOSAL (needs the user's decision, spec + stdlib): a pure `operation todo() -> Nothing @[host_implemented]` (or another name) whose host function FAULTS when run -- like Rust's todo!() / Scala's ???; Nothing conforms to every type, so `= todo()` is a body for any signature and a call fails loudly. Then replace the self-recursive stubs. Settle: is a pure fault (outside every effect row) admissible -- it rides the same channel as match_failed / division_by_zero host faults -- and whether todo() should be refused in a program that is RUN or codegen'd.

