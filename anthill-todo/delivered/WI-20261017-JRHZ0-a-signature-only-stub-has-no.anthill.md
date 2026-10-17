## Attributes

- id: WI-20261017-JRHZ0-a-signature-only-stub-has-no
- created: 2026-10-17T09:39:52Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-17T11:28:32Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A SIGNATURE-ONLY STUB HAS NO HONEST BODY, SO M8QWJ'S FIXTURES USE SELF-RECURSION, WHICH HANGS IF CALLED -- WI-20260909-M8QWJ refuses a namespace (or data-sort) operation that nothing defines, and ~127 typing-test stubs were given `= f(x)` bodies to keep their signatures. A call of one loops for ever: tail recursion is O(1) frames and tests run with no step cap (MEASURED: `stub(x) = stub(x)` called from `anthill run` ran 60 s until killed), where the stub used to die 'operation has no body' at once. PROPOSAL (needs the user's decision, spec + stdlib): a pure `operation todo() -> Nothing @[host_implemented]` (or another name) whose host function FAULTS when run -- like Rust's todo!() / Scala's ???; Nothing conforms to every type, so `= todo()` is a body for any signature and a call fails loudly. Then replace the self-recursive stubs. Settle: is a pure fault (outside every effect row) admissible -- it rides the same channel as match_failed / division_by_zero host faults -- and whether todo() should be refused in a program that is RUN or codegen'd.

## Changes

### 2026-10-17T09:57:48Z — feedback — user

USER'S DECISIONS 2026-10-17: (1) the name is `anthill.prelude.todo() -> Nothing @[host_implemented]`, nullary. (2) Reaching it is its OWN EvalError (`NotImplemented`, naming the running operation), outside every effect row and catchable by nothing -- the `Int64` `Overflow` precedent, not the `Error` channel `match_failed` rides; at the SLD bridge its disposition is `Fault`. (3) A program using it loads clean with no warning and runs; only a call that reaches it fails. (4) Codegen (cpp17-stl, scala-gen) refuses a body that calls it, with a dedicated message naming the operation that holds the hole -- not the generic 'add an operation_map'. Then M8QWJ's 128 self-recursive stubs become `= todo()`.

### 2026-10-17T10:50:06Z — feedback — user

Decision (4) as built: the refusal is at every backend that LOWERS a body; that is cpp17-stl today. scala-gen (`anthill-scala-gen` Generator is an empty skeleton) and scaland's/rustland's Rust and Scala codegen emit abstract signatures only and read no body, so there is nothing for them to refuse; the Rust bundle runs the interpreter and faults at the call. Stated so in kernel-language.md §5.4.

