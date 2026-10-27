## Attributes

- id: WI-20261027-T31R0-write-the-guardians-checker-in
- created: 2026-10-27T20:07:14Z

- status: Open
- status_agent: claude
- status_at: 2026-10-27T20:07:14Z

- acceptance: cargo-test, scaland-sbt-test

- tags: guardians

## Description

WRITE THE GUARDIANS CHECKER IN ANTHILL. `LoadChecker.check` (examples/guardians/lib/harness.anthill) is host Rust, `guardians_check` in rustland/anthill-core/tests/guardians_test.rs. WI-20260908-9WVT7 was driven by it: the one arm that needed the host was the catch of `KB.loaded`'s raise (`Err(e) => load_failure_to_rejected(interp, e)`), and `Error.reify` does that now. Filed from 9WVT7's leftovers with the user, 2026-10-27.

WHY. WI-20260908-K5HVE's finding: `-Permission[Llm]` on `check` constrains nothing while the body is host-bound — the row bounds the declaration, and the body is outside its reach. Written in anthill, the denial binds the real checker.

TWO DECISIONS ABOUT THE EXAMPLE, before the body can be written. The host body does two more things anthill cannot today:
 (1) `source_text(args[1])` reads `Source`'s internal `text`, which only `guardians.Source`'s scope can read (the seal harness.anthill describes: "THE SEAL IS AGAINST ANTHILL, NOT AGAINST THE HOST").
 (2) `spec_budget` builds the budget strings from `all_operation_effects` with `type_display_name_value` (Rust), read from the base before the candidate's layer loads, so a candidate cannot restate its own budget. Anthill has no operation for either.

RELATION. K5HVE moves `check` to an address no sort occupies and collapses `Checker` and `LoadChecker`; whichever lands second writes the body at the other's address.

ACCEPTANCE: decisions (1) and (2) recorded; `check` written in anthill with no host binding; every guardians_test row green, the count stated before and after; a row where the body breaks `-Permission[Llm]` refused.

