## Attributes

- id: WI-20261006-XQGEW-a-type-parameter-the-member
- created: 2026-10-06T07:37:10Z

- status: Open
- status_agent: claude
- status_at: 2026-10-06T07:37:10Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing, guardians

## Description

A TYPE PARAMETER THE MEMBER SUGAR MINTS IS PRINTED BY ITS BARE NAME, NOT AS THE MEMBER THE AUTHOR WROTE. `Triage.run(self: C, box: Mailbox, llm: Llm.C, …) effects {External, Llm.E, Error}` (examples/guardians/lib/spec.anthill): the budget the checker reports for it is `[External, ?E, Error]` (`guardians_test` asserts exactly that list), and a candidate that exceeds it is told "expected declared: [External, ?E, Error], got undeclared effect: Permission[T = Outbox]" (examples/guardians/README.md). `?E` is the operation type parameter §5.4's sugar mints for `Llm.E`; printed by its own name it does not say whose `E` it is. Before WI-20261005-KSSA4 the row was written `llm.E` and printed so. TWO SPECS WITH A MEMBER OF ONE NAME ARE NOT TOLD APART, MEASURED on the tree that delivers KSSA4: `sort Tagger { sort C = ?; effects E = ?; operation tag(self: C) -> Int64 effects {E} }`, `sort Other { sort C = ?; effects E = ?; operation oth(self: C) -> Int64 effects {E} }`, `operation both(x: Tagger.C, y: Other.C) -> Int64 effects {Tagger.E} = Tagger.tag(x) + Other.oth(y)` is refused "type mismatch in both.effects (op-effects): expected declared: [?E], got undeclared effect: ?_". The row the author wrote is `{Tagger.E}` and what is missing from it is `Other.E`; neither name is in the message, and the missing one is not even printed as a parameter. EXPECTED: a parameter minted for a member prints as that member — `Llm.E`, `Tagger.E`, `Other.E` — in type and effect-row diagnostics and in what reflection reports of a declared row (the guardians budget reads it through `spec_budget`). ACCEPTANCE: the guardians budget is `[External, Llm.E, Error]`, with `guardians_test`, examples/guardians/README.md and examples/guardians/docs/design/measured.md following; the `both` program is refused naming `Tagger.E` as declared and `Other.E` as undeclared; a parameter the author wrote in a bracket (`total[P, El, R]`) prints as before; full workspace green via rustland/scripts/test.sh. REFERENCE: kernel-language §5.4 (a bare spec member in a signature is a type parameter, spelled shorter); WI-20261005-KSSA4.

