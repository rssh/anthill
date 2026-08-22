## Attributes

- id: WI-20260822-AK2AJ-a-body-less-rule-whose-head
- created: 2026-08-22T06:45:52Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T06:45:52Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BODY-LESS RULE WHOSE HEAD CARRIES A USER FUNCTOR NAMED `typed_var` IS FALSELY REFUSED,
citing a typed column the source does not contain.

MEASURED (/code-review, on 061's tree): `rule p(typed_var(1))` with no body is refused
with "A typed column `?x: T` has exactly one enforcer, a rewrite's typed-pattern bound
(WI-903)…". Under 061 that head would otherwise DECLARE `p`, so this is a false REFUSAL,
not only a misleading sentence.

THE CAUSE IS A BARE NAME TEST. `is_typed_column` (kb/load.rs) asks
`parse_sym.local_name(*functor) == "typed_var"` with no provenance pairing — WI-948's
"a name, not a verdict" trap. `head_carries_typed_column`'s own doc records that the trap
was seen and that the head node is deliberately not asked for exactly this reason; the
split narrowed the trap from the head to the ARGUMENTS rather than removing it, and
`is_typed_column` recurses into nested arguments too.

THE REPAIR AND ITS HAZARD, both already established so they are not re-derived:
`parse/convert.rs`'s `typed_var_arg` arm builds the marker (`self.intern("typed_var")`)
and does NOT `mark_minted` the node it allocates. Minting it and pairing the name with
`is_minted` is the fix — but `is_minted` has TEN readers in `kb/load.rs` (arrow-functor
arms, connective heads, the equation-subject gate at `is_minted(subject)`, the
declaration reading's `is_minted(*tid)`), and `mark_minted` has seven producers, so
adding one is a CENSUSED change. Census per READER, not per method — the answer to "was
this written as a call" is not the same question each of those ten is asking.

ACCEPTANCE: `rule p(typed_var(1))` with no body LOADS and DECLARES `p` (drive it — ask
the KB for `p`'s clauses and its declaration, not that the load returned Ok), while a
genuine `rule p(?x: Int64) <=> …` typed column keeps its WI-903 enforcement and a
body-less rule carrying one is still refused with the same message. Say at each site
which rows fail on a back-out, and name any reader whose verdict the new mint moves.
cargo-test green via rustland/scripts/test.sh.

