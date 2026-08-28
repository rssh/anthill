## Attributes

- id: WI-20260828-2TMB5-typer-a-bare-operation-name
- created: 2026-08-28T15:22:28Z

- status: Open
- status_agent: user
- status_at: 2026-08-28T15:22:28Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

typer: a BARE OPERATION NAME supplied to a NON-CALLABLE constructor field loads CLEAN instead of being refused. MEASURED: `sort Plain { entity plain(v: Int64) }` with `operation probe() -> Plain = plain(inc)` (where `inc(x: Int64) -> Int64`) produces NO load error. An operation name is not an Int64; the eta arrow `(Int64) -> Int64 @ {}` is not the declared field type by any relation. PRE-EXISTING and independent of WI-20260828-8Q0Q5: measured identically with 8Q0Q5's hint in place and with its gate neutralized, so that change neither caused nor repaired it — which is why 8Q0Q5's test file deliberately does NOT pin today's acceptance (a row asserting it would enshrine laxity and go red on the repair). WHERE TO LOOK: the constructor field-value validation loop in typing.rs (`validate_field_arg` / the `field_types` loop in check_constructor_iter) is GROUNDNESS-GATED — WI-1059's note says a polymorphic field stays unchecked and the return-conformance path settles it. Check whether a bare-name argument reaches that check at all, and what type it is carrying when it does: before 8Q0Q5 it was typed with NO expected type, so `check_bare_ref` may have taken the zero-arg-call reading rather than the eta reading, and a zero-arg call of `inc` would report an arity error rather than a type mismatch — establish which of the two it is before choosing the site. ACCEPTANCE: the program above is a loud type error naming the field's declared type and what was supplied; the four rows of wi_8q0q5_arrow_field_eta_row_test stay green.

