## Attributes

- id: WI-20261001-KDMQS-a-const-in-fact-data-is-not
- created: 2026-10-01T05:07:20Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-01T10:28:11Z

- acceptance: cargo-test

## Description

A CONST IN FACT DATA IS NOT FOLDED TO ITS VALUE, so a persisted non-finite Float does not round-trip. WI-20260907-VM9Q7 made write_literal print the IEEE specials by the const names spec §2.4 gives them (Float.infinity / Float.negativeInfinity / Float.nan) -- they have no literal, Rust's own 'inf' reloads SILENTLY as an identifier, and the old 'inf.0' was a syntax error. The printer now names the right value; the LOADER reads the name as structure. MEASURED (2026-10-01): 'fact f(v: Float.infinity)' loads clean and 'f(v: ?x)' answers '?x = field_access(Float, infinity)'; 'rule j(?x) :- f(v: ?x), ?r <=> 1.0 / 0.0, ?x = ?r' answers NO solutions. So FileStore / ItemPerFileStore persist 1.0/0.0 as text that reloads as a different term, with nothing said. Related, measured the same day and NOT this ticket's to decide: 'fact g(v: inf)' also loads clean into a Float field, as an identifier -- a data slot admits an undefined name by design (wi1034 an_undefined_name_in_a_data_slot_is_not_a_goal), so a mistyped Float value is not refused either. ACCEPTANCE: drive the round trip, not the load -- persist (print_fact) a fact holding 1.0/0.0, -1.0/0.0 and 0.0/0.0, reload, and the join against the computed value answers one row each; say at the test's site which NaN equality holds (IEEE NaN != NaN, OrderedFloat NaN == NaN) and why. CONTROL: a finite Float field (3.0) round-trips before and after. REFERENCE: persistence/print.rs write_literal (the NOT YET RELOAD-FAITHFUL note), stdlib prelude/float.anthill 'const infinity: Float', WI-889 const_map.

## Changes

### 2026-10-01T10:27:53Z — feedback — user

DELIVERED in 7ca64491. Scope widened with the user (2026-10-01): a const folds to its value in EVERY clause data slot (fact/rule heads, rule/constraint body goal args, query patterns) at conversion time, from a load-time value table (literal body, alias, language-rust const_map); a computed const in a data slot is a located load error. Acceptance driven by wi_kdmqs_const_data_slot_test::persisted_ieee_specials_reload_as_the_float_they_were (match join one row each; IEEE = answers 0 for NaN by design, <=> and the match answer 1 because OrderedFloat makes every NaN one term) and the_store_retracts_a_persisted_ieee_special. Closes NDG34's value-slot rows; NDG34 keeps goal position.

