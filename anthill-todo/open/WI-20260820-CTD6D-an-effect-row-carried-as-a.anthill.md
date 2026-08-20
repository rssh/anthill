## Attributes

- id: WI-20260820-CTD6D-an-effect-row-carried-as-a
- created: 2026-08-20T18:22:55Z

- status: Open
- status_agent: user
- status_at: 2026-08-20T18:22:55Z

- acceptance: cargo-test, scaland-sbt-test

## Description

An effect row carried as a `Value::Entity` is not recognized as a row by either of the two sites that turn a walked row VALUE back into a row, so it is carried whole as a single opaque "label" instead of being flattened to its atoms. `wrap_bare_effect_expr_as_row` (kb/typing.rs, added by WI-329) matches `Value::Term` and `Value::Node` and returns `None` for everything else; `explode_incurred_effect_row` has had the identical hole since WI-441, where the same match is written inline. Both callers treat `None` as "not a row" and fall back to their non-row handling, so nothing is DROPPED -- the failure mode is the pre-WI-441 one: a row leaks as one opaque atom, which at an operation boundary renders as `undeclared effect: merge[left = present[...], ...]` (the shape WI-493's test asserts must not leak) and inside a lambda's arrow becomes the malformed `present(label = merge(...))` WI-329 fixed for the other carriers. HONESTY ABOUT THE EVIDENCE: this is a STATED gap, not a measured defect. No program was found that produces an Entity-carried effect row -- the rows reaching these sites in the current corpus are `Value::Term` (hash-consed) or `Value::Node` (occurrence-carried). It is filed because the repo principle is a loud error over a silent skip, and because the classification is by FUNCTOR HEAD (`value_is_bare_row_expr` reads `head(kb).functor_sym()`, which a `Value::Entity` answers), so an Entity-carried `merge(...)` is classified as a row and then silently declassified by the wrapper -- the same source shape producing two different incurred atoms depending purely on carrier. TWO ACCEPTABLE OUTCOMES, and the ticket is done when EITHER is reached with evidence: (a) the carrier is REACHABLE -- write the program that produces it, give the wrapper an Entity constructor (a `make_effects_rows_entity` sibling to `make_effects_rows_type` / `make_effects_rows_occ`), and drive the flatten with a test that fails when the constructor is removed; or (b) the carrier is UNREACHABLE BY CONSTRUCTION -- establish why (which producers can mint an effect-row Value, and that none of them mints an Entity), and replace the silent `None` with a loud error at both sites, so a future producer that does mint one is reported rather than silently mis-flattened. Do not close it by widening the match without deciding which of the two it is. ACCEPTANCE: whichever outcome, the reasoning lands at BOTH sites (they must not drift again -- WI-329 already extracted the shared helper for that reason); full cargo-test green.

