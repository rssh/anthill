## Attributes

- id: WI-20260824-JM6ZW-retire-the-expectation
- created: 2026-08-24T05:05:30Z

- status: Open
- status_agent: user
- status_at: 2026-08-24T05:05:30Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260824-Q0093-every-operation-expression, WI-20260824-PAPX0-decide-and-encode-the-dot

- tags: proposal-055

## Description

RETIRE THE EXPECTATION-DIRECTED CLASSIFIERS AND LAND UMBRELLA A'S DIAGNOSTICS (proposal 055 umbrella A, step 6 + §8).

Delete the expected-`Type` hint chain AS A CLASSIFIER. Expected `Type` survives only as an ordinary validation / inference input, per docs/design/055-implementation.md §10 step 6.

SITES (measured): `type_slot_arg_hint` (`typing.rs:9226`) and its gate `arg_names_sort` (`typing.rs:9252`); the `sort_app_hint` computed in `apply_arg_hints` (`typing.rs:9102`) and consumed at the Apply arm (`typing.rs:10512`); the `expects_reflect_type` call in `check_bare_ref`'s WI-206 sort arm (`typing.rs`, in the arm at ~6474); and the declared-type lookups that exist to FEED the hint (`typing.rs:10565`, `10769`, `10797`, `10817`). A lookup that also serves validation stays -- say at its site which of the two questions it is answering after this change, because that is the distinction the hint chain currently blurs.

DIAGNOSTICS (design §8) belonging to umbrella A: a wrong destination reads `expected String, got Type (Cell[Int64])` and names the DENOTED sort, never an unresolved nested name; a forgotten-parens constructor name in a `Type`-accepting position must name the denoted sort in the error or trace, so the implicit reading is visible -- proposal 055 §2 names this as the residual risk the uniform rule accepts and requires the diagnostic to cover it; the companion-versus-`Type`-member ambiguity names both routes, if WI-20260824-PAPX0 has not already landed it. NO fallback that retries a failed value resolution as a type, or the reverse: resolve the symbol once and classify loudly.

CONTROL -- THE SHARPEST IN THE UMBRELLA, and the reason this must not be folded into WAHB6. Two back-outs, stated separately: (1) restore the hints while keeping the record -- the classification tests still pass, which is what proves the hint is no longer load-bearing; if any row needs the hint back, the record did not reach that site and the finding belongs here, not in a later ticket; (2) remove the record while the hints are gone -- the WI-206 / WI-707 rows fail. A change that passes both ways measures nothing; name the rows for each direction at the test site.

ACCEPTANCE: WI-206 / WI-707 / WI-709 / WI-710 controls remain green; full Rust workspace via rustland/scripts/test.sh; run the /code-review skill before commit.

