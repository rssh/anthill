## Attributes

- id: WI-20260929-12NKG-a-value-in-type-or-type
- created: 2026-09-29T20:16:59Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T20:16:59Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A VALUE-IN-TYPE OR TYPE ARGUMENT INSIDE AN ARROW IS COMPARED BY THE ARROW'S HEAD, SO A REQUIREMENT AT ANOTHER CODOMAIN COVERS THE CALL AND ITS PROVIDER RUNS. `sort Apply { sort F = ?; operation run(f: F) -> Int64 }`, `CA provides Apply[F = (Int64) -> Buf[T = Int64, N = 3]]` (answers 30), `CB provides Apply[F = (Int64) -> Buf[T = Int64, N = 4]]` (answers 40), `sort User { requires Apply[F = (Int64) -> Buf[T = Int64, N = 3]]; operation via(f: (Int64) -> Buf[T = Int64, N = 4]) -> Int64 = Apply.run(f) }`, called `User.via(lambda (x: Int64) -> buf(v: x))`: runs CA (30) on an `N = 4` callback; without the `requires` the same call runs CB (40). The typed twin (requirement at `N = String`, call at `N = Bool`) also runs 30. MEASURED before and after WI-20260929-WBHTM. MECHANISM: the defer-match's coarse cover `entry_matches_subst` → `dispatch_values_match`, and the σ verdict `sigma_pair_precise` (dep_projection.rs ~675: `_ => dispatch_values_match(kb, a, b) || dispatch_values_match(kb, b, a)`), decide a compound that is not a parameterized application — an arrow, a tuple, a row — by its head once `types_lesseq` fails; `dispatch_values_match`'s doc records that coarse head as deliberate (WI-20260923-N3W68 #7, with a census of what relies on it), while direct dispatch tells the two arrows apart (without the requirement the call reaches CB), so the cover needs the structural answer for such compounds. FOUND by WI-20260929-WBHTM's /code-review. ACCEPTANCE: the program runs CB (40) — the requirement at `N = 3` does not cover a call at `N = 4` — in both spellings; full workspace green via rustland/scripts/test.sh.

