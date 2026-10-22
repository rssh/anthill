## Attributes

- id: WI-20261022-JBHQC-wi-6wvjb-s-later-load-row
- created: 2026-10-22T16:48:23Z

- status: Open
- status_agent: user
- status_at: 2026-10-22T16:48:23Z

- acceptance: cargo-test, scaland-sbt-test

## Description

WI-6WVJB'S LATER-LOAD ROW FAILS UNDER THE FRESH-LOAD RECIPE — decide: a regression to fix, or a row to pin. Found 2026-10-22 running WI-20261022-7EXEY's controls. `ANTHILL_TEST_OPT=2 ANTHILL_TEST_FRESH_LOAD=1 scripts/test.sh -p anthill-core` fails ONE row, `wi_6wvjb_one_arity_per_name_test::a_clause_against_an_earlier_loads_clauses_is_refused`; the default and the two-step recipes pass it. MEASURED on origin/main 31fef79b (WI-20261013-WF14Z delivered) WITHOUT 7EXEY's change: the same failure, so it predates 7EXEY. The fixture is `namespace ar9 { import anthill.reflect.feed.reaches; fact reaches(1) }`, and the row expects exactly one `LoadError::ClausesOfDifferentArity` naming `anthill.reflect.feed.reaches` at arities 2 and 1. Under the fresh recipe (one `load_all` over the stdlib and the fixture) it gets instead `Located { inner: UnresolvedImport { path: "anthill.reflect.feed.reaches" } }`. The row's own doc says the stdlib's clauses are those 'which every recipe but the fresh one loads first and seals', yet the row is not pinned to a recipe (`wi_rah0z_one_recipe_test`'s PINNED list does not name the file). TWO READINGS, TO DECIDE WITH THE USER: (1) A REGRESSION — in ONE load an import of a stdlib predicate from a program file should resolve (scan pass 4 defers predicate imports for exactly this), so `UnresolvedImport` is a loader defect, and once it resolves the row's refusal should hold in one load too (a fact of arity 1 against the predicate's arity-2 clauses is the same refusal whatever the load count); find which commit made the import unresolved under one call, bisecting the fresh recipe over this row. (2) THE ROW BELONGS TO A RECIPE — its subject is a LATER load against an earlier load's clauses, which one call does not have; pin it (`recipe_load` / a named `LoadRecipe`, with its PINNED entry and reason) and leave the one-call reading to a row of its own. The two are not exclusive: if (1) is a defect, fix it AND say at the row which recipe it measures. ACCEPTANCE (cargo-test, driven): the row passes under all three recipes, or is pinned with its reason; under (1) a row that drives the one-call import of a stdlib predicate from a program file, with its back-out named.

