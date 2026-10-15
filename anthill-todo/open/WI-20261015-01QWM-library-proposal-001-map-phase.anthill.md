## Attributes

- id: WI-20261015-01QWM-library-proposal-001-map-phase
- created: 2026-10-15T13:50:25Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T13:50:25Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261015-H6323-library-proposal-001-map

- tags: library-001-map

## Description

Library proposal 001-map, phase 3: today's Map becomes PersistentMap, its put becomes with and its remove without — one pass over every user, with no deprecated alias (docs/proposals/library/001-map.md §Migration of existing Map users, option 1, recommended there).

WHERE (counted 2026-10-15): stdlib/anthill/prelude/map.anthill and the stdlib files that name Map (sort, finite_collection, eq, set, sortedset, stream, reflect, realization/cpp_std); examples/classic-mini/map-colouring; about 40 test files under rustland (tests/include and the crates' tests); the Rust builtin dispatch and the type predicates that name anthill.prelude.Map (eval/builtins.rs, eval/value.rs, eval/eval.rs, kb/simp_rewrite.rs, kb/load.rs, kb/mod.rs, kb/execute.rs, typing/display.rs, typing/type_preds.rs, typing/type_ctor.rs); the code generators' realization mappings; scaland's loader and its tests.

EXPECTED: no `Map` sort left in the prelude, every user renamed in one change; the simp rules and laws restated over with / without; the suites green on the renamed tree, scaland testFull included.

