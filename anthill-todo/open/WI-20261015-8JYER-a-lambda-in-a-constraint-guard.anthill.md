## Attributes

- id: WI-20261015-8JYER-a-lambda-in-a-constraint-guard
- created: 2026-10-15T20:50:54Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T20:50:54Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

A LAMBDA IN A CONSTRAINT GUARD KEEPS THE PARSER'S PATTERN MARKER, so every higher-order call in a guard fails and the constraint is refused as undecidable.

MEASURED 2026-10-15 on cc3d1a7d, and the same before WI-20260908-9WVT7 (found by its review):
  operation plus1(n: Int64) -> Int64 = n + 1
  operation applyThunk(f: () -> Int64) -> Int64 = f()
  operation applyF(f: (Int64) -> Int64, x: Int64) -> Int64 = f(x)
  fact item(n: 3)
  constraint h_thunk: no ?n: item(n: ?n) -: applyThunk(lambda () -> plus1(?n), 0)
  constraint h_unary: no ?n: item(n: ?n) -: applyF(lambda (y) -> y + 1, ?n, 0)
Both hold, and the load is refused: "integrity constraint 'h_thunk' is undecidable … closure: expected 1 args, got 0" and "'h_unary' … raised match_failed(occurrence: lambda_expr(pattern_var(y), add(y, 1)), scrutinee: 3)". The same call in a rule body answers: `rule r(?r) :- item(n: ?n), applyThunk(lambda () -> plus1(?n), ?r)` gives 4. Since WI-20260908-9WVT7 a guard holding `Error.reify(lambda () -> mayFail(?n), err(?))` is refused the same way, where it used to load and hold vacuously.

MECHANISM (read, at the review): a guard body is built as a TERM, and its lambda's parameter is still the parser's marker (`pattern_tuple` / `pattern_var`). `node_occurrence::param_occurrence` maps only `anthill.reflect.Pattern.*`, so the marker falls to its `_ =>` arm as an Expr-kind parameter, and the closure built from it takes one argument (a `pattern_tuple` of none) or matches nothing (`pattern_var(y)`). A rule body's lambdas are converted at load (`load_pattern_var` and its siblings).

THE CHANGE: a guard's lambdas converted as a rule body's are, at load, by the converter that owns the markers — not `param_occurrence` taught the marker spellings, which are converter-only.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh): both constraints load, and their violated twins are reported as violations; a guard holding a rule-body `Error.reify` with a lambda loads and holds.

