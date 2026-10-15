## Attributes

- id: WI-20261015-HCQVS-an-operation-whose-row-guards
- created: 2026-10-15T17:32:01Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T17:32:01Z

- acceptance: cargo-test, scaland-sbt-test

- tags: effects

## Description

AN OPERATION WHOSE ROW GUARDS A ROW VARIABLE (`effects {Rho :- eq(b, 0)}`) IS REFUSED WHEN CALLED DIRECTLY, while the same call inside a lambda loads, so two spellings of one call disagree.

MEASURED (2026-10-15; the direct call the same on ee3696eb and after the WI-20260908-9WVT7 guarded-raise fix):
  operation guardedRow[Rho](f: () -> Int64 @ {Rho}, b: Int64) -> Int64 effects {Rho :- eq(b, 0)} = f()
  operation direct[R](h: () -> Int64 @ {R}, b: Int64) -> Int64 effects {R} = guardedRow(h, b)
`direct` is refused: "expected declared: [?R], got undeclared effect: ?R". Controls: the unguarded `{Rho}` twin loads; the guard refuted by a literal (`guardedRow(h, 1)`) loads; the call inside a lambda passed on (`runIt(lambda () -> guardedRow(h, b))`) loads since the 9WVT7 fix, which reads a function value's guarded atom as its label. Kernel-language §5.5 keeps the effect of a guard that is not refuted, and the grammar admits a row parameter as a guarded element, so the refusal is wrong.

MECHANISM, NOT TRACED TO THE END. A call that keeps a guarded atom pushes the callee's atom as declared (`push_effect_with_guard_discharge`, typing/carrier.rs), so its label is the callee's row variable; the operation boundary reads it through `explode_incurred_effect_row`, under an empty substitution. Resolving the kept atom through the call's σ (`walk_type_deep_value`) was tried and changed nothing (reverted). `decompose_effect_row_raw`'s guarded arm pushes the label as a PRESENT label even when it is a row variable (the WI-441 bug class), which is a likely second half.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh): `direct` loads; the same body under an operation declaring no effects is refused naming the row; rows for the direct call, the lambda-wrapped call and the literal-refuted call.

