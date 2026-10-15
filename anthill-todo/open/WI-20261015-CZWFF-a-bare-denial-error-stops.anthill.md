## Attributes

- id: WI-20261015-CZWFF-a-bare-denial-error-stops
- created: 2026-10-15T17:32:18Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T17:32:18Z

- acceptance: cargo-test, scaland-sbt-test

- tags: effects

## Description

A BARE DENIAL `-Error` STOPS `Error[DivisionByZero]` ONLY WHEN THE ROW VARIABLE IS INFERRED: written explicitly, the instantiated row admits the label it denies.

MEASURED (2026-10-15):
  operation run5[Rho](f: () -> Int64 @ {Rho, -Error}) -> Int64 effects {Rho} = f()
  operation t(a: Int64, b: Int64) -> Int64 effects {Error[DivisionByZero]} = run5(lambda () -> a / b)
is refused ("run5.type_arg: expected a type for 'Rho', got unconstrained"): binding `Rho` to the division's label is refused by `row_violates_lacks`, which unifies (`label_violates_lacks`, typing/effects.rs). Following the refusal's own advice, `run5[Rho = {Error[DivisionByZero]}](lambda () -> a / b)` LOADS, and so does its unguarded twin on every build; so does a written callback row `@ {Error[DivisionByZero], -Error}`. The instantiated row is checked by `row_self_contradiction` → `label_violates_absence`, which compares by structural equality, and the callback validator's absent arm matches with `labels_match_aligned`; neither reads a bare `-Error` as covering `Error[DivisionByZero]`. Two checks of one constraint disagree, and the verdict turns on whether `Rho` is written.

TO DECIDE: what a bare lacks constraint denies for an ordinary label. For `Permission` the bare denial is the general one (proposal 064); for other labels `permission_entails`' doc leaves it open. `wi_9wvt7_guarded_callback_row_test` reads `-Error` as denying `Error[DivisionByZero]`.

RELATED: WI-20260909-V4RVX (the `-Permission` entailment leg over a bound parameter), the same readers.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh): the reading stated in kernel-language.md §5.5; the inferred and the written instantiation give one verdict; rows for both and for a written `{Error[X], -Error}` row.

