## Attributes

- id: WI-20261104-6HVXM-every-arrow-is-a-function-in
- created: 2026-11-04T06:52:49Z

- status: Open
- status_agent: user
- status_at: 2026-11-04T06:52:49Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261104-5CNY5-proposal-002-s-correction-into

- tags: proposal-002, typing

## Description

EVERY ARROW IS A `Function`, IN THE TYPER AND THE RUN TIME (proposal 002 §"Correction (2026-11-03)", decided with the user 2026-11-03 and 2026-11-04). Today an arrow carries a parameter count (WI-791) and a call of a function value must pass that many arguments (WI-792), so a one-tuple-parameter operation and a two-parameter one are different types, and `h((1, 2))` over `h: (Int64, Int64) -> Int64` is refused "expected 2 arguments". WHAT: drop the count from the arrow (the `arity` child, `agreed_arrow_arity`, the two relations it selects, `TypeExtractor.Arrow.arity`, the printer's one-tuple wrapping); check every application by the application match against `A`, positional arguments by position and named ones by label, one tuple being always the argument list, through a value and in a call of an operation by its name; a callable at a function type meets it by label when the two tuples carry the same labels, by a mapping of labels by position otherwise (a lambda's tuple is its pattern's, an operation's its parameters); a callable's own count is checked where it becomes a value (WI-801's rule); the run time makes the same match where a callable takes the tuple (`classify_application`, `spread_eta_args`, `gather_closure_arg`). Measure first which tests move, and read each against 002. ACCEPTANCE: 002's programs, measured on 89500f50, give 002's values: q3 `h("a", 1)` refused at load; q6 6; fa 1, 1, 12, 12; fd `take2(get_a)` 1, `take2(two)` 12; q8 6; fc2 7 and its `y: Bool` twin 7; fe2 7 and its `Function`-typed twin loads; fg1 6; fh1 1; fw `forward((a: 1, b: 2), add2)` 12 and `add2((a: 1, b: 2))` 12; `add2((1, 2))` 3; fr1 `r((1, 2))` refused at `t` and `r(t: (1, 2))` 112. Full workspace green via rustland/scripts/test.sh; scripts/families.sh run and moved verdicts committed with the change.

