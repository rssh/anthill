## Attributes

- id: WI-20261103-BANCC-a-key-written-in-an-operation
- created: 2026-11-03T05:08:32Z

- status: Open
- status_agent: user
- status_at: 2026-11-03T05:08:32Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A KEY WRITTEN IN AN OPERATION BODY OFF A BINDER OF THE BODY IS NOT JUDGED: `operation k(x: Leaf) -> Bool =` / `let y = x` / `let z: Option[T = Set[T = y.E]] = none` / `true` is refused `KeyEqNotJudged` ("its receiver `y` is no parameter of `k`"), and so is a `match` arm's `case some(x) -> …` writing `Set[T = x.E]` over `o: Option[T = Leaf[E = Int64]]`, whose key is lawful (measured 2026-11-03, WI-20261102-7AB56's /code-review). MECHANISM: the use-site Eq check runs after the load over recorded sites (`ParameterizedSite`), which carry the operation they are written in and nothing of the body's scope, and `read_projection_key` reads a receiver off the operation's declared parameters only; the body typer reads the same annotation through its environment (`read_denoted_projections`, `Receivers::Own(Some(env))`, a `let` alias included). WHAT: judge a key written in an operation body where the body typer reads its annotation, or record at the site what the check needs to read the binder. ACCEPTANCE: the `let` alias over an open `E` loads and over `Leaf[E = Float]` is refused naming `Float`; the `match` binder over `Leaf[E = Int64]` loads and over `Leaf[E = Float]` is refused; a `let` that shadows a parameter is read as the binder, not the parameter; full workspace green via rustland/scripts/test.sh.

