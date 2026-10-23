## Attributes

- id: WI-20261023-GJVVW-import-ns-c-resolves-to-an
- created: 2026-10-23T17:13:09Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T17:13:09Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`import ns.{c}` resolves to an operation's PARAMETER named `c` rather than the relation `c` the namespace's facts define, so a goal `c(?x)` in the importing namespace answers nothing, silently. MEASURED 2026-10-23 (38a260a6): `namespace probe.imp  import anthill.prelude.{Int64}  operation useIt(c: Int64) -> Int64 = c  fact c(1)  end` and `namespace probe.imp2  import anthill.prelude.{Int64}  import probe.imp.{c}  rule r(?x) :- c(?x)  end`: `probe.imp2.r(?x)` answers no solutions; with the parameter renamed `d`, `?x = 1`. Seen first as `import probe.hand.{c}` printing the relation as `probe.hand.useVia.c`. A parameter is in its operation's scope only. ACCEPTANCE: `r(?x)` answers 1 with the parameter named `c`; a parameter is never reached by an import (selective, plain, or the qualified spelling `probe.imp.c`); in both implementations' name resolution.

