## Attributes

- id: WI-20261023-CX743-proposal-069-stage-3-operation
- created: 2026-10-23T05:45:56Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T05:45:56Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261023-GBH5F-proposal-069-stage-2-operation

- tags: proposal-069

## Description

PROPOSAL 069 STAGE 3 — OPERATION VALUE-PARAMETER DEFAULTS (§1.1, §3). `operation clamp(x: Int64, low: Int64 = 0, high: Int64 = 100) -> Int64`: a call leaving a parameter out takes its default, positional arguments fill the next unfilled slot, named ones fill by name, and a defaulted parameter need not form a suffix (`connect(host: String = "localhost", port: Int64)`, `connect(port: 5432)`). A default may name earlier parameters, the operation's and enclosing sort's type parameters, and visible constants, constructors and operations; a later parameter, `result` or a body-local is refused. The call is elaborated to full arity before evaluation — the evaluator, host ABI and generated code see the declared arity; each selected default is evaluated once, left to right, in the callee's frame, and its effects are the operation's and must fit its declared row. IN A RULE-BODY GOAL the result column is named `result:` (§1.1): positional arity + 1 keeps the functional view with every parameter written; a shorter goal is a call (a Bool operation succeeds on true; any other needs `result: ?r`); `result:` works at any arity; a short non-Bool goal without it is a load error naming `result:`. A spec operation owns its defaults; a provider's member does not redeclare them (refused), and a call through the spec elaborates from the spec. A function value obtained by eta-expansion is full-arity — no optionality in arrows. Reflect, persistence and both code generators keep the default. Also the `= none()` form of stage 2's `identity` row. ACCEPTANCE driven by value, each with a control that fails when default insertion is backed out: the clamp rows; a dependent default `range(first, last = first, step = 1)` evaluated once; an effectful default fitting / not fitting its operation's row; a missing required parameter declared after a defaulted one still refused naming it; `clamp(12, result: ?r)` binds 12, `clamp(12, 0, 100, ?r)` as today, `clamp(12, ?r)` refused naming `result:`; a Bool short goal; spec-owned defaults and refused redeclaration; a function value still needs full arity. Acceptance: rustland/scripts/test.sh, scaland sbt testFull, npx tree-sitter test.

