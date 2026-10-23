## Attributes

- id: WI-20261023-FHT5Z-proposal-069-stage-4-entity
- created: 2026-10-23T05:46:06Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T05:46:06Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261023-CX743-proposal-069-stage-3-operation

- tags: proposal-069

## Description

PROPOSAL 069 STAGE 4 — ENTITY-CONSTRUCTOR FIELD DEFAULTS, construction positions only (§1.2, §3). `entity Endpoint(host: String = "localhost", port: Int64 = 80)`: `Endpoint()` and `Endpoint(port: 8080)` construct with the omitted fields defaulted; the stored shape is unchanged and the constructor receives full arity. A default may name earlier fields and the enclosing sort's parameters, and must be PURE — a default whose inferred row is non-empty is a load error at the default naming its effects. In a fact head, rule head, match case or other pattern an omitted field keeps its pattern meaning (unconstrained). IN A RULE BODY THE POSITION DECIDES: a goal, an argument of a rule goal at any depth, or a side of `<=>` is a pattern (no default); an argument of an operation call (proposal 068 evaluates it) is a construction and takes the defaults; a position nested inside a construction inherits it, one inside a pattern inherits that, and an operation call inside a pattern starts a value position again. Reflect, persistence and both code generators keep the default. This is what WI-188's derived copy operation needs alongside stage 3. ACCEPTANCE driven by value, each with a back-out control: the Endpoint construction rows; an Endpoint pattern omitting host matches a stored non-default host; rule-body r1/r2/r3 of §1.2 (goal and rule-goal argument match any host, an operation-call argument receives Endpoint("localhost", 80) as in an operation body); nested `describe(Wrap(Endpoint(port: 80)))` fills both; an effectful field default refused; a dependent field default. Acceptance: rustland/scripts/test.sh, scaland sbt testFull, npx tree-sitter test.

