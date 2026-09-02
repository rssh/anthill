## Attributes

- id: WI-20260902-65QKB-a-constraint-body-type-checks
- created: 2026-09-02T17:33:25Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T17:33:25Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A CONSTRAINT BODY TYPE-CHECKS NOTHING: op-arg and eq-operand checking do not run there at all.

MEASURED, three bodies, each written twice — once as `constraint k :- <body>` and once as the byte-identical `rule r(1) :- <body>` — in one file (`namespace zc.inner` declares `rule rel(1) :- base(1)` and `operation dbl(x: Int64) -> Int64 = x`):

| body | constraint | rule |
|---|---|---|
| `zc.inner.dbl(true) = 1` | **0 errors** | 1: `dbl.x (op-arg): expected Int64, got Bool` |
| `zc.inner.dbl(zc.inner.rel) = 1` | **0 errors** | 1: `dbl.x (op-arg): expected Int64, got Relation[...]` |
| `zc.inner.rel = 7` | **0 errors** | 1: `eq.b (op-arg): expected Relation[...], got Int64` |

THE FIRST ROW IS THE CONTROL AND IT IS THE POINT. It contains no dotted name anywhere — a plain `Bool` passed to an `Int64` parameter — and it still loads with zero errors in a constraint. So this is NOT a citation defect and not a dotted-name defect: op-arg type checking simply does not run on constraint bodies. The one-segment spelling is equally unchecked, so the hole predates WI-20260902-4NEKZ and WI-20260902-40KSW.

WHY IT MATTERS MORE HERE THAN ELSEWHERE. A constraint is an integrity guard — the construct whose whole job is to refuse bad states. An unchecked guard body is the worst place in the language for a silent type error: a constraint whose body cannot be satisfied because it is ill-typed does not refuse anything and reports nothing, which reads as 'the constraint holds'.

AND IT INVALIDATES A SCOPING ARGUMENT. WI-20260902-4NEKZ's population census is a TWO-position matrix — operation body against rule body — over six name kinds, and that matrix is what assigned five name kinds to WI-20260902-40KSW and one to 4NEKZ. A constraint body is a THIRD position taking the same chain, and it was never looked at. Any conclusion of the form 'the two positions agree at every row' is drawn from a matrix missing a third of the positions.

SCOPE. Find why the typer's op-arg/eq-operand checking is not reached for a constraint body (a constraint is loaded as a rule with an integrity-guard flag, so the likely cause is a gate keyed on the rule-head reading that a constraint has no head for), and either run the same checking there or state at the site, with a measurement, why a constraint body is deliberately unchecked. Then re-take 4NEKZ's six-name-kind matrix as a THREE-position one and record which rows move.

Found by /code-review on WI-20260902-4NEKZ; the reproduction above was run in this repo on 2026-09-02.

