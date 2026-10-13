## Attributes

- id: WI-20261013-WF14Z-068-c1b-a-rule-variable-is
- created: 2026-10-13T08:03:12Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:03:12Z

- acceptance: cargo-test

- depends_on: WI-20261013-GGXCX-068-c1a-design-the-clause

- tags: proposal-068, typing

## Description

068 C1b — A RULE VARIABLE IS TYPED ACROSS ITS CLAUSE: by the goals that take it, both sides of `<=>`, a constructor's result and the head's written bound, tied to the enclosing sort's parameters. Part 2 of WI-20260926-7D48J, implementing C1a's decisions 1 and 2. ROWS, each measured on the ticket that found it: WI-20260925-0RRQP's `rule order(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)` inside `sort Box[T] requires O: WeakOrd[T]` — `?x` is at `Box`'s `T` and the inferred condition routes to `O`; a head typed `?a: Int64` reaches the call's element (7D48J note 2026-10-08, row 3); a dot on a rule variable whose type the clause determines is evaluated — over `sort Cnt { entity cnt(n: Int64); operation bump(c: Cnt) -> Int64 = … }`, `?c <=> cnt(n: 4), ?x <=> ?c.bump()` answers 5 as `Cnt.bump(?c)` does, and so does `rule inner(?c: Cnt, ?x) :- ?x <=> ?c.bump()` called with `cnt(n: 4)`; `?c.bump() = 5`, `p(?c.bump())` and the goal `?c.isPos()` answer as their written-call twins (note 2026-10-11, A3FY2); a field of a typed head parameter is a receiver — over `entity P(t: Int64)`, `rule r0(?p: P, ?x) :- ?x <=> (?p.t).abs()` and the sigil-free `rule r0(p: P, ?x) :- ?x <=> (p.t).abs()` answer 3 for `P(-3)` (note 2026-10-12, RXT6S). ACCEPTANCE (cargo-test via rustland/scripts/test.sh; driven): each row answers as stated, each back-out named at its site. CONTROLS: an operation body's typing unchanged; classic-mini unchanged.

