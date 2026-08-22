## Attributes

- id: WI-20260822-F0HHB-what-should-mean-in-a-rule
- created: 2026-08-22T08:54:04Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T08:54:04Z

- acceptance: cargo-test, scaland-sbt-test

## Description

WHAT SHOULD `=` MEAN IN A RULE BODY? — DEFERRED BY THE USER (2026-08-22): "interesting
but distinct question, are we want process `=` in rules. leave for later." Filed so the
measurements taken while delivering WI-20260822-J38JE are not re-derived.

`=` IS `PartialEq.eq` (§6.6's operator table), a semantic equality TEST that NEVER BINDS
(§8.3); `<=>` is `unify`, which does. In a rule body that makes `?r = <expr>` with `?r`
free a SUSPENSION, not an answer — and a suspension is easy to read as success, because
it is a solution in the result list.

MEASURED (rustland, current tree), with `fact ft(true)`, `fact ff(false)`:
  rule paren(?r) :- ft(?a), ff(?b), ?r = (?a & ?b)          total=1  definite=0
  rule meant(?r) :- ft(?a), ff(?b), ?r = Bool.and(?a, ?b)   total=1  definite=0
  rule uni(?r)   :- ft(?a), ff(?b), ?r <=> (?a & ?b)        total=1  definite=1
  rule eqlit(1)  :- ft(?a), ?a = true                       total=1  definite=1
  rule eqlitf(1) :- ff(?b), ?b = true                       total=0  definite=0
  pz.uni(false)                                             total=0  definite=0

TWO THINGS THE LAST ROW SHOWS, and the second is the sharper one. `unify` binds, so `uni`
is definite — but it is STRUCTURAL and never dispatches (proposal 049), so `?r` binds to
the TERM `and(true, false)` and NOT to the value `false`: asking `uni(false)` answers
nothing. That is §5.3's own warning about `unify` binding an unreduced call term, reached
here through the surface `<=>`. So neither spelling gives an author the obvious thing —
"compute this expression and name the result" — `=` suspends and `<=>` binds the syntax.

WHAT THIS TICKET MUST DECIDE:
 1. WHETHER `=` IN A RULE BODY EVALUATES ITS OPERANDS. §5.3 now reads a Bool-valued
    expression in GOAL position as a condition (WI-20260822-J38JE); an operand is a
    different position and this is the question for it. WI-1057 is the standing evidence
    AGAINST a blanket widening: making a body-less spec op's un-decided call count as
    "unreduced" broke 5 `wi616_semantic_eq_test` cases, turning definite FAILURES into
    residual successes, because `anthill.prelude.Set`'s `insert`/`empty` are body-less
    spec ops that are SYMBOLIC ALGEBRA and must keep comparing structurally. Any answer
    here has to say how it does not re-break that.
 2. WHETHER THERE IS A BINDING SPELLING THAT REDUCES. Today `<=>` binds the unreduced
    term. If "compute and name" is to be writable at all, decide whether `<=>` reduces a
    reducible operand first, or whether that is a third operator / the arity+1
    functional-relation view's job (WI-938 — which routes to `unify` for exactly this
    reason, and which does NOT yet work for a host-backed op: WI-20260822-ZJZS7).
 3. WHETHER A SUSPENSION SHOULD BE VISIBLE. `?r = <expr>` answering `total=1,
    definite=0` is indistinguishable from success to any caller counting solutions —
    including tests. WI-737 makes an ungrounded residual surface as a FLOUNDER; decide
    whether a rule body that can only ever residualize on this shape should say so at
    load, the way its neighbours in §5.3 now do.

ACCEPTANCE: drive every row of the table above and assert DEFINITE solution counts, not
`.len()` — the distinction is the whole subject and a `.len()` assertion measures nothing
here. CONTROLS THAT MUST STAY GREEN: `wi616_semantic_eq_test` in full (WI-1057's five
cases are the ones a widening breaks); `?a = true` on a GROUND operand still decides in
both polarities; and `<=>`'s structural, never-dispatching contract (proposal 049 /
WI-615). Say at each site which rows fail on a back-out.
cargo-test green via rustland/scripts/test.sh.

