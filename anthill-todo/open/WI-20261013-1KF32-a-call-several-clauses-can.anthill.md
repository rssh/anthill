## Attributes

- id: WI-20261013-1KF32-a-call-several-clauses-can
- created: 2026-10-13T06:18:40Z

- status: Open
- status_agent: user
- status_at: 2026-10-13T06:18:40Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A CALL SEVERAL CLAUSES CAN ANSWER IS REFUSED BY A `by z3` PROOF, AND WHAT IT MEANS IS THEIR DISJUNCTION — so a definition by cases and a table of facts cannot be called from a proved body at all. The refusal is WI-20261012-KF2SD's decision (2026-10-13, with the user: refused now, the disjunction a ticket of its own); this is that ticket. Measured 2026-10-13 on main at 70fffe8f with KF2SD's change on it, `anthill prove --no-cache`, z3 4.16.0.

THE MOTIVATING EXAMPLE — a definition by cases, which is how a piecewise relation is written in a language of Horn clauses:
  rule commanded_speed(?range, ?v) :- lt(?range, 5.0), ?v = 0.0          -- too close: hold
  rule commanded_speed(?range, ?v) :- gte(?range, 5.0), ?v = 2.0         -- else: close in
  rule speed_is_bounded: lte(?v, 2.0) :- commanded_speed(?range, ?v)     proof speed_is_bounded by z3 end
  rule never_moves:      lte(?v, 0.0) :- commanded_speed(?range, ?v)     proof never_moves by z3 end
`speed_is_bounded` is true of both cases and `never_moves` is false at range = 6. BEFORE KF2SD both were `✓ proved (z3: unsat)` — the call read as its first clause, `v = 0`. SINCE, both are `error: … the call of `….commanded_speed/2` can be answered by 2 clauses of the predicate (0 fact(s), 2 with a body), and a proof reads a call by ONE`. WRITTEN BY HAND, the disjunction
  (assert (or (and (< range 5.0) (= v 0.0)) (and (>= range 5.0) (= v 2.0))))
gives `unsat` for the first and `sat`, range = 5.0, v = 2.0, for the second: the two verdicts the rules have.

AND A TABLE, a claim of every row of it:
  fact speed_max(Leader, 8.0)      fact speed_max(Follower, 10.0)
  rule every_drone_is_bounded: lte(?v, 10.0) :- speed_max(?who, ?v)      true of both rows
  rule every_drone_is_slow:    lte(?v, 8.0)  :- speed_max(?who, ?v)      false of the Follower's
Both proved before (the first fact), both are refused since. A claim of ONE row is read today — `speed_max(Leader, ?v)`, the ground argument selects the fact — so what is lost is the claim of all of them.

WHAT IS THERE (`anthill-smt-gen`, `Emitter::answering_clause`): a call is read by the one clause of its arity whose head no argument of the call rules out — bound to a fact's slots, or inlined, or the one-argument form — and refused where there is more than one. Each reading writes into ONE frame: a variable is one SMT term (`bindings`), an entity-valued variable one occurrence whose fields are read statically (`entity_bindings`), and an assertion made while a body is read is the document's (`assertions`).

WHAT THE DISJUNCTION NEEDS, each to decide:
  (1) A BRANCH'S ASSERTIONS ARE ITS OWN — conjoined inside its disjunct, not pushed to the document — and so are the sorts and free variables it found.
  (2) A VARIABLE THE CALL BINDS HAS A TERM PER BRANCH: a constant the document declares, `(= v t_i)` in each disjunct, where one clause binds it by substitution today.
  (3) AN ENTITY-VALUED VARIABLE HAS NO TERM AT ALL (`real_pose_at(?k, Leader, ?l)`, then `?l.position.x`): per-field constants for it, or the DOCUMENT split by the choice of clause — proved when every one is `unsat` — which changes what a proof's record, cache key and witness are of.
  (4) A RECURSIVE CLAUSE is not unfolded: lf1's `real_pose_at` is a base clause and a step that calls itself, and the reading of the step is induction's. Refused as today, or the uninterpreted relation.
  (5) CALLS IN A BRANCH that several clauses answer in turn: the product, and where it stops.
  (6) A NULLARY CONSTRUCTOR CHOOSES THE BRANCH and has no term (WI-20261013-PR8SP): `?who = Follower, speed_max(?who, ?v)` is the table's second row only if `?who` is something.
BESIDE IT, a reading that needs none of this: a call that a lemma the proof CITES is about could be STATED and not read — the relation is declared for it (WI-20261012-CDHSQ) — where today it is read as well, so `rule cited: gte(?x, ?y + 1.0) :- related(?x, ?y)`, `proof cited using lemma by z3`, with `related` of two clauses, is refused though the lemma alone discharges it (measured; it proved before KF2SD, by the lemma and the first clause).

THE CONTROL: `speed_is_bounded` proves and `never_moves` is a COUNTEREXAMPLE with range ≥ 5; `every_drone_is_bounded` proves and `every_drone_is_slow` is a COUNTEREXAMPLE; KF2SD's two — `gte(?a, ?b) :- related(?a, ?b)` over `related` by `gte` and by `lte`, `gte(?d, 0.0) :- start(?d)` over `start(5.0)` and `start(-1.0)` — are COUNTEREXAMPLES, each a refusal when backed out; a call one clause answers has the document it had, to the byte; lf1's verdicts are as they are.

DONE WHEN: the control rows hold and fail when backed out; KF2SD's refusal rows are turned to the verdicts above or kept for what is still refused, each said; `docs/smtlib-forward-mapping.md` says what a call of several clauses is; the documents that moved are listed; the gate is green.

## Changes

### 2026-10-13T08:33:35Z — feedback — user

FROM WI-20261012-KF2SD's review (2026-10-13; docs/measurements/test-infrastructure/several-clauses-2026-10-13.txt §6, §7). THE REFUSAL STANDS IN ONE MORE PLACE THAT IS THIS TICKET'S: an ENTITY PREMISE over an entity of several facts (`Limit(cap: ?c)` over two `Limit` facts — "the entity … has several facts") is the table of this ticket in an entity's spelling, and its fields are constants of the document, one a field's name. NOT this ticket's: the rule being PROVED where its name is several clauses, which is a conjunction and needs each clause read in a frame of its own (KF2SD §7 (ii)). FOR THE DESIGN: every clause under the functor counts, a labeled lemma too (`rule safe_weaken: safe(?x, ?n) :- safe(?x, ?m), gte(?m, ?n)` beside the definition of `safe` makes every reading of `safe` "several"), and such a lemma calls its own predicate more often than not — (4) above, so a predicate with a lemma stated of it stays refused under the disjunction unless a labeled rule is read as a lemma and not as a clause (KF2SD §7 (iii), put to the user). And selection and binding are two walks of a head against a call (`admits`/`agree`; `bind_head_arg`, `bind_fact_call`) that disagree where a clause is admitted and then cannot be read: a branch's own bindings want them one (KF2SD §6 (13)).

