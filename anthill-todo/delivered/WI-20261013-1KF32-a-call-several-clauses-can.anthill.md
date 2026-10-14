## Attributes

- id: WI-20261013-1KF32-a-call-several-clauses-can
- created: 2026-10-13T06:18:40Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-14T09:09:05Z

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

### 2026-10-14T06:59:47Z — feedback — user

DECIDED (user, 2026-10-14), on the design put to them: (a) THE ENCODING is the document split by the choice of clause, kept ONE document — the whole body (the conclusion with it) is read once per combination of clause choices, a WORLD, and the document asserts the disjunction of the worlds; a proof that meets no choice point is the document it was, to the byte; the record, cache key and witness stay of one document. Checked by hand in z3 4.16.0: never_moves sat at range = 5.0, speed_is_bounded unsat. (b) (4) RECURSION IS REFUSED: a call of a predicate whose clause is being read is refused, the one-clause case too — which turns a stack overflow measured on 79a6703f (rule loop(?x) :- loop(?x), gte(?x, 0.0); gte(?x, 0.0) :- loop(?x): exit 134) into an error. (c) THE CAP is 64 worlds; above it the proof is refused. (d) A NUMBER IN A BODIED HEAD met by a free variable BINDS it, as a fact's slot does (mode(0, ?r), mode(1, ?r) called mode(?k, ?r)). TAKEN AS FOLLOWING, said with the design and not objected to: an entity premise over several facts is a world per fact its non-variable slots admit; upper-bound obligations keep the refusal; scaland keeps its refusal; a world in which a later call has no answering clause is refused, not dropped; the 'beside it' reading is not built separately; BR7P3 stays as it is inside a world.

### 2026-10-14T09:08:57Z — feedback — user

BUILT, REVIEWED AND MEASURED 2026-10-14 (docs/measurements/test-infrastructure/disjunction-2026-10-14.txt). WHAT IS BUILT (`anthill-smt-gen`): where several clauses can answer a call — or several facts an entity premise — `answering_clause` (`read_entity_row`) is a CHOICE POINT (`Emitter::choose`), and the body is read once for each combination of the choices its points take, a WORLD: the whole body and the conclusion in an emitter of its own, by replaying the deterministic walk with a longer prefix of choices (`read_worlds`), in the order of the choices, at most 64. The document (`render_worlds`, through the one renderer `render_check`) declares what the worlds declare, once — a free variable is one constant, sound because the worlds are disjuncts — and asserts `(or W1 … Wn)`, each world its hypotheses and its negated conclusion, a comment naming its choices; a function-like head's result is equated in each. One world: the document it was. THE TICKET'S SIX: (1) a world's assertions are its own; (2) a variable a clause binds is substituted in its world, as one clause always did; (3) an entity is an occurrence in its world, its fields read there; (4) a bodied clause read while a clause of its own predicate (name and arity) is being read is REFUSED; (5) calls in a world that several clauses answer are the product, to 64; (6) a fact's constructor slot binds the variable in its world and a later call is selected by it (`speed_max(?who, ?v), margin(?who, ?m)`: two worlds) — the equation `?who = Follower` binding nothing is still PR8SP's. BESIDE IT: a call a cited lemma is about is stated in each world as well as read, and `cited` proves through the worlds; nothing else built. THE CONTROL HOLDS: `speed_is_bounded` proved, `never_moves` COUNTEREXAMPLE with the range 5.0 in its model, `every_drone_is_bounded` proved, `every_drone_is_slow` COUNTEREXAMPLE, KF2SD's two COUNTEREXAMPLES; lf1 fourteen proved, its 16 documents byte for byte as on 79a6703f, and the suites' 277 of 291 — the 14 that moved are KF2SD's refusals of several, nine now documents, five refused for reasons of their own (recursive: `mixed.base`, `lemma.uses`; WI-687: `ctor.with_var`, `frames.claim0`, `frames.claim_a`). KF2SD's nine refusal rows say at their sites what they hold since. ALSO BUILT, decided with the user: a number in a bodied head met by a free variable binds it; and a one-clause recursive predicate, which overflowed the stack and aborted the CLI on 79a6703f, is refused. FROM /code-review (fourteen findings; twelve done, §6): every fact of an entity is a row, a variable field leaving the slot free, and the harvest refuses a field that is no number where it left 0.0 (on 79a6703f a lone `Lim(cap: ?any)` was 0.0 and, beside a number, no row: both proved a false claim); a value a world gives a variable already named or defined is equated, not substituted (`bind_variable`; `lte(?d, 10.0), start(?d)` was z3's "unknown constant" for one fact too); a variable written twice meets one value; the guard compares arity; a variable passed through an inlined rule is free for a head's number; an entity slot neither variable nor number is refused; one renderer; the builtin table resolved once. LEFT: the row of verdicts returns without z3 (the repository's convention, its documents under dry-run rows), and an entity's facts read twice a premise. 13 CLI rows and 4 of the emitter crate; 20 parts each backed out failing a row, the control passing either way and saying so; scaland keeps the refusal, one comment. Committed as de0fb6e3, merged with origin/main as 107a1a02; the gate of the merge 9786 passed, 0 failed; scaland 1 + 40 + 668 passed.

### 2026-10-14T09:09:02Z — feedback — user

FOUND, AND NOT OF THIS CHANGE (measurement file §7), each run on 79a6703f and as delivered. FILED with the user's word: WI-20261014-FHEEK — a variable an inlined rule binds, which its caller defined another variable by (`?e = ?d + 1.0, p(?d)`), is left undeclared, z3's "unknown constant" on both trees. NOT FILED: a free variable against a construction in a head (`gain(?o, ?r)` over `gain(some(?x), ?r)`) stays WI-687's refusal in that clause's world — binding it would carry the clause's own variables into the caller's frame (BR7P3); an entity of NO fact still reads its fields as 0.0, a reading of `false` that loses an `unsat` at most; whether scaland's one-argument reading has the recursion of §1 was not measured.

