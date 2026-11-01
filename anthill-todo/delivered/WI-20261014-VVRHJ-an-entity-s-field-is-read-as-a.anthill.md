## Attributes

- id: WI-20261014-VVRHJ-an-entity-s-field-is-read-as-a
- created: 2026-10-14T12:34:32Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-01T11:24:44Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN ENTITY'S FIELD IS READ AS A CONSTANT NAMED BY THE FIELD'S SHORT NAME — so two entities with a field of one name are ONE constant, and a FALSE claim proves; and a cited lemma's lift names that constant where its consumer does not declare it. Found while delivering WI-20261014-FHEEK / WI-20261012-1P005 (docs/measurements/test-infrastructure/inlined-names-2026-10-14.txt §9); measured 2026-10-14 on d7a8ffcb and on 6f5262ce, `anthill prove --no-cache`, z3 5.1.0.

MEASURED, BOTH TREES:
  entity A(cap: Float)   fact A(cap: 5.0)
  entity B(cap: Float)   fact B(cap: 1.0)
  rule small: lte(?a, 2.0) :- A(cap: ?a), B(cap: ?b)      proof small by z3 end
`✓ small: proved` — false: ?a = 5. The document is `(define-fun cap () Real 1.0)` and `(assert (not (<= cap 2.0)))`: A's `cap` and B's are one constant, set to the last fact read. The same with `gte(?a, 3.0)`, true, is a COUNTEREXAMPLE.
  entity Lim(cap: Float)   fact Lim(cap: 5.0)
  rule lemma: gte(?a, 0.0) :- Lim(cap: ?c), gte(?c, 1.0), ?c = ?a + 1.0     proof lemma by trust(…) end
  rule plain: gte(?x, 0.0) :- lte(?x, 100.0), gte(?w, 1.0)                  proof plain using lemma by z3 end
`? plain: unknown (z3 said (error "… unknown constant cap"))`: the lift is `(forall ((var_1 Real)) (=> (and (>= cap 1.0) (= cap (+ var_1 1.0))) (>= var_1 0.0)))`, and `plain` reads no `Lim`, so nothing declares `cap`. A consumer that reads `Lim` itself declares it (`(define-fun cap () Real 5.0)`) and the lift then means it — by the name alone, so a consumer reading another entity's field `cap` would give the lemma that one. Loud as it stands; the first face is not.
(On d7a8ffcb the lemma's lift also dropped `?c = ?a + 1.0` — the field's constant overwritten by the equation — and `reads: gte(?x, -10.0) :- Lim(cap: ?d), ?x = ?d - 20.0`, false, PROVED using it: the lift said every real is >= 0. Fixed by 6f5262ce, which equates a variable defined twice.)

WHAT IS THERE (`anthill-smt-gen`): `process_body_goal`'s entity destructure binds a field's variable to `sanitize_smt_id(local_name_of(field))` — the field's short name — in `field_consts`, which `collect_facts_for_referenced_entities` sets from the entity's one fact and the document renders as `(define-fun <field> () Real <value>)`. Nothing of the name says whose field it is (the user's rule: no check by short name). A lift (`lift_one_clause`) carries its clauses and `Declarations` (sorts, functions, relations), not the field constants its clauses name. An entity of several facts is a world per fact in a proof's own body (1KF32) and refused in a lift.

RELATED: WI-20261013-PR8SP (a construction has no SMT term; a datatype for an entity with fields is "a ticket of its own").

TO DECIDE: the name of a field's constant (the entity's qualified name with the field, as a function does); and what a lift does with one — carry the constant and its value with its declarations, or read the premise's field as a quantified variable the entity's fact constrains, or refuse it.

THE CONTROL: `small` is a COUNTEREXAMPLE and its twin `gte(?a, 3.0)` proves; `plain` has a verdict; lf1's documents are as they are, or each that is not is listed with its verdict.

DONE WHEN: the control rows hold and fail when backed out; the documents that moved are listed; the gate is green.

## Changes

### 2026-10-14T12:37:40Z — feedback — user

MEASURED, the same mechanism from the variable side: a field named like a variable collides with it. entity E(var_0: Float), fact E(var_0: 5.0), rule f: gte(?x, 3.0) :- E(var_0: ?v), lte(?x, 1.0), lte(?v, 9.0). On d7a8ffcb ?v was bound to the constant var_0, which is also ?v's own name, and the verdict (COUNTEREXAMPLE) came out right by that coincidence; on 6f5262ce bind_variable sees ?v given its own name and binds nothing, and the document both define-funs and declares var_0: z3 'named expression already defined with this name var_0'. Loud. sanitize_smt_id also folds distinct names into one (a.b and a_b are both a_b).

### 2026-10-14T13:35:01Z — feedback — user

NAMING DECIDED (user, 2026-10-14): docs/smtlib-forward-mapping.md §7.6, Names in a Document. An entity's field read as a constant is named by the entity's qualified name with the field (test.ent.A.cap), written by smt_symbol as an operation's name is; sanitize_smt_id goes with it. What stays to decide here is what a lift does with such a constant (carry it and its value with its declarations, read the field as a quantified variable its fact constrains, or refuse it).

### 2026-11-01T11:23:18Z — feedback — claude

BUILT, REVIEWED AND MEASURED 2026-11-01 (docs/measurements/test-infrastructure/field-constants-2026-11-01.txt). DECIDED (user, 2026-11-01): a lift reads the fact's value in place of the premise's variable and names no constant (option (b); (a) was to carry the constant with the lift's declarations); an entity of no fact is refused where a premise reads its field. WHAT IS BUILT (`anthill-smt-gen`): a field's constant is the entity's qualified name with the field (`Emitter::field_constant`, written by `smt_symbol`, §7.6); the harvest reads each field a premise binds off the entity's one fact and refuses several, none, a field the fact does not give and one of no number — the 0.0 placeholder is gone; a lift reads an entity premise by its row (`read_entity_row`), a field that is a variable leaving the variable quantified (`fact Lone(cap: ?any)` lifts, where it was refused), several facts refused through the choice point; `sanitize_smt_id` is gone, the bare-name fallback of `translate_expr` is a refusal (nothing reaches it, measured); WITNESS_FORMAT_VERSION 5 → 6. scaland (no lift): the naming, the refusals of no fact / several facts / a field of no number, and its free-variable scan reads `ns.E.var_0` whole. THE CONTROL: `small` COUNTEREXAMPLE, its twin proved; `plain` COUNTEREXAMPLE; the `var_0` field a verdict; a z3-proved lemma about `Lim` cited by a proof reading `B(cap: …)` — PROVED a false claim on 0e696fe2 — COUNTEREXAMPLE. 5 CLI rows (`wi_vvrhj_field_constant_test`), all five failing on 0e696fe2's binary; each part backed out alone fails its rows (Rust 3 switches, scaland 5). DOCUMENTS: lf1 16 — 5 to the byte, 11 moved by the constants' names alone; emitter suite 63 — 47 / 13 by names / 1 new (`kf32.emit.lone`'s lift); CLI suite 269 — 208 / 52 by names / 6 otherwise (the two lifts that named a constant, their consumers, `prove_ranking_test`'s sub-queries) / 12 new; each listed in the measurement file §5. `prove_ranking_test`'s fixture had no `State` fact and proved because `lt(?u, 0)` is false at 0.0 — vacuously true, never checked of every state; it now has `fact State(upc: ?u, upc_next: ?n)` and proves for its own reason. /code-review: 11 findings, 10 done. FOUND, NOT OF THIS: scaland does not resolve a rule named `none`.

### 2026-11-01T11:24:43Z — feedback — claude

Committed as 66da0a5d on 0e696fe2.

