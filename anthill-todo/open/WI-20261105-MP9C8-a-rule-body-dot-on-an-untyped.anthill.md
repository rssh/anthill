## Attributes

- id: WI-20261105-MP9C8-a-rule-body-dot-on-an-untyped
- created: 2026-11-05T17:16:29Z

- status: Open
- status_agent: claude
- status_at: 2026-11-05T17:16:29Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068, critical

## Description

A RULE-BODY DOT ON AN UNTYPED HEAD VARIABLE IS NEVER DISPATCHED AND ANSWERS ITS TEXT AS DATA; refusing it needs smt-gen to map the dot first (found on WI-20261013-DEY66, 2026-11-05; decided there with the user: a dot is decided by its receiver's type, never by a value — DEY66 refuses a dot on a query variable). MEASURED on ab6d7288, the same on fd640523: over sort Box { entity box(v: Int64)  operation peek(b: Self) -> Int64 = b.v }, rule u(?b, ?x) :- ?x <=> ?b.peek() loads and u(box(v: 4), ?x) answers ?x = box(v: 4).peek, definite; rule fx(?p, ?x) :- ?x <=> ?p.v answers ?x = box(v: 4).v; rule fy(?p, ?x) :- ?x = ?p.v + 1 leaves fy(box(v: 4), 5) and fy(box(v: 4), 6) both conditional. The typer leaves such a dot standing (WI-282's exemption: typing::rule_dispatch::undecidable_by_this_typer, DotDispatchNoMatch with receiver_sort None) and nothing decides it later. THE CHANGE: refuse it at load, with the qualified-call repair a query's gets (LoadError::QueryDotOnVariable's rule), keeping the exemption's other case — the reflect Expr.dot_apply constructor carried as data (an Expr induction principle). WHAT IT REACHES (measured with the refusal switched on): examples/webots-modelling/lf1/safety_common.anthill:299, position_distance_sq(?d_sq, ?p1, ?p2) :- ?dx = ?p1.position.x - ?p2.position.x, …, read only by smt-gen (lf1: 14 proved). Typing its heads (?p1: Pose, ?p2: Pose) fails 4 of the 14 (safety_bounded_excursion_transponder, safety_no_collision_transponder, …: 'the bound of ?var_4 has no SMT sort: a bound is lowered when it is Int64, Float, Bool or an abstract parameter of an enclosing sort'). So smt-gen first gets a custom mapping of dot_apply (user, 2026-11-05): a field read on an entity-sorted variable, or an entity bound, lowered. ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): u and fx refused at load naming the repair; lf1 14 proved with its heads typed (or the dot mapped); the reflect-data exemption's rows unchanged.

## Changes

### 2026-11-15T13:21:18Z — feedback — user

MEASURED 2026-11-15 on 53a0d453b: two more rows of this defect, and both are DEFINITE wrong answers, not conditional ones (entity Product(id: Int64, price: Int64)).
- `=` / `!=` compare the two unevaluated `dot_apply` terms structurally. With `rule neq2(?a, ?b) :- ?a.id != ?b.id`, `neq2(Product(1, 10), Product(1, 20))` answers true, though the ids are equal. With `rule eq2(?a, ?b) :- ?a.id = ?b.id`, `eq2(Product(1, 10), Product(1, 20))` answers no solutions. For comparison, `?a.price > 100` stays conditional, with a warning naming `dot_apply`.
- The receiver can also be a bounded-quantifier binder over an untyped head variable. `rule ids_unique(?xs) :- (forall ?a in ?xs: (forall ?b in ?xs: (?a.id != ?b.id) | (?a = ?b)))` answers true for `[Product(1, "A"), Product(1, "B")]`. The same body under `rule r(Holder(products: ?xs))`, where destructuring types the list, answers false.
Found while writing key-uniqueness invariants for a shop state modelled as a value. The generic helper silently accepted duplicate ids, and only the negative fixtures caught it. The load-time refusal this item plans would have caught both rows, so add them to its acceptance.

### 2026-11-21T17:16:38Z — feedback — claude

CRITICAL (decided with the user 2026-11-21): definite wrong answers, and negation over one proves a falsehood. Until the load-time refusal above lands, a standing dot must never be decided as data.

MEASURED on a4fb58dc9 (debug CLI of 2026-11-21), `entity P(id: Int64, name: String)`, every rule untyped:
  1 `rule id_of(?xs, ?v) :- (some ?a in ?xs: ?v <=> ?a.id)`: `id_of([P(1, "A")], ?v)` answers `?v = P(id: 1, name: "A").id`, definite. The typed control `rule id_of_typed(?a: P, ?v) :- ?v <=> ?a.id` answers `?v = 1`.
  2 `rule id_is(?xs) :- (forall ?a in ?xs: ?a.id === 1)`: `id_is([P(1, "A")])` answers no solutions. The truth is true.
  3 `rule id_isnt(?xs) :- (forall ?a in ?xs: ?a.id !== 1)`: `id_isnt([P(1, "A")])` answers true. The truth is false.
  4 `rule not_id_is(?xs) :- !id_is(?xs)`: `not_id_is([P(1, "A")])` answers true. Negation over row 2 proves a falsehood.
  5 the key helper of 2026-11-15, written with `!==` / `===`: `rule ids_unique(?xs) :- (forall ?a in ?xs: (forall ?b in ?xs: (?a.id !== ?b.id) | (?a === ?b)))` answers true for `[Product(1, "A", 100, true), Product(1, "B", 100, true)]`.
  6 the `=` / `!=` rows of 2026-11-15 are now refused at load: "the call is at a type no head column of the clause reaches … give the variable a type, or put it in a head column and declare the requirement there; `===` compares any two values structurally". The message's suggestion leads to rows 2-5.
  7 control: `(forall ?a in ?xs: ?a.id > 0)` warns "`PartialOrd.gt` has no order for this operand pair (dot_apply and Int64) — the goal is UNDECIDED, not false", and answers conditional. This is the safe behaviour.

WHY these rows decide: `===` / `!==` (`struct_eq` / `struct_neq`) and `<=>` (`unify`) are structural and never dispatch, so they compare or bind the standing `dot_apply` term as data. `gt` reads it as an operand it cannot order, and delays.

PROPOSED, a stopgap that does not wait for smt-gen. It is placed at the dot, not at each connective: a dot that stays undispatched is a pending goal, never data, wherever it is used. Every consumer (`===`, `!==`, `<=>`, `=`, an argument, a head) then sees an undecided goal with the warning naming `dot_apply`, as `gt` does now. Negation over it is undecided, like any other residual. The refusal in row 6 stops recommending `===` and names the repair that works: give the receiver a type, for example by destructuring the value that holds it. The load-time refusal above remains the full fix, and when it lands this stopgap is removed.

ACCEPTANCE, added:
- rows 1-3 and 5 answer conditional, each with the warning naming `dot_apply`;
- row 4 is undecided, not true;
- row 7 and the typed controls are unchanged;
- row 6's message no longer recommends `===`;
- back-out: with the stopgap removed, rows 2-4 answer definitely again.

