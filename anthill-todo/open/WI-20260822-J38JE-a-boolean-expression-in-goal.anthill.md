## Attributes

- id: WI-20260822-J38JE-a-boolean-expression-in-goal
- created: 2026-08-22T00:27:29Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T00:27:29Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BOOLEAN EXPRESSION IN GOAL POSITION MUST MEAN WHAT LOGIC SAYS — `:- true`, `:- false`
and any Bool-valued expression. Today `true` means one thing at the top of a body and
another one level down, `false` fails only by accident, and a non-Bool constant is
silently dead.

USER POSITION (2026-08-22): `x :- true`, `x :- false` and `x :- <any boolean expression>`
need special handling to match logic semantics.

MEASURED (rustland, current tree, after WI-20260821-FQC85):
  rule ptrue(1)    :- true                     -> 1 solution
  rule pfalse(1)   :- false                    -> 0, BY ACCIDENT (see below)
  rule pint(1)     :- 42                       -> LOADS CLEAN, 0 solutions, no diagnostic
  rule pstr(1)     :- "hello"                  -> LOADS CLEAN, 0 solutions, no diagnostic
  rule nottrue(1)  :- not(true)                -> 1   <-- logic says 0
  rule notfalse(1) :- not(false)               -> 1
  rule mixed(1)    :- base(7), true            -> 1
  rule ortrue(1)   :- base(9) | true           -> 0   <-- logic says 1 (base(9) fails)
  rule pop(1)      :- Box.isbig(box(n: 5))     -> 1   (a Bool OPERATION call: WORKS)
  rule pop2(1)     :- Box.issmall(box(n: 5))   -> 0   (and it is not vacuous)
  rule pand(?b)    :- Bool.and(?b, ?b)         -> REFUSED, located (§6.6 / WI-1046)

BY ACCIDENT is the load-bearing word. `false` does not FAIL, it never becomes a goal: a
boolean literal is a `Term::Const`, so it resolves to no clause and no builtin, and
WI-1034's "rule-body goal `x` names nothing" refusal cannot reach it because a CONSTANT
NAMES NO NAME. `42` and `"hello"` fall through the same hole and are equally silent —
which means a typo that lands a constant in goal position is indistinguishable from a
deliberate `false`, and a clause that can never fire loads with no word said.

PART OF THIS IS FQC85's DOING, and it should be read that way. 061 gave the TOP-LEVEL
`true` a meaning — the empty conjunction, which is what `fact` desugars to (§6.1) — and
left every other constant, and every nested position, alone. Before that change `:- true`
also answered 0: uniformly wrong rather than position-dependent. `not(true) -> 1` is the
row that shows the seam, and §6.6 already says where the seam should not be: the boolean
operators are redirected "at every GOAL position (the body's atoms, AND THE GOAL SLOTS OF
THE CONNECTIVES ABOVE THEM)". The constants must get their reading in the same places, or
`not(true)` stays wrong however `true` is spelled at the top.

WHAT THIS TICKET MUST DECIDE:
 1. THE READING. Is a Bool-valued expression in goal position a CONDITION — succeeds iff
    it evaluates to `true` — or is goal position closed to expressions, with only `true`
    and `false` given constant readings? §6.6 settles the OPERATORS the other way and
    says so as a design rule: in a rule body `not`/`or` are the resolver primitives, not
    the `Bool` value ops, and `and` has no goal reading at all, so `a & b` is REFUSED
    naming the comma. An evaluated-condition reading has to say how it does not reopen
    exactly what WI-1046 closed. The Bool-OPERATION rows above are the awkward evidence:
    `Box.isbig(box(n: 5))` already evaluates in goal position, through WI-938's derived
    relational view at the operation's own arity — so "a boolean expression as a goal" is
    half-delivered already, by a different mechanism, and the two readings meet here.
 2. WHERE THE MEANING IS ATTACHED. Today it is a strip over the body's TOP-LEVEL goal
    list (`is_empty_conjunction_goal`, kb/load.rs), which by construction cannot reach a
    goal nested under `not` or `|`. Attaching it where a GOAL is built instead is what
    makes `not(true)` and `base(9) | true` agree with the top level.
 3. `false` AND THE DEAD CLAUSE. Is `p(1) :- false` legal-and-dead, or refused? It is the
    honest way to disable a clause, and it is also exactly the never-fires shape this repo
    refuses elsewhere. Whichever way, it must stop being an accident.
 4. A NON-BOOL CONSTANT IN GOAL POSITION (`:- 42`, `:- "hello"`) must become a located
    error — the loud counterpart of WI-1034 for the population that names no name. This
    is the half of the ticket with no design question in it.
 5. WHAT `fact`'S DESUGARING BECOMES. §6.1 now reads `fact H` as `H :- true`, and the
    loader makes that the EMPTY body — which is what makes the two spellings the same
    clause (FQC85 drove it). If `true` becomes an evaluated condition, the desugaring must
    still produce an empty body: a clause carrying one always-succeeding goal is a
    different clause (a different `is_equation`, and it misses the WI-624 ground-fact
    fast path).

ACCEPTANCE: drive every row of the table above, in both polarities, and assert the
ANSWER COUNT — not that it loads. `not(true)` answers 0 and `not(false)` answers 1;
`base(9) | true` answers 1 and `base(9) | false` answers 0; a non-Bool constant goal is a
located load error naming its position. CONTROLS THAT MUST STAY GREEN: the Bool-operation
rows keep answering 1 and 0 (WI-938's derived view); WI-1046's `and`-in-a-goal refusal
still fires with its §6.6 message; and `fact H` and `rule H :- true` remain the SAME
clause with the same empty body (wi_fqc85_rule_declaration_test's own row). Say at each
site which rows fail on a back-out. cargo-test green via rustland/scripts/test.sh.

