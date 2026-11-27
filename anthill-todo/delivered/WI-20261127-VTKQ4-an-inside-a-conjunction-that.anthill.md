## Attributes

- id: WI-20261127-VTKQ4-an-inside-a-conjunction-that
- created: 2026-11-27T06:42:34Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-27T08:00:02Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN `=` INSIDE A CONJUNCTION THAT IS A BRANCH OF A DISJUNCTION IS REACHED BY NO TYPE IN A QUERY, SO IT IS NEVER DECIDED, WHERE THE SAME SHAPE IN A RULE BODY IS. kernel-language §8.3 says of the equality no type reached (WI-20261105-CBRD2): 'A written query is typed where it is read, and a rule body's `=` at load, so neither reaches it.' This shape in a query does. MEASURED 2026-11-27 at 8595d254f (debug CLI, `anthill query -p f.anthill '<G>'`, f declaring `rule pos(?x) :- ?x > 0`):
  G = (1 = 1) | (0 = 1)                              true, no warning
  G = (true = true) | (false = true)                 true, no warning
  G = (1 = 1, 1 > 0) | (0 = 1, 1 <= 0)               no solutions, INCOMPLETE; warnings on `eq(1, 1)` and `eq(0, 1)`: 'compares two values with no `eq` member: no type reached the comparison'
  G = (true = true, 1 > 0) | (false = true, 1 <= 0)  the same, at Bool
  G = (1 = 1, pos(1)) | (0 = 1, pos(0))              the same, a rule goal beside the `=`
  G = (1 = 1) | (0 = 1, 1 > 0)                       true, INCOMPLETE; a warning on `eq(0, 1)` alone: the branch that is a bare `=` is typed, the one that is a conjunction is not
  G = (1 > 0, 1 = 1) | (0 = 1)                       no solutions, INCOMPLETE; a warning on `eq(1, 1)` alone
  G = (1 > 0) | (1 = 1, 0 > 1)                       true, INCOMPLETE; a warning on `eq(1, 1)`
In a rule body the shape is typed at load: `rule both(?x: Int64) :- (?x = 1, ?x > 0) | (?x = 0, ?x <= 0)`, and the same with `?x` untyped, answer `both(1)` and `both(0)` true and `both(5)` no solution, with no warning. A query built as a value takes the same route (`execute_typed_logical_query_with` routes its goals as a written query's, `load::convert_query_terms` → `typing::route_query_goals`): measured from anthill-traces, whose contract evaluator gives a clause's goal to it as a `pattern_query`, on `ensures (result = true, live(s, k, now)) | (result = false, !live(s, k, now))` with `result` a ground Bool — each `eq` left with the same error, every step undecided. That spec now writes the clause as a rule with one head per answer (`is_live(?s, ?k, ?now, true) :- live(…)`, `… false) :- !live(…)`), which is decided. READ, not traced: `route_query_goals` collects a query's nested goals through `nested_goals` / `proved_goal_children` (an `|` / `&` branch, a negand, …, 'each component of a slot the table wraps in tuple(…)'); which step misses an `=` in a `,` conjunction under an `|` is not found. RELATED: WI-20261126-QJ9NW (a contract goal that names nothing loads under a disjunction, where alone it is refused). WANTED: every `=` of a query typed wherever it stands among the connectives a rule body's `=` is typed through, so each G above answers as the rule body does. ACCEPTANCE: a row per G above, as a written query and as a query built as a value through `execute_typed_logical_query_with`, each decided with no warning; the back-out measured at its site; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-27T08:00:00Z — feedback — user

DONE (3469ab354). WHAT WAS GOING ON, MEASURED: in a query a parenthesized goal list was the TUPLE, not the conjunction — d72b59670 gave the §5.3 reading to the clause body walk alone, and the query walk (convert_query_term_expecting) never got it. The typer descends only a connective's goal slots, so an `=` in a branch's `TupleLiteral(_1: eq(1, 1), _2: gt(1, 0))` was no site and was never typed (the ticket's 'which step misses it'). WIDER THAN FILED, MEASURED: a tuple heads no clause, so `(pos(1), pos(2)) | false` answered nothing with no warning, `not((pos(1), pos(2)))` and `not(pos(1), pos(2))` held, and a quantifier body's list failed; and the CONTRACT-CLAUSE walk had the same defect — `requires (x > 0, x < 10)` was stored as the tuple, so `inRange(20)` loaded and ran where `requires x > 0, x < 10` / `x > 0 & x < 10` refuse it, and `requires not(x > 0, x < 10)` let `outOfRange(5)` through. That is the anthill-traces route: its `ensures (result = true, live(…)) | (…)` reached `execute_typed_logical_query_with` holding tuples. Folded in at the user's call. DONE: both walks lower a positional list at a goal position to `and(g1, and(…))`, the term `&` builds (`query_goal_list`, `Loader::contract_goal_list`); `()` is `true`; a named tuple is refused with the clause's sentence; in a value position the list stays a tuple. Spec §5.3 (wording approved by the user) names a query's goal and a requires / ensures clause among the positions. VERDICTS: every G of the ticket answers true with no warning, as a written query and as a value query (execute and refute alike); `(0 = 1, 1 > 0) | (2 = 3)` is refuted, not undecided; isLive's stored ensures, its places bound, run as pattern_query is answered or refuted per binding. ROWS: tests/include/wi_vtkq4_query_goal_list_test.rs, 11. BACK-OUTS, MEASURED in a temporary binary: the query half fails 6; the contract half fails 3; two pass either way by design (a value-position tuple, the `&`-written contract). /code-review (high): one fixed (a user's unresolved `TupleLiteral(…)` in a contract no longer reported twice); one needed no change (contract readers see `and`, the gate covers the codegens); one pre-existing, left (an alias-written binding inside a contract list is not kept on its occurrence). Gate 12952 / 0; families green, no verdict moved; scaland testFull 811 / 0.

