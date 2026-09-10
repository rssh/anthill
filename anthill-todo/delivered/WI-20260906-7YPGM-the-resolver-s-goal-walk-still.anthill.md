## Attributes

- id: WI-20260906-7YPGM-the-resolver-s-goal-walk-still
- created: 2026-09-06T03:49:10Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-10T12:19:00Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE RESOLVER'S GOAL WALK STILL INTERNS AN UNBOUND ANSWER LINK IT WALKS OVER. WI-20260905-N20EZ moved the answer LINK off the hash-consed store (Value::Var / Value::Entity / shared Value::Term via substitute_vars_transient; walk retired for chase_var). The goal walk that sigma-applies a Value::Term goal (resolve.rs step_init; node_occurrence.rs subst_var_leaf's Term arm) goes through KnowledgeBase::reify, whose fn_value lowers an all-leaf result back to a hash-consed term -- and lowers_to_leaf_term accepts a Value::Var, so a linked leaf that is still UNBOUND at that walk is interned as a new Term::Var (never dedups) plus the rebuilt goal. MEASURED: resolve(&[loose(?x, ?y), simple(?y)]) as Value::Term goals over `rule loose(?x, ?y) :- Box(v: ?x)`, `rule simple(?x) :- Box(v: ?x)` grows term_store_len by +2 per resolve for ever; the designed-to-trip row wi_n20ez_answer_links_transient_test::a_term_conjunction_with_an_unbound_link_still_interns asserts the growth and must be DELETED, not relaxed, when this closes. Only a Value::Term CONJUNCTION reaches it (a rule body walks its own vars as occurrences; the CLI's goals are occurrence patterns since J0RM4), so the shapes are direct kb.resolve callers, execute_logical_query and the reflect `execute(and(..))`. WHY IT IS NOT A ONE-LINER: a non-interning walk was tried (a transient twin of reify) and makes every such goal a Value::Entity, and the goal READERS that fold Term / Node only went blind -- the constraint guard (wi_dqd5w: `no ?ls: Box(items: ?ls) -: contains(?ls, "z")` loaded clean), the Bool relation hook and its Entity operand, the arity+1 relational-view hook, is_unreduced_builtin_call, and simp reassemble_value. So the work is making every goal reader Entity-neutral (read through TermView, never `let Value::Term = goal else ...`), THEN switching the walk to the transient applier. ACCEPTANCE: the row above goes red and is deleted; a new flatness row drives N resolves of the conjunction and asserts term_store_len UNCHANGED after the first; every reader named above is driven with an Entity-carried goal (each: a test that fails when its Term-only narrowing is put back); answers identical before and after across the whole suite; cargo-test green via scripts/test.sh. NOT SCALAND.

## Changes

### 2026-09-10T12:19:05Z — feedback — user

DELIVERED with two of the ticket's own claims CORRECTED BY MEASUREMENT, and one residue PINNED rather than closed.

WHAT LANDED. `reify` gained a carrier parameter (`ReifyCarrier`) and `step_init`'s lazy goal walk takes `Transient`: a σ-moved application rebuilds as a `Value::Entity` spine instead of an interned `Term::Fn`. The walk is also TOTAL now — it calls `reify_value_transient` on the whole goal rather than matching Term/Node with an `other => other` fall-through, because it MEMOIZES the walked goal back into `goals[0]` and that fall-through froze a goal at the first visit's σ the moment it moved onto the Entity carrier.

THE TICKET NAMED TWO SITES; ONLY ONE IS ONE. `subst_var_leaf`'s Term arm was instrumented with `term_store_len()` either side and run over `wi_tests`: 31 084 entries, 0 that grew the store, 0 that rebuilt an application at all. It is unchanged and the census is recorded at the site — reaching that arm means σ bound an occurrence's var to a `Value::Term`, and the compound bindings with a var beneath them do not arrive on that carrier.

THE TICKET NAMED FOUR BLIND READERS; THERE WERE FIVE. The four (Bool relational view, arity+1 functional view, `is_unreduced_builtin_call`, `op_call_as_occ`) are fixed, the first three through one new materializer `node_occurrence::value_as_occurrence`. /code-review then found `walk_arg`, which chased `Term::Var` and `Expr::Var` but not the bare `Value::Var` (WI-109): `[loose(?x,?y), eq(?y,1), simple(?y)]` answered 1 definite solution at HEAD and 0 — a rotated `eq` reading a link its sibling had already bound. A LOST SOLUTION, and the one finding that was a wrong answer rather than a missing one.

THE ACCEPTANCE, ROW BY ROW. The pinned N20EZ row tripped and is DELETED. `wi_7ypgm_goal_walk_flatness_test` (8 rows) drives the flatness and every reader with an Entity-carried goal; each repair backed out one at a time leaves exactly ONE row red, and the table naming which is in that file's header — including the one PAIR (the walk's totality and `walk_arg`'s chase) that no fixture separates, which is stated rather than credited to either. cargo-test: 6800 passed / 0 failed / 11 ignored, from 6793 before (−1 deleted, +8 new). scaland untouched, per the ticket.

WHAT IS NOT CLOSED, AND WHY IT IS PINNED RATHER THAN FIXED. /code-review measured that the leak is HALVED on a goal that then makes a HEAD MATCH, not closed: `with_fresh_vars` normalizes every non-`Term` `tree_subst` entry back through `value_to_term`, and a σ-moved goal is now exactly what arrives there. `[loose(?a,?y), unify(?x, Box(v: ?y)), takes(?x)]` grew +4 per resolve at HEAD and grows +2 here. My first cut's `with_fresh_vars` doc claimed 'nothing on this path enters' the store; that was FALSE and is corrected at the site. Closing it means retiring the term-only `tree_subst` reads beneath that normalization (the WI-636 boundary — three walks), which is a bigger job than this ticket. Pinned by `a_head_match_over_an_entity_goal_still_interns`, to be DELETED when that boundary goes.

ONE MORE THING RAISED AND DECLINED, recorded at its site: `is_unreduced_op_call` is still `Value::Node` only. A `Value::Term` bodied op-call operand already answered false there and always has, so an Entity one is PARITY rather than a regression this change introduced; under `eq` both are picked up by `unfold_eq_operand` → `op_call_as_occ`, and under `cmp` neither is — a pre-existing hole this ticket neither widened nor closed. Widening that predicate decides `eq`'s DOMAIN, where 5 measured failures are already recorded against admitting too much, so it needs its own measurement.

