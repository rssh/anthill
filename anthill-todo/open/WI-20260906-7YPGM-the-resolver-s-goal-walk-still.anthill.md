## Attributes

- id: WI-20260906-7YPGM-the-resolver-s-goal-walk-still
- created: 2026-09-06T03:49:10Z

- status: Open
- status_agent: user
- status_at: 2026-09-06T03:49:10Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE RESOLVER'S GOAL WALK STILL INTERNS AN UNBOUND ANSWER LINK IT WALKS OVER. WI-20260905-N20EZ moved the answer LINK off the hash-consed store (Value::Var / Value::Entity / shared Value::Term via substitute_vars_transient; walk retired for chase_var). The goal walk that sigma-applies a Value::Term goal (resolve.rs step_init; node_occurrence.rs subst_var_leaf's Term arm) goes through KnowledgeBase::reify, whose fn_value lowers an all-leaf result back to a hash-consed term -- and lowers_to_leaf_term accepts a Value::Var, so a linked leaf that is still UNBOUND at that walk is interned as a new Term::Var (never dedups) plus the rebuilt goal. MEASURED: resolve(&[loose(?x, ?y), simple(?y)]) as Value::Term goals over `rule loose(?x, ?y) :- Box(v: ?x)`, `rule simple(?x) :- Box(v: ?x)` grows term_store_len by +2 per resolve for ever; the designed-to-trip row wi_n20ez_answer_links_transient_test::a_term_conjunction_with_an_unbound_link_still_interns asserts the growth and must be DELETED, not relaxed, when this closes. Only a Value::Term CONJUNCTION reaches it (a rule body walks its own vars as occurrences; the CLI's goals are occurrence patterns since J0RM4), so the shapes are direct kb.resolve callers, execute_logical_query and the reflect `execute(and(..))`. WHY IT IS NOT A ONE-LINER: a non-interning walk was tried (a transient twin of reify) and makes every such goal a Value::Entity, and the goal READERS that fold Term / Node only went blind -- the constraint guard (wi_dqd5w: `no ?ls: Box(items: ?ls) -: contains(?ls, "z")` loaded clean), the Bool relation hook and its Entity operand, the arity+1 relational-view hook, is_unreduced_builtin_call, and simp reassemble_value. So the work is making every goal reader Entity-neutral (read through TermView, never `let Value::Term = goal else ...`), THEN switching the walk to the transient applier. ACCEPTANCE: the row above goes red and is deleted; a new flatness row drives N resolves of the conjunction and asserts term_store_len UNCHANGED after the first; every reader named above is driven with an Entity-carried goal (each: a test that fails when its Term-only narrowing is put back); answers identical before and after across the whole suite; cargo-test green via scripts/test.sh. NOT SCALAND.

