## Attributes

- id: WI-20261030-BXMPK-a-goal-holding-a-value-with-no
- created: 2026-10-30T15:21:47Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-30T16:34:03Z

- acceptance: cargo-test

- depends_on: WI-20261023-W2JP7-a-closure-handed-to-another

- tags: value-to-term, resolver

## Description

A GOAL HOLDING A VALUE WITH NO TERM FORM IS STILL LOWERED AT RESOLUTION TIME, AND FOUR OF THOSE SITES LOSE IT IN SILENCE — step 2 of retiring `value_to_term` (step 1, the head match, was WI-20261023-W2JP7, c541ef90). Filed by the user's decision, 2026-10-30.

THE SITES (READ, an audit of every `value_to_term` / `alloc_from_value` caller after c541ef90; rustland/anthill-core/src, lines as of then; a lower bound):
  - `lower_ho_apply` (kb/resolve.rs ~4018): `value_to_term(kb, a).ok()?` per argument. A closure argument makes the `ho_apply` goal fail as if its predicate were unbound (caller ~2547), and a `forall_impl` antecedent stays `ho_apply(…)` so the hypothesis never matches (caller ~3497). Its producer is the induction schemas (`<Sort>.induction`): MEASURED, a program cannot write `ho_apply` by name ("rule-body goal `ho_apply` names nothing"), so no program reaching it with a closure is known yet.
  - `contract_clause_conjuncts` (kb/proof_verify.rs ~789): a conjunct carried as an Entity with no term form (a lambda argument inside a `requires`) empties the whole clause — a `requires` is then not assumed, silently (caller ~637); an `ensures` writes `Failed` (~648).
  - `value_as_occurrence` (kb/node_occurrence.rs ~6110): an Entity headed by a reflect-form functor that holds a closure becomes `Expr::Spliced`, so the WI-580 Bool view, the arity+1 view and `op_call_as_occ` see no call and answer nothing.
  - `unfold_eq_operand` (kb/resolve.rs ~13800, through `alloc_from_value`): a closure OTHER declines the case-split (nothing lost: the ordinary `=` runs), but an Entity OTHER with a nested `Node` child is refused where `value_to_term` would lower it, so it skips the unfolding and may delay to a residual.
  - Loud today, on the same boundary: `goal_value_to_term` (kb/execute.rs ~800, an `or(l, r)` branch or a synthesized conjunction built as a `Term::Fn`), `lower_leaf` (execute.rs ~881, a query leaf), and `try_occurrence_to_term`'s `Expr::Spliced` arm (node_occurrence.rs ~5130).

THE CHANGE: each reads its goal through the view and builds what it needs on the value carrier (an occurrence or an entity spine), as `with_fresh_vars` has since W2JP7; a goal value with no term form is carried, never a failed goal and never a dropped clause. No `value_to_term` / `alloc_from_value` call remains on a goal in kb/resolve.rs, kb/execute.rs or kb/proof_verify.rs. WI-20261013-2HX69 (068 D1c) rewrites `unfold_eq_operand` too; whichever lands second rebases on the other.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh): a row per site a program reaches, driving a closure or a lambda through it and failing with that site's lowering put back — a contract `requires` holding a lambda is assumed; an entity headed by a reflect-form functor with a closure child reduces; `unfold_eq_operand` unfolds an Entity OTHER with an occurrence child; a query with a lambda leaf keeps it as a lambda (WI-20261023-Y6QW2's query half). For a site no program reaches, the measured statement at the site and the lowering removed all the same. The rows of wi_w2jp7_closure_through_a_head_test pass either way.

## Changes

### 2026-10-30T16:33:55Z — feedback — claude

DELIVERED cf906e65. A goal holding a value with no term form is carried: `?p(args…)` is applied as a goal over its arguments as they are, so a closure or a lambda reaches the predicate (and a `forall` antecedent applies to a lambda); an operation that queries with a function it was handed keeps the query's leaf on its carrier (put in the form a fact is stored in), and an `or` and a multi-goal branch are goals over their parts — the multi-goal branch is its `push_and` conjunction, which replaced the synthesized `_synth_N` rule, so no query mints a rule. `unfold_eq_operand` and the contract proof's conjuncts read through the view; no program reaches either old lowering (measured, stated at each site). `value_as_occurrence`'s reflect-form arm keeps its lowering: a keyed functor is a call only for an operation named like a form, which the loader loses first. Found on the way and fixed: a contract proof over an `if` / `match` / `let` / lambda body panicked in debug and read `result` as ⊥ in release; it is Deferred. Rows: wi_bxmpk_goal_value_carried_test (12, three controls), each part measured backed out alone. Not this ticket's, reported to the user: a `forall` hypothesis holding a closure panics the matcher (HEAD too), and an operation named like a reflect form is read as the form by its name's last segment.

