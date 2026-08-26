## Attributes

- id: WI-20260826-VPEWK-a-rule-body-operand-does-not
- created: 2026-08-26T16:56:10Z

- status: Open
- status_agent: claude
- status_at: 2026-08-26T16:56:10Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A rule-body OPERAND does not reduce a HOST-IMPLEMENTED operation, while the same call at a GOAL position does — one call, two positions, two answers, and nothing states the asymmetry.

THE GAP, DRIVEN. All rows measured through `anthill query` on a rule body, in one file, on the built tree.

  goal      :- Bool.and(true, true)                              1 solution
  goal      :- Bool.and(true, false)                             no solutions
  operand   :- Bool.and(true, true) = true                       NO SOLUTIONS   <- the gap
  operand   :- bodied() = true      (operation bodied() -> Bool = true)     1 solution
  operand   :- bodiedF() = true     (operation bodiedF() -> Bool = false)   no solutions
  operand   :- viaHost() = true     (a BODIED op whose body calls Bool.and) 1 solution

So the value-slot evaluator EXISTS and computes correctly — `reduce_operand` (WI-482/WI-483), the single pipeline shared by `eq` / `cmp` / `arith` / `unify`. What it declines is a BODY-LESS operation. `anthill.prelude.Bool.{and,or,not}` are declared body-less and backed by host functions (`eval/builtins.rs:91-93`), so they land in the declined class; `viaHost` is the same computation one level down and answers, which is what says the host function itself is reachable and only the OPERAND POSITION is not.

WHY THE TWO SIDES DISAGREE. The goal side asks `op_reducible_in_rule_body` = `op_body_node(f).is_some() || is_interpreter_mapped_op(f)`; the second supplier is WI-20260822-J38JE's, added for exactly this reason — before it "a host-implemented operation was callable from an OPERATION BODY and inert in a RULE BODY, for no reason anyone had stated". The operand side asks `reduce_op_value(.., dispatch_body_less: false)`, i.e. a BODY and nothing else. J38JE fixed one position and the other kept the old question.

WHAT THE FLAG IS PROTECTING, so a fix does not delete it. `reduce_dispatched_goal_call`'s doc states it: an operand is a term a RULE WROTE, and a body-less spec op there may be SYMBOLIC ALGEBRA rather than a computation. `anthill.prelude.Set`'s `insert` / `empty` are the named case — parametric parent, no body, a real signature, and the terms the membership rules resolve over. Dispatching them would reduce DATA, which is the same failure as the five wi616 regressions `is_unreduced_op_call` records, reached through the other door.

THE SEPARATOR IS EXACT, AND IT IS THE PREDICATE THE GOAL SIDE ALREADY USES. `is_interpreter_mapped_op` answers TRUE for `Bool.and` (registered at `eval/builtins.rs:92`) and FALSE for `Set.insert` (registered nowhere — zero `register_if_present` entries under `anthill.prelude.Set`). Driven, same file, both arms:

  :- Bool.and(true, true) = true                             no solutions   (host-mapped, wrongly declined)
  :- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 1) 1 solution     (symbolic, correctly left as DATA)

That second row is the CONTROL a fix must keep green, and it is the whole reason the gate cannot simply become "dispatch body-less ops too".

DIRECTION (from the user). Add handling of host-implemented operations to the interpreter's operand path: admit an interpreter-mapped op at the operand, so the gate asks the consumer's real question instead of the `body-less` proxy. GROUNDNESS DECIDES THE REST — if the arguments are known and concrete, reduce; if unground or ABSTRACT (a rigid var, an unbound operand), the evaluator returns DELAY rather than an answer, which is the residual discipline the goal side already follows (WI-519 / `is_unreduced_op_call`) and never a silent decline.

NOT DRIVEN: everything under DIRECTION is a code read plus the user's design call. The eight rows above ARE driven.

CONTROL, when it is fixed: `:- Bool.and(true, true) = true` answers 1 and `:- Bool.and(true, false) = true` answers 0 (the pair, so the row measures the COMPUTATION and not merely that something reduced); `:- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 1)` still answers 1; and an unground operand SUSPENDS as a residual rather than answering or vanishing. Do not state the fix's control as "the corpus is still green" — `reduce_operand` is shared by `eq` / `cmp` / `arith` / `unify`, so a corpus run is the blast-radius check, not the measurement.

BLAST RADIUS, why this is not inline in another ticket. `reduce_operand` serves every operand comparison in the language. Its own doc calls keeping `dispatch_body_less` off "a correctness rule, not a cost tweak" and names five wi616 regressions as what the other setting cost. A change here needs its own full-workspace run and its own reading of those five.

FOUND BY WI-20260825-P9Y67, which needed to know whether a rule-body value position could be driven at all. Two wrong diagnoses were recorded and corrected on the way, and both are in kernel-language.md §5.2 now: that a host-backed op is inert in a rule body (false — it reduces at a goal), and that a value slot is not evaluated (false — `reduce_operand` runs).

ACCEPTANCE: the six DRIVEN rows above, plus the `Set` control, plus an unground-operand delay row. Full workspace green via rustland/scripts/test.sh.

