## Attributes

- id: WI-20260930-MHRN1-two-readers-still-pair-a-mixed
- created: 2026-09-30T20:43:48Z

- status: Open
- status_agent: user
- status_at: 2026-09-30T20:43:48Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

TWO READERS STILL PAIR A MIXED CALL'S POSITIONAL ARGUMENTS BY INDEX: typing/anchor.rs align_call_args_to_params (the positionalizer behind the @[simp] require-witness rewrite, anchor.rs make_witness, and the WI-20260925-P7VP4 rule-body demand and witness paths, rule_requirements.rs inferred_slot_demand and its two siblings) and typing/value_type.rs self_return_spec_op_result_type (the WI-611 value typer, which reads a self-returning spec op's receiver child as pos_child_types.get(idx)). In a MIXED call positional arguments rank among the parameters the labels left open (WI-20260827-1F0QP, positional_param_indices), so the one at index i need not be bound to parameter i: f(1, 2, a: 3) over (a, b, c) is read a := 1. Every other reader of a call's arguments by parameter was moved to that ranking by WI-20260929-0RP29 (bound_arg / bound_arg_result, carrier_param_receiver, the WI-793 hint staging). NOT REPRODUCED: no program in the suite makes a mixed call on either path — found by reading (WI-20260929-0RP29's fourth /code-review) and left, because the right fix needs a convention first. A RULE-BODY call is RELATIONAL: its result is an extra positional, so the ranking reads a mixed spelling (Util.sign(?b, ?c, x: ?a)) as over-applied and aligns nothing — a first attempt turned the silent misalignment into an unaligned refusal, and was reverted. The value typer reads @[simp] law TERMS, which carry no result column (positional_param_indices over the children's labels would do). FIX: state how a relational call's result column ranks (it is the last positional, past the parameters — rank the others among the open parameters), then read both through bound_arg. ACCEPTANCE: a driving row for each — a mixed rule-body call whose slot condition routes the caller's dictionary as its positional twin does (WI-20260925-P7VP4's SLOT_PROGRAM, spelled mixed), and a @[simp] law over a self-returning spec op whose receiver is passed by label — each failing with the index read restored; full workspace green via rustland/scripts/test.sh.

