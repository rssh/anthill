## Attributes

- id: WI-20261014-EDPF6-a-lambda-taken-out-of-a-tuple
- created: 2026-10-14T08:35:09Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-23T22:43:38Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A lambda taken out of a tuple is refused at a slot naming its parameter, where the same lambda held in a let is admitted.

PROGRAM (family c-callback-row's slot=own,passed=tuple,takes=cell,does=writes-own, and e-applied-arrow's typed=tuple,applied=slot,does=writes-own; measured 2026-10-14):

  operation run(p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {Modify[k]}) -> Int64 effects {Modify[p]} = f(p)
  …
    let t = (lambda (k: Cell[V = Int64]) -> put(r, 5), 1)
    run(q, t._1)

and with the lambda writing its own parameter (put(k, 5)): refused at the argument (TypeMismatch/op-arg), where let g = lambda (k: Cell[V = Int64]) -> put(k, 5) then run(q, g) runs to 552. The value is the same lambda and its type the same arrow, (k: Cell[V = Int64]) -> Int64 @ {Modify[k]}.

WHY: by 1TJQH's design callback_at_slot renames a callback's own parameters to the slot's by position only where the argument is the lambda or a let holding it; the binder of a lambda taken out of a tuple is treated as out of scope at the call, and the slot's row lacks the label. That is the safe direction, and a limit, not a reading the language asks for: the component's type names its parameter as the let's does.

EXPECTED: the tuple's lambda is renamed by position as the let's is, and runs to 552; the families' verdicts for it move from refused to runs, and e-applied-arrow's exception naming this ticket excuses nothing.

## Changes

### 2026-10-14T08:35:19Z — feedback — user

CORRECTION to the PROGRAM: the lambda in the tuple is the one writing its own parameter, let t = (lambda (k: Cell[V = Int64]) -> put(k, 5), 1) then run(q, t._1) — the put(r, 5) in the first snippet is a slip (a write to r is refused at that slot in every spelling, as it should be).

### 2026-10-23T22:43:08Z — feedback — claude

DELIVERED (user decisions 2026-10-23: an arity-1 binder is recorded and the relation ignores it; a lambda's binder names count as _1.._n; the record is the binder's own symbol). A function type records its own parameters: TypeNode::Arrow gains a binders child, a Value-carried list of the places by position (a denoted occurrence of the binder, the positional label _i at a slot binding no single name), outside param for the reason arity is (a wrapper inside param at arity 1 was WI-782's reverted encoding). A lambda's arrow (lambda_binder_slots, LambdaBody) and an operation's eta arrow (its arg_places) always record them; a written arrow records none, a callback parameter's place saying its position itself (a loader recording was built, measured undriven over 614 rows, and removed). The stdlib's TypeExtractor.Arrow declares binders: List[Term]; the term twin, TermView, deep_clone, the sigma walk, the generic map, the ref re-key and the extractor rebuilds carry it; unify and compat do not read it, so binder names still make no arrows differ. The callback row check (validate_callback_effect_row, callback_at_slot) reads positions off the argument's TYPE (arrow_own_binders): callback_actual_places and the let record (TypingEnv::callable_places) are deleted. So let t = (lambda (k: Cell[V = Int64]) -> put(k, 5), 1) then run(q, t._1) runs to 552, as do a named tuple's field, a pattern's binder and a list's element; refused under -Modify[x] by the absence, and a pure slot by the closed row. The out-of-scope refusal (unplaced_binder) is ungated and kept for a binder the type does not record: an enclosing lambda's, named by a lambda it returned, or a part of a destructured parameter. kernel-language section 4.4 (the arity-1 note and the alignment paragraph) and the stdlib comment updated. Families: c-callback-row and e-applied-arrow move 4 lines each (the tuple spellings run where the let does, or are refused for the undeclared write), e-applied-arrow's two exceptions naming this ticket removed; all families hold, plain and under ANTHILL_TEST_NODE_CARRIER=1. Rows: wi_edpf6_arrow_records_its_binders_test (back-outs at its head); wi_1tjqh and wi_0rp29 rows rewritten to the aligned verdicts, their ledgers re-measured. NOT IN: a multi-binder lambda's parameter list as (_1: A, _2: B) was built and taken out, WI-20260904-34J8Z's (note there). Gate 10619/0, also under ANTHILL_TEST_NODE_CARRIER=1; scaland testFull 796/0.

