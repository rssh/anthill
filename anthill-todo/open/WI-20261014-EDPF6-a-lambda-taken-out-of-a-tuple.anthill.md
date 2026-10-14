## Attributes

- id: WI-20261014-EDPF6-a-lambda-taken-out-of-a-tuple
- created: 2026-10-14T08:35:09Z

- status: Open
- status_agent: user
- status_at: 2026-10-14T08:35:09Z

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

