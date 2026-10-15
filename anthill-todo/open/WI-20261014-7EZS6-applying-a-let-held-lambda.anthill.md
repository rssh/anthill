## Attributes

- id: WI-20261014-7EZS6-applying-a-let-held-lambda
- created: 2026-10-14T08:24:53Z

- status: Open
- status_agent: user
- status_at: 2026-10-14T08:24:53Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261015-809JN-proposal-050-1-stage-1-a-write

- tags: typing, proposal-050.1

## Description

Applying a let-held lambda that writes its own parameter is refused for an undeclared write to that parameter.

PROGRAM (measured 2026-10-14, plain and ANTHILL_TEST_NODE_CARRIER=1 alike):

  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation go() -> Int64 effects {Error[String]} =
    let r: Cell[V = Int64] = Cell.new(1)
    let w = lambda (z: Cell[V = Int64]) -> put(z, 5)
    let n = w(r)
    n * 10 + Cell.get(r)

is refused: "type mismatch in go.effects (op-effects): expected declared: [Error[T = String]], got undeclared effect: Modify[T = z]". The lambda's write to its own parameter z reaches go's row as written, where the application w(r) makes it a write to r — a let-local cell, which go owes nothing for. Handed to an operation instead (apply(r: Cell[V = Int64], f: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]}) -> Int64 effects {Modify[r]} = f(r), then apply(r, w)) the same lambda runs to 55.

EXPECTED: w(r) is 55, the write read as Modify[r] at the application, as an operation's parameter is read at a call.

WHERE TO LOOK: found during 1TJQH; the application of a let-held function value (apply.rs, function-value Path 2) types the callee's row with its own binders unrenamed — callback_at_slot renames a callback's binders where it meets a slot, and nothing renames a called value's binders to its arguments.

## Changes

### 2026-10-14T08:25:11Z — feedback — user

CORRECTION to WHERE TO LOOK: the reading of apply.rs is a guess, not measured — what is measured is the program and its refusal, and the twin through an operation's slot running to 55.

### 2026-10-14T08:35:06Z — feedback — user

ACCEPTANCE ADDENDUM (user, 2026-10-14: fold it here, one fix should close both) — A SOUNDNESS HOLE BY THE SAME MECHANISM, found by the family e-applied-arrow. use[R](q: Cell[V = Int64], r: Cell[V = Int64], h: (n: Int64) -> Int64 @ {R}, w: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]}) -> Int64 = (let v = w; v(q)) DECLARES NO EFFECTS AND RUNS, writing q (go: use(c, d, lambda (n: Int64) -> n, lambda (z: Cell[V = Int64]) -> put(z, 5)) gives 552); the same with w at @ {Modify[z], EW}. Applying w(q) directly is refused, correctly. So applying a function value does not rename its own parameter to the argument, and the label left over is reported as undeclared where the parameter is a lambda's (this ticket's program) and DROPPED where it is a callback parameter's (this one). EXPECTED: v(q) is the write Modify[q], refused where use declares none and running where it declares it. The family's exceptions name this ticket for both; when the fix lands they excuse nothing and the run says so.

