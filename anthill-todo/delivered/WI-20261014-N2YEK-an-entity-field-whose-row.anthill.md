## Attributes

- id: WI-20261014-N2YEK-an-entity-field-whose-row
- created: 2026-10-14T08:47:41Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-05T13:14:01Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

An entity field whose row parameter is bound to nothing admits a lambda that writes its own parameter, and applying the field's function then writes with nothing declared.

PROGRAM (measured 2026-10-14, plain and ANTHILL_TEST_NODE_CARRIER=1 alike, and on the tree before 1TJQH as well):

  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  sort Box
    effects EB = ?
    entity box(g: (z: Cell[V = Int64]) -> Int64 @ {EB})
  end
  operation use(q: Cell[V = Int64]) -> Int64 =
    let b: Box[EB = {}] = box(g: lambda (z: Cell[V = Int64]) -> put(z, 5))
    let w = b.g
    w(q)

use declares no effects, and RUNS, writing q (called over a cell holding 1, use(c) * 10 + Cell.get(c) is 55). The construction alone loads (let b: Box[EB = {}] = box(g: lambda (z: Cell[V = Int64]) -> put(z, 5)), then 0). The field's row says the function does nothing; the lambda writes the cell it is handed. A lambda writing a cell in scope at the same field is refused, correctly: put(q, 5) gives "expected Box[EB = {}], got Box[EB = Modify[T = q]]" (since 1TJQH; admitted before it).

EXPECTED: the construction is refused — a callback writing its own parameter is no label the field's row parameter takes, as at an operation's slot @ {EffP} — and so use never runs. 1TJQH's delivery said this of a constructor's field; no row drove it, the family c-callback-row's field naming the parameter in its row (@ {Modify[k], EB}), which 6T5C6 refuses.

THE FAMILY e-applied-arrow lists the programs typed=field,row=open,does=writes-own,declares=none (applied=call, alias, slot) as P3 exceptions naming this ticket: UNSOUND runs 552. When the fix lands they excuse nothing and the run says so.

## Changes

### 2026-11-05T13:00:12Z — feedback — claude

Fixed (2026-11-05, on 0be62d04, not yet committed). The cause: a construction checks its fields before its expectation binds the sort's parameters (WI-384's order), and the callback row check read the field's row `@ {EB}` as open, admitting any label — though `callback_at_slot` had already made `EB` lack `Modify[z]`, the field's unification failing and its result discarded. The annotation then bound `EB = {}` and `b.g` wrote `q` (55). Every later binding did the same, measured on the CLI: `Box[EB = {Modify[q]}]`, a result `-> Box[EB = {}]`, `mk[E]() -> Box[EB = E]` (loaded), the construction handed straight to `consume(b: Box[EB = {}], …)` (55), and `apply[E = {}](q, box(g: …).g)` (55) — so a re-check after the expectation would not have been enough. FIX (`callback_row_error`, kb/typing/args.rs): an open row whose every flexible tail lacks a label does not admit it, whatever the tail is bound to later; the tails' lacks are read once per check. So the construction is refused at the field, `box.g (entity-field)`, naming the label and that the callback's own parameter names nothing where the row variable stands; and an operation's slot `@ {EffP}` refuses the same callback at the argument, where it said "expected a type for 'EffP', got unconstrained — use `run[EffP = …]`", a repair no bracket makes good; a label over a binder out of scope that is not the callback's own (`Modify[y]` of a lambda an enclosing lambda returns, `Modify[g.y]` of a lambda applying a callback parameter) is refused there too. Rows: wi_n2yek_field_row_own_parameter_test, 6 rows — 5 fail backed out (one build, an env switch, removed), the controls pass either way; rows moved to the new site: wi_1tjqh ×3, wi_6mpn2 ×2, wi424 ×1, wi_r1w5a (writesOwnParam, storeWriter: refused at the argument, as in an operation body; refuse_performed_effects' second half is driven by no row now — backed out, the whole wi_tests binary 8,970 passed either way — kept, undriven, not shown unreachable). Families: e's exception for this ticket excuses nothing and is gone, its 8 field rows refused at the field (the 4 declares=all rows that ran among them), 8 parameter rows and 40 of c's writes-own rows move from "refused" (unconstrained) to refused at the argument; all seven families green on both carriers. Full workspace 11,689 passed and 0 failed; scaland testFull 799 passed. FOUND BESIDE IT, the same on 0be62d04, not fixed: at a construction, an arrow nested in a field — `Option[T = (z) -> Int64 @ {EB}]` given a bare lambda (the some-coercion), `List[T = …]` given a list literal — never binds `EB` from the callback's row, and the expectation then closes it: `let b: Box[EB = {}] = box(g: lambda (z) -> put(q, 5))` over the Option field runs 55, and so does the list literal; a hinted literal at a callable element type takes the hint as its element type although §5.4 says a slot whose element type holds a parameter the call instantiates declares nothing and the literal joins (`each(q, [lambda (z) -> put(q, 5)])` is refused unconstrained at a call); in a rule body `eachL([lambda () -> now()], ?r)` and `runOpt(lambda () -> now(), ?r)` load. Spec: a sentence for kernel-language §4.4 drafted, to be agreed.

