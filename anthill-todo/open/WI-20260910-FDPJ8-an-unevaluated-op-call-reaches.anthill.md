## Attributes

- id: WI-20260910-FDPJ8-an-unevaluated-op-call-reaches
- created: 2026-09-10T13:14:24Z

- status: Open
- status_agent: user
- status_at: 2026-09-10T13:14:24Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN UNEVALUATED OP CALL REACHES eq/cmp/arith AS DATA ON THE TERM AND ENTITY CARRIERS, AND THE VERDICT IS WRONG.

THE DEFECT, MEASURED. `reduce_op_value` (resolve.rs) folds ONLY a `Value::Node`: `let occ = match &v { Value::Node(o) => .., _ => return v }`. Its partner `is_unreduced_op_call` — the WI-738 soundness floor that makes an unfolded call DELAY instead of being compared — opens with the same `let Value::Node(occ) = v else { return false }`. The pair is internally consistent, and the consequence is one level up: on the `Value::Term` and `Value::Entity` carriers a bodied op call is NEITHER REDUCED NOR DELAYED. It enters `sem_eq_values`' ladder as DATA, and every arm of that ladder asks about a CARRIER (reflexivity, a head `Eq` override, a Float, a partial carrier); an operation application matches none, so it falls out the structural tail.

ONE PROGRAM, TWO READINGS, decided only by where the goal was written. Over `operation dbl(n: Int64) -> Int64 = add(n, n)`:

| goal | truth | rule body (Node) | term-carried |
|---|---|---|---|
| `neq(dbl(2), 4)` | 0 | 0 correct | 1 — WRONG VERDICT |
| `eq(dbl(2), 4)`  | 1 | — | 0 — lost answer |
| `lt(dbl(2), 5)`  | 1 | 1 correct | 0 — lost answer |

AND IT IS REACHABLE FROM SOURCE, not only from a hand-built `kb.resolve`. A CONSTRAINT GUARD is term-carried (`lower_query`), which is DQD5W's own population:

  constraint none_bad:
    no ?v: Box(w: ?v) -: neq(dbl(?v), 4)
  fact Box(w: 2)          -- dbl(2) = 4, so NO witness exists

loads and reports `integrity constraint 'none_bad' is violated by the loaded facts`. With `Int64.lt` in the guard instead, BOTH polarities report `undecidable within the resolver depth budget` — loud rather than silent, but still wrong for a well-formed program. The other term-carried producers (`execute_logical_query`, the reflect `execute(and(..))`, an `or`/`push_choice` branch body) are the same shape.

`unfold_eq_operand` DOES NOT COVER IT, and I checked rather than assumed: that route is gated on `BuiltinTag::SemEq` and declines a GROUND scrutinee at `folded_call_match`'s flex check, which is why `eq(dbl(2), 4)` measured 0. `cmp`/`arith` have no such route at all.

THE REPAIR SHAPE, and the piece that was missing now exists. Widening `is_unreduced_op_call` ALONE is wrong — the operand would report un-reduced for ever (nothing reduces it), trading a sometimes-wrong answer for a never-answer. The order is:

  1. `reduce_op_value` materializes a non-`Node` call through `node_occurrence::value_as_occurrence` (added by WI-20260906-7YPGM for the two relational-view hooks) and folds it, so a call is reduced on every carrier;
  2. `is_unreduced_op_call` then needs no carrier match at all — it becomes a `head()` read like its neighbour `is_unreduced_builtin_call` already is.

Carrier-neutral means reading `TermView`, not adding an arm per carrier.

THE TRAP TO MEASURE AGAINST, named because this exact door has been walked through before. WI-1057 widened `is_unreduced_op_call` to admit body-less spec ops and it broke 5 `wi616_semantic_eq_test` cases, turning definite FAILURES into residual successes — `eq({1,2},{1,3})` and even `{1,2} === {2,1}` answered 1 where they must answer 0 — because `anthill.prelude.Set`'s `insert`/`empty` are body-less spec ops that are SYMBOLIC ALGEBRA and `eq` must keep comparing them structurally. This predicate decides `eq`'s DOMAIN. Also keep `reduce_operand`'s `dispatch_body_less: false` OFF the operand path (WI-1057's `reduce_dispatched_goal_call` split) — widening the CARRIER must not widen the DISPATCH.

ACCEPTANCE. The three rows in the table above answer their truth column on the term carrier AND on the entity carrier, each beside its rule-body twin as the control that passes either way; the constraint-guard program above LOADS, and its `Box(w: 3)` twin is REFUSED, so a predicate that answers a constant fails whichever way it is wrong; `is_unreduced_op_call` reads `head()` with no carrier match; `wi616_semantic_eq_test` green, named as the row set this widening is measured against; the whole suite green via scripts/test.sh. NOT SCALAND.

