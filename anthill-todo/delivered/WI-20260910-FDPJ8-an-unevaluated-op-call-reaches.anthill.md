## Attributes

- id: WI-20260910-FDPJ8-an-unevaluated-op-call-reaches
- created: 2026-09-10T13:14:24Z

- status: Delivered
- status_agent: user
- status_at: 2026-09-10T15:18:26Z

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


### Delivery

BOTH HALVES LANDED. (1) `reduce_op_value` materializes a non-`Node` call through `node_occurrence::value_as_occurrence`, behind a new `op_call_occurrence_to_reduce` gate; (2) `is_unreduced_op_call` reads `TermView::head`. Every cell of the table above answers its truth column on the `Term` AND `Entity` carriers beside its rule-body twin; the constraint-guard program LOADS for `Box(w: 2)` and is REFUSED naming `none_bad` for `Box(w: 3)`. `wi616_semantic_eq_test` (the named trap) green; whole workspace 6812 passed / 0 failed via `scripts/test.sh`.

DEVIATION FROM THE ACCEPTANCE, and it is a correction rather than a shortfall. The acceptance asked that `is_unreduced_op_call` read `head()` "with no carrier match". The op-call DECISION is one shared `head()`-driven predicate, but TWO shapes are still asked on the `Node` carrier because the view cannot express them, and each is a recorded decision of another ticket rather than a carrier list being kept: `Expr::ApplyWithin` is un-reduced BY ITS FORM (WI-1040), not by its functor — the view arm decides by head functor, and `apply_within` is an entity with no body, so it would answer `false` where WI-1040 requires `true`; and a NULLARY `Expr::Apply` is a call unambiguously only on that carrier, since the storage canon collapses `Fn{f}` to `Ref(f)` (WI-436) and reading a bare name as a call is what WI-20260902-VZC2C explicitly refused at this very function ("a bare nullary op in an ARROW-typed slot is §5.4's unapplied function value ... which is also why `reduce_op_value` may not simply open a `Ref`").

WHAT `/code-review` FOUND, and the one finding that was wrong. Four fixed with a row or a named doc correction each: `unify_terms` collapsed `UnifyOutcome::Delay` onto `None` — "these terms do not unify" — ring-fenced by a doc claim ("only reachable from occurrence-carried inputs") this ticket falsifies, so it is now three-state `TermUnification` and `reflect_unify` raises `EvalError::Suspended`; the reduce gate was not a superset of its delay partner (`interpreter_mapped_ops` is keyed under a `canonical_sym` twin that `op_records` is not), so the gate now asks the delay predicate itself; the entity-carried delay row measured the `Term` carrier TWICE (blinding the predicate to `Value::Entity` left all six rows green) and its fixture is now `neq(dbl(add(?v, ?y)), 4)`, which goes red under that blind; and a "cost gate" headline that is a behavioural narrowing on one carrier now says so.

The fifth — that this ticket makes `unify` / `===` DISPATCH where they are documented not to — is a MIS-ATTRIBUTION, and `a_folding_operand_is_not_new_under_unify_or_struct_eq` is the control: rule-body `unify(dbl(2), 4)` and `struct_eq(dbl(2), 4)` both answer 1 AT HEAD. They share one operand pipeline with `eq`/`cmp` and have folded op-call operands since WI-483/WI-738. The stale docs were corrected (`kernel.anthill`'s `unify` and `struct_eq` declarations, `BuiltinTag::Eq`/`Unify`, `builtin_unify`) rather than the code reverted: "never dispatches" is true of the COMPARISON — no carrier's `Eq` member is selected — and was never true of the OPERANDS.

### Follow-on delivered in the same change: one apply_within shape

RAISED BY THE USER against this ticket's own note that `Expr::ApplyWithin` heads `ViewHead::Opaque` "by design". It is not a design, and the recorded reason argued against a DIFFERENT head: it rejected a TRANSPARENT one (functor = the callee) because "its faithful term twin is the WRAPPED reflect shape `apply_within(fn = …, args = …, requirements = …)`, whose head functor is `apply_within` and NOT the callee" — which is an argument FOR the wrapped head, the one `expr_wrapped_shape` already serves for `dot_apply` / `var_ref` / `lambda_expr` / `if_expr` / `let_expr` / `proof_stmt` / `match_expr`. `ApplyWithin` was missing from that table. `Opaque` is payload-free, so this lost no precision: it made two structurally DIFFERENT woven calls compare EQUAL and share a `GoalKey`.

THE CANONICAL FORM IS THE ENTITY'S, because `apply_within` IS a declared entity — and its declaration was the incomplete one of the three. `entity apply(fn, args, type_args: Option[T = List[type_arg]])` has carried `type_args` since WI-1013; `apply_within` did not, while `Expr::ApplyWithin` carries the channel (`weave_covered_call` copies it off the `Expr::Apply` it rewrites) and `visit_fn`'s `"apply_within"` arm already READ a `type_args` named arg. Reader and occurrence agreed with each other and disagreed with the schema. Shipped: the field added; `record_apply_within_concrete` drops its positional channel — and the PARAMETER, so a future caller cannot hand it positionals to discard in silence — and goes through `canonicalize_record_named_args`; `expr_wrapped_shape` gains the `ApplyWithin` arm (`type_args` CONDITIONAL, exactly as `Expr::Apply`'s head makes it); `try_occurrence_to_term` gains the matching twin, because a head with no twin is not agreement but a different disagreement.

MEASURED rather than argued: the positional channel was DEAD — its only caller, `req_insertion::materialize_apply`, hardcodes `pos_args: SmallVec::new()` — so dropping it moves no value any program ever produced, and no row is claimed for it. `wi1040_require_clause_dictionary_test`'s twelve rows (the weave's own suite, and the producer of every occurrence the new test reads) are green, which is what says the HEAD moved and the DISPATCH did not.

TWO OF MY OWN CLAIMS FELL TO THEIR OWN PROBES, recorded because the sites now say what was measured: the first fixture wrote the covered call as an `eq` OPERAND and produced ZERO woven calls (`collect_covered_calls` weaves only the WI-938 arity+1 GOAL form) — caught by a count assertion, not by a row quietly passing over an occurrence that was never there; and the claim that the deep occurrence↔twin comparison catches a wrong `nil` convention is FALSE, since `head` canonicalizes `Ref(f)` and a nullary `Fn{f}` to one `ViewHead::nullary` (WI-436), so no view comparison can separate them. It does catch a wrong `ApplyArg` cell constructor, which is what the site now claims.

NOT SCALAND, as the ticket says.

