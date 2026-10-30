## Attributes

- id: WI-20261015-8Z5TK-a-function-value-that-reaches
- created: 2026-10-15T20:50:53Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-30T15:20:45Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

A FUNCTION VALUE THAT REACHES A CLAUSE THROUGH ITS HEAD DROPS THE MATCH, SILENTLY — a rule parameter bound to a lambda, a closure or an operation reference, and every `|` / `&` branch that holds a lambda (the kernel's `or(?a, ?b) :- push_choice(?a, ?b)` clause receives its branches through its head).

MEASURED 2026-10-15 on cc3d1a7d, and the same before WI-20260908-9WVT7 (found by its review):
  operation pureOp(n: Int64) -> Int64 = n + 1
  operation mkPure() -> () -> Int64 = lambda () -> pureOp(1)
  operation apply0[T](f: () -> T) -> T = f()
  rule applyIt(?f, ?r) :- apply0(?f, ?r)
`mkPure(?f), applyIt(?f, ?r)` and `applyIt(lambda () -> pureOp(1), ?r)` answer NO SOLUTIONS with nothing said, while `mkPure(?f), apply0(?f, ?r)` in one body answers 2. No call is needed: `rule anyF(?f, ?n) :- ?n <=> 1` answers 1 for `anyF(5, ?n)` and nothing for `mkPure(?f), anyF(?f, ?n)`. `rule disj(?r) :- apply0(lambda () -> pureOp(1), ?r) | (?r <=> 0)` answers nothing — the lambda-free branch's `0` is lost with it — beside `(?r <=> 7) | (?r <=> 0)` answering both.

MECHANISM (read, at the review): the head match renames the clause body through hash-consed terms (`with_fresh_vars`, kb/mod.rs), `value_to_term` fails for a closure, a map, an operation reference or a lambda occurrence, and the match is marked a contradiction, which `step_choice_point` drops as a false match — no fault, no truncation.

THE CHANGE: carry such a value through the head match (opened on the occurrence carrier, as a body variable's binding already is); at the floor, refuse loudly — a fault on the stream and the search marked incomplete, never a contradiction.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh): the rows above answer as their one-body twins do (2; 1; 2 and 0), or, at the floor, each marks the search incomplete with a message; the plain disjunction and the one-body twins unchanged.

## Changes

### 2026-10-30T15:20:42Z — feedback — claude

DELIVERED c541ef90, by WI-20261023-W2JP7's change (the same mechanism: `with_fresh_vars` lowered every head-match binding through `value_to_term` and a binding with no term form marked the match contradictory). Each program answers as its one-body twin: `mkPure(?f), applyIt(?f, ?r)` and `applyIt(lambda () -> pureOp(1), ?r)` 2, `mkPure(?f), anyF(?f, ?n)` 1, the lambda disjunction 2 and 0; the twins and the plain disjunction unchanged (rows z5tk_* in wi_w2jp7_closure_through_a_head_test, failing with the change backed out, the twins' row passing either way). No floor was needed: the value is carried, never refused. The ticket's operation reference passed from a rule body to a function parameter (`apply1(pureOp, 4, ?r)`) faults "unknown operation: apply1.f" before and after, in one clause too, so it is not the head's: it is WI-20261023-Y6QW2's second half.

