## Attributes

- id: WI-20261115-25AXJ-a-body-less-declaration
- created: 2026-11-15T11:07:30Z

- status: Open
- status_agent: user
- status_at: 2026-11-15T11:07:30Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BODY-LESS DECLARATION REFUSES A TYPED COLUMN, SO A PREDICATE ASSEMBLED FROM SEVERAL FILES CANNOT CARRY ITS SCHEMA (user, 2026-11-15: "should be allowed").

MEASURED on 53a0d453b (anthill CLI of 2026-11-13), in a test harness for an explicit-state specification: one file declares the predicates, and every test file asserts them.

```anthill
-- harness.anthill
namespace shop.test
  import shop.{ShopState, violation}
  rule state(?s: ShopState)
  rule expected(?n: String)
  rule violated(?n) :- state(?s), violation(?s, ?n)
  constraint expected_violation_holds: forall ?n: expected(?n) -: violated(?n)
  constraint no_unexpected_violation: forall ?n: violated(?n) -: expected(?n)
end
-- a test file
namespace shop.test
  import shop.{ShopState, ...}
  fact expected("order_total_positive")
  fact state(ShopState(...))
end
```

1. As written, both declarations are refused: "A typed column `?x: T` has exactly one enforcer, ... a DECLARATION is neither ... The declaration reading, where the annotation is the column's type with nothing to enforce it, is undelivered."
2. The repair that message advises, `:- true`, does not keep the meaning. The rule is no longer a declaration, so each test file's `fact state(...)` is refused ("the predicate `state` has rule heads in 2 files ... and no declaration"). The clause it adds, `state(?s) :- domain(?s, ShopState)`, is the universal relation, after which both constraints are "not decided: forall constraint undecidable within depth budget".
3. Untyped `rule state(?s)` / `rule expected(?n)` loads and the harness answers right: a state with its expected violation passes, and a state missing it fails `check` with exit 1. But the column types are gone, and nothing refuses `fact state(42)`.

So the one construct that declares a predicate filled from several files is the one that cannot carry the predicate's types.

WHAT IT SHOULD MEAN. Proposal 061 §5 already says it: on a body-less head "the ascription is free to be what it looks like: the column's type" (`rule allowed(?from: Stage, ?to: Stage)`). It leaves this undelivered, with the reading to be written into 060. Proposed:
- The declaration's `?x: T` is the predicate's column type, i.e. the relation's row type (052).
- Every clause that joins the predicate, in any file, is checked against it at load. A head argument that does not conform is a load error at that clause, naming the declaration and the column (`fact state(42)` is refused). A clause's own `?x: T` must agree with the declared column.
- A goal over the predicate types its argument at the column type (`state(?s)` gives `?s: ShopState` to the caller's typer), the way an operation's parameter types do.
- It is NOT a `domain(?x, T)` goal. A declaration stores no clause and still asserts nothing (061).

ACCEPTANCE: the harness above loads with the typed declarations and answers exactly as the untyped one does. Drive it: run `check` on a passing state, a state with the wrong expectation, and a state with an unexpected violation, and assert the exit codes. `fact state(42)` beside the typed declaration is a load error naming the declaration and the column. An untyped declaration still loads as it does today. Update the refusal site, 061 §5's "Not claimed as delivered" paragraph, 060 and kernel-language §5.3. Back-out: with the conformance check removed, `fact state(42)` loads again.

