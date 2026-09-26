## Attributes

- id: WI-20260926-NEKR0-a-repeated-type-parameter-is
- created: 2026-09-26T10:01:36Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T10:01:36Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A REPEATED TYPE PARAMETER IS INSTANTIATED FROM ITS FIRST ARGUMENT, so under subtyping a call's typing depends on the order of its arguments. Found closing WI-20260925-PRVA2 (e).

MEASURED (028e13f8 + PRVA2's fixes). `operation cmp2[A](x: A, y: A) -> Int64 requires Cmp[T = A]`, `Circle provides Shape`, `s: Shape`, `c: Circle`. In an operation body `Util.cmp2(s, c)` loads and types `A = Shape` (answers ShapeCmp's 2), while `Util.cmp2(c, s)` is REFUSED: "type mismatch in cmp2.y (op-arg): expected Circle, got Shape". A citation of a rule calling it refuses the same order: "argument binding column `b` has an incompatible type". The first argument pins `A`; every later one must be its subtype. Pinned by `wi_prva2_pre_existing_defects_test::the_other_order_is_refused_by_the_typer`.

THE PRECEDENT. kernel-language's collection literals (WI-20260829-WBXGX): a position declaring nothing takes the JOIN of the elements' own types, "so one relation answers 'several expressions, one type' wherever it is asked" — the first-element rule it replaced "showed as an order-dependence: `[1, "a"]` loaded in a `List[T = Int64]` slot and `["a", 1]` did not". A type parameter bound by several arguments is the same question.

PROPOSED: instantiate a type parameter that several arguments bind at the join of their types (the `if`/`match` arm join), refused where there is none — both orders then load at `A = Shape`. A SPEC CHANGE (§8.1 call typing): discuss with the user before implementing. The rule-body slot router (`op_slot_route`, typing/relation.rs) pins with `unify_types` in parameter order and, since PRVA2, requires every argument to conform to its PINNED parameter; under a join it must instantiate the same way, or the `(Circle, Shape)` citation routes nothing where the typer instantiates `A = Shape`.

ACCEPTANCE: both orders load and answer 2, in an operation body and through a citation (the PRVA2 row flips); the router agrees in both orders; full workspace green via rustland/scripts/test.sh; scaland testFull.

