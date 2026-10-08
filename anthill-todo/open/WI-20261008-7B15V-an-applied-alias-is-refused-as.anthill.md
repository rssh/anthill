## Attributes

- id: WI-20261008-7B15V-an-applied-alias-is-refused-as
- created: 2026-10-08T09:06:19Z

- status: Open
- status_agent: claude
- status_at: 2026-10-08T09:06:19Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

AN APPLIED ALIAS IS REFUSED AS A TYPE VALUE WHERE THE SAME TEXT LOADS AS A COMPANION RECEIVER — over `sort Box[V]` and `sort CB = Box`, `CB[Int64].wrap(5)` answers 5 and `let t = CB[Int64]` is refused: "`CB` is over-applied: 1 positional type argument(s) but only 0 declared type parameter(s) left to bind — it declares no type parameters". Measured 2026-10-08 on fd1cf282.

WHY. A companion receiver's bracket is lowered as a type (`type_expr_to_value`), which reads an alias through to the parameters it leaves open. The value position asks `check_sort_type_args` of the alias's own symbol, which declares none (`TypeBuildFrame::TypeValue` in kb/typing/build.rs; eval's `finish_sort_type` asks the same way). So one written type is admitted in one position and refused in the other, and WI-20260824-PAPX0's let-bound spelling stops at the `let`.

WHAT. First say which is the rule: `dealias_type`'s doc (kb/typing/sort_alias.rs) states "an applied alias (`Name[…]`) is refused where it is written", and the companion spelling admits one. If it is admitted: fit an applied alias in value position as the type position does — the typer's check, eval's, and `type_value_denoted_type` (kb/typing/type_receiver.rs), which names positionals against the head's own parameters. If it is refused: refuse the companion spelling too.

CONTROL. `CB[Int64]`, `CB[V = Int64]` and an alias that fixes one of two parameters (`sort IP = Pair[L = Int64]`, `IP[String]`), each as a companion receiver, as a let-bound receiver and as a plain value. Say which rows fail with the change backed out.

DONE WHEN: the written and let-bound spellings give one verdict for an applied alias; the gate is green.

