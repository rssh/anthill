## Attributes

- id: WI-20261008-7B15V-an-applied-alias-is-refused-as
- created: 2026-10-08T09:06:19Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-29T21:29:47Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

AN APPLIED ALIAS IS REFUSED AS A TYPE VALUE WHERE THE SAME TEXT LOADS AS A COMPANION RECEIVER — over `sort Box[V]` and `sort CB = Box`, `CB[Int64].wrap(5)` answers 5 and `let t = CB[Int64]` is refused: "`CB` is over-applied: 1 positional type argument(s) but only 0 declared type parameter(s) left to bind — it declares no type parameters". Measured 2026-10-08 on fd1cf282.

WHY. A companion receiver's bracket is lowered as a type (`type_expr_to_value`), which reads an alias through to the parameters it leaves open. The value position asks `check_sort_type_args` of the alias's own symbol, which declares none (`TypeBuildFrame::TypeValue` in kb/typing/build.rs; eval's `finish_sort_type` asks the same way). So one written type is admitted in one position and refused in the other, and WI-20260824-PAPX0's let-bound spelling stops at the `let`.

WHAT. First say which is the rule: `dealias_type`'s doc (kb/typing/sort_alias.rs) states "an applied alias (`Name[…]`) is refused where it is written", and the companion spelling admits one. If it is admitted: fit an applied alias in value position as the type position does — the typer's check, eval's, and `type_value_denoted_type` (kb/typing/type_receiver.rs), which names positionals against the head's own parameters. If it is refused: refuse the companion spelling too.

CONTROL. `CB[Int64]`, `CB[V = Int64]` and an alias that fixes one of two parameters (`sort IP = Pair[L = Int64]`, `IP[String]`), each as a companion receiver, as a let-bound receiver and as a plain value. Say which rows fail with the change backed out.

DONE WHEN: the written and let-bound spellings give one verdict for an applied alias; the gate is green.

## Changes

### 2026-10-29T21:29:46Z — feedback — claude

DELIVERED in e6075272. THE TICKET'S PROGRAM WAS ALREADY CLOSED on e6cbb76a, by WI-20260908-9WVT7 (cef5913b, Loader::applied_value_alias: an applied alias in value position is the sort it stands for with both bindings) and WI-20261008-HZVQA (a receiver through an alias carries what it fixes). MEASURED: over sort CB = Box and sort IP = Duo[L = Int64], CB[Int64], CB[V = Int64], IP[String] and IP[R = String] answer the same call as a companion receiver, through a let-bound name and in a rule body's value slot, refuse the same ill-typed argument naming the same parameter (IP[String] fixes R), and equal their types as values. With applied_value_alias reading the alias as its own name the ticket's refusal returns verbatim. WHICH IS THE RULE: admitted — kernel-language §5.1 ('a type written as a value … an alias applied further is the sort it stands for with both bindings'); dealias_type's doc saying an applied alias is refused is corrected. FOUND ON THE WAY AND FIXED in the same commit: (1) a type written as an argument of a rule-body call in a value slot kept a positional unbound (?n <=> isIB(Box[Int64]) and isIB(CB[Int64]) false, List[T = Box[Int64]] nested, a fact holding Box[V = Int64] not found through ?t <=> idt(CB[Int64])) — bound at load, type_value_as_one_term; (2) binding again what an alias fixes was reported twice in a type position, with a cascade at a receiver, an annotation, a rule head's bound and a provision, and a bounding guard dropped — refuse_type_alias_rebinding takes the alias's binding out for all five callers; (3) a head's bound over a guarded rule variable called the guard's spec 'a type alias' — refuse_guard_rebinding names the variable. ROWS: wi_7b15v_applied_alias_test (9), back-out ledger at its head. Full workspace 11,136 passed, 0 failed; families unmoved; scaland testFull 770 + 47 + 1.

