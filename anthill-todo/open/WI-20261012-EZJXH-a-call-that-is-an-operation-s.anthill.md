## Attributes

- id: WI-20261012-EZJXH-a-call-that-is-an-operation-s
- created: 2026-10-12T14:24:01Z

- status: Open
- status_agent: claude
- status_at: 2026-10-12T14:24:01Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CALL THAT IS AN OPERATION'S WHOLE BODY, TO AN OPERATION WHOSE `TypeValue` REQUIREMENT ONLY THE CALL'S BRACKET FIXES, ABORTS THE PROCESS WHEN THE OUTER OPERATION IS REACHED FROM A RULE BODY — over `sort Box[V] { operation elem() -> Type requires TypeValue[T = V] = V }` and `operation g[T]() -> Type requires TypeValue[T = T] = Box[V = T]`, each of `operation c() -> Type = g[T = String]()`, `operation c(n: Int64) -> Type = g[T = String]()` and `operation c() -> Type = Box[V = String].elem()` loads clean, and `rule q(?x) :- ?x <=> c()` (`c(1)`) panics: "bridge_op_to_eval: internal evaluator error bridging `g`: DeferToRequirement: requirement param `__req_typevalue` not bound in caller frame (running `g`, requires-chain owner `g`; frame binds [])" (kb/resolve.rs, `bridge_op_to_eval`; `Box.elem` in the third). ANSWERS, each through the same rule: the same call where it is not the whole body — `let t = g[T = String]()` then `t`, `idt(g[T = String]())`, `idt(Box[V = String].elem())` over `operation idt(t: Type) -> Type = t` — `Box(V: String)`, `Box(V: String)`, `String`; the whole-body call whose type an argument fixes — `operation gv[T](w: T) -> Type requires TypeValue[T = T] = Box[V = T]`, `operation c() -> Type = gv("a")` — `Box(V: String)`; and the whole-body call to an operation that requires another spec, fixed by the bracket alone — `operation d[T]() -> Int64 requires Desc[T = T] = Desc.tag()`, `operation c1() -> Int64 = d[T = Leaf]()` over `Leaf provides Desc[T = Leaf]` — 7. Measured 2026-10-12 on 930dba3b with `anthill query`; found with WI-20261012-TCSGT.

WHY, NOT LOCATED. The error names `g`, not `c`, as the operation bridged, and a frame that binds nothing. The dictionary the call site holds for `TypeValue[T = String]` — the derived instance, which the same call is handed when it is an argument or a `let` value — does not reach `g` when the call is the body's last word, and `g`'s read of `T` is a dispatch through that slot (proposal 065 §1, `lower_rigid_read_to_slot`). An argument's value supplies it by another route (the `gv` row), and another spec's slot is filled (the `d` row), so it is the `TypeValue` slot under a bracket-only call in that position. Whether the resolver reduces `c` to its body's call and bridges that, or the evaluator's call in tail position drops the call's requirement channel, was not measured; nor was the program run outside a rule body.

RELATED, NOT THE SAME: WI-20260923-KCNA0 — a rule-body call whose requirement NO provider covers aborts at the same line — and row 2 of WI-20260909-M8QWJ. Here a provider exists and the call site resolved it.

WHAT. Find which route loses the dictionary and hand it on. Where a route cannot supply a requirement the body reads, that is a load error or a resolver error naming the call, not a process abort.

CONTROL. The three whole-body rows above, asserting the value. Fences: the three not-whole-body rows, the argument-fixed row, the other-spec row. Say which rows fail with the change backed out.

DONE WHEN: the three rows answer what their not-whole-body twins answer; the gate is green.

