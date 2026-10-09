## Attributes

- id: WI-20261009-ZY11J-a-value-typed-by-an-alias-that
- created: 2026-10-09T06:44:23Z

- status: Open
- status_agent: claude
- status_at: 2026-10-09T06:44:23Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A VALUE TYPED BY AN ALIAS THAT FIXES A PARAMETER IS REFUSED BY THE SORT'S OWN OPERATIONS — over `sort Box[V]` with `entity mk(v: V)`, `operation unbox(b: Self) -> V` and `sort CA = Box[V = Int64]`, `let b: CA = Box.mk(5)` then `Box.unbox(b)` is refused: `Box.unbox.dispatch: expected matching impl for per-call bindings, got no impl matches — unresolved: Box[V = Int64] (no impl provides Box …)`. The same value annotated `Box[V = Int64]` answers 5. Measured 2026-10-09 on ebe92670 under WI-20261008-HZVQA's working tree. The program makes no call through the alias, so it is not that ticket's.

WHAT FAILS AND WHAT DOES NOT. Refused, each at `<op>.dispatch` with that message: `Box.unbox(b)`; `b.unbox()`; `Box.same(b)` over `same(b: Self) -> Self`; `Box.unboxV(b)` over `unboxV(b: Box[V = V]) -> V`; and `operation via(b: CA) -> Int64 = Box.unbox(b)`, the alias as a parameter's type. Loads: the same programs with `b: Box[V = Int64]` or with no annotation; `b: CB` over the bare alias `sort CB = Box`; `Box.count(b)` over `count(b: Box)`, which takes any box.

WHY (not traced). The message is the one a spec operation's dispatch gives when no provider answers, so the call is dispatched as if `Box` were a spec required of the value's sort, where the value's type is written `CA`. Spec §5.1 says a value typed by an alias has the fields and dot-operations of the type it stands for.

WHAT. Find where an argument typed by an alias of the callee's own sort is not read as that sort, at a parameter that is the sort at its own parameters, and read it through.

CONTROL. Each refused row answers; a value typed by an alias at another instance (`sort CS = Box[V = String]`, `Box.unbox(b)` where an Int64 is asked) is still refused, at the use; the bare-alias and plain-sort rows do not move. Say which rows fail with the change backed out.

DONE WHEN: the five refused rows answer; the gate is green.

