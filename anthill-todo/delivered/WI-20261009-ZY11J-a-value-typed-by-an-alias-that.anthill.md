## Attributes

- id: WI-20261009-ZY11J-a-value-typed-by-an-alias-that
- created: 2026-10-09T06:44:23Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-09T13:10:50Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A VALUE TYPED BY AN ALIAS THAT FIXES A PARAMETER IS REFUSED BY THE SORT'S OWN OPERATIONS — over `sort Box[V]` with `entity mk(v: V)`, `operation unbox(b: Self) -> V` and `sort CA = Box[V = Int64]`, `let b: CA = Box.mk(5)` then `Box.unbox(b)` is refused: `Box.unbox.dispatch: expected matching impl for per-call bindings, got no impl matches — unresolved: Box[V = Int64] (no impl provides Box …)`. The same value annotated `Box[V = Int64]` answers 5. Measured 2026-10-09 on ebe92670 under WI-20261008-HZVQA's working tree. The program makes no call through the alias, so it is not that ticket's.

WHAT FAILS AND WHAT DOES NOT. Refused, each at `<op>.dispatch` with that message: `Box.unbox(b)`; `b.unbox()`; `Box.same(b)` over `same(b: Self) -> Self`; `Box.unboxV(b)` over `unboxV(b: Box[V = V]) -> V`; and `operation via(b: CA) -> Int64 = Box.unbox(b)`, the alias as a parameter's type. Loads: the same programs with `b: Box[V = Int64]` or with no annotation; `b: CB` over the bare alias `sort CB = Box`; `Box.count(b)` over `count(b: Box)`, which takes any box.

WHY (not traced). The message is the one a spec operation's dispatch gives when no provider answers, so the call is dispatched as if `Box` were a spec required of the value's sort, where the value's type is written `CA`. Spec §5.1 says a value typed by an alias has the fields and dot-operations of the type it stands for.

WHAT. Find where an argument typed by an alias of the callee's own sort is not read as that sort, at a parameter that is the sort at its own parameters, and read it through.

CONTROL. Each refused row answers; a value typed by an alias at another instance (`sort CS = Box[V = String]`, `Box.unbox(b)` where an Int64 is asked) is still refused, at the use; the bare-alias and plain-sort rows do not move. Say which rows fail with the change backed out.

DONE WHEN: the five refused rows answer; the gate is green.

## Changes

### 2026-10-09T13:10:37Z — feedback — claude

DELIVERED 2026-10-09. CAUSE: the loader read an alias through where it is applied (`IntPair[R = String]`) and left an alias written bare as its own name, which is no sort — so every reader that keys on the sort took `CA` for a carrier that provides nothing, and the callee's own sort for a spec required of it. FIX, in the loader's type lowering: a bare alias in a type position is the type it stands for (`Loader::bare_alias_read`, off a record kept where the alias is declared, `KnowledgeBase::alias_types`); the elements of an operation's own `effects` clause keep the alias as written, since the effect rules follow it and name it. A clause binding's value is read the same way, in a sort's clause and in an operation's `requires` (`Loader::clause_alias_type`). ALSO CLOSED, each measured on HEAD first: a slot the alias leaves open was open to anything — `via(b: CB) -> Int64 = b.v` over `sort CB = Box` loaded and returned a String where the written `b: Box` is refused; a spec's operations refused a carrier typed by an alias; an alias reached as a child of a sort (`Host.HA`); an arrow's row naming a bound alias; two provisions of one type, one written through the alias, of which a call ran one in silence. CHANGED FOR EVERY PROGRAM: a refusal prints the type an alias stands for, not the alias's name. NOT DONE: an alias that names a type parameter, as a clause binding's value, stays as written (`requires Show[T = OS]` over `sort OS = Sx[A = S]`); kernel-language.md §5.1's list is not extended yet, the text is with the user. CONTROLS: the header of wi_zy11j_alias_typed_value_test. Scaland: nothing to port — its loader reads no alias in a type position and it has no typer.

