## Attributes

- id: WI-20261009-B6QYA-a-member-that-uses-its-sort-s
- created: 2026-10-09T06:44:42Z

- status: Open
- status_agent: claude
- status_at: 2026-10-09T06:57:35Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261008-HZVQA-the-parameters-an-alias-fixes

- tags: typing

## Description

A MEMBER THAT USES ITS SORT'S PARAMETER COULD TAKE IT AS A TYPE PARAMETER OF ITS OWN, A CONSTRUCTOR INCLUDED — so the callee's bracket binds it on a constructor as it does on an operation. PROPOSED by the user 2026-10-09 while closing WI-20261008-HZVQA ("maybe we want to extend operations which accept V (types, defined in the enclosed sort), and not only operations, but constructors, migrate to operation type parameters. But this is an additional rule"). Not to be started without a design pass.

THE PROGRAM. Over `sort Box[V]` with `entity mk(v: V)` and `operation wrap(x: V) -> Self = mk(x)`:

  Box.wrap[V = Int64](5)      -- loads: the callee's bracket may name the sort's parameter
  Box[V = Int64].wrap(5)      -- loads
  Box[V = Int64].mk(5)        -- loads since HZVQA: a constructor reads its receiver
  Box.mk[V = Int64](5)        -- refused

TODAY (measured 2026-10-09). A callee's bracket key resolves among the operation's own parameters and its sort's (spec §5.4, "What a key may name"), for an operation. A constructor has no type-parameter list, so the bracket on it is a load error: "call-site type arguments `Box.mk[…](…)` are not supported here … an entity-constructor call … have no channel for it". The receiver's bracket and an alias bind the sort's parameter for a constructor (HZVQA), so two of the three spellings work for it and one does not.

THE PROPOSAL. A member whose signature uses a parameter of its enclosing sort — an operation's parameter or return, a constructor's field — has that parameter as a type parameter of its own. The callee's bracket on a constructor then binds by the operation rule and needs no rule of its own, and the receiver's bracket, an alias and the callee's bracket are three spellings of one binding for every member.

TO DECIDE WITH THE USER BEFORE IMPLEMENTING. (1) Whether only the parameters a member's signature uses migrate, or all of the sort's: today `Cell.empty[V = Int64]()` over `empty() -> Cell` binds a `V` the signature does not use, and loads. (2) What a positional bracket counts: today it counts the parameters the operation writes in its own bracket, so `Cell.empty[Int64]()` is refused and `Cell.pick[String](1, "s")` over `pick[W](x: V, y: W)` binds `W`. (3) Whether a member's own parameter and its sort's may share a name once both are the member's; today the collision is refused at the declaration. (4) How it meets WI-20261004-KEGNC's question (2), an operation's own parameter a call leaves unfixed: `Opt[T = Int64].make()` over `make[A]() -> Opt[T = A]` is refused for `A` today, in every spelling.

ACCEPTANCE. `Box.mk[V = Int64](5)` is a `Box[V = Int64]`; `Box.mk[V = Int64]("s")` is refused at `mk.v`, as `Box[V = Int64].mk("s")` is; the three spellings give one verdict at one site, for an operation and for a constructor; no program that loads before is refused after. Full workspace green via `rustland/scripts/test.sh`; scaland parity stated.

## Changes

### 2026-10-09T06:58:30Z — feedback — claude

PROMOTED TO OPEN 2026-10-09 on the user's word, the same day it was filed PreOpened: "Type parameter migration - it's relative small change, let make it open". The four points under TO DECIDE stand.

