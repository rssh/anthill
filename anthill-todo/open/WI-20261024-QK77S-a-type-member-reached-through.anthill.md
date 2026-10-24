## Attributes

- id: WI-20261024-QK77S-a-type-member-reached-through
- created: 2026-10-24T13:31:22Z

- status: Open
- status_agent: claude
- status_at: 2026-10-24T13:31:22Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A TYPE MEMBER REACHED THROUGH A VALUE THAT DENOTES ITS SORT IS REFUSED WHERE THE SORT'S NAME REACHES IT. Over `sort D { sort T = Int64; entity d(x: T) }` (MEASURED 2026-10-24 on ce1e37d9): written with the sort's name the member works in both positions — `operation f(x: D.T) -> Int64 = x + 1` answers `f(5)` = 6 and refuses `f("s")` ('expected T (Int64), got String'), and `idt(D.T)` over `operation idt(t: Type) -> Type = t` is the type value `Int64`. Through a value that denotes `D` it is refused in both: `let dd = D` then `let y: dd.T = 5` is refused 'y.annotation (let-binding): expected a well-formed type projection, got type anthill.prelude.Type has no member T' (the projection reads the value's type, `Type`, not its denotation), and `let dd = D` then `idt(dd.T)` is refused '<dot projection>.T: expected an operation, a constructor or a rule of D, got T is declared in D and is none of them; a receiver that denotes a sort reaches the sort's operations, constructors and rules only' (kb/typing/type_receiver.rs, the `declared.is_some()` arm). The user's question when this was measured (2026-10-24, from WI-20261003-KPBVX): does `D.T` and `let d = D; d.T` work — if not, file. RELATES TO WI-20260824-PAPX0, whose user decision (option B, 2026-09-13) is that a receiver whose type is `Type` and whose denotation is a known sort resolves `.m` in that sort's scope however it is spelled; PAPX0 measured and scopes it for operations (`let t = Box[V = Int64]; t.tag()`), and this is the same rule for a type member, in a type position as well as a value one. TO DRIVE, each beside the name spelling: the annotation and the value read through `let dd = D`, through a parameter `t: Type` holding `D`, and through an applied sort whose member is a parameter (`sort P { sort T = ? }`, `let pp = P[T = String]`, `pp.T` is `String`); a refusal of `dd.T` where `dd` denotes no sort known at load. CONTROL: each row fails with the denotation not read. Acceptance: cargo-test via rustland/scripts/test.sh.

