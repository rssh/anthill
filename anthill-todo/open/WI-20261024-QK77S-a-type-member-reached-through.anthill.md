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

## Changes

### 2026-10-24T14:46:46Z — feedback — claude

IMPLEMENTED (9f5621bb), not pushed; the ticket stays Open for the kernel-language §5.4 sentence, which waits for the user's word. Under let dd = D, dd.T is D.T in a type (let annotation, lambda binder, pattern binder; the refusal in the written spelling's words, 'expected T (Int64), got String') and as a value (PartialEq.eq(dd.T, Int64)); pp.T under let pp = P[T = String] is String, positional brackets, an alias's fixed parameters and a type parameter of the enclosing operation (P[T = X] under requires TypeValue[T = X]) too; a parameter the receiver leaves open is refused as the written P.T is, in both positions; a member defined over the sort's parameters is refused through a receiver that binds them; dd.T() is refused; an internal member is hidden as its written name is, read in the scope the text is written in (a @[simp] right-hand side inside the sort reads it). BOUNDARY, as PAPX0 decided: a parameter t: Type denotes no sort at the dot, so t.T stays refused in both positions (row a_type_that_denotes_nothing_here_keeps_its_refusal, passes either way by design). FOUND AND FIXED WITH IT: a rule body's dot carried no paren-less mark, so (D).T there was refused as a call; a dotted structural alias as a call argument in a rule body (isTup(D.TT) over sort TT = (Int64, String)) crashed the load on a debug_assert in written_type_receiver_occurrence (before-binary too). Rows: wi_qk77s_type_member_through_a_denoting_value_test (18), back-outs per piece at its header; wi_papx0's nested-sort refusal row now uses a constant (a nested sort is a type member now). Full Rust gate 36 suites, 10733 passed, 0 failed, 17 ignored; families unchanged; node carrier rows and family c green; scaland testFull 745 passed. /code-review: 13 findings, 10 fixed, 2 not needed, 1 (the spec) open.

