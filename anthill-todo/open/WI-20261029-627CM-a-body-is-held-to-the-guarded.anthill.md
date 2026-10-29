## Attributes

- id: WI-20261029-627CM-a-body-is-held-to-the-guarded
- created: 2026-10-29T17:15:15Z

- status: Open
- status_agent: claude
- status_at: 2026-10-29T17:15:15Z

- acceptance: cargo-test

- depends_on: WI-20261015-809JN-proposal-050-1-stage-1-a-write

- tags: typing, proposal-048

## Description

A body is held to the guarded elements of its own effect row. `L :- g` in an operation's row says that after a call `L` is possible only where `g` holds. At each call in the body that can cause `L`, where the row declares `L` only under `g`: `g` must be proved from the context at that call (branch conditions, match arms, the KB's laws), or the call's own guard for `L` must imply `g` with its arguments substituted. Otherwise the call is refused, naming `L` and `g` (user, 2026-10-29).

MEASURED on 60265141. `always(s, b) effects { Modify[s] :- eq(b, true) }` writes `s` for every `b`; `caller(c) = always(c, false)` declares nothing; a `main` over `Cell.new(1)` prints 7. The same with the write only in the branch where `b` is false prints 9. Cause: commit 809ee0f2 (WI-818) let a declared `L :- g` admit `L` without reading `g` (`undeclared_effects` in `typing/op_bodies.rs`, through `guarded_effect_label`, and `decompose_effect_row_raw`'s guarded arm on the declared side), so that `Stream.head`'s new body would load. Kernel-language §5.5 checks the same promise for a callback argument ("nothing shows it raises that only where the guard holds") and says nothing for an operation's own row.

ROWS: `always` and the else-branch twin refused; `if b then Cell.set(s, 1)…` accepted; `safeDiv(a, b) effects { Error[DivisionByZero] :- eq(b, 0) } = div(a, b)` accepted (the call's own guard); `Stream.head` / `Stream.tail`, whose raise is under `splitFirst(s)` is `none()`, accepted through the law `isEmpty(?s) = true :- splitFirst(?s) === none`; `List.head`, whose raise is under `headOption(xs)` is `none()`, measured, then given a law or rewritten to match on `xs`; WI-818's negative control (`Boom`) unchanged. Spec §5.5 states the rule. PTT6D's premise ("this declaration is refused") gets a correcting note.

NEXT TO 809JN. A write through a `let`- or pattern-bound name is charged to a parameter only where the name's scope ends (050.1 §3). Where the guard names that parameter, the check reads the name's resolution as known at the call.

