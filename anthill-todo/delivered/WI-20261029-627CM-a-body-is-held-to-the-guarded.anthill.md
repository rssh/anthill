## Attributes

- id: WI-20261029-627CM-a-body-is-held-to-the-guarded
- created: 2026-10-29T17:15:15Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-01T10:11:25Z

- acceptance: cargo-test

- depends_on: WI-20261015-809JN-proposal-050-1-stage-1-a-write

- tags: typing, proposal-048

## Description

A body is held to the guarded elements of its own effect row. `L :- g` in an operation's row says that after a call `L` is possible only where `g` holds. At each call in the body that can cause `L`, where the row declares `L` only under `g`: `g` must be proved from the context at that call (branch conditions, match arms, the KB's laws), or the call's own guard for `L` must imply `g` with its arguments substituted. Otherwise the call is refused, naming `L` and `g` (user, 2026-10-29).

MEASURED on 60265141. `always(s, b) effects { Modify[s] :- eq(b, true) }` writes `s` for every `b`; `caller(c) = always(c, false)` declares nothing; a `main` over `Cell.new(1)` prints 7. The same with the write only in the branch where `b` is false prints 9. Cause: commit 809ee0f2 (WI-818) let a declared `L :- g` admit `L` without reading `g` (`undeclared_effects` in `typing/op_bodies.rs`, through `guarded_effect_label`, and `decompose_effect_row_raw`'s guarded arm on the declared side), so that `Stream.head`'s new body would load. Kernel-language §5.5 checks the same promise for a callback argument ("nothing shows it raises that only where the guard holds") and says nothing for an operation's own row.

ROWS: `always` and the else-branch twin refused; `if b then Cell.set(s, 1)…` accepted; `safeDiv(a, b) effects { Error[DivisionByZero] :- eq(b, 0) } = div(a, b)` accepted (the call's own guard); `Stream.head` / `Stream.tail`, whose raise is under `splitFirst(s)` is `none()`, accepted through the law `isEmpty(?s) = true :- splitFirst(?s) === none`; `List.head`, whose raise is under `headOption(xs)` is `none()`, measured, then given a law or rewritten to match on `xs`; WI-818's negative control (`Boom`) unchanged. Spec §5.5 states the rule. PTT6D's premise ("this declaration is refused") gets a correcting note.

NEXT TO 809JN. A write through a `let`- or pattern-bound name is charged to a parameter only where the name's scope ends (050.1 §3). Where the guard names that parameter, the check reads the name's resolution as known at the call.

## Changes

### 2026-11-01T10:11:24Z — feedback — claude

DELIVERED (2026-11-01, 20240428). Decided with the user on the way: Stream.head's raise is shown through the law as the ticket expected, which the prover could not do — (a) a match arm now also shows scrutinee === pattern (the law's body asks ===, the arm said =), and (b) in a proof from Γ a guarded = law is a clause of eq (beside the eq builtin no equational head was tried, WI-899). MEASURED: always and the else-branch twin refused; if b then Cell.set(s, 1) loads (the branches of if b show b = true / b = false) and runs; safeDiv = div(a, b) loads through div's own guard; Stream.head / tail load through isEmpty(?s) = true :- splitFirst(?s) === none; List.head (raise under headOption(xs) = none(): undecided) rewritten to match on xs with the law isEmpty(?xs) = true :- ?xs === nil; WI-818's Boom control unchanged. Also held: a call pinned to an override, a function value's application (its row's guard, binders by the call's ranking), a parameter default; a lambda's body where it is applied; a write through a let/pattern name as the memory it reaches at the call. Found on the way and fixed: 809JN's scope-end charge did not read a guarded atom a call kept (a guarded write to a fresh cell was undeclared, one through let x = p uncharged); a hypothesis that is a Bool-view goal as written answered nothing on the Γ bridge (if isEmpty(xs) did not show isEmpty(xs)). Review (xhigh, 11 findings): fixed a recursive call assuming the caller's own guard (an unbound callee parameter), the else-branch fact, a mixed callback call's σ, the D3 skip narrowed to eq, hypotheses incl. forall antecedents; skipped the Γ-only gate row (not observable from a rule body: D3 evaluates the call first), the Bool-proposition normalization at goal_form, a clause-search cost (gate 173 s), the guard dropped at a local name's scope end (no reader before stage 6). Rows: wi_627cm_guarded_row_test (15), each part backed out alone. Full workspace 11,356 passed; families green (node carrier too); scaland 792 + 47 passed.

