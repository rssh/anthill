## Attributes

- id: WI-20260921-28TAT-remove-the-frame-type-argument
- created: 2026-09-21T09:07:19Z

- status: Open
- status_agent: claude
- status_at: 2026-09-21T09:07:19Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

REMOVE THE FRAME TYPE-ARGUMENT CHANNEL. It is down to ONE reader; this is the cleanup that finishes it.

WHAT IT IS. `Frame.type_args`: a per-call list of (type-parameter symbol -> resolved type term), written by the typer as `resolved_type_args` on each call site and GROUNDED at dispatch against the calling frame (`collect_closed_type_args`, because one level up the callee's `T` is the caller's skolem). Never specified — it grew for WI-272/708 to answer 'what does this type parameter stand for at run time' and R541X extended it to sort parameters. Proposal 065 §1 answers that question through the requirement channel instead.

STATE (after WI-20260919-N31XX, commit 16da9206). Three readers removed, each measured on its own: `Expr::TypeValue`'s bare-head arm, `reduce_var`'s `.or_else(find_type_arg(..))`, and the CLOSURE SNAPSHOT (`Closure::type_args`, `ClosureTypeArgs`, capture + restore). Full workspace green at each step.

WHAT IS LEFT: ONE reader — `enter_reify_boundary`'s `find_type_arg(type_args, T1)`. Feeding that single call still costs two build sites, a recursive grounding walk (`ground_type_params`), typer-side per-call-site stamping, 12 function signatures threading `type_args: FrameTypeArgs`, 11 field slots across `Frame` and both `ApplyArgs`, and 86 references in `eval.rs`. `wi272_op_type_args_frame_test`'s three rows assert the channel gets FILLED; nothing reads what they check except reify. They go with it.

THE BLOCKER, MEASURED, and it is bigger than plumbing. Putting `requires TypeValue[T = T1]` on `Error.reify` LOADS CLEAN and all 28 reify rows still pass — and NO DICTIONARY EVER ARRIVES. Probed at the dispatch site: `reqs=[] type_args=3`. Adding `requires TypeValue[T = P]` to the fixture's `catchIt`/`catchItEsc` changed nothing. CAUSE: the reify call is NEVER CLASSIFIED — a probe in `classify` for the reify functor produced no output at all. The typer says why at `typing.rs:21085`: `reify[Rho, X, T1]`, declared inside `sort Error { sort T = ? }`, names the sort's `T` NOWHERE, so there is no carrier to dispatch on and the call is deliberately excluded from the spec-op machinery. `build_op_scoped_dicts` runs only inside the classification arms, so an op-level `requires` on `reify` is declared, accepted, and never built. Requirements ARE in scope at both dispatch sites (`dispatch_call_with_requirements_inner`, `dispatch_resolved_operation`) — necessary but not sufficient.

THREE ROUTES, none cheap, all typer work of the same class as WI-20260919-H20YY:
 (a) classify the reify call so `build_op_scoped_dicts` runs for it;
 (b) have the boundary read the ENCLOSING frame's `__req_typevalue` — but it must know `T1 := P` to pick the slot, which is what the channel records, so this is circular without (c);
 (c) have the typer record at the reify call site WHICH enclosing slot supplies the payload evidence — a narrow (a).

THE SURFACE SHAPE (user, 2026-09-21): `Error.reify ... requires ErrorTag[T1]`, with `Error[X] provides ErrorTag[T = X] requires TypeValue[T = X]` — the tag rides the effect marker rather than being derived for every sort, and `TypeValue` underneath is what makes the payload READABLE. 065 §3's note anticipates this ('whether ErrorTag IS TypeValue or refines it is 3MV2C's to decide'). `ErrorTag` does not exist yet.

RELATION TO WI-20260911-3MV2C — IT DOES NOT CLOSE IT, and an earlier reading of mine that said so was wrong. 3MV2C needs the RAISED VALUE's type arguments, which the interpreter does not reconstruct; `TypeValue` supplies the BOUNDARY's side as a full `Type` instead of a bare `Symbol`, which removes one of the two obstacles `payload_matches` has. 3MV2C's three directions (reconstruct from the value / carry arguments on the value / refuse at install) are still its own question. Doing this ticket first makes 3MV2C's cheapest direction cheaper, nothing more.

ACCEPTANCE:
 - a reify boundary at an enclosing operation's type parameter still NARROWS, driven by the row that needs it (`genericDeclineOuter` must see the `Other` the inner boundary left it — the row that fails if the boundary catches wide);
 - a RULE BODY can narrow one, which the channel could never do, via `require[X]` (WI-1040, delivered) — a new row, since this is capability the migration adds;
 - host entry states its outcome either way: `seed_entry_op_requirements` resolves the op half value-directed from the arguments, and whether that reaches `T1` through a closure's effect row is UNMEASURED — if it cannot, the boundary catches wide as it does today and the row says so;
 - `Frame.type_args`, `FrameTypeArgs`, `ClosureTypeArgs`' remains, `find_type_arg`, `ground_type_params`, `collect_closed_type_args`, `collect_resolved_type_args` and the typer's `resolved_type_args` stamping are GONE, with `wi272_op_type_args_frame_test` deleted and its deletion explained;
 - full workspace green via rustland/scripts/test.sh; scaland `sbt testFull`.

## Changes

### 2026-09-21T09:08:57Z — feedback — claude

ROUTE (a) IS MISSTATED IN THE DESCRIPTION — 'classify the reify call' is the wrong fix, and the real one is smaller and general (user, 2026-09-21: 'why reify is not classified automatically by requirement in signature?').

WHY REIFY IS NOT CLASSIFIED, and why that is CORRECT. All five `CallClass` variants are DISPATCH REWRITES — PinNow, ConcreteApplyWithin, DeferToRequirement, UnresolvedSpecOp, EtaOpRef. Classification means 'send this call somewhere else'. `Error.reify` needs no rewrite: the stdlib declares it body-less ON PURPOSE because 'the boundary is a FRAME, and the interpreter installs it BY SYMBOL'. There is nothing to redirect, so the absence of a classification is right.

THE ACTUAL DEFECT IS A COUPLING. `op_dicts` lives INSIDE `CallClass::ConcreteApplyWithin`, and `build_op_scoped_dicts` has exactly three callers, all on dispatch paths: `eta_op_scoped_dicts`, `classify_pin_or_apply_within`, and `check_apply_iter`'s ConcreteApplyWithin arm. But an OPERATION-LEVEL `requires` is an INPUT THE CALLER OWES THE CALLEE — a fact about the callee's SIGNATURE, not about where the call goes. Nothing about 'who do I dispatch to' should decide whether an input is supplied. An operation that HAS a requirement but needs NO dispatch rewrite falls between the two, and `reify` is the first such operation to exist.

IT FAILS SILENTLY, which is what makes it worth fixing generally rather than for reify: `requires TypeValue[T = T1]` on `Error.reify` LOADS CLEAN, the typer accepts it, and the dictionary is simply never built — measured `reqs=[]` at the dispatch site. Any future body-less, specially-dispatched operation with a `requires` hits the same hole with no diagnostic.

REPLACES ROUTE (a) WITH: build op-scoped dictionaries whenever the CALLEE HAS A NON-EMPTY OP HALF (`op_dict_entries(callee).op_entries()`), independently of the dispatch decision — either a `CallClass` variant carrying only `op_dicts` and no rewrite, or lifting `op_dicts` out of `ConcreteApplyWithin` onto its own occurrence stamp. Routes (b) and (c) in the description are then unnecessary: (b) was circular and (c) was a narrow (a).

WORTH A ROW OF ITS OWN whichever way this lands: an operation with an op-level `requires` that the call site never builds should not load clean. Today it does.

