## Attributes

- id: WI-20260921-28TAT-remove-the-frame-type-argument
- created: 2026-09-21T09:07:19Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-21T15:16:47Z

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

### 2026-09-21T15:16:32Z — feedback — claude

DELIVERED — THE CHANNEL IS GONE, and the route that replaced it is the requirement channel, as 065 §1 said it would be.

THE COUPLING WAS THE REAL DEFECT, and fixing it is what unblocked everything else. Op-level `requires` evidence lived in `CallClass::ConcreteApplyWithin`, i.e. in a DISPATCH REWRITE. It is now a `NodeOccurrence` stamp (`op_dicts`), written by one function (`stamp_op_scoped_dicts`) and read on every apply route. What a call CARRIES is independent of where it GOES: `Error.reify` needs no rewrite — the prelude declares it body-less because the boundary is a FRAME the interpreter installs by symbol — so no classification described it and nothing handed it its input. Measured before: `reqs=[]` at the dispatch site, loading clean. After: `reqs=1`, carrying the payload sort.

THE SURFACE IS THE USER'S `ErrorTag`, and my first report on it was WRONG — recorded because the correction matters. I reported that `Error provides ErrorTag[T = T] :- TypeValue[T = T]` "resolves to nothing, a universal provision carries no content". It resolves fine. What was broken was the DEMAND GATE, and it took two fixes: `any_requirement_names_spec` scanned sort-level and operation-level `requires` but NOT provision conditions, so with `ErrorTag` the only demand for `TypeValue` in the program was that condition, the gate answered "nobody asks", `type_value_derive` emitted nothing, and every `ErrorTag` resolution failed on its own condition — 23 call sites, silently. The first fix then matched NOTHING because conditions are `SortView`-shaped and I decoded them with the bare-application reader; all 21 stdlib condition facts answered `anthill.reflect.SortView`. 23 unresolved → 1.

`ErrorTag` EARNS ITS KEEP, which was not obvious. It keeps `TypeValue`'s "never benignly unfilled" rule (N31XX) intact for source rigid reads while reify's evidence rides a separate spec judged by the general rule — the gate I had added to that leg was backed out and is not in the diff. The boundary reads TWO hops: the tag's own `impl` is `Error` for every payload alike (the provision is universal), so the payload is in the `TypeValue` evidence it is conditioned on, at an index resolved from the layout rather than written as `0`.

THE CONDITION CONFLATION, and the bug my first fix caused. `sort Narrow requires Boom` is a REFINEMENT — `Boom` is a data sort, no type parameter, nothing can provide it — but it rode the same `SortRequiresInfo` fact as a spec demand, so it put an unfillable slot in `Narrow`'s dictionary chain and NO dictionary whose impl is `Narrow` could be built (`TypeValue[T = Narrow]` surfaced it; `Narrow provides Eq` would have failed identically). I first filtered it out of `direct_requires_chain_rc` — WRONG: `find_requires_location` names slots by walking the UNFILTERED `requires_tree`, so indices went out of range and 253 anthill-todo rows died `index out of bounds: the len is 1 but the index is 1`. I DISMISSED THOSE AS A REBUILD ARTIFACT ONCE; they were real, and the second look is what caught it. The codebase had already learned this exact lesson about the `EffectsRuntime` kind-anchor ("a provider built a dictionary SHORTER than the chain it is indexed by"), so the fix follows that precedent: the clause KEEPS ITS SLOT and resolves to a structural `Leaf` rooted at itself.

WHAT WENT: `Frame.type_args`, `FrameTypeArgs`, `collect_closed_type_args`, `collect_resolved_type_args`, `ground_type_params`, `find_type_arg`, `inherit_enclosing_sort_type_args`, `top_frame_type_args_for_test`, the typer's ~90-line stamping block, `set_resolved_type_args` / `with_resolved_type_args` / `NodeKind::Expr.resolved_type_args`, and behind them `op_own_param_ref_rewrite`, `enclosing_sort_param_ref_rewrite`, `apply_enclosing_param_refs`, `op_scoped_type_param_symbol`, `op_own_param_rigids`, `payload_sort_of`, `ErrorLayer::reify_payload_param`. `wi272_op_type_args_frame_test` deleted with its deletion explained at the registration site: its three rows asserted the channel got FILLED and nothing read what they checked.

ACCEPTANCE, against the ticket's list:
 - a boundary at an enclosing operation's type parameter still NARROWS — `genericDeclineOuter` sees its `Other`. It is driven through the caller's own `requires ErrorTag[T = P]`, which `catchIt`/`catchItEsc` now declare: the capability the channel had, now expressed rather than inferred.
 - an unevidenced boundary is a LOAD ERROR naming the clause, not a silent catch-wide. `native_backing_reads_slots` is what makes it fire: body-less is not "reads nothing" when the backing is the interpreter. The tuple-payload rows go with that — a structural former has no derived `TypeValue`, so reify at a tuple is refused until one exists.
 - host entry: unchanged, and the rule-body row (`viaGenericRule`) still answers.
 - the channel and its stamping are GONE; `wi272` deleted.
 - kernel-language.md §8.7's sentence was WRONG as written ("is not an error at all") and is corrected to describe the conditional refusal, its body-walk blind spot, and the open general question.

NOT DELIVERED, filed instead after discussion: WI-20260921-3G1YT (a declared `requires` unconditionally owed — 4808/21 measured, blocked on receiver-parameter inference for the stdlib combinators) and WI-20260921-6JP6N (a deferred call supplies no op-scoped `requires`; the inline fix was attempted and REFUTED by `wi456_sorted_set_collection_test`, and the site records why).

ONE SITE FOR THE REFINEMENT LEAF, MEASURED. The `EffectsRuntime` anchor it mirrors is exempted at two other sites as well; mirroring it there was tried and is NOT needed — backed out of both, `wi_tests` is 4826/0. Every refinement clause reaches `resolve_inner` as a goal, so that is the one place it belongs; the other two would have been dead code carrying a confident comment. Recorded at the live site with why the anchor differs (it is SYNTHESIZED into chains those sites build directly; a refinement clause is author-written and only ever arrives as a goal).

GREEN: Rust core `wi_tests` 4826/0; full workspace 7227/0 across 36 binaries via rustland/scripts/test.sh; scaland `sbt testFull` 578/0. Scaland needed one fix of its own — `BootstrapTest`'s "effects.anthill's nine siblings emit" is ten now that `ErrorTag` is declared there, and the row records why it moved by exactly one (`ErrorTag` is reflect-FREE; what names `anthill.reflect` is the CONDITION on `Error`'s provision of it, not a field type).

SELF-REVIEW (/code-review high): 2 findings, both addressed — the deferred-call gap above, and `ErrorLayer::resolve` now needing six symbols instead of three (a prelude-without-reflect KB would lose the boundary; believed unreachable since `sort Error` imports `TypeValue`, and nothing asserts it). Two stale docs of my own fixed.

