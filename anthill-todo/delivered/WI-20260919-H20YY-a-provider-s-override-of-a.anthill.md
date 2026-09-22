## Attributes

- id: WI-20260919-H20YY-a-provider-s-override-of-a
- created: 2026-09-19T13:38:40Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-22T17:33:48Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260919-891QP-a-provider-s-or-witness-s-own

- tags: typing

## Description

A PROVIDER'S OVERRIDE OF A DEFAULTED, RECEIVER-LESS SPEC MEMBER IS NEVER REACHED THROUGH A REQUIREMENT SLOT -- the spec's DEFAULT body runs instead, silently. Found while writing WI-20260918-R541X's (C) fixtures (recorded in its feedback).

MEASURED 2026-09-19, on the R541X delivery commit (c3fe68ab):
      sort TypeTerm { sort T = ?  operation valueOf() -> Type = T }          -- a DEFAULT body
      sort Boom { entity boom(why: String)  provides TypeTerm[T = Boom] }
      sort Box  { sort V = ?  entity box(v: V)  provides TypeTerm[T = Box[V = V]]
                  operation valueOf() -> Type = Option[T = V] }              -- Box's OVERRIDE
      operation tagOfP[P](x: P) -> Type requires TypeTerm[T = P] = TypeTerm.valueOf()
      tagOfP(box(boom("x")))   answers `Box(V: Boom)` -- the DEFAULT's `T`; wanted the override's `Option(T: Boom)`
    Loads clean, no diagnostic. CONTROL: the same member made BODY-LESS (`TypeTermB.valueOfB`, R541X's (C) fixture) DOES dispatch to the provider's member through the slot.

CAUSE, FROM READING (NOT INSTRUMENTED). In `check_apply_iter` (kb/typing.rs), the requirement-slot routes -- the WI-239 `find_requires_location` pre-check, `defer_to_op_scoped_slot` (WI-822/1091), and the `DispatchOutcome` arms -- all sit inside the `lookup_spec_op_dispatch(kb, fn_sym).is_some()` block, which covers BODY-LESS spec ops only. A defaulted member is consumed as a NORMAL op (WI-365). WI-365's own carve-out threads a self-RECEIVER carrier (`self_receiver_spec_sort`), and eval's `resolve_carrier_override_by_value` directs by an argument VALUE. A receiver-less member has neither, so the call is a plain apply of the default: `classification = None` at eval, which was observed for this very call while debugging R541X. WI-1093's note that a receiver-less spec op has no value-directed repair applies here verbatim: only the dictionary can direct it, and nothing consults the dictionary.
    NOT MEASURED: the SORT-level `requires` spelling of the same program, and a defaulted member WITH a receiver argument reached through a slot inside a generic scope.

WHY IT MATTERS NOW. WI-20260911-3MV2C's direction is `raise(error: T) ... requires ErrorTag[T]` whose DEFAULT is the type term. A provider that overrides `ErrorTag`'s default -- the one reason to write a provision beyond the default -- would be ignored exactly like this, silently. And R541X's (A) made the default's answer RIGHT for the spec's own `T`, which makes the ignored override harder to notice.

DIRECTION, not decided here: route a defaulted spec member called inside a scope that holds a slot over its spec through the SAME slot dispatch a body-less one takes (the dictionary's provider member if it has one, else the default). That is the dictionary-passing reading 058 gives a spec op. The open question is whether a defaulted member reached with NO slot in scope should keep today's plain-default reading (probably yes: nothing selects a provider there).

ACCEPTANCE: the fixture above DRIVEN to `Option(T: Boom)` through the op-scoped slot, and through the sort-level spelling. A provider WITHOUT an override still gets the default (control: `tagOfP(boom("x"))` -> `Boom`, R541X's headline row, which must stay green). The body-less control is stated as passing either way. Each positive row names the back-out that turns it red. Full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-09-22T17:33:28Z — feedback — claude

DELIVERED. A defaulted, receiver-less spec member called inside a scope holding a slot over its spec is now classified `DeferToRequirement` -- the SAME classification a body-less one gets -- so eval walks the slot's dictionary and reaches the provider's override.

MEASURED, the ticket's fixture DRIVEN: `tagOfP(box(boom("x")))` answers `Option(T: Boom)` where it answered the default's `Box(V: Boom)`; through TWO generic levels; and through the SORT-level spelling (`SHold[E = Box[V = Boom]].f()`), which the ticket listed as NOT MEASURED and which reproduced the same wrong answer. CONTROLS green in both spellings: a provider WITHOUT an override still runs the default (`tagOfP(boom("x"))` -> `Boom`, R541X's headline row).

TWO CAUSES, NOT ONE -- and the second is why the ticket's own DIRECTION was necessary but not sufficient.
 (1) THE ROUTE WAS MISSING, as the ticket read it: the slot routes sit inside `lookup_spec_op_dispatch`'s body-less-only block. New `defer_defaulted_call_to_slot` calls the SAME two from the WI-444 defaulted block -- WI-239's `find_requires_location` on the sort chain, then WI-822/1091's `defer_to_op_scoped_slot`. BOTH are needed: `tagOfP` is a FREE operation, so `enclosing_sort` is `None` and only the op half can serve it, while `SHold`'s sort-level clause is reached only by the first.
 (2) A TYPE PARAMETER WAS BEING PINNED AS A CARRIER, which left the new route unreachable even once added -- found by instrumenting, not by reading. `carrier_from_declared_slot`'s binding filter (`provision_binding_at_param`) admits any base of `SymbolKind::Sort`, and a type parameter IS one: it is DECLARED `sort T = ?`. So `requires TypeTerm[T = P]` pinned `P` itself as the carrier sort; `carrier_override_suppliers` finds no supplier at a parameter, so the block took its no-supplier arm and ran the default. That function's own doc claimed the opposite -- "a type PARAMETER pins nothing here ... That case is the caller's to supply and already works" -- true of the intent, false of the code. Now filtered through `genuine_concrete_sort`, the predicate whose two existing readers ask this exact question ("may I treat this as a carrier now").

THIS IS WI-20260917-NR6FJ DEFECT B'S OTHER HALF, and that ticket had PINNED it as an open residue rather than left it unknown: `a_type_variable_slot_is_unchanged_and_still_disagrees` asserted `(1, 7)` -- the defaulted spelling folding while the body-less one dispatched -- and its doc said it was "written so that fixing the residue FAILS THIS ROW -- which is the intent." Flipped, and renamed `a_type_variable_slot_now_reaches_the_provider_too`, asserting `(7, 7)`.

THE INSTRUMENT MATTERS, and NR6FJ had already MEASURED the wrong one: routing every such call into the WI-210 dispatch block makes the cells answer 7 and breaks three shipped rows where the default is RIGHT (wi886 cpp-mapping, wi876 operation-mapping, wi869 per-provision-conditions). A DEFERRAL reroutes nothing -- `resolve_op_target` yields the provider's override when it has one and the SPEC OP ITSELF when it does not -- so all three stay green, and that fall-through is exactly what the two "no override" controls drive. NR6FJ's own prose named this instrument ("with no concrete carrier the dispatch belongs at the call, where the frame holds the dictionary").

A GATE THE FIRST CUT LACKED, found by the full run and not by reading. Without it the deferral PICKS among clauses: `requires Desc[T = Rich], Desc[T = Other]` answered `Rich`'s 7 where the default (1) is the only honest answer, and R541X's `twoReq[P, Q] requires TypeTerm[T = P], TypeTerm[T = Q]` LOADED -- the deferral silently supplying the evidence whose absence is what N31XX refuses the program for. Both are the ORDER-DEPENDENT answer, off the soft first-match tie-break the locating walks fall back to. Now gated on `sole_chain_entry_over_spec`, EXTRACTED from `bind_sort_params_from_sole_enclosing_requirement` -- which already applies that same refusal to that same shape -- so the binder and the deferral cannot drift about what "sole" means.

NOT COVERED, DELIBERATELY: a defaulted member WITH a receiver/carrier argument (the ticket's other NOT-MEASURED row). `call_names_no_carrier` -- the "call is silent about its carrier" gate, extracted so both slot routes ask it in one place -- declines it, and eval's value-directed dispatch keeps it. Pre-empting that with the slot is the wrong answer NR6FJ measured (`viaop[U](x: U) requires Desc[T = Rich] = Desc.describe(x)` computing `Rich`'s 7 for a `plain()`); its row `an_abstract_argument_still_dispatches_on_the_runtime_value` is green.

ONE RESIDUAL DIVERGENCE, NAMED AT THE GATE rather than left silent: the clause count is over the WHOLE composed chain, so a spec required at BOTH the enclosing sort and the enclosing operation reads as two and the deferral declines, where a body-less op's sort half would win. Counting per half would match that precedence and hold both refusals -- not done, because no corpus program writes the shape and a gate split on a case nothing drives would pin an unmeasurable claim. The cost is a fall-back to the default; the cost of guessing would be a silent wrong answer.

BACK-OUTS, each MEASURED on its own over this file's rows:
 * (deferral) `defer_defaulted_call_to_slot` returns `false` at entry -> the THREE positives red, both controls green (and NR6FJ's flipped row red).
 * (filter) drop the `genuine_concrete_sort` filter in `carrier_from_declared_slot` -> the same three red, both controls green. It is what makes the deferral REACHABLE.
 * (gate) drop `sole_chain_entry_over_spec` -> these five green and two OTHER rows red: NR6FJ's `two_slots_that_disagree_pin_nothing` and R541X's `two_clauses_over_one_spec_are_refused_at_load`.

Rows: `wi_h20yy_defaulted_member_override_test` (3 positives + 2 controls). scaland untouched -- it has no typing/dispatch module -- and green.

