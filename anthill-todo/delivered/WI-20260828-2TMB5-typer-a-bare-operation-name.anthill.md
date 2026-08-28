## Attributes

- id: WI-20260828-2TMB5-typer-a-bare-operation-name
- created: 2026-08-28T15:22:28Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-28T22:12:13Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

typer: a BARE OPERATION NAME supplied to a NON-CALLABLE constructor field loads CLEAN instead of being refused. MEASURED: `sort Plain { entity plain(v: Int64) }` with `operation probe() -> Plain = plain(inc)` (where `inc(x: Int64) -> Int64`) produces NO load error. An operation name is not an Int64; the eta arrow `(Int64) -> Int64 @ {}` is not the declared field type by any relation. PRE-EXISTING and independent of WI-20260828-8Q0Q5: measured identically with 8Q0Q5's hint in place and with its gate neutralized, so that change neither caused nor repaired it — which is why 8Q0Q5's test file deliberately does NOT pin today's acceptance (a row asserting it would enshrine laxity and go red on the repair). WHERE TO LOOK: the constructor field-value validation loop in typing.rs (`validate_field_arg` / the `field_types` loop in check_constructor_iter) is GROUNDNESS-GATED — WI-1059's note says a polymorphic field stays unchecked and the return-conformance path settles it. Check whether a bare-name argument reaches that check at all, and what type it is carrying when it does: before 8Q0Q5 it was typed with NO expected type, so `check_bare_ref` may have taken the zero-arg-call reading rather than the eta reading, and a zero-arg call of `inc` would report an arity error rather than a type mismatch — establish which of the two it is before choosing the site. ACCEPTANCE: the program above is a loud type error naming the field's declared type and what was supplied; the four rows of wi_8q0q5_arrow_field_eta_row_test stay green.

## Changes

### 2026-08-28T22:12:05Z — feedback — user

DELIVERED, and NOT at the site the ticket pointed at. The ticket asked which of two readings `plain(inc)` was taking; MEASURED, it is the ZERO-ARG-CALL reading, and that arm of `check_bare_ref` was never gated on the operation being NULLARY. `inc` typed as its RETURN type `Int64` — exactly the declared field type — so the WI-385 field validation had nothing to object to. The applied spelling `plain(inc())` is an arity error; the bare one skipped the arity check by never being routed through a call.

TWO OF THE TICKET'S OWN PREMISES WERE WRONG, both measured. (1) It is not the hint path: `arrow_slot_arg_hint` is gated on `type_head_is_callable` and `Int64` is not callable, so the argument reaches `check_bare_ref` with `expected = None` — a repair keyed on a known non-arrow expected type would not have touched the ticket's own program. (2) It is not the FIELD path: an ordinary operation parameter (`take(v: Int64)` fed `inc`) has the identical hole, which is why the fix sits in `check_bare_ref` and not in the constructor hint chain. That row is in the test file.

THE FIX. A non-nullary bare name has exactly one reading — the eta lift — because the other is an arity error. It needs an arrow to lift AGAINST, and reaching the zero-arg-call arm means there is none (the WI-275 arm above returns whenever `expected` is an arrow and the operation has a function-value form). So the reference denotes nothing and is refused there, naming the operation. A nullary name is untouched: both its readings survive and WI-700's `eta_shadows_return_type` keeps arbitrating them. This is the THIRD visit to this fall-through — WI-1063 found it laundering an existential return, WI-1083 a ∀; both repaired the arm ABOVE so fewer references reached this one, and this repairs the reading itself.

THE FIRST CUT LIFTED INSTEAD, AND /code-review CAUGHT IT AS UNSOUND. With no arrow it pinned the dispatch dictionary against the operation's OWN arrow; self-unification pins nothing, and `attach_eta_dispatch_dict` reads that arrow for BOTH the requirement dictionary and the argument-spread labels (WI-1087). MEASURED: `via_option(some(sub2))` returned -7 where its arrow-slot twin `direct(sub2)` returned 7, same operation, same declared slot, same applied tuple. On main that program is a LOAD ERROR, so the lift did not restore a capability — it turned a correct refusal into a silently wrong answer, which is worse than the defect being fixed. `the_polymorphic_slot_is_refused_and_the_arrow_slot_still_runs` holds both halves, the `direct` half DRIVEN at 7 so the refusal cannot take the arrow-slot path with it.

POPULATION CENSUSED, not guessed: with a probe on the zero-arg-call arm the WHOLE workspace reaches it with a non-nullary operation exactly FIVE times, and every one is a row in the test file — `is_big` under an unknown dot head, `sub2` into a List/Option field x2, `widen_named` in an eta slot, and `as_term`, the one body-less case.

CONTROL: 6 defect rows go red when the gate is neutralised (`if false && !op_info.params.is_empty()`), 3 pass either way BY DESIGN — the nullary reading, the inline-lambda twin, and the well-typed field value, which is what keeps the refusals from being satisfied by a fix that simply rejects `plain(...)`.

TWO NEIGHBOURING TESTS MOVED, both repairs, each measured rather than assumed. wi1078's `the_bare_nullary_name_and_the_eta_lift_open_it_too` wrote an `apply_it(f: Function[...])` slot in a fixture whose preamble never imported `Function` — the slot was not an arrow, so that half was riding the zero-arg refusal, not the lift. Import added; the file's back-out table was RE-MEASURED (still 6) and both halves measured SEPARATELY, since the shared `refusal` panics on the first and would hide the second. wi836's callback row needed an argument typed `List[T = Int64]` against a `List[T = Function[...]]` slot and got its `Int64` from the very reading removed here; it is re-spelled to the literal `1` and RENAMED to `a_callback_slot_nested_in_a_sort_application_still_withholds`, since the withholding is a property of the SLOT. An inline lambda was tried FIRST and REJECTED: under a head-only-degraded `type_contains_callable` it stayed green, i.e. it would have looked like a control while measuring nothing. The literal goes red under that same degradation with the identical diagnostic the original produced.

/code-review RAN TWICE. The first pass found the unsound lift (2 HIGH). The second found 7, all fixed: a stale comment describing the abandoned first cut; the two halves of the diagnostic computed independently, so a body-less operation was advised to find an arrow slot no rule would accept; `operation_as_function_value` called only to pick an error string, minting a skolem into the KB (now the read-only `op_has_runnable_body`); "a builtin or a spec declaration" also firing for a rule-defined operation; a stray blank line; the wi836 name/prose drift; and the wi1078 table row. Restoring the slot type to the body-less message was driven by `wi275_hof_inference_test::body_less_builtin_in_function_slot_is_rejected_not_crashed` going red without it.

WHAT NOTHING COVERS, said rather than credited to a neighbour: the gate reads the record through `lookup_operation_info_full`, a DIFFERENT reader of the `OperationInfo` facts from the `lookup_operation_return_type` whose arm it guards (it decodes a whole signature, through a cache tier the other has not got). Nothing in the corpus makes them disagree, so that third arm is written and never driven — a loud error rather than a fall-through precisely because it cannot be tested.

KNOWN LIMIT, and the follow-up: a bare operation name in a POLYMORPHIC slot (`some(sub2)` where the element type is pinned to an arrow only by the CALLER) is now refused, because the arrow never reaches the reference — the op-arg hint chain does not push a non-entity parameter type down into a constructor argument. Restoring it needs the declared parameter type to reach a name buried in a nested constructor slot; a naive version was written and MEASURED not to suffice. Filed separately.

Spec: docs/kernel-language.md gains the paragraph partitioning the two readings, stating that lifting without an arrow is forbidden because such a value cannot be MINTED.

Tests: rustland/scripts/test.sh green — 36 binaries, 5992 passed, 0 failures. scaland sbt test green — 544 passed, 0 failures.

