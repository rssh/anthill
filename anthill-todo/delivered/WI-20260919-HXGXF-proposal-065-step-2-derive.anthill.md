## Attributes

- id: WI-20260919-HXGXF-proposal-065-step-2-derive
- created: 2026-09-19T15:19:32Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-20T09:34:26Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260918-CKD4J-eq-derive-derives-nothing-for

- tags: typing

## Description

PROPOSAL 065 STEP 2 — DERIVE `anthill.reflect.TypeValue` FOR EVERY SORT, CONDITIONAL FOR A PARAMETRIC ONE; REFUSE A HAND-WRITTEN ONE.

THE SPEC (065, "The rule"): `sort anthill.reflect.TypeValue { sort T = ?  operation type_value() -> Type }`, body-less. 055 §8's `type_value[T = B]()` is this member called with a callee bracket.

WHAT IS DERIVED.
 * A concrete sort `S` gets `S provides TypeValue[T = S]`, with `type_value()` answering `S`.
 * A parametric sort gets a CONDITIONAL instance over its parameters: `Box provides TypeValue[T = Box[V = V]] requires TypeValue[T = V]`, whose `type_value()` builds `Box[V = <V's type_value>]`. That is `Typeable a => Typeable (Box a)`.
 * One instance per structural FORMER — named tuples, arrows — built the same way.
 * Effect rows get none. 065 open question 3 proposes refusing a value read that needs one, naming the row.

REUSE, NOT A SECOND MECHANISM. This is CKD4J's conditional derivation (`provides Eq[S] :- Eq[P…]`) with a different spec. Depends on CKD4J and builds on whatever it delivers. CKD4J's two unmeasured questions apply verbatim: a goal over a type EXPRESSION in the provision tail, and a CYCLE through two conditional provisions. Answer them once.

DERIVED-ONLY. A user-written `provides TypeValue[…]` is a load error naming the sort. A forgeable instance turns every type read into a claim (065 §2; 3MV2C reached the same line). The refusal covers every place a provision is written: the carrier's body, a `namespace` block at its qualified address, and a witness sort.

TRANSIENTS (065 open question 4): a parametric instance BUILDS its `Type` per dispatch, so the result must not be interned per call (CLAUDE.md's representation note).

ACCEPTANCE, each row DRIVEN by calling `type_value` through a requirement slot, and each saying which back-out turns it red:
 - concrete `Boom` gives `Boom`; parametric `Box[V = Boom]` gives `Box(V: Boom)`; a nested `Box[V = List[T = Int64]]` gives the whole nested term; one tuple and one arrow give their types;
 - the hand-written refusal, in all three places;
 - a mutually recursive pair of parametric sorts loads and answers.
The load rule is NOT on yet (step 3), so existing reads are unaffected, which is itself a control. Full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-09-20T05:52:19Z — feedback — claude

PARTIAL — foundation in the working tree, UNCOMMITTED and not driven by any test. Full workspace suite green (0 failures) with it in place.

THREE DECISIONS TAKEN (user, 2026-09-20). (1) BACKING: a dictionary-walking implementation, NOT a synthesized per-sort `where` body. Measured why: `set_op_body_node` has three callers (the loader from parsed source, two @[simp] write-backs), so loader-synthesized bodies are machinery that has never existed; and 065's literal design does not RUN until 891QP (step 4) closes the instance-context gap, because a derived body `Box[V = V]` reads V as a value through a slot-entered member with no call site to write the frame channel. (2) ADDRESS: `anthill.reflect.TypeValue`, as 065 §3 literally says. NOTE THE DISCREPANCY 065 CARRIES: it says 'beside Type itself', but `Type` is declared in anthill.prelude (stdlib/anthill/prelude/sort.anthill, co-defined with EffectExpression for an import-cycle reason). reflect.anthill already imports prelude.Type, so no new import was needed. (3) SCOPE: sorts only. Structural FORMERS (named tuples, arrows) deferred — they have no sort to carry a provision, the same shape as the named-tuple key gap kernel-language.md §8.3 names and WI-20260919-9KYPA left open; they need a structural reading, not a provision row.

IN THE TREE. stdlib/anthill/reflect/reflect.anthill: `sort TypeValue { sort T = ?; operation type_value() -> Type = type_value_of_self() }` plus a bodyless namespace-level `operation type_value_of_self() -> Type`. anthill-core/src/eval/builtins.rs: the `type_value_of_self` builtin — reads the running frame's `__req_self` and rebuilds the Type by walking the dictionary.

PROVEN. (a) The spec loads clean against the full stdlib. (b) A DEFAULT BODY ON THE SPEC OP BACKS EVERY PROVIDER AT ONCE (op_backed's op_has_runnable_body leg): a hand-written `provides TypeValue[T = Boom]` loaded clean with no per-carrier implementation, which is what makes ~220 derived provisions viable without body synthesis. (c) THE DICTIONARY IS THE TYPE: `Dictionary(sub0..subn-1, impl: S)` — impl is the head, subs are the arguments' evidence — and eval/dictionary.rs's header states it is deliberately NOT interned, which answers 065 open question 4 (transients) by construction rather than by effort. (d) TypeValue's shape (sole type parameter, no operation receiving on it) reaches rung 2 of spec_carrier_param_or_sole, the same rung Eq and NonEq reach, so the carrier parameter resolves correctly.

BLOCKED, and this is the next step. The spike evaluated type_value() but the frame carried NO requirements at all (measured: 'binds []'), so no dictionary reached the builtin — the call was not classified DeferToRequirement. Two candidates, NOT yet separated: (i) unique resolution with few providers — weakened, because adding a second provider did not change it; (ii) the SPELLING. `TypeValue.type_value()` may bypass the WI-239 slot pre-check, and 065's own spelling `type_value[T = B]()` is REFUSED today ('expected an operation, which declares the type parameters a call-site [..] bracket binds, got a callee with no type-parameter list') because T is the SORT's parameter, not the operation's; 065 §8 attributes that binding to WI-20260911-RS2G4, which may not be wired for this shape.

NEXT STEP, concrete: wi_1z3e7_provision_where_blocks_test's `PartialEq.eq(x, y)` inside a `where` block is a PROVEN-WORKING call that does reach its slot at run time. Diffing how that classifies against the spike should identify the right spelling in one pass.

OPEN FOR THE USER. Whether the blocker is step 2's to solve or belongs with 891QP/RS2G4; and whether to keep the in-tree changes or revert them — as it stands there is a builtin no test drives, which the repo's own rule says is not evidence.

STILL UNBUILT: the derivation itself (unconditional rows for concrete sorts, conditional per-parameter rows for parametric ones, reusing CKD4J/9KYPA's mechanism), the derived-only refusal in all three provision-writing places, and the acceptance test file. CKD4J's two unmeasured questions (a goal over a type EXPRESSION in a provision tail; a CYCLE through two conditional provisions) are also still unanswered.

### 2026-09-20T07:37:37Z — feedback — claude

STEP 2 IS FUNCTIONALLY COMPLETE AND GREEN, uncommitted. Full workspace suite exit 0, 0 failures. 18 files, ~384 lines + two new files.

THE DESIGN, and the four facts that FORCED it (each measured, not reasoned):
(1) A spec op with a DEFAULT BODY is dispatched STATICALLY and never reaches the requirement slot — measured, the body ran with an empty requirements frame. So TypeValue.type_value is BODY-LESS.
(2) A body-less spec op with no carrier member is refused at load ('backs no operation type_value ... no default on TypeValue, no own type_value on Boom'), and the loader CANNOT synthesize a per-carrier body (set_op_body_node takes only parsed source or a @[simp] rewrite). The remaining backing kind is a BUILTIN ON THE SPEC OP (BuiltinTag::TypeValueOf), which op_backed accepts and which covers every carrier at once — the PartialEq.eq route.
(3) THE DICTIONARY IS THE TYPE: Dictionary(sub0..subn-1, impl: S) names the head in impl and carries one sub per condition, so the answer is a walk of the evidence that selected the call — GHC's Typeable. eval/dictionary.rs's header states dictionaries are deliberately NOT interned, which answers 065 open question 4 for the EVIDENCE side.
(4) The derivation must run BEFORE THE TYPER: the typer resolves a call's requires against the provider relation, so a row asserted after it does not exist for the only reader that would use it. Measured — with the pass below the typer every call was refused 'no impl provides anthill.reflect.TypeValue' while the rows sat in the KB.

WHY type_value() IS THE HARD CASE: it is NULLARY. No argument and no receiver names the type, so WI-350's abstract-receiver fallback has nothing to resolve from and the dictionary is the ONLY carrier of the answer. That is what makes deferral mandatory and therefore a default body impossible.

ONE CORE CHANGE OUTSIDE THE FEATURE: a builtin receives no Frame (dispatch_resolved_operation calls it and drops the requirements expand_dispatching_dict just built), so Interpreter gained builtin_dispatch_dict — set and RESTORED around the builtin call, so a builtin that calls back into anthill sees its own dictionary in and the caller's out.

THREE FILTERS, each found by a failure, each with its measurement at its site: (a) a TYPE PARAMETER is not a carrier — SortInfo records 'sort M = ?' like any sort but its name term is a VARIABLE, so TypeValue[T = M] unified with every goal ('ambiguous among providers: Monad.M, DelayMonad.M, PartialEq'); (b) a SPEC is not a carrier — List provides Iterable, so a goal about List[T = Int64] reached Iterable's row by subsumption ('ambiguous among providers: PersistentCollection, FiniteCollection, IndexedSeq, Iterable, Iteration'); (c) the conditions DO NOT START AT SUB 0 — a provision's dictionary is the carrier's own sort-level requires first, conditions after, so Map (requires Eq[T = K]) would have handed back the Eq dictionary's impl sort as a type argument, silently.

DERIVED-ONLY REFUSAL: implemented, inside the derivation pass — the one moment the two populations are distinguishable, since it runs before a row is derived. It reads the PROVISION RELATION, not the three syntaxes that fill it. Provenance is RECORDED (kb.derived_type_value_carriers), not inferred from timing: reading 'everything present before I derive' is right in phase 1 and wrong in every later one because the rows persist — the WI-1103 hazard, which cost 126 failing tests before it was fixed. Deliberately NOT mark_derived_provision: self_supplied_entries reads that mark to decide a derived row adds NO dictionary slot, and these rows' conditions MUST become slots.

MIGRATION, 20 tests in 6 files, three genuinely different kinds: 17 were universal-row noise (TypeValue is derived for EVERY sort so it can never be what a fixture wrote — filtered inside the shared sort_provisions probe, with sort_provisions_all as the escape hatch); 1 was a CORRECT expectation change (Pair really does have a sixth conditioned provision, so provides_when answers 12 not 10); and 1 was A PRE-EXISTING BUG THIS EXPOSED — render_row printed the carrier through type_display_name (which has an arm for the BOTTOM type) and the provider through local_name_of, so they disagreed for exactly one sort, invisible until type_value_derive filed the first provision ever held at Nothing. Fixed at source via DefaultRow::provider_name.

SELF-REVIEW (/code-review high) found two of my own, both fixed: the already-provides guard called sort_provides per sort — a TRANSITIVE relation scan while provides_index is unbuilt, quadratic over a relation the loop is growing (eq_derive::total_composites memoizes for exactly this reason); and the refusal list sorted through format!('{:?}'), two String allocations per comparison.

STILL OPEN: (i) TRANSIENTS — type_of_dictionary builds the ANSWER with kb.alloc, which interns, and the parametric family is unbounded (065 open question 4). The evidence side is transient; the built type is not. fn_value is not the builder for it (it interns when children are leaves), so this needs a Value::Entity carrier and a check of every Type reader. (ii) PERFORMANCE — the suite ran 720s against a ~560-570s baseline before the quadratic fix; the re-measurement after it was still in flight at session end, so whether that scan was the whole cost is UNVERIFIED. Nothing consumes TypeValue until step 3 (N31XX), so paying a permanent load cost for it may argue for lazy derivation. (iii) MUTUAL RECURSION between two parametric sorts is not tested. (iv) CKD4J's two questions (a goal over a type EXPRESSION in a provision tail; a CYCLE through two conditional provisions) remain unanswered. (v) scaland testFull not run; docs (065 §7 step 2, kernel-language.md) not updated.

### 2026-09-20T07:48:25Z — feedback — claude

PERFORMANCE MEASURED — THE REGRESSION IS REAL AND NOT CLOSED. Full workspace via rustland/scripts/test.sh, same machine, all runs exit 0 / 0 failures:
  baseline before this ticket      ~560-570s
  with derivation, quadratic scan   720s   (+27%)
  with derivation, scan fixed       670s   (+18%)
So the O(n^2) sort_provides scan the self-review found was REAL but only about a THIRD of the added cost; ~100s remains and it is NOT in that loop. The residual is most likely VOLUME rather than a hot spot: every sort now carries a provision row, parametric ones carry ProvidesConditionInfo rows too, and the provider relation is read by many downstream passes — so everything touching it got slower.

RECOMMENDATION: do NOT commit as-is. An 18% permanent load regression across the workspace, for a capability NOTHING CONSUMES until step 3 (WI-20260919-N31XX), is a bad trade, and it is much harder to argue for removing once it is in and green.

THE LEVER: make the derivation LAZY / DEMAND-DRIVEN — derive a row only for sorts some `requires TypeValue[...]` can actually reach, instead of all ~200 up front. That is a design change to type_value_derive, not a rewrite, and step 3 is where the demand first appears, so the two fit together naturally. Note the ordering constraint this must respect: the pass has to run BEFORE the typer (the typer resolves a call's requires against the provider relation), so 'lazy' cannot mean 'on first dispatch' — it means deriving from the set of TypeValue requirements the typer is about to resolve.

THREE WAYS FORWARD, for the user to pick: (a) land now and file the perf as follow-on — fastest, everyone pays until someone picks it up; (b) make it lazy now — closes the regression before it ships, expands this change again; (c) hold the branch until N31XX needs it, so cost and benefit arrive together. Recommend (c) if N31XX is near, (b) otherwise.

ALSO GREEN THIS SESSION: scaland testFull 577 passed / 0 failed (a real 577, not a stale-server zero — sbt shutdown first). docs/proposals/065-type-value-requirement.md §7 step 2 updated with what was built, the three facts that forced the design, the three load-bearing exclusions, and that open question 4 is only HALF answered (the evidence is transient; the built Type still interns).

