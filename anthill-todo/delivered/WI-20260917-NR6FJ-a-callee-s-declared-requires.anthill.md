## Attributes

- id: WI-20260917-NR6FJ-a-callee-s-declared-requires
- created: 2026-09-17T05:07:35Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-17T08:09:06Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A CALLEE'S DECLARED `requires` OVER AN UNSATISFIABLE CONCRETE CARRIER IS IGNORED, and the call folds the spec's DEFAULT BODY and ANSWERS — where the identical demand written in the rule body correctly refuses to fire. Silent, and in the direction that produces a value.

MEASURED 2026-09-16 against HEAD, five rows, written up as 060-implementation §8.9's table. `Desc` declares `operation describe(x: T) -> Int64 = 1` (a DEFAULT body) and `Plain` provides NO `Desc`:

  I1  a rule inside `sort Holder { requires Desc[T = Plain] }`, body calls Desc.describe(plain(), ?r)   -> 1, the spec default
  I2  the same call with `requires(Desc[T = Plain])` written IN THE RULE BODY                            -> [], the guard DontFires
  I3  the same call, NOTHING declared anywhere                                                            -> 1
  I4  the same call through `operation viaop(x: Plain) -> Int64 requires Desc[T = Plain] = Desc.describe(x)`, the rule writing nothing -> 1
  I5  I4 with a carrier that DOES provide (`Rich provides Desc[T = Rich]`)                                -> 7, the provider's own implementation

THIS TICKET IS I4 ONLY. I1 ≡ I3 is a DIFFERENT question and it is settled: `check_rule_body_requirements`' own documented rule says a Horn rule does not inherit its enclosing sort's `requires` chain (that gates @[simp]/@[unfold] equations, not clause bodies), §8.9 re-measured it against HEAD and it is unchanged. Out of scope here, deliberately.

WHY I4 IS A DEFECT AND NOT A POLICY. The channel ALREADY refuses the undischargeable case in the shape one step over: `operation outer(b: Box) = pick(b)` where `pick` declares `requires Desc[T = x.E]` and `outer` declares nothing is a LOAD ERROR naming the receiver and the repair ('its carrier is a projection this call does not ground, and no `requires` of the caller names that same receiver'), driven by wi_s8cbv_projection_requirement_test::a_projection_the_caller_cannot_ground_is_refused_at_load_not_at_eval. So one unsatisfiable requirement is refused with a located sentence and another folds a default, and the difference is not one an author can see.

AND IT IS DECIDABLE AT LOAD, which is what makes the fold indefensible rather than merely unfortunate. `Plain` is a CONCRETE carrier: whether it provides `Desc` is a `sort_provides` question answered at load, and NO caller can change it — unlike a projection or a type variable, where the caller is exactly who supplies the instance (that case is S8CBV's and already refused). So a `requires` whose carrier binding names a concrete sort that does not provide the spec is unsatisfiable BY CONSTRUCTION at its own declaration site.

SHAPE OF THE FIX (a direction — verify before building). The provider side already has this check and its two diagnostics: `UnsatisfiedProviderRequires` and `ProvisionConditionsTooWeak` (WI-1033) walk a provider's requires chain and refuse where the carrier does not satisfy it, including the case where it provides only under conditions this provision's own conditions do not force. What is missing is the same question asked of an OPERATION's requires chain. Reuse those diagnostics rather than minting a third sentence for one situation.

THE CENSUS THAT DECIDES THE SIZE, and it must run FIRST: how many operation-level `requires` in stdlib, examples and anthill-todo bind a CONCRETE carrier that does not provide the spec? If any ship, they are either latent bugs of this exact kind or a use of the fold as a feature, and which one they are changes this ticket. 060-implementation §8.6 measured a comparable corpus question for rule-body requires and found the whole corpus contains none at all; nothing equivalent has been asked at the operation level.

ACCEPTANCE. I4's program is REFUSED at load, with a message naming the carrier, the spec, and that the carrier provides no such thing — never the spec default. CONTROLS, each stated at its site: I5 answers 7 (passes either way BY DESIGN — this must not disturb the case where the requirement CAN be met, which is the channel working); I2 still answers [] (the in-body guard is untouched); a requires over a PROJECTION or a type VARIABLE keeps today's behaviour, since there the caller is the one who supplies and S8CBV's caller_covers refusal already owns it; and a spec op with NO default body must be measured before and after — with nothing to fold, the call already fails, so the row that moves is the DEFAULTED one. Say which rows fail when the change is backed out and run each back-out with a patch that ASSERTS it applied. cargo-test green via scripts/test.sh.

## Changes

### 2026-09-17T07:13:19Z — feedback — user

ATTEMPT 2, ALSO NOT DELIVERED — but TWO HYPOTHESES ARE NOW DEAD with measurements, which is what a next attempt should not re-derive. Tree clean; work at stash@{0} and scratchpad/nr6fj-precheck-inert.diff.

THE MODEL IS SETTLED (user, 2026-09-17): a `requires` is an IMPLICIT PARAMETER — 'if we know an implementation of Spec[T] we can put it', which is `SupplySource`'s own documented reading ('the A dictionary is PASSED IN — an inbound slot the caller fills'). Three consequences, and the first two are already consistent with what ships: the DECLARATION is always legal (it opens a slot — wi840); the CALL is where it can fail (nothing to fill the slot), which is WI-1102's park and S8CBV's caller_covers; and THE BODY MUST READ THE SLOT rather than fold the spec's default. I4 fails on the third.

HYPOTHESIS A — REFUTED. 'The fold is a NAMESPACE-LEVEL blind spot, because the WI-239 defer-to-requirement pre-check is gated on `enclosing_sort`.' MEASURED: the identical program with the operation declared INSIDE A SORT also answers 1. Where the operation is declared is not the variable.

WHAT THE SAME MEASUREMENT DID ESTABLISH, and it is the sharpest statement of the defect so far: ONE DECLARATION MEANS TWO DIFFERENT THINGS depending on whether the spec op carries a DEFAULT BODY. `requires Desc[T = X]` + a BODY-LESS spec op dispatches through the slot (WI-20260909-S8CBV's `pick`, answering 7 and 9 per carrier); the same declaration + a DEFAULTED spec op folds the default (I4, answering 1). A defaulted op always RESOLVES, so dispatch never returns `Deferred` and the op-slot fallback below it never runs. The author's declaration loses to a default they did not ask for, and nothing says so.

HYPOTHESIS B — BUILT AND INERT. Give the op's own slots the same PRE-DISPATCH priority the enclosing sort's tree has: `find_requires_slot(kb, &subst, spec_sort, enclosing_requires, ...)` as an `.or()` beside the `find_requires_location` lookup, the same call the post-dispatch fallback already makes. Full workspace with it in: 7099 passed, 0 failed — and I4 STILL ANSWERS 1. Zero rows moved in either direction, so the branch cannot be driven and does not ship (this repo's own rule, and the third time today it has decided a diff).

SO THE NEXT QUESTION IS WHY THAT LOOKUP DECLINES: either `enclosing_requires` does not carry the operation's own slot at the point the pre-check runs (it is gated `!enclosing_requires.is_empty()`, so it is non-empty — but it may be the enclosing SORT's chain only), or `find_requires_slot` matches on bindings the call cannot satisfy (`T = Plain` against a carrier that provides nothing). Instrument THAT lookup first — one eprintln at typing.rs's WI-239 pre-check saying what `enclosing_requires` holds in viaop's body — before writing any more code. Both attempts so far were built on a mechanism read from source and neither survived its first measurement.

### 2026-09-17T07:18:05Z — feedback — user

THE 2x2 THAT REFRAMES THIS TICKET, measured 2026-09-17. The defect is NOT 'a decorative requires'. It is: A CALL WHOSE REQUIREMENT SLOT NOTHING CAN FILL IS NOT REFUSED, and what happens next depends on an irrelevance — whether the spec op happens to carry a default body.

  spec op     carrier provides    result
  body-less   yes                 7 / 9   correct, the slot is used (WI-20260909-S8CBV's pick)
  defaulted   yes                 7       correct, the provider's own impl
  defaulted   NO                  1       SILENT — the spec's default is folded, row I4
  body-less   NO                  ABORT   loads clean, then dies at run time

THE FOURTH CELL IS THE URGENT ONE and it is verbatim the failure S6 already refuses for the PROJECTION spelling: 'bridge_op_to_eval: internal evaluator error bridging viaop: DeferToRequirement: requirement param __req_desc not bound in caller frame (running viaop, requires-chain owner viaop; frame binds [])'. S8CBV's own words for it: 'it LOADED CLEAN and died DeferToRequirement ... raised as EvalError::Internal, which trips bridge_op_to_eval's debug_assert and ABORTS a debug build. Loading clean and aborting is the worst of the outcomes available here, so it is refused where it is written.' That refusal exists for `requires Desc[T = x.E]` and has NO counterpart for `requires Desc[T = Plain]` — a CONCRETE carrier that provides nothing.

SO THE ACCEPTANCE SHOULD BE RESTATED: refuse the CALL whose slot cannot be filled — no provision for the pinned concrete carrier and no caller forwarding a matching requires — exactly as caller_covers does one carrier-shape over. Not the declaration (wi840 refutes that), and not by making the default lose to the slot (that is a separate semantics question, and the abort cell shows the bug is present with no default in sight).

THREE MECHANISM HYPOTHESES ARE DEAD, each by its own measurement, and a next attempt should not re-derive them: (a) a namespace-level blind spot — the same program with the op inside a SORT also folds; (b) the WI-239 defer-to-requirement pre-check not consulting an op's own slots — extending it is INERT, full workspace 7099 passed and I4 unchanged; (c) the unique-impl arm above that pre-check pinning the spec default — instrumented, and NEITHER that arm NOR the pre-check is reached for this call at all. Whatever classifies `Desc.describe(x)` inside viaop's body is somewhere else in the typer; find it by instrumenting the CLASSIFICATION of that call node rather than by reading dispatch code, which is how all three of these were lost.

Tree clean. stash@{0} instrumentation, stash@{1} the inert pre-check extension, stash@{2} the load-sweep; diffs also at scratchpad/nr6fj-*.diff. Census remains clean (zero shipped programs affected).

### 2026-09-17T07:22:45Z — feedback — user

MECHANISM FOUND, and it is TWO DEFECTS with one cause. Instrumenting `classify()` — the single funnel every CallClass passes through — was the measurement that found it; three earlier attempts read dispatch code instead and each died on its first run. Trace, both cells of the unprovided-carrier column:

  BODY-LESS spec op:   CLASSIFY c.bl.noprov.Desc.describe => DeferToRequirement(slot=0)
  DEFAULTED spec op:   (no CLASSIFY line at all)

DEFECT A — THE ABORT, and it is unambiguous. The body-less case classifies CORRECTLY: the body defers to slot 0, exactly as the implicit-parameter model says it should. What is missing is that NOTHING CHECKS THE SLOT CAN BE FILLED. At run time the caller's frame binds nothing and `bridge_op_to_eval` raises `DeferToRequirement: requirement param __req_desc not bound in caller frame` — a debug-build ABORT from a program that type-checked. WHERE THE GAP IS, now measured twice from opposite directions: WI-1102's use-site discharge (`build_op_scoped_dicts`, typing.rs ~24710) parks exactly this condition — 'this call PINNED a carrier and the goal Spec[T = Carrier] has no provider' — but it is on the TYPED CALL SITE path. A call from a RULE BODY reaches the callee through `resolve_bridge_requirements` instead, which has no counterpart, so neither the park nor its drain ever runs (instrumented on this program: both silent). Note `op_body_reads_op_requirement_slot` WOULD answer true here — the classification IS DeferToRequirement at slot 0 — so the report machinery is ready and only the park is missing.

DEFECT B — THE SILENT FOLD (row I4). A spec op WITH a default body is never classified at all: it is an ordinary callable operation, so the call is resolved to the default statically and the enclosing `requires` slot is never consulted. That is why the author's declaration has no effect, and why the same declaration means one thing over a body-less op and another over a defaulted one.

A IS A BUG, B IS A SEMANTICS DECISION. A: a program that type-checks must not abort; refuse the call whose slot cannot be filled, mirroring S8CBV's caller_covers one carrier-shape over. B: does a declared `requires Spec[T = C]` outrank Spec's own DEFAULT body inside the declaring operation? The implicit-parameter reading says yes (the default is the fallback for when nothing was demanded). Deciding B does not block A, and A is the one with a crash behind it.

SUGGESTED SPLIT: take A as this ticket (call-site refusal on the rule->op edge, acceptance = the body-less + unprovided program is REFUSED at load instead of aborting, control = the providing carrier still answers 7 and the projection spelling is untouched), and file B separately as the default-vs-slot precedence question. Four attempts are parked: stash@{0} the classify trace, stash@{1} instrumentation, stash@{2} the inert pre-check extension, stash@{3} the load sweep; diffs at scratchpad/nr6fj-*.diff.

### 2026-09-17T07:34:57Z — feedback — user

THE MAP IS COMPLETE FOR DEFECT A, and the answer is that NOTHING CHECKS THIS CALL SHAPE AT ALL. Measured by instrumenting each step rather than reading it:

  1. the CALLEE's body classifies CORRECTLY — `CLASSIFY Desc.describe => DeferToRequirement(slot=0)`. The declared slot is read, exactly as the implicit-parameter model wants;
  2. the CALL SITE never builds op-scoped dictionaries — `build_op_scoped_dicts` is NEVER CALLED for `viaop` when the caller is a RULE BODY (instrumented at its first line: no output). WI-1102's use-site discharge lives INSIDE that function, so the park can never fire for this shape;
  3. at run time the bridge raises `EvalError::Internal` and `bridge_op_to_eval` aborts a debug build.

AND THE PARK'S RULE-BODY GATE IS NOT WHAT BLOCKS IT. `OpSlotParkSite::for_call` gates on `enclosing_op.is_some()`, whose stated justification is that a rule-body goal 'reaches eval through the SLD bridge, which resolves real provider dictionaries from the CONCRETE argument values at fire time and suspends when it cannot'. TWO MEASUREMENTS AGAINST THAT: (a) removing the gate costs NOTHING — full workspace 7099 passed, 0 failed, so its cited witness (`platform.needs_rebuild`'s `gt` over `Timestamp`) is covered by the sibling BUILTIN gate and the rule-body half is undriven; and (b) removing it does NOT fix the abort either, because of (2) above — the park is unreachable, not merely gated. The gate's premise is also false for this program: the bridge does not suspend, it aborts.

SO DEFECT A'S FIX IS ONE OF TWO PLACES, and choosing between them is the next decision:
  (i) WHATEVER TYPE-CHECKS A RULE-BODY CALL TO AN OPERATION gets the slot-fillability check `build_op_scoped_dicts` performs for operation-body call sites. Right place in principle (a load refusal, which is what the eval site's own WI-1102 comment asks for), but it means finding that path — four attempts have shown this control flow is not readable from source, so instrument first: print at every `classify()` for the CALLER's occurrence and see which arm takes `viaop(plain(), ?r)`.
  (ii) THE BRIDGE STOPS ABORTING. `eval.rs`'s `DeferToRequirement: requirement param ... not bound in caller frame` becomes a failed/suspended goal rather than `EvalError::Internal`. Smaller and strictly an improvement over a crash, but it makes the program answer NOTHING instead of naming the missing provision, and that site's own comment argues the refusal belongs at the call.

FIVE ATTEMPTS ARE PARKED (stash@{0}..{4}, diffs at scratchpad/nr6fj-*.diff). What every one of them has in common: it was designed by reading code and refuted by its first measurement. The instrument that finally worked was `classify()` — one funnel every variant passes through. Instrument the funnel, not the branch.

### 2026-09-17T07:36:48Z — feedback — user

ON THE RULE-BODY GATE, since 'removing it changes nothing' is easy to misread as 'it is dead code'. It is not dead; its POPULATION IS CURRENTLY EMPTY. `OpSlotParkSite::for_call`'s `enclosing_op.is_some()` only bites for a rule-body call that REACHES `build_op_scoped_dicts`, and no such call exists in the corpus today (measured: removing the gate moves ZERO of 7099 rows) — which is the same fact as 'the park is unreachable for this shape', seen from the other side.

THE CONSEQUENCE IS FOR FIX (i), AND IT MAKES THEM ONE CHANGE. Option (i) is exactly 'make a rule-body call reach that machinery'. The moment it does, this gate blocks it again — so whoever implements (i) must remove the gate in the same diff, and can now do so knowing it costs nothing today and that its stated premise is measured FALSE for this program (it claims the bridge 'suspends when it cannot'; the bridge aborts).

AND IT MUST NOT BE REMOVED ON ITS OWN, for the reason this repo keeps applying: with an empty population there is no row that moves either way, so the removal cannot be driven, and a change nothing can drive does not ship. It is a guard waiting for its population, not a branch to delete.

