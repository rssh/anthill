## Attributes

- id: WI-20260917-NR6FJ-a-callee-s-declared-requires
- created: 2026-09-17T05:07:35Z

- status: Open
- status_agent: user
- status_at: 2026-09-17T05:07:35Z

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

