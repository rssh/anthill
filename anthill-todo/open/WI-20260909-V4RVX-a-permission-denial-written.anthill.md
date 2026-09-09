## Attributes

- id: WI-20260909-V4RVX-a-permission-denial-written
- created: 2026-09-09T08:11:32Z

- status: Open
- status_agent: user
- status_at: 2026-09-09T08:11:32Z

- acceptance: cargo-test

- tags: typing

## Description

A `-Permission` DENIAL WRITTEN OVER A BOUND TYPE PARAMETER IS UNTESTED, AND ITS ENTAILMENT LEG STILL BAILS -- proposal 064's downward-closed denial is the security-relevant half of `Permission`, and the variable spelling has no coverage.

WHAT WI-9WVT7 ALREADY FIXED, so this ticket starts from the right line. Before it, `validate_callback_effect_row` deep-resolved neither list, so a denial whose capability is a call-site-bound type parameter never matched the label it denies. MEASURED then: `wrap[Eff, C](cap: C, body: () -> Int64 @ {Eff, -Permission[C]})` at `C := Llm`, applied to a body acquiring `Permission[Llm]`, NEVER REACHED the lacks check -- it died later on an unconstrained tail. That is now refused, exactly as the concrete `-Permission[Llm]` twin always was, because that ticket walks `e_absent` through the substitution beside the present lists.

WHAT IS STILL OPEN, and it is the ENTAILMENT leg rather than the exact match. `permission_entails` (rustland/anthill-core/src/kb/typing.rs) is the rule that makes a denial DOWNWARD-CLOSED -- `-Permission[Y]` forbids `Permission[X]` for every `X <: Y`, which permission.anthill's header calls out as the rule that "needed a rule of its own" and whose absence "is exactly the escalation that makes `-Permission[Model]` worth writing". It ends:

    if view_contains_type_param(kb, &p_arg) || view_contains_type_param(kb, &a_arg) {
        return false;
    }

so a capability argument containing a type parameter DECIDES NOTHING. For the anonymous `-Permission[?]` that is deliberate and documented ("an undecided argument leaves the pair undecided"). For a denial over a parameter the call site has BOUND to a real capability it is a different case, and the bail does not distinguish them.

AND ITS CALLERS STILL READ SHALLOW. `permission_entails` is reached from `label_violates_absence` / `row_self_contradiction`, which compare through `walk_value_to_resolved` -- a TOP-LEVEL variable chase that does not descend into an `Fn`'s arguments. WI-9WVT7 resolved the labels at ONE consumer (`validate_callback_effect_row`); these other consumers were left, so a resolved capability argument does not reach them either. Reported as a code-path reading (from /code-review on the WI-9WVT7 diff), NOT driven: building the fixture is this ticket's first step, and if the shape turns out unreachable say so and close, with the reason written at `permission_entails`.

NO TEST COVERS THE VARIABLE SPELLING. Measured over `wi_cbrsw_permission_effect_test.rs`: the denials written there are `-Permission[Model]` (11), `-Permission[AdminFs]` (1) and `-Permission[?]` (1). The first two are CONCRETE; the third is the deliberately-inert anonymous one. Nothing pins a denial over a BOUND parameter, which is why WI-9WVT7 could repair a real hole in that mechanism without a single `Permission` row going red -- the repair was caught by a fixture in another ticket's file.

ACCEPTANCE: a driven escalation fixture in `wi_cbrsw_permission_effect_test.rs` -- `-Permission[C]` at `C := Model` against a body acquiring `Permission[GptModel]` where `GptModel <: Model` -- answering per the decision, with the CONCRETE `-Permission[Model]` twin as the control and the anonymous `-Permission[?]` row pinned as still inert; whichever way `permission_entails`' type-param bail is settled, its reason is written at the site; full workspace green via rustland/scripts/test.sh.

REFERENCE: WI-CBRSW (the effect and its entailment rule), proposal 064, WI-9WVT7 (the `e_absent` resolve and the measurement above), stdlib/anthill/prelude/permission.anthill (the header that states both directions).

