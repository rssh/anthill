## Attributes

- id: WI-20261025-7K84M-one-answer-to-which
- created: 2026-10-25T11:01:42Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-25T19:49:26Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

ONE ANSWER TO "WHICH IMPLEMENTATION RUNS THIS CALL" ON THE BODY-LESS PATH TOO — a spec operation with no default body still has its supplier chosen by readers with rules of their own, and the supplier matrix (docs/design/supplier-question-map.md) has 13 of its 112 programs contradicting kernel-language §8.7 (Operation override; Backing is executable; One carrier declaring one spec twice), every one of them body-less. Measured 2026-10-25 on d6a28558 and again on 1373e04f, after WI-20261025-ZAWX9 (3657c39d) gave the DEFAULTED path one answer: `resolve_op_target_at` reads the provider's suppliers over every route there, refuses a tie and narrows to what runs. Its two D-rows, the default over a binding and a silent tie through a dictionary, are gone for a defaulted operation.

WHAT IS LEFT (each program is a row of the map's matrix and of the family below):
  D1 — a supplier tie (the carrier's own member beside an instance binding) of a BODY-LESS operation runs the own member through a `requires` dictionary, both shapes; with no receiver the call by name does too (`Desc.name[T = Leaf]()` answers 2 where the tie is due).
  D3 — a body-less operation with no receiver, supplied by a binding alone, LOADS CLEAN AND DIES when called by name: `Desc.name[T = Leaf]()` over `Leaf provides Desc[T = Leaf, name = other]` exits 1 with `operation has no body: Desc.name`; through a dictionary it answers 3.
  D5 — a binding written in `namespace Leaf` does not back the body-less provision written in `Leaf`'s body: `backs no operation` on every route, where §8.7 merges agreeing provisions into one view and dispatch does (the defaulted twin answers 3 on every route).

MECHANISM, as read (not traced). `resolve_op_target_at`'s body-less branch is still the first-match chain `own.or_else(binding)`, with no tie (D1). `dispatch_spec_op_cached` pins a body-less call by name and reads no binding (apply.rs, its comment at the `instance_fact_op_binding` site says so); with a receiver eval re-dispatches by the value and recovers, with none nothing does (D3). The backing check reads one provision row's bindings (coherence.rs, `instance_fact_op_in_bindings(kb, &bindings, …)` for row `p`) (D5). The fork is the default itself: `op_body_node(spec_op).and_then(defaulted_spec_op_parent)` takes the new path, `lookup_spec_op_dispatch` (body-less only, 18 callers) the old one.

WHAT. The body-less path asks what the defaulted path now asks — the suppliers over the three routes, narrowed to what runs, one runs, two are a tie — so the default decides only what fills an empty set, as §8.7 says, and not which path a call takes. The call by name of a body-less operation pins its supplier as the defaulted one does, binding included. The backing check reads the merged provision view and refuses only "nothing runs". The per-application question of a dictionary is WI-20261025-MS797's; the rule-body route is proposal 068's (§3).

ACCEPTANCE: the generated family `f-supplier-routes` (rustland/anthill-core/tests/families/supplier_routes.rs): the exceptions it lists under this ticket cleared, each such cell at §8.7's answer, and no other verdict moved — D5's body-less `binding-both` rows, a refusal no property sees, move from `refused UnbackedProviderOperation` to `runs 3` in its verdict file; the full gate green; the families green on both carriers.

## Changes

### 2026-10-25T12:19:53Z — feedback — claude

Measured by the family's judge once it was narrowed to the receiver route (2026-10-25, 1373e04f): since WI-20261025-ZAWX9 a DEFAULTED tie through a dictionary is refused, but only when the call runs — `gen(leaf())` over `gen[A](x: A) requires Desc[T = A] = Desc.describe(x)` loads clean and dies `AmbiguousSpecOpDispatch` (both shapes), where the call by name refuses the same tie at load. §8.7 refuses a tie at load where the carrier is statically known, and `gen(leaf())` names `Leaf` at load. It is this ticket's question — who answers, and when — and is listed on the family under it (Sound and OneVerdict, default=defaulted, supplied=own+binding, route=dictionary).

### 2026-10-25T19:49:25Z — feedback — claude

Delivered (56059e50). One answer for both halves: resolve_op_target_at resolves a body-less operation through the provider's suppliers as it resolves a defaulted one (one runs, two are a tie; the default fills an empty set, and a body-less op with none answers the table's inherited row); instance_fact_op_binding deleted. The readers that answered it by rules of their own now ask it — resolve_at_goal's projection (D3: the binding pinned at load; D1 by name with no receiver: refused), the higher-kinded arm, resolve_nullary_result_carrier, Dictionary.ops (spec_op_backed_by) — and the backing check reads the provider's merged view (D5). Semantic equality keeps the table's answer in the projection: pinned to a provision's eq = loopEq, wi625's circular binding never returned. D1 through a dictionary: the user decided (2026-10-25) the tie is refused where the dictionary is resolved, at load — not at the provisions, since default provides chooses between providers but not between two texts of one — so a call that builds a dictionary from an instance whose provider supplies an operation of the spec twice is refused there, naming the requirement, whichever operation the callee dispatches and in an instance a condition resolved to; kernel-language §8.7 says so (wording approved by the user). Acceptance: family f-supplier-routes lists no exceptions, 13 verdicts moved and blessed; all families green on both carriers; gate 10882 passed, 0 failed; scaland testFull 766 passed. Rows: wi_7k84m_one_supplier_answer_test (13), back-outs K1-K7 and the equality clause measured in its header. Cost: a body-less dictionary dispatch about 0.85 us more, optimized (1.65 to 2.5 us). Found, not changed: a carrier's OWN circular eq member (eq(x, y) = PartialEq.eq(x, y)) still never returns, before and after — it is pinned at load as it always was.

### 2026-10-25T20:00:05Z — feedback — claude

Correction to the delivery note: a carrier's OWN circular eq member does return — it runs until the global step budget (`evaluation exceeded the step budget of 100000000`, about 9 s), where the probe that reported 'never returns' was cut off at 30 s under a concurrent gate. The asymmetry it belongs to is wider than the circular case — an own eq and a binding of it answer a reflexive call differently — and is filed as WI-20261025-TSYS6 (user, 2026-10-25).

