## Attributes

- id: WI-20260822-1MAGR-a-provision-s-member-signature
- created: 2026-08-22T22:11:19Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T22:11:19Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A PROVISION'S MEMBER SIGNATURE IS STILL UNCOMPARED — arity, parameter order, and the return type wherever no contract clause reads `result`.

STATE, and it is a deliberate one. `op_backed` matches a declared member by SHORT NAME ONLY. kernel-language.md's "Backing conformance is NOT checked beyond the name (WI-935, measured)" states it: `fact VectorSpace[BadVec, Float]` loads clean when `vec_add` takes one argument, when `vec_sub` returns `Float`, or when `vec_scale`'s parameters are swapped. Each then mis-dispatches or dies at the call.

WHAT 59CDQ CHANGED, AND WHAT IT DELIBERATELY DID NOT. `check_override_refinement` now compares the RETURN TYPE in exactly one place: where a `requires`/`ensures` clause MENTIONS `result`. That is not a general conformance check — it is the soundness condition of the result-binder alignment, which is what makes such a clause compare equal at all, and discharging `ensures P(result)` across two different return types promises P of a value of the wrong type. Everything else is untouched, and the two scope-control tests in wi347_override_refinement_test pin the boundary: a return-type mismatch no compared clause reads must still LOAD.

THE MACHINERY ALREADY EXISTS, AND ITS DOC SAYS WHY IT WAS NOT REUSED. `check_instance_fact_op_signatures` (rustland/anthill-core/src/kb/typing.rs) already does same param ARITY, contravariant PARAM types, covariant RETURN type, ground-gated with σ applied — for INSTANCE FACTS. Its own doc comment states the reason it is a separate pass: "A dedicated pass (not folded into check_override_refinement) so the carrier-own override path is untouched; instance facts have no stdlib presence yet, so this can be strict without regressing existing providers." So the obstacle is not the check; it is the unmeasured blast radius on the `provides` population. REGRESS MEANS REFUSE AT LOAD, not run slower: this pass emits `LoadError`s, so a provision that loads clean today and does not conform would stop the file loading at all. Instance facts could be checked strictly because nothing in the tree writes one — there was no population to break. The carrier-own path has the stdlib's provisions and every example behind it, and how many of those declare a member whose arity, parameter order or return type does not match the spec's is simply not known.

THE WORK IS THE MEASUREMENT FIRST. Run the instance-fact pass's per-op comparison over the CARRIER-OWN override path in report-only mode and count the population across stdlib, examples/, docs/measurements/ and the fixture corpus, BROKEN DOWN per failure kind (arity / parameter order / return type) and per carrier. A single count is not the answer: WI-935's own history is that one apparently-safe tightening moved an unrelated imported short name from 1 solution to 0 with no diagnostic. Only after that census is it decidable whether to enforce all three legs, enforce arity alone, or enforce with a documented exemption list.

DO NOT ASSUME THE THREE LEGS SHARE A VERDICT. Arity is always decidable and is the cheapest to enforce; parameter ORDER is decidable only when the types differ (two `Int64` params in either order are indistinguishable, so the check is a partial one and must say so); the RETURN type needs σ and fails open where the provision binds nothing to the spec's parameter — which 59CDQ measured as a live case, not a hypothetical.

ACCEPTANCE: the three WI-935 repros (`vec_add` at one argument, `vec_sub` returning `Float`, `vec_scale` with swapped parameters) are each refused naming the spec's declared shape and the member's, or each is documented as still admitted with the reason at the enforcement site; the census above is recorded in the ticket with its per-kind numbers; every stdlib/example provision either still loads or is named individually with its own reason; kernel-language.md's "Backing conformance is NOT checked beyond the name" paragraph is rewritten to what then actually holds, and the 59CDQ sentence appended to it is folded in rather than left beside a contradicting one; cargo-test green via rustland/scripts/test.sh.

SOURCE: WI-20260822-59CDQ, which asked whether the two are one ticket or two and answers TWO — its own change is the contract-discharge slice and stops there. WI-935 is Delivered and its statement is a measurement, not an open obligation, so nothing owned this until now.

