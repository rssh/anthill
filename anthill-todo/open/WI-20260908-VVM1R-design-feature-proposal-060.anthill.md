## Attributes

- id: WI-20260908-VVM1R-design-feature-proposal-060
- created: 2026-09-08T10:22:01Z

- status: Open
- status_agent: user
- status_at: 2026-09-08T10:22:01Z

- acceptance: cargo-test

## Description

DESIGN + FEATURE: proposal 060 sec 3 -- make a TYPED HEAD BINDING the second ANCHOR for the requirement channel, so a clause's require[Spec[T]] is grounded by `?x: T` on its head instead of by a covered witness call. The LAST unowned section of proposal 060: WI-1040 delivered sec 1, WI-742 delivered sec 2 / sec 2.1 / the C666A relaxation, WI-743 owns sec 2.2. Design, mechanism sketch and measurements: docs/design/060-implementation.md sec 8 -- read it first; this ticket deliberately does not restate it.

THE DRIVING SURFACE, refused today: `rule anchored(?x: Colour, ?d) :- ?d = require[Desc[T = Colour]], seed(?x)` where `Colour provides Desc` and NO body call reaches a Desc operation. Measured 2026-09-08 (after WI-742 landed, so the typed head itself now loads): it reports `expected a body call to one of Desc's operations ... to ground the requirement, got no such call in the rule body` -- the same error its UNTYPED twin reports, so the annotation buys nothing here yet. requirement-channel.md's "The anchor rule" already names both anchors and already names this as the second one's owner; what is missing is the reader.

WHY IT IS NOT ONE DISJUNCT AT THE REFUSAL (measured, and the reason this is its own ticket rather than WI-742 residue). The refusal lives in record_find_dictionary_grounding, but the refusal is not the mechanism: the rewritten goal is find_dictionary(spec_base, op_functor, witness_args...) and EVERY consumer below it is keyed on that op_functor -- simp_guard_holds_core reads the op's params to learn which argument positions carry the spec (param_is_spec_carrier / spec_self_represented_by, WI-596's TWO SHAPES), and witness_sort_goal reads the same signature to learn which spec PARAMETER each argument's carried type binds. A typed head has no op.

AND THE SURFACE HAS ALREADY THROWN AWAY WHAT WOULD REPLACE IT. The author writes require[Desc[T = Colour]], which NAMES the binding, but the converter STRIPS a spec's type arguments at the guard tier -- record_find_dictionary_grounding's own note says so, and it is why two `requires` on one spec base are refused as unattributable. NOTE THE STALE CITATION AT THAT SITE: it calls the repair "Tier B (WI-613)", WI-613 is DELIVERED, and both the strip and its refusal are still live -- so retaining the bracket currently has NO OWNER. Do not open this ticket by declaring a dependency on WI-613 and waiting; re-read the comment.

SHAPE OF THE FIX (a direction, not a diagnosis -- verify before building). The grounding is STATIC: the bound is a TermId at load, so sort_provides(bound_sort, spec_sort) is decidable at typing, which is proposal 060's own rule (selection happens in the typing pass) and a STRONGER position than the witness path rather than a weaker one. What is needed beside it is a carrier-to-parameter map that does not come from an op, and WI-596's two shapes answer that differently: a SELF-REPRESENTING spec (Set, Map, List) names its carrier by the SORT, so the bound maps straight onto it; a CARRIER-PARAMETER typeclass (Eq, Numeric) names it by a type-parameter, which is exactly what the stripped bracket would have said. Two viable routes, each needing its own measurement: (a) settle type-argument RETENTION first and read the attribution off the written bracket; (b) restrict the first cut to the self-representing shape and SAY SO at the site, leaving the typeclass shape refused with a located error rather than silently ungrounded. A SYNTHETIC WITNESS (borrow some spec op purely to locate the carrier slot) is a third route and the one to be most careful with: it raises WHICH op stands in (the choice must not change the answer), what fills its CONTENT parameter positions (passing the carrier there would bind content params to the carrier's type), and how WI-860's supplied-vs-derived agreement reads against a dictionary derived that way.

ACCEPTANCE. The driving surface above LOADS and THREADS -- the covered call dispatches through the dictionary the annotation grounded, asserted by VALUE and not by a clean load. CONTROLS, each stated at its test site: the UNTYPED twin of the same clause stays refused (this is what says the ANNOTATION is what grounds it, and it must pass either way under the WI-742 half alone); a typed head whose bound does NOT provide the spec stays refused; and a clause that has BOTH a typed head and a covered witness call keeps answering exactly as it does today (the witness path is not displaced). If route (b) is taken, a carrier-parameter-shaped spec must produce a LOCATED refusal naming the shape, never a silent non-grounding. Say at the test sites which rows fail when the anchor recognition is backed out, and which pass either way by design. cargo-test green via scripts/test.sh.

