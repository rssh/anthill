## Attributes

- id: WI-20260919-HXGXF-proposal-065-step-2-derive
- created: 2026-09-19T15:19:32Z

- status: Open
- status_agent: user
- status_at: 2026-09-19T15:19:32Z

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

