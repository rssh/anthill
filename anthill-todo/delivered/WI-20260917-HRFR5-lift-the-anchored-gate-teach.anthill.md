## Attributes

- id: WI-20260917-HRFR5-lift-the-anchored-gate-teach
- created: 2026-09-17T05:05:36Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-17T05:54:31Z

- acceptance: cargo-test, scaland-sbt-test

- tags: vvm1r

## Description

LIFT THE ANCHORED GATE — teach the WITNESS path to attribute a `require` by its ROOT, so two `require`s on one spec are admitted however they were grounded. Today they are admitted only where EVERY one of them was grounded by a TYPED HEAD ANCHOR: the gate is `if !found.anchored || !*prev_anchored` (typing.rs:72587) over `GroundedRequirement::anchored` (typing.rs:74306), and where one was grounded by a body call instead the clause is refused — 'at most one `require` on spec X per rule, unless every one of them is grounded by a TYPED HEAD BINDING … one of them is grounded by a body call instead, and a witness is chosen by scan order, so the written bracket cannot say which dictionary this is'. WI-20260909-S8CBV named this as one of three things its attribution would remove; the other two are REFUTED (see below) and this one is the survivor, and it is a BUILD rather than a deletion.

WHY THE GATE EXISTS, and it is not caution. The ANCHOR path is the only place the written bracket is READ — reading it is what chooses the head binding. On the WITNESS path the bracket is never consulted at all: the witness is picked by SCAN ORDER (`anchor_grounding` is consulted LAST, after four witness scans), so two `require`s there would bind whatever the scan reached first. The hazard is measured and recorded at the gate's own site: a BODY-LESS spec op is never a covered call (`collect_covered_calls` gates on `functional_relation_arity`), so `weaves` stays empty, the one-dictionary-per-call refusal never fires, and `?d1 = require[PartialEq[T = Thing]], ?d2 = require[PartialEq[T = Gadget]], eq(?a, ?b)` LOADS CLEAN with BOTH bound to Thing's dictionary. Five shapes, every one of them 'HEAD refused loudly, this answers wrongly'. Lifting the gate without giving the witness path an attribution is exactly that regression.

SIZED BY MEASUREMENT 2026-09-16, and it is small: backing the gate out (`if false`) against the full wi_tests fails EXACTLY ONE row — `wi_96ztm_two_dictionaries_test::a_witness_grounded_pair_is_refused_whatever_the_bracket_says` — out of 4707. So the gate guards precisely one shape and nothing else in the suite depends on it. (The sibling back-outs, for contrast: S4's written-bracket selector fails 4 rows and the >1-anchor refusal fails 6, which is why those two are NOT removable and this one is the only live thread.)

THE SHAPE OF THE FIX, S8CBV's own sentence: match the `require`'s named ROOT against the WITNESS CALL's carrier argument — which is the thing scan order currently decides. Two facts make this smaller than it was when S8CBV wrote it. (1) The projected path ALREADY attributes by root and is driven (commit 9c53f205, four rows in wi_s8cbv_projection_requirement_test): `x.E` and `y.E` δ-ground to their roots' ELEMENTS and the fetch keys on the carried type, so the attribution mechanism exists and needs porting, not inventing. (2) THE COMPARISON IS ALREADY SETTLED and needs no `unify_types` ζ arm: the duplicate-require refusal in this same function uses `views_structurally_equal`, 'the codebase's own route for spec-value equality — NOT a hand-rolled key', after a hand-rolled one compared `Desc[T = Box[E = Leaf]]` equal to `Desc[T = Box[E = Other]]`. δ grounds the roots to concrete carriers before any comparison runs.

ACCEPTANCE. A clause with two `require`s on ONE spec where at least one is WITNESS-grounded LOADS and THREADS, each call dispatching through the dictionary its own carrier names, asserted BY VALUE — two different numbers from one clause, with the spec op BODY-LESS so no default can stand in and nothing can value-dispatch.

CONTROLS, each stated at its site. The five shapes named at the gate must be driven, not argued: in particular `?d1 = require[PartialEq[T = Thing]], ?d2 = require[PartialEq[T = Gadget]], eq(?a, ?b)` must NOT load clean with both bound to Thing's dictionary — that is the exact regression a naive lift ships, and a body-less spec op is how it hides (no covered call ⇒ no weave ⇒ the one-dictionary-per-call refusal never fires). A witness call whose carrier matches NEITHER root must still be REFUSED, and `a_witness_grounded_pair_is_refused_whatever_the_bracket_says` must be re-aimed at that case rather than deleted — it is the only row the gate holds up, so deleting it would retire the coverage along with the gate. The anchor-grounded pair answers exactly as today (passes either way by design). Say which rows fail per back-out and run each back-out with a patch that ASSERTS it applied. cargo-test green via scripts/test.sh.

