## Attributes

- id: WI-20260831-RSRP5-the-three-sibling-per-label
- created: 2026-08-31T13:50:22Z

- status: Open
- status_agent: user
- status_at: 2026-08-31T13:50:22Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE THREE SIBLING PER-LABEL EFFECT GATES ARE BLIND THROUGH A PROJECTED ROW, the same blindness WI-20260830-APWM3 fixed in the fourth. `check_modify_targets`, `check_declared_row_contradiction` and `check_effect_registration` (all in `kb/typing.rs`) walk `all_operation_effects` and ask a question about LABELS, while the list they walk holds ELEMENTS. The two coincide only while every element is a bare label; they come apart at a projection, where `effects {llm.E, Error}` is two elements and, once `llm`'s type is CONCRETE, three labels.

WHAT EACH ADMITS TODAY (shapes, not yet driven — build the fixture first):

  * `check_modify_targets`: a carrier binding `provides Spec[E = {Modify[SomeSort]}]` puts a TYPE-targeted `Modify` into every caller's projected row, and no operation row names it literally, so the "a Modify target is a PLACE" refusal never fires.
  * `check_declared_row_contradiction`: `effects {llm.E, -External}` with `llm.E = {External}` is an uninhabitable `{External, -External}` and loads. NOTE THIS ONE HAS A DOCUMENTED STANCE TO OVERRIDE: its own doc says "An EMPTY substitution: this reads the row AS DECLARED. Anything an instantiation makes contradictory is WI-705's, at the call." Decide whether a projection off a CONCRETE PARAMETER is "as declared" (it is not a type-param instantiation) before widening it — that is a design call, not a mechanical edit.
  * `check_effect_registration`: a kind reachable only through a carrier's row binding is never tested against `fact Effect[T = K]`, so a misspelled label reads as a new effect.

`load.rs::check_macro_purity` reads the same facts with `effect_label_names_sort` and carries the same blindness; a macro with a projected row is far-fetched but it is the same population — census it, do not assume.

THE MECHANISM IS ALREADY BUILT AND SHARED: `typing::declared_row_labels_read_through` (private) eliminates each element's projections against that fact's own parameter types and flattens the resulting rows, over `op_info::all_operation_params_and_effects` (the PAIRED per-fact walk — params and effects cannot be zipped by symbol, since a spec op and its impl are two facts under one symbol). Wiring is ~3 lines per gate.

WHY IT WAS NOT DONE IN APWM3, stated so this is not read as an oversight: APWM3's change did not worsen these three, while it DID worsen `check_branch_external_exclusion` — closing the coverage gap admitted a `Branch × External` row that gate had been refusing by accident. That one had to move in the same commit; these three are pre-existing and each is load-BLOCKING, so widening them is its own corpus measurement.

ACCEPTANCE: one driven fixture per gate showing the shape ADMITTED before and REFUSED after, plus a control at `E = {}` (an empty projected row must stay clean), plus the full suite green. For `check_declared_row_contradiction`, the ticket is discharged by a recorded DECISION even if the answer is "leave it to WI-705" — but the decision must be written at the gate, not here.

## Changes

### 2026-08-31T14:24:22Z — feedback — user

READ THE SPEC BEFORE WIDENING `check_effect_registration` — IT EXEMPTS THE PROJECTION ON PURPOSE. `docs/kernel-language.md` §5.5, in the registration paragraph: "Positions that name no kind are not judged: a sort's declared effect row parameter while it is still a hole (`effects E = ?`, and the `effects E` that uses it), a RECEIVER PROJECTION (`s.E`), and a row variable the checker has opened."

So that bullet of this ticket is NOT straightforwardly a gap. The exemption's own justification is "positions that name NO KIND", which is true of `s.E` on an ABSTRACT receiver and FALSE on a concrete one — the sentence was written when the projection could not be read through at all. Whether the concrete case falls under the exemption's letter or only under its historical reach is the actual question, and answering it means editing that sentence either way, not just the code.

Found while adding §5.5's new "a row ELEMENT may be a projection" paragraph for WI-20260830-APWM3, which now states which rules ARE read through (coverage, `Branch × External`) and points at this ticket for the rest.

### 2026-08-31T14:37:47Z — feedback — user

SCOPE CORRECTION — THE `check_declared_row_contradiction` BULLET IS DELIVERED, AND THIS TICKET'S ORIGINAL RATIONALE WAS WRONG FOR IT.

This ticket said all three siblings could wait because "APWM3's change did not worsen them". /code-review measured that false for `check_declared_row_contradiction`: APWM3's flattening REMOVED an accidental refusal. `effects {llm.E, Error, -External}` at `llm: LiveLlm` had been caught one pass downstream — the op-effects coverage check could not match the incurred `External` against the un-flattened merge, fell to the denial arm, and reported a violated `-X`. Once the flattening made that match succeed, nothing caught it, and a body performing `External` under a row denying it LOADED CLEAN.

Fixed in APWM3's own commit, since a change that breaks a gate owns it. Two things were needed, and the second was a latent bug of the gate's own:

  1. `eliminate_declared_row_projections` (the elimination half of `declared_row_labels_read_through`) runs before the gate's classification.
  2. Its hand-written `row_shaped` list read the LOCAL name and spelled the wrapper `"effects_rows"` — the `effects_rows` wrapper's local name is `EffectsRows`. So a WRAPPED row matched no arm, was not a TYPE head either, and contributed NOTHING in silence. Latent while every element was written bare; live the moment elimination began producing wrapped rows. It now uses the shared `effect_value_is_row_shaped`, which reads the QUALIFIED functor.

The gate's "AS DECLARED / empty substitution" stance was NOT breached and needed no renegotiation: that stance is about a type-parameter INSTANTIATION, which arrives at a call and is WI-705's. A receiver projection reads the type a parameter is DECLARED with, in the same signature.

REMAINING SCOPE IS TWO GATES, not three: `check_modify_targets` and `check_effect_registration`. The spec-exemption note in the earlier feedback applies to the registration one only.

