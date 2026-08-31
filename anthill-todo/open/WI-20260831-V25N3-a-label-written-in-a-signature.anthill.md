## Attributes

- id: WI-20260831-V25N3-a-label-written-in-a-signature
- created: 2026-08-31T16:49:50Z

- status: Open
- status_agent: user
- status_at: 2026-08-31T16:49:50Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A LABEL WRITTEN IN A SIGNATURE'S ROW TYPE-ARGUMENT IS JUDGED BY NOTHING — route C of WI-20260831-RSRP5's census.

RSRP5 established that an effect label is judged where the ROW is written, and closed two of the three routes there: a carrier's `provides Spec[E = {…}]` binding (`check_provision_row_bindings`) and a sort's bound alias `effects E = K`. The third — a row written as a TYPE ARGUMENT in a signature, `operation ask(s: Spec[E = {…}], …)` — has no gate at all.

MEASURED, both spellings loading CLEAN:

    operation ask(s: Spec[E = {Beep}], p: String) -> Out
      effects {s.E, Error} = Spec.go(s, p)              -- Beep is no registered Effect kind

    operation ask(s: Spec[E = {Modify[Thing]}], p: String) -> Out
      effects {s.E, Error} = Spec.go(s, p)              -- a TYPE-targeted Modify (§5.6)

The identical labels are REFUSED in an operation's own row and in a `provides` binding.

PRE-EXISTING, NOT OPENED BY WI-20260831-PYNS2, and that is measured rather than assumed: the same hole is drivable on the guardians `Llm` — `operation ask(m: Llm[E = {Error, LlmOutput}], p: Prompt) effects {m.E, Error} = Llm.complete(m, p)` loads clean today, and did before PYNS2, because `Llm` has two carriers and the route was already reachable there. PYNS2 widened WHICH specs the shape works on (one with no carrier yet); it did not create the gap.

WHY IT MATTERS. §5.5 now claims a row element is judged ONCE, AT ITS ORIGIN, so that a projection can be exempt. That claim is false for this origin, and every operation projecting `s.E` inherits an unjudged label — a misspelled kind reads as a new effect exactly as RSRP5 describes.

THE POPULATION IS THE WORK, and it is why this is not inline in PYNS2. `check_provision_row_bindings` walks `all_provisions`; this one has to census every TYPE POSITION where a spec application can bind a row parameter, not just a parameter's type — at minimum: an operation's parameter types and return type (`all_operation_params_and_effects` reaches both), an entity FIELD's type, a sort's own type-param binding, and a `requires Spec[E = {…}]` clause. Enumerate the producers before writing the gate; a list drawn from this ticket's two examples will be short (WI-20260830-APXSS).

The judging half is already built and shared: `effect_element_labels` + `classify_modify_target` + `registered_effect_kinds`, exactly as `check_provision_row_bindings` composes them, with the same per-slot dedup key and a message naming the written slot.

ACCEPTANCE: both fixtures above REFUSED, each naming the slot as written; a benign `E = {Error}` control that must still load; a control at a TYPE parameter binding (`Spec[C = Int64]`) that must NOT be read as an effect row (RSRP5's `a_type_parameter_binding_is_not_read_as_an_effect_row`, at the new site); and the census of type positions recorded, with a driven fixture per position covered and a named reason per position not.

