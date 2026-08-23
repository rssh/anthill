## Attributes

- id: WI-20260822-1TKN0-a-modify-p-target-is-not
- created: 2026-08-22T09:29:31Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-23T09:42:25Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `Modify[p]` TARGET IS NOT COMPARED BY THE OVERRIDE ROW-REFINEMENT CHECK, so a provider can acquire a Modify the spec never granted. The effects-must-not-widen leg of the provides/override check (rustland/anthill-core/src/kb/typing.rs) refuses a NAMED effect loudly and lets a `Modify` target through.

MEASURED, while building the row-widening fixture for examples/guardians:

  sort Triage
    sort C = ?
    operation run(self: C, box: Mailbox, oracle: Oracle) -> Report
      effects {External, Model, Error}
  end

  sort WideRowTriage
    operation run(self: WideRowTriage, box: Mailbox, oracle: Oracle) -> Report
      effects {External, Model, Error, Modify[box]}      -- LOADS CLEAN
    provides Triage[C = WideRowTriage]
  end

CONTROL, and it is what makes this precise rather than 'the check does not work'. The SAME file with `Filesystem` (an ordinary declared effect sort) in place of `Modify[box]` is refused loudly:

  error: 'WideRowTriage' overrides 'Triage.run' but does not refine it: the override
         declares effect `Filesystem`, which is not covered by any effect the spec
         operation declares (effects must not widen)

So the widening rule fires; it just does not treat a `Modify` target as something to compare.

NOT DIAGNOSED, ONLY OBSERVED. Two candidate causes worth checking before assuming: (a) the leg is gated on `confident` -- both sides ground, `contains_type_param` false -- and a `Modify[p]` whose target is a PARAMETER may be failing that test and fail-opening, which is the documented conservative behaviour rather than a bug; (b) the `align` map rewrites the impl's parameter to the spec's, and if the two ops name the parameter identically no substitution happens, so the comparison should succeed and does not. Establishing which decides whether this is a defect or a deliberate fail-open that needs documenting.

WHY IT MATTERS. `Modify[r]` is the frame condition (kernel-language.md 5.6: for every resource not in the Modify set, Env_after = Env_before). A spec that grants no Modify is asserting the implementation changes nothing; a provider that can add one silently makes that assertion unenforced on exactly the axis 5.6 is about. Adjacent, and probably the same question: a `Modify[p]` target is not checked for `Modifiable[p]` either -- `Modify[pattern]` on a `pattern: String` parameter loads clean, measured separately.

ACCEPTANCE: the `Modify[box]` case above is refused with the same diagnostic the `Filesystem` case produces, OR the fail-open is confirmed deliberate and documented at the site with the reason. The `Filesystem` control must still be refused, and examples/guardians/agent/rejected/wide_row.anthill (which uses `Filesystem` precisely because `Modify` did not bite) still refused. Recorded as C9 in examples/guardians/docs/design/measured.md.

## Changes

### 2026-08-23T09:22:39Z — feedback — user

DIAGNOSED — AND NEITHER CANDIDATE CAUSE WAS RIGHT. Not the `confident` gate's groundness test (a) and not the parameter alignment (b). The gate read `matches!(e, Value::Term { .. })`: a CARRIER test standing in for an ABSTRACTNESS test. A denoted `Modify[c]` rides a `Value::Node` because it carries an occurrence, not because it is parametric, and the gate had no way to tell the two apart. (a) is close but names the wrong predicate -- `contains_type_param` never ran on the label at all, because it takes a `TermId` and the label is not one.

THE MEASUREMENT THIS TICKET DID NOT HAVE, and it is worse than the headline: THE FAIL-OPEN WAS ROW-WIDE. `confident` was an `all` over the whole effect row, so ONE `Modify[c]` disabled the widening check for every effect beside it. The ticket's own CONTROL is the witness: `Eff2` alone IS refused, and it went UNREPORTED the moment a `Modify[box]` sat next to it in the same row. So a provider could hide ANY capability widening behind one `Modify`, not just acquire a Modify. Driven by `wi347_override_refinement_test::a_modify_target_does_not_mask_a_named_effect_widening`.

A SECOND COMPARISON WAS ALSO NEVER RUN, and the ticket did not name it: the frame condition is PER RESOURCE. A spec granting `Modify[box]` is not granting `Modify[box2]` even where the two parameters have the SAME TYPE. That case loaded clean too and is now refused (`a_modify_on_a_resource_the_spec_did_not_name_is_refused`).

THE ALIGNMENT WAS THE OTHER HALF, and it was load-bearing for the STDLIB. `substitute_clause` no-ops on a `Value::Node`, so once the labels became comparable, an override restating the spec's own `Modify[c]` compared two DISTINCT symbols (`Stream.op.s` vs `FiniteStream.op.s`). MEASURED: without the Node arm, `MutableStack` over `MutableCollection.{new, insert, clear}` is refused and 19 of the wi347 file's 34 rows fall. `docs/design/spec-instance-dispatch.md` §"What about parametric effects?" already PRESCRIBED this ("both substitute to `{Modify[<actual-arg-sym>], Error}` and the check passes trivially") -- it had never been implemented, and the row-wide fail-open is why nobody noticed.

A THIRD READER APPEARED for `wants_result_alignment`, whose comment claimed "an op pair with no contract clauses can never read this entry". `Modify[result]` NAMES the binder, and `MutableStack.new` over `MutableCollection.new` is exactly such a pair. The gate now carries the effects leg's own driving condition.

WHAT IS DELIBERATELY LEFT OPEN, with a reason and an owner: a denoted PLACE facing a spec `Modify` over a resource TYPE (`Cell.set`'s `Modify[c]` refining `ModifyRuntime.set`'s `Modify[T = Cell]`). MEASURED: comparing it anyway refuses `Cell.set` and nothing else in the corpus, so the fail-open is currently load-bearing. That, and the `Modifiable[typeof(target)]` check this ticket also observed (which exists at NO site -- `is_modifiable_sort` has two readers, a reflect builtin and the WI-314 region masking, neither a load-time check), both want one relation: WI-20260823-39AD2.

