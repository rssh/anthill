## Attributes

- id: WI-20260822-1TKN0-a-modify-p-target-is-not
- created: 2026-08-22T09:29:31Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T09:29:31Z

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

