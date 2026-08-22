## Attributes

- id: WI-20260822-59CDQ-contract-refinement-matches
- created: 2026-08-22T10:27:54Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-22T23:12:04Z

- acceptance: cargo-test

## Description

CONTRACT REFINEMENT MATCHES `ensures P(result)` ACROSS OPERATIONS WHOSE RETURN TYPES ARE NEVER COMPARED. `check_override_refinement` (rustland/anthill-core/src/kb/typing.rs) compares an override's contract clauses against the spec's structurally, and never reads `return_type`. kernel-language.md:3796 says so outright, as a measured statement about the pass: "Arity, return type and parameter order are not compared against the spec's declaration in either direction, and `check_override_refinement` compares only the effect row". `check_instance_fact_op_signatures` is a SEPARATE pass, written explicitly so the carrier-own override path is untouched.

WHY THIS IS NOW REACHABLE AND WAS NOT BEFORE. Until the result binder was aligned (same file, the `align` map, fixing the C8 false refusal), NO clause mentioning `result` could ever compare equal -- the spec's `<spec op>.result` and the override's `<impl op>.result` are distinct symbols, so every such clause mismatched and every provider of an `ensures`-carrying spec op was refused. That unconditional refusal was ACCIDENTALLY PLUGGING this hole: nothing could be discharged, so nothing could be discharged wrongly. Aligning the binder is the first thing that lets a result clause be discharged, and it discharges it against an unchecked return type.

SHAPE OF THE DEFECT:

  sort Sp
    sort T = ?
    operation op(x: T) -> Report
      ensures mentions_all(result)
  end

  sort Carrier
    operation op(x: Carrier) -> Int64
      ensures mentions_all(result) = 0
    provides Sp[T = Carrier]
  end

Both clauses normalize to `mentions_all(Ref(Sp.op.result))`, `views_structurally_equal` returns true, and the override loads clean -- promising `mentions_all` of an `Int64` where the spec promised it of a `Report`.

NOT MEASURED. This is read off the pass and off 3796, from the /code-review sweep of 2026-08-22; the repro above has not been run. Establishing whether it actually loads is step one, and if it does not, finding out what refuses it is just as useful -- because then 3796 is stale.

RELATED, AND POSSIBLY THE SAME FIX: WI-935 is the same gap one level up (a provision certifies that a member of that NAME exists, not that it FITS -- arity, parameter order and return type all uncompared). A return-type comparison added for this ticket would cover part of WI-935's scope; deciding whether the two are one ticket or two is part of the work.

A SECOND, INDEPENDENT REASON THE CLAUSES ARE NOT TRUSTWORTHY: a contract clause's PREDICATE NAME is never resolved at load. Measured in the same sweep: replacing `ensures mentions_all(result)` with `ensures totally_bogus_predicate(result)` in examples/guardians/agent/good.anthill loads byte-identically. So an unresolved functor compares equal to another unresolved functor of the same spelling and unequal to everything else, with no diagnostic either way -- which means the refinement check can both accept and refuse on names that denote nothing. Worth fixing alongside, since it decides what "structurally equal" is even quantifying over.

ACCEPTANCE: the Sp/Carrier repro above is refused with a diagnostic naming both return types, OR it is confirmed already refused and kernel-language.md:3796 is corrected. A verbatim override of an `ensures`-carrying spec op whose return type DOES match must still load (the C8 case), and a genuinely weaker postcondition must still be refused. An `ensures` naming an undeclared predicate is a load error, or the reason it is not is documented at the site.

## Changes

### 2026-08-22T23:11:48Z — feedback — user

DELIVERED. The ticket's own repro was ALREADY REFUSED, and that was not the answer -- the case it could not see was the one that loaded clean.

WHAT WAS MEASURED FIRST, because the ticket said "NOT MEASURED" and it was right to.
  probe A  the ticket's repro verbatim (spec -> Report GROUND, impl -> Int64): REFUSED, but as
           "it weakens the postcondition" -- a message naming the clause the author wrote
           correctly instead of the signature that makes it undischargeable. The `demonstrably_differ`
           guard added in 266245d7 was already catching it.
  probe B  spec returns its own TYPE PARAMETER (`op(x: T) -> T`), provision binds `T = Carrier`,
           impl returns `Int64`: LOADS CLEAN, zero errors. This is the live hole, and the
           parametric shape is the ORDINARY one -- so the guard 266245d7 shipped was covering the
           rarer half.
  probe C  `ensures totally_bogus_predicate(result)`: loads clean. Confirmed.
  probe D  the parametric CONTROL (spec -> T, impl -> Carrier): loads clean, correctly.

WHY B LOADED, and it is not what the guard's own comment claimed ("a σ story this pass does not
have"). The pass HAS σ and applies it. It keyed σ on the RAW provision binding key instead of the
RESOLVED spec-param symbol, so `substitute_impl_params_alloc`'s Symbol-equality match was a SILENT
NO-OP -- instrumented: the key was Symbol(2626) where the spec's return type held Symbol(2563).
That is verbatim the hazard WI-431 (B) documents ON `type_param_sym_of_binding`, and the two sibling
σ sites (`check_instance_fact_op_signatures`, `requires_shadow_is_confusable`) both already route
through it with a comment saying why. `check_override_refinement` was the one outlier. Fixing the
keying makes the parametric case DECIDABLE and probe B refuse; probe D still loads. Zero blast
radius on the effects leg, which shares σ (3335 wi_tests green).

THE GUARD'S CONDITION IS THE DISCHARGE, NOT "A CLAUSE MENTIONS result". Three cases separate only
under that reading and each wants a different message: spec P(result)/impl P(result) is discharged
by the alignment alone, so the return types decide and are named; spec P(x)/impl P(x) matches with
or without the binder, so a differing return type is the general signature question this pass does
not ask; spec P(x)/impl P(result) matches under neither, so the override genuinely weakens the
postcondition and naming the return types would send the author to a line whose repair would not
load. The test is run by RUNNING the legs' own comparison twice (with and without the binder entry),
not by a hand-written "does this clause mention result" walk -- which would both drift from
`substitute_impl_params_alloc` and answer the wrong question. Comparison is COVARIANT
(`types_compatible(impl_ret, spec_ret)`), driven by a carrier that provides the spec's return sort.

THE SECOND HALF -- an unresolved predicate name in a contract clause -- IS NOW A LOAD ERROR, not a
documented gap. `check_contract_clause_goals` (kb/load.rs), the contract-clause peer of WI-1034's
`check_rule_body_goals`, located at the operation's declaration site. It re-spells none of the three
authorities it needs: `clause_conjuncts` for the `conjunction(...)` wrapper, `undefined_query_goal_functors`
for the head test and connective descent, `op_decl_sites_iter` for the population and the span.
kernel-language.md §5.3 now names the contract clause as the third goal position.

THE CENSUS SAID ZERO AND THE POPULATION WAS NOT ZERO. Measured across stdlib and every .anthill
project with a positive control that fired: 0 undeclared contract names. The full suite then found
one -- `wi618_bare_arrow_logic_test`'s placeholder `mentions`, a fixture written inline in RUST,
where no .anthill census could reach it. It now carries a rule and that file says why. (Same lesson
as WI-061: a feature's population includes the test fixtures.)

/code-review FOUND THE READER I DID NOT MEASURE, and it was the important one. σ has TWO readers and
I had a fixture for one. The EFFECTS-subset leg gates on the σ-substituted spec row being GROUND, so
while σ no-opped a spec op whose row names a spec type parameter (`effects E`, provision
`fact Sp[T = Carrier, E = Eff1]`) stayed parametric and the leg FAIL-OPENED. Measured both ways: an
override raising an unrelated `Eff2` loaded with ZERO errors before, is refused now. Pinned by
`a_sigma_bound_effect_row_is_compared` plus a control that passes either way by design. This is the
"reusing a shared source when it answers two questions" defect, and the census rule that catches it
is per READER, not per method.

FIVE MORE REVIEW FINDINGS, all real, all fixed:
  * the return-type refusal `continue`d past the contract legs, so an override that ALSO strengthened
    a precondition reported one defect and revealed the second only after a reload. It now reports
    beside them, with the binder still ALIGNED so the `result` clause does not also read as weakened
    -- which is the double-report this error exists to replace. Test: two defects, one load.
  * `wants_result_alignment` read the RAW `requires` list, into which the loader injects an
    `EffectsRuntime[Effects = E]` clause per free row variable -- so the gate opened for every
    effect-polymorphic override and its own cost sentence ("~146 provisions") was false. Now asks
    `user_precondition_clauses`' predicate, which is what the leg it gates actually drives on.
  * the dedup was keyed on the functor alone, so one misspelling written in BOTH clause lists of one
    operation reported once. Both report at the same declaration span, so the clause kind is the only
    thing telling them apart; keyed on it now, with a test.
  * two silent `continue`s in the new pass. A missing `OperationInfo` is now a debug_assert (measured
    zero over 378 operations); a `Value::Node` conjunct now gets the carrier-neutral HEAD test its
    `Term` sibling is built on instead of being skipped whole.
  * a stale fixture path in a doc comment.

WHAT NOTHING DRIVES, said rather than credited to a neighbour: the `Value::Node` arm above. Zero such
conjuncts exist in the corpus -- `denoted` reaches an EFFECT label and no contract clause in the tree
carries one -- so the arm mirrors its sibling's authority and a comment at the site is the record.

BACK-OUTS MEASURED, NOT PREDICTED -- ten mutations applied and re-run, recorded at the test site:
  σ raw key                       -> 2 tests         return-type guard off        -> 3
  "mentions" not "discharges"     -> 1                that widened to any aligned symbol -> 2
  equality not `<:`               -> 1                contract-name pass off       -> 3
  the refusal `continue`ing       -> 1                dedup by functor alone       -> 1
  wants_result_alignment widened  -> NOTHING alone; needs the "mentions" back-out too, and the
                                     ground gate likewise flips NOTHING alone -- with the σ back-out
                                     it takes four, including the C8 case. Those pairs are the only
                                     evidence either guard has, and are why neither is deleted as dead.

WI-935 IS THE OTHER TICKET, NOT THE SAME ONE. It is Delivered; its "backing conformance is NOT
checked beyond the name" is a measurement, not an open obligation, so the general check had no
owner. Filed as WI-20260822-1MAGR, with the reason it is a ticket and not an inline change: the
machinery already exists (`check_instance_fact_op_signatures` does arity, contravariant params,
covariant return for INSTANCE FACTS) and is a separate pass precisely because its own doc says
turning it on for the carrier-own path would regress existing providers -- by an unmeasured amount.
This change took only the slice contract discharge depends on, and two scope-control tests pin the
boundary: a return-type mismatch no compared clause reads must still LOAD.

SPEC: kernel-language.md's §8.7 "the requires/ensures check is a planned follow-up" was stale (the
legs have existed since WI-347) and "check_override_refinement compares only the effect row" was
stale twice over. Both rewritten. examples/guardians/docs/design/measured.md C8 records the
narrowing, including that C8's unconditional refusal had been accidentally plugging this hole.

TESTS: 24 in wi347_override_refinement_test (was 12). Full workspace green via
rustland/scripts/test.sh -- 5556 passed, 0 failed, 36 suites, 30 binaries.

