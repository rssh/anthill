## Attributes

- id: WI-20260822-59CDQ-contract-refinement-matches
- created: 2026-08-22T10:27:54Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T10:27:54Z

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

