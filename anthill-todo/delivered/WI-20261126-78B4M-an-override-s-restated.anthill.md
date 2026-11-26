## Attributes

- id: WI-20261126-78B4M-an-override-s-restated
- created: 2026-11-26T07:17:05Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-26T09:01:22Z

- acceptance: cargo-test

## Description

An override's restated `requires` that names the spec sort's const never matches the spec's
WHO NEEDS IT. A provider restating a spec operation's `requires`: anthill-traces' model of a spec (its WI-20261122-4067S) restates them, as WI-20261126-JR3AD's rule makes it where an `ensures` restates a variable a `requires` binds, and as a faithful provider does elsewhere. Three of that spec's `requires` clauses name a const of the spec sort.
MEASURED 2026-11-26, the loader through anthill-traces' binary on 2f7cbd4a2:
  namespace probe2
    import anthill.prelude.{Int64}
    sort Spec
      const lim: Int64 = 5
      operation qualified(n: Int64) -> Int64
        requires n < lim
      operation unqualified(n: Int64) -> Int64
        requires n < lim
      operation sub(n: Int64) -> Int64
        requires n - 1 >= 0
    end
    sort Impl
      entity mk
      operation qualified(n: Int64) -> Int64
        requires n < Spec.lim
        = n
      operation unqualified(n: Int64) -> Int64
        requires n < lim
        = n
      operation sub(n: Int64) -> Int64
        requires n - 1 >= 0
        = n
      provides Spec
    end
  end
`sub` loads. `qualified` and `unqualified` are refused: "'probe2.Impl' overrides 'probe2.Spec.qualified' but does not refine it: it strengthens the precondition — the override `requires` a condition the spec operation does not", and the same for `unqualified`.
NOT READ: why. Whether `Spec.lim` written in `Impl` is stored as another term than the spec's `lim` (a member access rather than the reference), whether the const is substituted on one side, and what the bare `lim` in `Impl` resolves to (it loads, so to something).
WHY IT MATTERS. A provider cannot restate a precondition that names a const. It can leave it out, a weaker precondition being a refinement, which is what anthill-traces' model does; but where an `ensures` restates one of that clause's variables, JR3AD's rule then refuses the override, and nothing restates it.
WHAT IS ASKED. A restated clause naming the spec sort's const matches the spec's clause: written qualified (`Spec.lim`) at least. The bare name in the provider either reaches the spec's const or is refused as unknown, not loaded as another thing. The same in the `ensures` leg.
DONE WHEN. (1) The probe's `qualified` loads. (2) Controls refused: another const, and a literal in the const's place. (3) `unqualified` decided and stated, with a row. (4) An `ensures` naming a const, a row. (5) The back-out measured, and said at the rows.

## Changes

### 2026-11-26T09:01:08Z — feedback — user

Implemented 2026-11-26 (86be3521a). WHY: a contract clause converts with consts kept as symbols (ConstFold::Off), so the spec's bare lim was Ref(Spec.lim) while the provider's Spec.lim stayed the converter's field_access(Spec, lim) chain, which override refinement, comparing clauses structurally, matched with no clause; and the provider's bare lim resolves to nothing in its scope (its body refuses it: 'expected resolved name, got unresolved'), so it was kept as a symbolic constant, Ident(lim) — as was requires n < nosuch on any operation (measured: loaded clean).
FIX (kb/load.rs): (1) Loader::contract_clause_qualified_reference — in a DATA slot of a requires or ensures clause, a minted dotted chain rooted at no binding whose whole name is a const, an entity constructor or a sort is resolved_name_term's term, the one the one-segment spelling builds; so Spec.lim is Ref(Spec.lim), Colour.red is red, ns.Colour is Colour. A goal slot is not this question (a requirement, a proposition). A chain rooted at an operation parameter or result resolves no whole name (measured: p.x beside a namespace p declaring const x stays the field read). (2) LoadError::UnresolvedContractName — a bare name in a data slot of a contract clause that resolves to nothing is refused at load, at the name's line:col. THE USER'S DECISION (2026-11-26, asked with the census): refused, as the body refuses it; the provider writes Spec.lim. Not judged: a goal slot (check_contract_clause_goals' — the clause's goal slots are read by a shadow ConstFold, ContractClauseReading::slot, through the same goal-slot table); a name a binder in the clause binds (lambda (y: Int64) -> y + x); a quoted Term field; a name whose resolution already reported (Self, found by /code-review — was reported twice).
CENSUS before deciding: zero unresolved bare names in contract clauses across the stdlib and every corpus directory (examples/*, anthill-stl, anthill-cpp-gen, anthill-todo bundle, anthill-testcases), positive control fired on the probes. The gate then found two: parse_test's load_banking_namespace and load_sort_with_operation wrote requires gt(m, zero-val), the additive identity's name before WI-20260825-1WBZT, which names nothing since; the fixtures compare a parameter's field instead.
DONE: tests/include/wi_78b4m_contract_clause_names_test.rs (wi_tests), 14 rows; each that loads runs the override. (1) the probe's qualified loads and runs (through call_assuming_requires, go's own m < Spec.lim discharging the call); the same over a predicate; (2) controls refused: another const of the same value (both legs), the literal 5; (3) unqualified decided: refused naming lim at the name, beside the strengthened-precondition refusal it leaves; any operation's bare name refused in both lists; (4) ensures naming a const restated qualified loads; a constructor and a sort qualified load; a caller's m < lim discharges a callee's n < A.lim. (5) Back-outs measured on a binary of the file alone, each listed at the file's head: rung out -> 6 RED; refusal out -> 2 RED, 4 GREEN by design; goal slots read as data -> 1; binder exemption out -> 1; quoted exemption out -> 1; one-report rule out -> 1.
SPEC: kernel-language.md §5.4 states the rule (a name in a contract clause denotes what it names in the operation's scope; the qualified spelling is the reference), §8.7 how a restated name compares, §5.3 points to it.
/code-review (xhigh, 9 findings): fixed — Self reported twice; §5.4 overclaimed that a goal-slot name naming nothing is refused (not under | or a quantifier, stated); the clause and its slot reading were two fields (one ContractClauseReading). Not reproduced — a parameter-rooted field read lowered to a namespace const; a requires bracket entry refused twice. Left — the provider's bare name gets the name refusal and the strengthening one; a qualified const in a call-site diagnostic now renders bare (lt(3, lim)). PRE-EXISTING, not fixed: a goal naming nothing under | or a quantifier body loads (requires n < 5 | nosuch); a qualified path naming nothing (Spec.limm) loads on an operation no spec stands over — the selector is a member name, and telling it from a lent member read needs the op-body ladder.
Gate: workspace 12837 passed, 0 failed; scripts/families.sh green, no verdicts moved. Scaland not run (no Scala touched; acceptance cargo-test).

