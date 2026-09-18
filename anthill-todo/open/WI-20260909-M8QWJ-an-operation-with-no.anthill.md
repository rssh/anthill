## Attributes

- id: WI-20260909-M8QWJ-an-operation-with-no
- created: 2026-09-09T08:10:48Z

- status: Open
- status_agent: user
- status_at: 2026-09-09T08:10:48Z

- acceptance: cargo-test

- tags: typing

## Description

AN OPERATION WITH NO IMPLEMENTATION IS CALLABLE AT LOAD AND ONLY FAILS AT EVAL -- a body-less operation with no body, no host binding and no provider loads clean, and the failure lands at the first call as a runtime fault.

MEASURED, four shapes, all `anthill load` CLEAN on the current tree:
  (a) namespace-level `operation ping() -> Int64` (no body), CALLED by `drive()`
  (b) a SPEC-sort member `MySpec.ping()` with no provider, CALLED
  (c) the same declaration never called
  (d) a sort member `h.ping()` on a carrier that implements nothing, CALLED
The eval side is already LOUD -- `anthill run` on (a) gives "operation has no body: test.u.ping - nothing this runtime can run is registered for it: no operation body, no host..." -- so the diagnostic exists; what is missing is reaching it at LOAD, where the program is in front of the author.

WHY IT SURFACED NOW, and the correction that comes with it. WI-9WVT7's fix (b) stopped the WI-325 abstract-param loop demanding a `requires` for a spec parameter the called operation neither mentions nor receives. A /code-review finding read that as opening this hole. It does not: MEASURED both namespaces on `MySpec.ping()`, before that change the call was refused in a USER namespace and LOADED under `anthill.*`; after it, both load. The condition was already undetected for every stdlib spec.

AND `missing requires MySpec[T = ...]` WAS NEVER THE RIGHT MESSAGE FOR IT. It is what a user namespace used to print, and following it does not help: adding that clause to the enclosing sort leaves `ping` with no implementation, so the program still cannot run. It was a PROXY for "unimplemented operation", firing inconsistently and prescribing a repair that does not fix the problem. This ticket is the real condition; WI-325's check keeps its own job (a spec-op call whose dispatch genuinely turns on an abstract parameter).

THE DIFFICULTY, and it is why this is not a two-line check. A body-less declaration is USUALLY legitimate: ~110 candidate body-less operation declarations in the prelude alone (host-mapped ops, spec members a provider supplies, defaults filled at dispatch). The check must therefore ask "is there anything that could run this?" -- body, host mapping, a provider's implementation, an eq-bridge predicate, a `@[simp]` defining equation -- not "does it have a body". `Interpreter::unrunnable_target_error` and the `invoke_op_with_requirements` fall-through already enumerate those routes at RUNTIME; the load-time question is whether that enumeration can be answered statically, and for a value-directed dispatch it may not be.

QUESTIONS TO ANSWER, not prescriptions:
 1. WHERE. At the CALL (the WI-325 site has the substitution in scope) or as a whole-KB pass after load (every route is then known)? The call site can be wrong about a provider loaded later in the same run; the whole-KB pass cannot say which call site is at fault.
 2. WHAT COUNTS AS RUNNABLE. Enumerate against `unrunnable_target_error`'s own arms rather than from scratch, and say which are decidable at load.
 3. THE ABSTRACT CASE. A spec op called on a still-abstract carrier is legitimately deferred to runtime dispatch -- that is exactly what WI-325's `requires` licence means -- so the check must not fire where a `requires` covers it.
 4. WARN OR ERROR. An error changes what loads today; measure the stdlib and examples first.

ACCEPTANCE: the four shapes above answer per the decision, with a control that a host-mapped body-less op and a provider-supplied spec member still load; the chosen site says why it is that site; stdlib, examples and the full workspace stay green via rustland/scripts/test.sh.

REFERENCE: WI-9WVT7 (where this was measured and why its fix is not the cause), WI-325 (the check whose message was standing in for this), WI-818 (`unrunnable_target_error`, the runtime classifier).

## Changes

### 2026-09-13T18:35:08Z — feedback — user

ADJACENT: WI-20260913-KXNEX. A provision that leaves its spec's carrier parameter unbound (`provides Llm[E = …]`, bare `provides Harness`) loads clean and dies `OperationBodyMissing` at dispatch against a provider that DOES implement the operation — measured in WI-20260830-7MK73. This ticket's check would not see it (question 3 defers the abstract-carrier call, which is where it lives); KXNEX refuses it at the declaration instead, and once it lands every written provision names its carrier, so question 2's 'a provider's implementation' route reads off provisions with no silent None arm. Cross-reference, not a dependency.

### 2026-09-18T12:53:07Z — feedback — claude

ADJACENT, MEASURED 2026-09-18 on 19f73ff1 (while probing WI-20260918-R541X): AN UNDECLARED REQUIREMENT OVER A RIGID IS NOT REFUSED AT LOAD. Same FAMILY as this ticket -- loads clean, the trouble lands at the call -- but a DIFFERENT CONDITION: every operation here HAS an implementation; what is missing is the CALLER'S LICENCE.

    sort TypeTerm { sort T = ?  operation valueOf() -> Type }        -- each provider implements valueOf
    operation tagOf[P](x: P) -> Type requires TypeTerm[T = P] = TypeTerm.valueOf()
    operation bad[Q](y: Q) -> Type = tagOf(y)                        -- declares NO requires

ROW 1 -- ONE provider in the program (`Boom`): `bad(7)` LOADS and answers `Boom`. `Int64` has no instance, and the direct `tagOf(7)` IS refused ("a requirement suppliable at this call site", delivered WI-1102). This is a SILENT WRONG ANSWER, not a late failure: the goal `TypeTerm[T = Q]` with `Q` RIGID resolves `Unique` against the only provider head. `start_apply_deferred`'s own comment records that mechanism for the concrete case ("with one provider the goal resolves `Unique` and never defers").

ROW 2 -- several providers: the same program dies at eval, `DeferToRequirement: requirement param __req_typeterm not bound in caller frame (running tagOf, requires-chain owner tagOf; frame binds [])`, and through the rule-body bridge that is a PROCESS PANIC (`bridge_op_to_eval`, kb/resolve.rs).

THIS TICKET'S CHECK WOULD SEE NEITHER. Question 3 defers the abstract case WHERE A `requires` COVERS IT; this is the abstract case NO `requires` covers, reached through a NON-spec callee's op-scoped clause. It is the RIGID complement of WI-1102 (concrete carrier -> load diagnostic), and the repair it wants is the WI-325 / WI-823 "missing requires" ladder applied to a CALLEE-declared requirement -- "add `requires TypeTerm[T = Q]` to `bad`". Row 1 says in addition that resolution must not answer `Unique` for a rigid.

WHY IT MATTERS BEYOND ITSELF: WI-20260911-3MV2C's direction is `raise(error: T) ... requires ErrorTag[T]`. A generic raiser that forgets the clause would raise under ANOTHER TYPE'S tag (row 1) -- a misrouted raise, silently.

ROOT CAUSE NOT INVESTIGATED, NO TICKET FILED. Cross-reference, not a dependency.

