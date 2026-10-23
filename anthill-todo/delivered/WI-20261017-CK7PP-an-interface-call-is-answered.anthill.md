## Attributes

- id: WI-20261017-CK7PP-an-interface-call-is-answered
- created: 2026-10-17T09:39:26Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-23T09:22:23Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN INTERFACE CALL IS ANSWERED THROUGH A DICTIONARY, AND WHETHER ONE EXISTS IS A LOAD-TIME QUESTION -- three call shapes still load clean and die at eval after WI-20260909-M8QWJ, whose call check covers only a signature that names NO carrier (user, 2026-10-17: 'if we have a call of Set operation, we have required dictionary of Set implementation of the first argument ... we can check existence at compile time').

MEASURED on the M8QWJ tree, each in an operation body:
  (1) RESULT-ONLY CARRIER, left abstract: `g() -> LogicalStream[T = Unit, E = {}] = LogicalStream.guard(true)` and `s() -> Set[T = Int64] = Set.insert(Set.empty(), 1)` load; both die 'operation has no body' (LogicalStream.guard / Set.empty). The carrier stands only in the result, nothing pins it to a provider, and no requires / bracket supplies the dictionary. M8QWJ's check skips them because the signature names the carrier (in the result) and is not ground.
  (2) CONCRETE CARRIER WHOSE DICTIONARY LACKS THE MEMBER: `h(r: Relation[T = Int64, E = {}]) = LogicalStream.mplus(r, r)` loads; the dictionary is Relation's, which has no mplus (nor empty / pure / guard / interleave).
  (3) ABSTRACT ARGUMENT OF AN INTERFACE NOTHING PROVIDES: `c(s: Set[T = Int64]) = Set.contains(s, 1)` loads; no provider of Set exists, so no dictionary and no value can. WI-325 waves stdlib specs with no provider through on the 'host built-in' reading that WI-20260922-BRT4Y's @[host_implemented] retired.
  (4) A RESULT PINNED BY THE EXPECTED TYPE is refused but with the wrong message: `g() -> Relation[T = Unit, E = {}] = LogicalStream.guard(true)` reports a return mismatch and 'missing requires LogicalStream[E = ...]' instead of 'Relation does not supply guard'.

THE RULE TO STATE: a call of a member of a sort that may be provided reaches a dictionary chosen by the carrier the call names -- an argument's type, the result's expected type, a bracket, or a requires in scope; when none names a carrier the call is refused (no dictionary can exist), and when one names a concrete carrier its dictionary must have the member (else refused naming carrier and member). Value-directed dispatch on an abstract ARGUMENT stays legal only where some provider exists. Rule bodies are untouched (§8.3 UNREDUCED).

RELATION: extends M8QWJ's call check (unselectable_spec_operation_call, kb/typing/call_class.rs); the Relation-LogicalStream provision gap and WI-20261017-AT8V3 (SortedSet provides Set at the factor domain) decide what (2) and (3) refuse in the stdlib. Expect fixture churn in Set-in-operation-body tests (QCJ0B's list).

## Changes

### 2026-10-23T09:22:20Z — feedback — claude

DELIVERED 2026-10-23 (claude), d1633320. DECISIONS (user, 2026-10-23): a call on an argument typed at the sort is NOT refused — the value exists, its own sort answers when the call runs, with or without a loaded provider and at whatever type arguments; the error belongs where a value is made with no carrier. §5.4's 'At the call' bullet restated short: refused when the carrier (§5.3) is the sort itself and its own member runs nothing, or a sort that supplies no such member; a result names a carrier only through a type parameter of the sort, since Self in a sort is that sort. The lone-provider clause deleted from §5.4. CASES: (1) refused — Set.empty(), LogicalStream.guard/pure/empty, user Mon.unit(7); (2) refused naming carrier and member — LogicalStream.mplus(r, r) and r.mplus(r) over a Relation; (3) loads, by the decision above; (4) the call's refusal stands and 'missing requires LogicalStream[E = …]' is gone — the return mismatch is not reported, the call failing first; the ticket's 'Relation does not supply guard' does not follow, guard's result being LogicalStream (Self = the sort, proposal 070). MEASURED BY REVIEW: a result-only member at a sort with parameters is answered by a provision at the binding the expected type gives (IntBag provides Bag[T = Int64] answers Bag.empty() at Bag[T = Int64]), so it is judged after the dispatch; refused before it only where ground, or at the bare zero-arg reading, which never dispatches. ALSO FIXED in M8QWJ's call check: a member of a sort WITH constructors that provides the called sort is no longer exempt (Sp.name() in W provides Sp died); the default-body walk follows result-only siblings and members of provided sorts (Mon.two() = unit(2); Mid.other() = Sp.name() run at Mid); a sort with no parameter is advised the provider's member, not an empty bracket. WI-508's lone-provider pick removed. SITES: unselectable_spec_operation_call + nothing_in_scope_selects + sibling_reached_unrunnable (kb/typing/call_class.rs), SignatureCarrier (value_type.rs), the result-only and CarrierSuppliesNoMember checks after the dispatch (apply.rs), resolve_nullary_result_carrier (candidates.rs). ROWS: wi_ck7pp_interface_call_test (17), each part backed out alone reds its own rows and no other. LEFT: the set literal {1, 2} in an operation body (a Set with no carrier) to WI-20260926-QCJ0B; a host-realized carrier's member is still exempt (not declarable by a program, unmeasured); case (2) stands in for WI-20261017-D36RN. Gate: 10513 passed, 0 failed; families hold; scaland 718+47+1.

