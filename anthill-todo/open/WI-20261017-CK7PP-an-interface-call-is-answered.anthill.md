## Attributes

- id: WI-20261017-CK7PP-an-interface-call-is-answered
- created: 2026-10-17T09:39:26Z

- status: Open
- status_agent: user
- status_at: 2026-10-17T09:39:26Z

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

