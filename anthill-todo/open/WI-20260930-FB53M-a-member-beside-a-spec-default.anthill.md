## Attributes

- id: WI-20260930-FB53M-a-member-beside-a-spec-default
- created: 2026-09-30T16:25:09Z

- status: Open
- status_agent: user
- status_at: 2026-09-30T16:25:09Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A MEMBER BESIDE A SPEC DEFAULT BODY IS NEVER COMPARED WITH THE SPEC OPERATION, YET DISPATCH RUNS IT FOR A CALL WRITTEN AGAINST THE SPEC. `sort Sp { sort T = ?; operation peek(s: Sp, k: Int64) -> Int64 = 0 }`, `sort Car { sort V = ?; entity car(v: V); provides Sp[T = Car]; operation peek(s: Car) -> Int64 = 7 }`, `Sp.peek(car(v: 1), 5)`: loads clean and dies at run time 'operation call: expected 1 args, got 2'. A member returning String behind the spec's Int64 (`Sp.peek(car(v: 1)) + 1`) dies 'type mismatch: expected Int64, got String and Int64'; a member taking `k: String` behind the spec's `k: Int64` dies 'type mismatch: expected String, got Int64'. Without the default body each member is refused at load ('… does not fit …'). MEASURED identically on the pre-WI-20260929-0RP29 binary. (A spec needs a type parameter — proposal 058: over a non-parametric `sort Sp` the named call runs Sp's own body, by design; wi1042_defaulted_gate_test pins it.) THE PREMISE THAT DOES NOT HOLD: the member-fit check (WI-20260822-1MAGR, typing/signature.rs check_member_signature; kernel-language.md *Backing conformance*) runs only where the member is the SOLE backing, because beside a default 'a same-named member of a different signature is then a DISTINCT operation, and the default is what backs the provision … and a call that expected the spec's shape is already a loud type error naming both types'. Dispatch does not read it that way: the call types against the spec, and the carrier's member is chosen by its short name whatever its signature (call_class.rs carrier_own_op, read by WI-1010's carrier_override_suppliers). WI-20260929-0RP29's member-narrower rule shares the gate; its WI-606 fallback had threaded such a member (Sp.peek(a) over Car.peek(s: Car, k: Int64) died 'expected 2 args, got 1') and now declines another arity, but a same-arity mismatch beside a default is still dispatched. DECIDE (a spec question — with the user): (A) the documented reading — a member that does not fit the spec operation is not its supplier, so dispatch skips it and the default runs: 'is this member the spec op's supplier' gets one owner, decided once at load by the member-fit comparison and read by every dispatch site (the evaluator's supplier lookup, the typer's static dispatch and the WI-606 fallback, the rule-body dispatch), and WI-1125's decided programs (wi1125.nullary, wi1125.witnessunrelated) keep loading; or (B) refuse the member at load beside a default too, overturning those decisions (and wi1042.nonparametric). FOUND by WI-20260929-0RP29's third /code-review (its C20). ACCEPTANCE: the three programs above run the default (A) or are refused at load (B), the decision recorded in the spec; the sole-backing refusals unchanged; full workspace green via rustland/scripts/test.sh.

