## Attributes

- id: WI-20261113-S4D63-proposal-074-stage-10-the-host
- created: 2026-11-13T23:22:43Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T23:22:43Z

- acceptance: cargo-test

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 10 — THE HOST BOUNDARY (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§1.4, "A host call and the code generators"; split from stage 1 after the third review). `zeroOf()` from the host refused at the boundary naming `X`, `add2(7, 2, 3)` naming `x`; `sum2(2, 3)` 5 and `add2(intInstance(), 2, 3)` 5 as today. The Scala emitter measured on a dictionary parameter, and refusing it loudly if it emits anything else. Until stage 1 lands, `intInstance` is written as the tree writes it today, and stage 1 rewrites it. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

## Changes

### 2026-11-13T23:42:21Z — feedback — claude

Rows moved here from WI-20261105-CBRD2 (073 §6.1) with the user 2026-11-13, 074 §1.4 superseding 073's host entry: over sort Desc { sort T = ?  operation describe(x: T) -> Int64 }, Leaf providing Desc[T = Leaf] at 7, and gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x), interp.call("gen", &[leaf]) answers 7 — leaf fixes A = Leaf at the boundary and Desc[T = Leaf] is built there (measured on bf311200: 7; Desc.describe(leaf) 7; sum2(2, 3) 5; sum2(1.5, 2.5) 4.0; zeroOf() dies Internal 'requirement param __req_additive not bound'). has(s, "a") without s.O is refused naming s.O, the MySet value not holding its O: WI-20260923-DK0QJ's half (a) (its fixture landmines are in that ticket; the nested slot ranked by resolve_inner on the host route is the defect to drive). The three entries (call, call_with_witnesses, call_with_requirements) become one: a witness named by its sort is that sort's dictionary, and an operation's own requires — which call_with_requirements has no spelling for today (WI-822) — is passed the same way.

### 2026-11-18T15:05:46Z — feedback — claude

Delivered 2026-11-18, decided with the user that day: a host call is typed exactly as the same call written in an operation body (074 §1.4). Interpreter::call(op, &[HostValue]) builds op(x1, …, xn), each xi a local at the type the host holds its argument at (the type the call that returned it answered, a type the host states with HostValue::typed, or for a bare value the type its value reads as), types it where an operation body is (enclosing op anthill.host.call, requiring nothing), reports what the typing parks, and runs it; the result is at the type the typer gave the call. Nothing in a host call is chosen by a value. A refusal is HostCallRefused in the body's load-error sentence: zeroOf() names X, add2(7, 2, 3) names add2.x; sum2(2, 3) 5, sum2(1.5, 2.5) 4.0, add2(intInstance(), 2, 3) 5, gen(leaf) 7. call_with_witnesses and the bare-value call are gone; call_with_requirements stays as the untyped entry for a cross-sort chain the host supplies. Changed verdicts, each as a body has it: one() over one[X]() -> Int64 refused; add2(intInstance(), 1.5, 2.5) refused at the call (was a run-time TypeMismatch); a set passed bare whose type leaves O open refused, with one provider too and when the body never reads the slot (EE0EP rows renamed); WI-822's open-ended rival answers 1 by §8.7's order; PartialEq.eq from the host pinned to the binding. Body fix found on the way: let s = mk() over mk() -> MySet[T = String], then has(s, "aa"), loaded and ran with String's own ordering; it is refused, as §5.2 says for an existential return (build_op_scoped_dicts). Scala emitter measured: x: Additive refused loudly; x: Additive[T = Int64] and x: Additive[T = P] emit the trait-typed parameter (BootstrapTest row). Found, not fixed: Bootstrap drops an operation's own spec requires (sum2 emits no using; List.contains, Map.empty in the prelude), asked of the user. Open with the user: the resolver bridge passing dictionaries (CBRD2's), inside S4D63 or next. Gap: a host writes no bracket, so Store.persist at IndexedFileStore (NonMonotonicStore and QueryableStore) goes through a wrapper operation. Back-outs measured and named at the rows; the host_calls clearing at a layer load/discard is driven by no row. Gate 12330 / 0 / 17; families green on both carriers; scaland testFull 860. /code-review high: 9 findings, 8 fixed, 1 skipped (the layer clearing undriven).

