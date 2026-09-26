## Attributes

- id: WI-20260926-ACG10-proposal-068-an-operation
- created: 2026-09-26T08:20:13Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T08:20:13Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

PROPOSAL 068 — AN OPERATION APPLICATION IN A RULE BODY IS A COMPUTATION: typed as in an operation body, evaluated by value. FIRST STEP: REVIEW THE PROPOSAL, docs/proposals/068-rule-body-operation-applications.md (Draft, 2026-09-26). Nothing is implemented until the review settles it, and the review's outcome is recorded in the proposal's Status line.

THE PROBLEM (measured on main at fa32695e; 068's problem section has the tables). In a rule body an operation call is evaluated before a comparison, or not, depending on WHERE it is written and WHICH builtin compares it. Unevaluated, it is compared AS DATA, so a true equation is answered false DEFINITELY and NAF over it proves a falsehood:
  String.contains("abc", "b") = true                     1   (call at the top of the operand: evaluated)
  bb(v: String.contains("abc", "b")) = bb(v: true)       0   (the same call nested: compared as data)
  box(v: C.tag(red())) = box(v: 1)                       0   (C.tag(red()) is 1)
  not(intersection({1,2}, {2}) = {2})                    1   (an operation with no implementation, compared as data)
The cause: a rule body is stored untyped (data slots are only name-checked, WI-1058), so the resolver guesses call-versus-data from the value at run time, in each consumer separately, to a different depth — `=` the top of an operand, `<=>` every level but a bind keeps its interior unevaluated, the WI-580 case-split none. WI-20260827-XBHX3 is one instance, in the case-split.

WHAT 068 DECIDES (summary; the proposal is authoritative). §1 an operation application in a rule body denotes its value at any depth, evaluated strictly by the operation-body evaluator; a value is what evaluation produces; `<=>` still binds, and a bound application keeps its mark; inside a quote nothing is evaluated. §2 an application not evaluated is SUSPENDED (carries its blockers; re-evaluated only after one is bound) or UNREDUCED (no implementation reachable: a load error at a call site where the typer can decide it, otherwise evaluated once and parked, never retried); a comparison takes the state of its operands and UNREDUCED wins; no library sort's interpretation is a dependency. §3 functional fragments are typed by the operation-body typer with simp off. §4 evaluate / suspend / narrow / unreduced. §5 heads, fact heads included, stay patterns; `=` never binds; `===` reduces its operands. §6 untyped carriers (queries, run-time goals) must answer as the typed path does.

PLAN (068 §8; refined in docs/design/068-implementation.md after the review): (1) measure only — type fragments stamp-only, count the reports across the corpus, list the library code that relies on comparing unevaluated applications as data (known: Set's equality, the five wi616 rows); (2) one walker + one evaluator — the bridge interpreter carries logic variables and names its blockers, UNREDUCED goals are parked; (3) retire the per-consumer reductions (`reduce_op_value`'s fold, `body_specialize`'s reducer, XBHX3's gate); (4) the unfold threads dictionaries instead of declining every operation with `requires`. The kernel-language edits (§8.3, §5.3, §8.1) land with step 2.

ACCEPTANCE: the proposal reviewed and its Status updated; docs/design/068-implementation.md written; every row in 068's problem section answers its truth column, or UNREDUCED / undecided where the operation has no implementation — each driven, with its back-out stated at the test; kernel-language.md updated; full workspace green via rustland/scripts/test.sh; scaland green (sbt testFull).

## Changes

### 2026-09-26T10:01:39Z — feedback — user

NARROWED (2026-09-26, user: 'ACG10 — as you wish'). This ticket is now step A0 of the 068/060 sequence: (1) the REVIEW — done; its outcome is recorded in 068's Status line (two rounds: one evaluation strategy for <=>, =, === and goal arguments; nothing stored in a binding is an unevaluated call; a call is data only inside a quote, which produces a plain Term; heads are an implicit quote; splice evaluates, a typed quote is deferred; @[simp] does not fire inside the evaluation; typing creates a rule-body call's dictionary, 060 / P7VP4); (2) docs/design/068-implementation.md; (3) 068 §8 step 1's census, changing no behaviour — fragment-typing report counts, the library code that compares unevaluated calls as data, and a re-measure of 068's problem rows on current main (P7VP4's weaving already moved part of 35E14's population). The IMPLEMENTATION and this description's per-row acceptance moved to: WI-20260926-CYNPE (A1, resolver scheduling: blockers, parking), WI-20260926-K4JGC (A2, the evaluation strategy; depends on A1), WI-20260926-7D48J (C1, one rule-clause typing for 060's inference and 068's fragments; design first; depends on P7VP4), WI-20260926-DSEXA (D1, dictionary blockers, retiring the per-consumer reductions, the unfold threads dictionaries; depends on A2 and C1), and the library ticket WI-20260926-QCJ0B (Set). XBHX3 now depends on DSEXA and 35E14 on CYNPE — the tickets that fix them — instead of on this one. 0RRQP stays its own ticket (user). ACCEPTANCE for this narrowed scope: the design doc written and reviewed; the census numbers recorded in it.

