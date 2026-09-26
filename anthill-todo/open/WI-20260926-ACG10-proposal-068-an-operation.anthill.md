## Attributes

- id: WI-20260926-ACG10-proposal-068-an-operation
- created: 2026-09-26T08:20:13Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T08:20:13Z

- acceptance: cargo-test, scaland-sbt-test

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

### 2026-09-26T10:01:15Z — feedback — user

WI-20260925-PRVA2 (d) MOVED HERE (user, 2026-09-26): 068 §1–§2 decides it, so §5.3's 'what the gate still declines' changes with 068 step 2 and not before. PRVA2 (d) read a SPLIT — `PartialEq.eq(WeakOrd.compare(1, 5), -1)` holding with its carrier known at load, while `rule below(?a, ?b) :- PartialEq.eq(WeakOrd.compare(?a, ?b), -1)` fails `below(1, 5)` silently. MEASURED at 028e13f8 (PRVA2's fixes do not touch it): there is NO split — both are refuted. `WeakOrd.compare(1, 5) = -1` answers no solutions; `below(1, 5)` no solutions; `not(below(1, 5))` HOLDS (NAF proves a falsehood); the functional-relation view `WeakOrd.compare(1, 5, ?r)` answers -1; and `?r <=> WeakOrd.compare(1, 5)` binds `?r` to the unreduced `compare(1, 5)` as a DEFINITE answer. A body-less spec op in a value slot is compared as data wherever it is written; under 068 its carrier is ground, it dispatches, and each row answers its truth. Candidate rows for 068's problem table.

### 2026-09-26T11:39:59Z — feedback — user

FOUR MORE ROWS FOR 068, found reviewing WI-20260925-PRVA2 (2026-09-26); each pre-existing and MEASURED.
(1) A BODY-LESS SPEC Bool OP AS A GOAL answers nothing, and NAF proves the falsehood. The Bool-view hook gates on bare_bodied_bool_relation of the SPELLED functor (a runnable body) and never reads the typer's pin, as dispatched_relation_arity does for the arity+1 view. Desc.isGood(leaf()) (one parameter): no solutions, not(...) holds. The two-parameter twin Conv.ok(m(v: 3), "km") behaves the same, and loads since PRVA2 (c) (HEAD refused it with the false "String provides no Conv"); the functional-relation form Conv.ok(m(v: 3), "km", ?r) answers true.
(2) A TYPER @[simp] LAW WHOSE RIGHT SIDE CALLS BODY-LESS SPEC OPS leaves those calls unpinned, so a rule-body value slot gets a conditional row: with rule twice(?a, ?b) <=> Int64.add(conv(?a, ?b), conv(?a, ?b)) @[simp], ?r <=> Conv.twice(m(v: 3), "km") is unify(?_, add(conv(..), conv(..))), conditional; untagged it answers 14 (the one-parameter control is identical).
(3) A RULE-BODY CALL VALUE DISPATCH CANNOT EVALUATE ANSWERS NOTHING, SILENTLY. Conv.tag(b: B) has no argument at Conv's carrier parameter A, so ?s <=> "km", Conv.tag(?s, ?r) answers no solutions (the op-body twin fails at run time, "operation has no body"); with require[Conv[A = Meters, B = String]] it answers 3 since PRVA2 (c). HEAD refused the rule at load, for a false reason PRVA2 removed. The WI-20260924-35E14 class.
(4) WI-670's open-time refutation (body_refuted_by_ground_conjunct) judges a conjunct by its discrim candidates, behind a hand-kept list of the routes step_init answers off the tree (extents, the Bool view, scoping markers, woven calls, and since PRVA2 functional-relation goals, evaluated when ground). 068's fragments add routes that depend on a goal's ARGUMENTS: in rule r(?x) :- ground(?x), p(add(?x, 1)) over fact p(3) the refutation keys add structurally and refutes where 068 would suspend and answer. 068's implementation must teach this check its fragments, or refuse to judge an atom holding one.

