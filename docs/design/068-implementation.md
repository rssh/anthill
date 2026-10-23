# 068 implementation — an operation application in a rule body is a computation

## Status: Reviewed (2026-09-29; WI-20260926-ACG10, delivered). The proposal is
[`../proposals/068-rule-body-operation-applications.md`](../proposals/068-rule-body-operation-applications.md);
this document owns HOW. Decided with the user (2026-09-29): D1–D7 (§3); the clause environment,
how far data is typed, the new load errors and equations in a fragment (2026-10-21, §6.2).

## 0. The sequence

Tag `proposal-068`; every edge is technical.

| step | ticket | what | after |
|---|---|---|---|
| A0 | WI-20260926-ACG10 | this document; the census (§1) | — |
| A1 | WI-20260926-CYNPE | resolver scheduling: blockers, parking (068 §2.2) | — |
| A2 | WI-20260926-K4JGC | the evaluation strategy (068 §1.1–1.2) | — (D4: may go first) |
| C1 | WI-20260926-7D48J | one rule-clause typing for 060's inference and 068's fragments | WI-20260925-P7VP4 |
| D1 | WI-20260926-DSEXA | dictionary blockers; the per-consumer reductions retired; the unfold threads dictionaries | K4JGC, 7D48J |
| — | WI-20260926-QCJ0B | `Set`'s library route (implementation or quoted algebra) | — |
| — | WI-20260929-QA700 | `Lattice`'s `less_bottom` / `less_top` clauses shadow a carrier's `less` (a defect today; §1.3) | — |

Waiting on the sequence: WI-20260924-35E14 → CYNPE, WI-20260827-XBHX3 → DSEXA,
WI-20260926-Y6ZCD → 7D48J (one dispatch decision for operation and rule bodies).

## 1. Census

### 1.1 The problem rows, re-measured on `main` at `2b6cac2c`

`anthill query` over six probe fixtures built from the tickets' own (`C.tag` a bodied `match`,
`tag(red()) = 1`; `fact p(1)`; the P1TPE fixture for the unfold rows; `Score` with `Colour`
as its only provider; `WeakOrd` at `Int64`; PRVA2's `Conv.tag`). `(total, definite)`.

| row | today | truth | owner |
|---|---|---|---|
| `String.contains("abc", "b") = true` | (1, 1) | 1 | control |
| `bb(v: String.contains("abc", "b")) = bb(v: true)` | (0, 0) | 1 | K4JGC |
| `box(v: C.tag(red())) = box(v: 1)` | (0, 0) | 1 | K4JGC |
| `?v <=> box(v: C.tag(red()))` | binds `box(v: tag(red))` | `box(v: 1)` | K4JGC |
| `?v <=> box(v: C.tag(red())), ?v = box(v: 1)` | (0, 0) | 1 | K4JGC |
| `box(v: ?n) <=> box(v: C.tag(red())), ?n = 1` | (1, 1) | 1 | control |
| `p(C.tag(red()))` | (0, 0) | 1 | K4JGC |
| `not(p(C.tag(red())))` | (1, 1) — a falsehood | 0 | K4JGC |
| `?v <=> C.tag(?c)` | (1, 0), residual `unify(?_, tag(?_))` | conditional | control |
| `?v <=> box(v: C.tag(?c))` | (1, 1), `box(v: tag(?_))` | conditional | K4JGC |
| `box(v: C.tag(red())) === box(v: 1)` | (0, 0) | 1 | K4JGC |
| `insert(insert(empty(),1),2) = insert(insert(empty(),2),1)` | (1, 1) | 1 → undecided after K4JGC | QCJ0B |
| `intersection({1,2}, {2}) = {2}` | (0, 0) | undecided | K4JGC / QCJ0B |
| `not(intersection({1,2}, {2}) = {2})` | (1, 1) — a falsehood | undecided | K4JGC |
| `union({1}, {2}) = {1, 2}` | (0, 0) | undecided | K4JGC / QCJ0B |
| `C.bpick(?c) = box(v: C.tag(red()))` | (1, 0) | `?c = red` | DSEXA |
| `C.pick(?c) = C.mk(red())` (custom `Eq`) | (1, 0) | never a wrong refutation | DSEXA |
| `List.append(?a, [3]) = List.append(?b, [4])` | (1, 0), terminates | terminates | DSEXA |
| `List.append(?a, [3]) = [1, 3]` | `?a = [1]` | `?a = [1]` | control |
| `WeakOrd.compare(1, 5) = -1` | (0, 0) | 1 | K4JGC |
| `below(1, 5)` (`PartialEq.eq(WeakOrd.compare(?a, ?b), -1)`) | (0, 0) | 1 | K4JGC |
| `not(below(1, 5))` | (1, 1) — a falsehood | 0 | K4JGC |
| `WeakOrd.compare(1, 5, ?r)` | `-1` | `-1` | control |
| `?r <=> WeakOrd.compare(1, 5)` | (1, 1), `?r = compare(1, 5)` | `-1` | K4JGC |
| `?s <=> "km", Conv.tag(?s, ?r)` | (0, 0), silently | load error or undecided | 7D48J / CYNPE |
| `require[Conv[…]], Conv.tag("km", ?r)` | `3` | `3` | control |

**Moved since the proposal.** WI-20260924-35E14 is fixed for a SPEC operation by P7VP4's
weaving: `rule late(x: Colour) :- Score.score(x, 3)` answers `blue`, and `rule unbound(?r) :-
Score.score(?v, ?r)` is a conditional answer carrying `find_dictionary(…), unify(?_, score(?_))`.
It is NOT fixed for an ordinary BODIED operation, which P7VP4 does not weave:
`Colour.score(x, 3)` and `Colour.score(?v, ?r)` answer nothing, silently, while
`Colour.score(x) = 3` answers `blue`. 35E14's population narrows to that (D6).

**Masked.** The WI-670 open-time refutation row (`r(?x) :- ground(?x), p(add(?x, 1))` over
`fact p(3)`) cannot be seen today: head matching fails `p(add(…))` structurally even with `?x`
bound first. It appears once K4JGC evaluates goal arguments, and K4JGC owns it.

### 1.2 Fragments by position and callee (D5)

MEASURED on `main` at `145457c7` by `wi_acg10_census_test::acg10_census` (`#[ignore]`d — a
measurement: `scripts/test.sh -p anthill-core --test wi_tests -- --ignored acg10_census
--nocapture`). Each project loads with stdlib; only rules whose source file is the project's own
are counted. A FRAGMENT ROOT is an operation application in a value position (068 §1); calls
inside a root's own arguments belong to that fragment. Callee: `builtin` (a resolver builtin
backs it), `bodied`, `host` (an `operation_map`), `spec` (dispatched through a provider — none of
these rule-body calls carries a typer pin today), `none` (no implementation reachable).

| project | rules | roots | where |
|---|---|---|---|
| stdlib (+ rust stl bindings) | 434 | 28 | `<=>` operand 5 (4 `spec` — the `splitFirst(?s) <=> some(…)` guards — 1 `host`); `===` operand 3; `>` / `>=` operand 2; a higher-order goal `?P(…)`'s argument 9 (3 `builtin` — the induction schemas' `?P(add(?n, 1))` / `?P(sub(?n, …))`, 4 binder forms, 1 dot, 1 woven); the goal itself a call 9 (5 `spec`, 4 `none`) |
| examples/webots-modelling/lf1 | 84 | 55 | `=` operand 47 (43 `builtin` arithmetic, 4 dot calls); `<=` operand 6 `host`; the goal itself a call 2 `bodied` |
| anthill-todo, classic-mini ×4, github-todo, sql-store, guardians/lib | 157 | 0 | — |

**What this says about K4JGC.** No predicate goal in the shipped corpus has a call in its
arguments: D3's population is the higher-order goals of the induction schemas, and the test
fixtures. The operand population is small and concentrated — `lf1`'s `=` over arithmetic (which
today's top-of-operand reduction already handles) and stdlib's guarded-equation guards. The
defects of §1.1 live in programs the corpus does not yet contain; the test fixtures are where
K4JGC's rows are driven. No set literal occurs in a shipped rule body.

Heads, for §1.3: 53 equation heads (`lhs <=> rhs`) and 15 guarded equations (`lhs = rhs :- g`)
hold an application inside their subject's arguments — rewrite patterns, which 068 §5 leaves
alone; 3 quantified-guard consequents in `lf1` (`-: lte(?n_sum, ?na + ?nb)`) are comparisons,
evaluated as goals.

### 1.3 Library code that compares an unevaluated application as data

From the walk of §1.2 — every RELATIONAL head holding an operation application, and every call
whose callee has no implementation:

- **`Set`** — `set.anthill:50–53`: `subset(empty, …)`, `subset(insert(…), …)`,
  `contains(insert(…), …)` match unevaluated `insert` / `empty` in their heads; the five
  `wi616_semantic_eq_test` rows ride on them. Route: WI-20260926-QCJ0B.
- **`Lattice`** — `lattice.anthill:44–45`: `less(bottom, ?a) :- true` and `less(?a, top) :- true`
  are clauses of `Lattice.less` over the TERM `bottom` / `top`. A defect TODAY, measured with a
  two-point lattice (`bottom() = lo()`): `Lattice.less(BoundedLattice.bottom(), hi())` holds
  through the clause, `Lattice.less(lo(), hi())` answers nothing — the clauses shadow the
  carrier's own `less` — and `not(...)` over it proves a falsehood. Once goal arguments are
  evaluated (D3) even the `bottom()` spelling stops matching. WI-20260929-QA700.
- **`Filesystem`** — `platform.anthill:152–155`: `needs_rebuild` calls `exists` / `status` as
  goals, and nothing in the corpus provides `Filesystem`. Today the goal falls to candidate
  selection and fails silently; under 068 it is UNREDUCED — undecided, parked (§2).
- **The guards that keep today's reading:** `reduce_operand`'s `dispatch_body_less: false`
  (WI-1057), and P7VP4's refusal to weave an unpinned body-less spec op in a value slot — both
  exist to keep the `Set` reading, and both go with K4JGC.

## 2. Code map — where each consumer evaluates today

| consumer | site | evaluates | under 068 |
|---|---|---|---|
| `=` / cmp / arith | `reduce_operand` → `reduce_op_value` | the top of each operand | §1.1's strategy |
| `<=>` | `unify_values`, `unify_bind` | the node the walk is at; a bind stores the rest unvisited | the strategy, then structural |
| head matching | `unify_match_values` (discrim re-bind) | nothing | unchanged; goal arguments evaluated BEFORE it |
| WI-670 open-time refutation | `body_refuted_by_ground_conjunct` | nothing (discrim candidates) | must not judge an atom holding a call |
| Bool view / arity+1 view | `dispatched_bool_relation`, `functional_relation_goal` | the goal's own call, through the bridge | unchanged readers |
| WI-580 unfold | `unfold_eq_operand`, `body_specialize::folded_call_match` | case-split on a flex scrutinee | DSEXA reads OTHER through the strategy |
| the bridge | `run_in_bridge_interp` (a fresh interpreter per call) | the operation body | the strategy's only evaluator |
| delay | `delay_goal` | re-evaluated from scratch on every rotation | CYNPE (§4.1): passed over unless a blocker was bound |
| typing | `type_rule_bodies`, `collect_rule_var_types`; `infer_rule_body_requirements` (P7VP4) | variable types; goal shapes; no data slot | 7D48J |

## 3. Decisions

- **D1 — blockers are coarse first** (DECIDED). A waiting goal's blockers are the free variables
  of its arguments under σ when it waits. Sound: it is re-evaluated only when one of them is
  bound. Naming the exact variable the evaluator needed means changing `EvalError::Suspended`
  (`{ detail: String, truncated }` today, no variable) — an optimization, later.
- **D2 — a pending equation is a delayed `unify(?t, call)` goal, spliced by a builtin RESULT**
  (DECIDED, user 2026-09-29). Today only `step_init`'s special cases add goals: `push_and` splices
  its two operands in place of itself and resets `delay_mode` (the goal count changed), before
  `execute_builtin` runs. `<=>` cannot use that route — it finds its stuck calls only partway
  through the walk. A new `BuiltinResult` variant carries the bindings AND the goals to splice;
  its handler is `push_and`'s splice and reset, and `push_and` becomes one of its producers,
  leaving `step_init` with one splice path instead of two.
- **D3 — a goal's arguments are evaluated before candidate selection, by a run-time scan first**
  (DECIDED, user 2026-09-29). Candidate selection matches a goal's arguments against clause heads
  structurally, so `p(C.tag(red()))` must reach the discrim tree as `p(1)`. The arguments name
  variables earlier goals bind, so this happens when the goal is picked, in `step_init`, not at load.
  - **The unit** is a GOAL: one conjunct of a stored rule body, the `NodeOccurrence` placed in
    `ResolverFrame.goals` when the clause is opened — for a predicate atom, `Expr::Apply
    { functor: p, … }`. Only a goal that goes to candidate selection is scanned: a builtin
    evaluates its own operands (§5), and an operation goal is its own call (Bool / arity+1 views).
  - **What is evaluated:** every operation application WRITTEN in the goal's arguments — a node
    written with parentheses whose functor resolves to an OPERATION (not an entity constructor,
    tuple, collection literal or variable). The scan descends through constructors, tuples and
    collection literals; not into a quote (`↑…`, a `Term`-typed slot); a binder form in an argument
    is a call, evaluated whole. A value that arrives through σ is not written code and is not
    walked; a bare nullary name is §5.4's type-directed question and is left alone.

    | goal | evaluated before the tree |
    |---|---|
    | `p(C.tag(?x))`, `p(box(v: C.tag(?x)))`, `p([1, List.length(?l)])` | the call |
    | `p(box(v: ?x))`, `p(?x)` | nothing |
    | `C.tag(?x, ?r)` (the goal IS the call), `?v <=> C.tag(?x)`, `C.tag(?x) = 1` (builtins) | not scanned |
    | `p(↑C.tag(?x))` (quoted), `p(Box.zero)` (bare name) | nothing |
    | `not(p(C.tag(?x)))` | the inner goal's call, when NAF resolves it |

  - **A call that cannot run yet** becomes a fresh variable plus a pending `unify(?t, call)` (D2),
    and the goal reaches the tree with `?t`.
  - **The scan first, a flag only if measured** (068 §7: measure, not assume). Every such goal is
    scanned when picked — one path for loaded rules, CLI queries and run-time goals alike. If the
    scan shows up in the measurement (§8.1), the recorded fallback is a load-time stamp on the goal
    node beside the typer's `classification` (`NodeKind::Expr`), three-valued so "never checked"
    cannot read as "no call" — `HasCall` / `NoCall` / `Unknown`, set in the walk WI-1058's name
    check already makes, carried by `open_debruijn_node` and `substitute_occurrence` as
    `classification` is; `Unknown` (a goal the loader never saw) is scanned.
  - **Rejected:** rewriting the stored rule at load (`p(C.tag(?x))` stored as `p(?t), unify(?t,
    C.tag(?x))`) — the stored body would no longer be what was written (printing, reflection,
    proofs, citations see the rewrite), and CLI / run-time goals would still need the scan: two
    mechanisms instead of one.
- **D4 — K4JGC does not technically need CYNPE** (DECIDED; the edge is removed). A pending equation is a delayed goal
  that today's rotation already re-tries — slower, not wrong. K4JGC is the risky change (every
  consumer; `Set`'s rows flip), so it may go first or in parallel.
- **D5 — the census counts fragments by syntax** (DECIDED; §1.2).
- **D6 — 35E14 narrows to the bodied-operation population** (DECIDED, recorded on 35E14; §1.1).
- **D7 — a call stuck only on a RIGID variable stays a symbolic term** (DECIDED; found by the
  census, §1.2). In a proof, `forall(?n)` introduces an eigenvariable — a rigid skolem — and the
  induction schemas' consequent `?P(add(?n, 1))` then holds `add(n, 1)`, which can never run: it
  is neither SUSPENDED (no binding can reach a rigid variable) nor UNREDUCED (`add` has an
  implementation), and it is the most precise name its value has. Proposed: such a call is kept
  as a SYMBOLIC term — not replaced by a fresh variable, since §1.2's pending equation could never
  be discharged — and compared structurally: identical subtrees are equal (§1.1's reflexivity),
  and a structural mismatch against anything else is UNDECIDED, because the verdict depends on
  what the eigenvariable stands for. That is the rule the resolver already applies to a skolem
  verdict (`skolem_verdict_is_value_dependent`: an `eq` / `unify` FAILURE over a skolem becomes
  `Unknown`), extended from the comparison to the call.

## 4. CYNPE — blockers and parking

- **A goal carries its wait state.** `ResolverFrame.goals: Vec<Value>` becomes a vector of goal
  entries `{ goal, wait }`, `wait` being `Ready`, `Suspended(blockers)` or `Parked(cause)`, so
  the state rotates WITH its goal and cannot drift from it. Frame-local, never on the occurrence
  (068 §2.2). The existing `undecided: Vec<(Value, UnknownCause)>` is what `Parked` subsumes.
- **On its turn** a `Suspended` goal is re-evaluated only if some blocker is now bound
  (`chase_var`); otherwise it rotates without evaluation. A `Parked` goal rotates and is never
  re-asked. The residualization gate (`consecutive_delays >= goals.len()`) is unchanged.
- **Producers.** `BuiltinResult::Delay` gains its blockers (D1: computed from the goal at the
  delay site). The WI-938 hook's three declines split: an unbound argument is `Suspended`; no
  supplier and a tie are `Parked` with a named cause.
- **Rows.** 35E14's bodied rows (`Colour.score(x, 3)`, `Colour.score(?v, ?r)`); the run-time half
  of `Conv.tag(?s, ?r)`; a suspended goal evaluated once, not once per rotation (counted); a
  parked goal behind a failing sibling still refutes the clause.

### 4.1 As delivered (WI-20260926-CYNPE, 2026-09-30)

`ResolverFrame.goals: Vec<FrameGoal>`, `FrameGoal { goal, wait }`, `Wait::{Ready, Suspended {
blockers, cause }, Parked}` (`kb/resolve.rs`); `ResolverFrame::undecided` is gone — the gate reads
each residual goal's cause off its wait, so neither its "filter to the goals still pending" nor
the delay fallback's hand-inherited copy is needed. What differs from the sketch above, each
driven by `wi_cynpe_waiting_goals_test` (back-outs stated at its sites):

- **Blockers are computed where the goal waits, not carried by the answer.** `BuiltinResult::Delay`
  gains no blockers (it keeps its `truncated` flag): D1's coarse blockers are the goal's unbound
  variables under σ (`collect_unbound_vars_value`, the WI-322 pre-check's reader), computed when
  the goal ROTATES. Every waiting goal — a builtin's `Delay`, `Unknown` or `Error`, a call the
  WI-938 hook could not run, a NAF goal, a bounded quantifier over an open spine, a rule goal whose
  every candidate delayed — rotates through one primitive, `rotate_first`, and so does a goal
  passed over on its turn (`pass_over_waiting_goal`), with its wait unchanged. The sole-goal case
  residualizes through one helper, `yield_sole_goal`.
- **UNREDUCED parks — unless a call beside it still waits.** An undecided answer over a UNIVERSAL
  (`OpenWorldParameter`, `OpaqueSkolem`) and a FAULT are SUSPENDED on their blockers with their
  cause: a binding can still change such an answer (a Γ fact can match the goal then). An
  UNREDUCED call never runs, but a SUSPENDED call in the same goal may, and turn out ABSENT — which
  outranks UNREDUCED (`Stuck::join`) and fails the goal: `Int64.div(1, ?z) = Conv.tag("km")`,
  `?z` later bound to `0`, must be asked again rather than parked (it then raises, and since
  2026-10-23 the raise marks the answer set incomplete instead of refuting the clause). So an UNREDUCED goal is PARKED only when no
  call written in its arguments holds an unbound variable (`unbound_vars_in_goal_calls` — a
  variable outside every call cannot matter, since no binding holds a call); otherwise it is
  SUSPENDED on exactly those, with its cause. Found by this ticket's `/code-review`.
- **The WI-938 hook answers a stuck call with the call's state, on the goal as written.** A call
  that ran is routed to `unify(?r, value)` as before. One that did not is no longer sent to
  candidate selection (where no clause is written for `f/n+1`): SUSPENDED and SYMBOLIC delay the
  goal, UNREDUCED is scheduled as undecided, ABSENT fails. The goal keeps its own spelling — not
  rewritten to `unify(?r, call)`, which the first cut did — so a re-ask evaluates the call ONCE, in
  the hook, where the first cut evaluated it twice (in the hook, then again in `<=>`). WI-1040's
  woven route is subsumed, and `FunctionalRelationCall::woven` is gone. A supplier TIE at a
  carrier the typer sees is refused at load ("ambiguous dispatch"); one that reaches run time — a
  carrier-less call with two providers, NAR1X's no-`require` row — is UNREDUCED through
  `stuck_state`, like no supplier.
- **A hypothesis still answers a stuck call.** A call that did not run goes to candidate selection
  when a HYPOTHESIS in scope — a `forall_impl` antecedent, a Γ fact — matches the goal as written
  (`hypothesis_candidates`, found once and handed to candidate selection).
  `(forall(?c), Colour.score(?c, 3) -: Colour.score(?c, 3))` answered 1 through its antecedent by
  the old fall-through; without the exception the consequent's call, stuck on the eigenvariable,
  waited and the tautology came back conditional. Because the goal is not rewritten, the question
  is asked again at every re-ask, under what has been bound since — a Γ fact matches only a goal
  identical up to variable identity. (The Bool view never consulted hypotheses, before or after.)
- **No goal is made ready by an assumption.** `forall_impl`'s antecedents could in principle
  answer a rule goal waiting in the tail without binding its blockers — but the tail sits behind
  the `__pop_assumption` marker, and rotation only moves the head to the back, so no tail goal is
  asked before the assumptions are gone again. (A first cut reset the tail to `Ready` there; the
  review found it could never fire.)
- **Counted, not timed:** `ResolveStats::goals_asked`. A goal suspended on a variable nothing binds,
  among three siblings that progress one at a time, is asked once (4 times before).
- **What waiting costs where failing was free.** A functional-relation call over an argument
  nothing binds used to fail at once; it now waits, so a recursive clause that relied on the
  failure (`rule chain(?r) :- f(?x, ?r), chain(?x)`) recurses to `max_depth` and the search
  reports itself TRUNCATED — undecided where it was a (wrong) complete 0. The same holds of any
  delayed builtin in that position today; recorded, not changed.
- **Rows moved outside the module:** five rows that pinned the silent empty answer now pin its
  honest replacement — NAR1X's and S8CBV's no-`require` controls (UNDECIDED, `Unreduced`), 96ZTM's
  (every `combo` row UNDECIDED), WI-1043's un-ground body-less goal (conditional, `?r` free), and
  `anthill-stl`'s exhaustion-door row, whose fixture now fails its branch by a sibling instead.

## 5. K4JGC — the evaluation strategy

- **One function.** `normalize(value, σ)` walks a value bottom-up, evaluates every call that can
  run through `reduce_op_value` (the bridge), and returns the value with each STUCK call replaced
  by a fresh variable, plus the list of stuck calls — each with its fresh variable and its state:
  suspended (blockers) or unreduced (cause). Identical stuck calls share one variable (068 §1.1,
  reflexivity). §1.2 is then not a special case of `<=>`: every consumer sees a value with holes.
- **Consumers.**
  - `<=>`: normalize both sides, unify structurally, and return D2's result — the bindings and one
    `unify(?t, call)` per stuck call. A mismatch anywhere fails definitely.
  - `=` / `neq` / `===` / cmp / arith: normalize; any unreduced call → `Unknown`; else any
    suspended call → `Delay` with its blockers; else compare. `=` never binds.
  - A goal bound for candidate selection (D3): normalize its arguments in `step_init`, splice the pending equations after
    it, and query the discrim tree with the normalized goal — `p(C.tag(red()))` meets `fact p(1)`
    as `p(1)`.
  - WI-670's refutation: an atom whose arguments hold a written call is not judged.
- **Body-less spec operations dispatch in a value slot.** `reduce_operand`'s `dispatch_body_less`
  becomes true (068 §2.3): a ground carrier with a supplier runs; none is unreduced. `Set`'s rows
  become undecided — QCJ0B's consequence, asserted at the test.
- **Unchanged here:** the WI-580 unfold (DSEXA), head matching itself, `@[simp]` (068 §5).
- **The spec edit** — kernel-language §8.3's `<=>` bullet and evaluation paragraph — lands with
  this ticket.

### 5.1 As delivered (WI-20260926-K4JGC, 2026-09-30)

`kb/resolve/evaluate.rs`. What differs from the sketch above, each measured and driven by
`wi_k4jgc_evaluation_strategy_test` (back-outs stated at its sites):

- **Two entries, not one `normalize`.** `evaluate_value` for a TEST (a stuck call makes the
  operand stuck, the comparison takes its state) and `evaluate_with_holes` for a value that is
  BUILT (`<=>`'s operands, a goal's arguments). A WHOLE side that is a stuck call is not holed —
  it is the pending equation itself, and `<=>` waits as it always did.
- **A hole nothing reached pends nothing** — its variable neither bound nor inside a binding —
  which is how identical stuck calls unify by reflexivity.
- **Four states, not two.** SUSPENDED and UNREDUCED as §2; SYMBOLIC (D7's rigid-variable call,
  and a ground call the evaluator declined — an effect row, a fault) is kept as the term and a
  test over it waits; ABSENT — an arithmetic builtin over NUMBERS with no answer — fails
  whatever reads it, as its relation fails. A zero divisor was the example here (`div(1, 0)`)
  until 2026-10-23, when the user decided its declared `Error[DivisionByZero]` propagates
  (WI-20260827-NFXPZ): the builtin now faults, so the call still has no value and the goal
  still answers nothing, but the answer set is marked incomplete and `not(…)` over it is
  undecided.
- **Builtins in a value slot compute** through their result column (`add(a, b)` as
  `add(a, b, ?r)`): arithmetic in an operand or a goal argument answered nothing before, and the
  WI-670 row needed it. A GOAL-ONLY builtin (`eq`, `not`, …) written as data is SYMBOLIC — a goal
  passed to a relation stays the term.
- **A dotted NAME is not a call** (`Box.zero`, `ns.inner.rel` — a receiver that names a scope):
  at the top of an operand it is read as before (`reduce_dot_value`: a nullary operation's call,
  else the name); in a data slot and a goal argument it stays the chain, so `fact holds(ns.rel)`
  and the goal `holds(ns.rel)` still spell one term. A projection of a VALUE (`?p.x`) is a call.
- **The WI-938 hook and WI-670's functional-relation check** evaluate their call by the same
  strategy, arguments first; `reduce_operand`, `reduce_dispatched_goal_call` and
  `reduction_left_body_less_call` are retired.
- **Kept, not retired:** P7VP4's load-time refusal to weave an unpinned body-less spec op in a
  value slot — removing it makes a no-provider call FAIL at its `find_dictionary`, where §2 says
  UNREDUCED; run-time dispatch by the ground carrier gives the value. Recorded on DSEXA.
- **`Set`:** 18 rows (not 5) assert UNDECIDED, including `Set` equality reached from an operation
  body through the eval bridge; listed on QCJ0B, with the pre-existing rule-body set-literal row.
- **Cost:** no measurable difference on `classic_mini`, `github_todo`, `guardians` (§8.1; a busy
  machine, so a coarse bound). A SYMBOLIC call in a delayed goal is re-evaluated per rotation —
  CYNPE's blockers make that cheap.

## 6. 7D48J and DSEXA

Their tickets hold their design questions: 7D48J — the clause environment, how far data is typed
(0RRQP's `<=>`-with-constructor tie), the typer's per-call classification as P7VP4's one input,
the census's typing count, and Y6ZCD's single dispatch decision; DSEXA — `?d` as a blocker, the
retired per-consumer reductions, the unfold threading dictionaries. 7D48J's clause environment,
data typing, load errors and equations are decided in §6.2.

### 6.1 D1a as delivered (WI-20261013-GFS6A, 2026-10-14)

`?d` was already among a woven call's blockers: CYNPE's coarse blockers are a waiting goal's
unbound variables, and the walk descends into an `ApplyWithin`'s requirements. What kept the
call from answering was how its dictionary was found and passed, at the places below, each
driven by `wi_gfs6a_woven_call_waits_on_its_dictionary_test` (back-outs stated at its sites):

- **A self-represented spec's elements come off the carrier's provision**
  (`self_represented_elements`, read by `witness_sort_goal` and `anchor_sort_goal` alike, through
  the typer's `bind_spec_params_from_provision`). Left to the wildcard tail, `T` under `Car
  provides Sp[T = Int64]` met the concrete binding and was refused, so the read never found the
  provider. An element the written bracket names still selects the row. A carrier type that
  pins no carrier (`concrete_receiver_carrier`: the spec itself, a sort others provide) builds
  no goal, so a citation from `viaSp(s: Sp) = dflted(s).head.x` leaves the read to the value
  instead of filling it with `Sp`'s own dictionary, which the read then refused.
- **A goal its receiver made is answered by the receiver's sort** (`resolve_inner`): the
  refinement leaf a sort with no type parameter takes is for a `requires` clause, not for a goal
  with a carrier. Taken there, the read bound `Sp`'s own dictionary and a defaulted call ran the
  default.
- **An unbound carrier at an abstract bound waits** (`guard_over_arg_types`, through
  `concrete_receiver_carrier`): the variable's bound is the spec or a sort others provide, so
  the value bound later decides. Read as the carrier, a call whose receiver a later goal binds
  ran `Sp`'s default.
- **No provider at a ground carrier is a failure, not an undecided answer** (decided by the
  user, 2026-10-14, reversing the 2026-09-30 note on DSEXA: a missing provider is no undecided
  answer, and where a provider exists its dictionary is threaded). The read fails, written or
  inferred, as it did before. At the bridge, an operation's own requirement the arguments pin
  and no provider answers is a recorded absence (`UnavailableWhy::NoProvider`) rather than a
  skipped slot; a body that reads it raises `UnpinnedRequirement`, whose disposition is
  `BridgeDisposition::NoProvider`, and `evaluate_call` reads the call as `Stuck::Absent` — it
  has no value, as `div(1, 0)` has none (KCNA0's three programs: no answer, where a debug build
  aborted).
- **A selection an operation makes reaches the rule when the operation runs from a rule**
  (`WovenDispatch::Stamped`, `Interpreter::call_op_bridged_stamped`). The fold bridged a nested
  call to an operation with its own `requires` from the argument values alone, so
  `viaRule[A = Int64, WeakOrd = Descending](1, 5)` inside `desc` answered `Int64`'s own -1 when a
  rule ran `desc`, where the interpreter answers `Descending`'s 4. The call's own stamps
  (`op_dicts`) now ride to the bridge and supply the slots they can; a stamp that forwards a
  caller's slot the bridge has no frame for is read as unbound (`try_eval_requirement_chain_node`)
  and its slot derived, as before.

### 6.2 C1a — the clause environment and how far data is typed (WI-20261013-GGXCX)

Decided with the user 2026-10-21; no code. Measured on `bb99c630` with the CLI built from the
tree. Amends 068 §1 ("the walk … never types those") and §3 ("fragments are typed with simp
OFF"). Built by C1b (WI-20261013-WF14Z) and C1c (WI-20261013-R1W5A); C1d (WI-20261013-RYDNV)
reads what they build.

**Decision 1 — the clause environment.** A clause is typed as a whole, as an operation body
is: one substitution over its variables, in any order of its goals. Every position that
declares a type contributes to it:

- the head's bound, written or inferred — one type (decided on WI-20260925-0RRQP);
- a constructor's fields and result, and an entity goal's fields (built by 0RRQP);
- an operation call's parameters and result, in a value slot and as the result column of
  `f(args, ?r)`;
- a rule goal's columns: the callee's, written or inferred — there is no difference between
  written and inferred — opened fresh at each goal as at a citation. Relations are typed callee
  before caller; a relation that calls itself reads its own columns as one type within its
  clauses;
- a field read: `?p.t` is at the field's type.

The enclosing sort's parameters, a named requirement's slot included, are variables of the
clause that a citation fixes (rigid in the body — decision 3). A variable no position types
stays open, and a call at it is dispatched by the value at run time (068 §3, the WI-282
exemption).

Today only a constructor types a variable (goal order already makes no difference). Over
`sort Cnt { entity cnt(n: Int64); operation bump(c: Cnt) -> Int64 = … }`, `mk4() -> Cnt =
cnt(n: 4)`, `entity P(t: Int64)`:

| clause | today | decided |
|---|---|---|
| `?c <=> cnt(n: 4), ?x <=> ?c.bump()`, and the two goals reversed | `5` | `5` |
| `rule h1(?a: Int64, ?x) :- ?x <=> ?a.abs()`, called with `-3` | the term `-3.abs` | `3` |
| `rule inner(?c: Cnt, ?x) :- ?x <=> ?c.bump()` | the term `cnt(n: 4).bump` | `5` |
| `?c <=> Mk.mk4(), ?x <=> ?c.bump()`; `Mk.mk4(?c), ?x <=> ?c.bump()` | the term | `5` |
| `gen(?c), ?x <=> ?c.bump()` over `rule gen(?c) :- ?c <=> cnt(n: 4)` | the term | `5` |
| `rule r0(?p: P, ?x) :- ?x <=> (?p.t).abs()`, called with `P(t: -3)` | the term `P(t: -3).t.abs` | `3` |
| 0RRQP's `Box.order(mk()).head.c`, `mk() -> Box[T = Int64, O = Ascending]` | `-1` | `-4`, `O` read off the argument's type |

**Decision 2 — how far data is typed.**

- *Every entity construction written in a rule or a fact is typed*: each argument checked
  against its field, which gives it its expected type, and the construction's type given to
  its position — a `<=>` side, a comparison operand, a goal's argument (relation or entity), a
  call's argument, a field of another construction, an element of a tuple or collection
  literal, a head's argument, a fact's argument. A mismatch is a load error naming the field.
  068 §5 already says heads are "typed, never evaluated".
- *Not constructions, and not typed as data*: a type written as a value (`holds(Box[String])`,
  `domain_member(?x, Colour)`), a bracket entry (`require[Desc[T = p.E]]`), a discharge's
  binders and antecedents, a slot declared `Term` (a quote, 068 §1.3). These are where the
  2026-10-13 measurement's 21 extra failures came from (GGXCX's note of that day, (3b)).
- *WI-1058's three reasons*, answered for a construction: the expectation comes from the field,
  the column, the other side of `<=>` or the enclosing field, and unification carries it both
  ways; a construction binds nothing, and a binder form inside one is a fragment typed whole;
  typing records types and stamps and replaces no node of the stored data.
- *A relation whose clauses give one column types with no join* (`fact holds(1)`, `fact
  holds("a")`; or two rule clauses at `Int64` and `String`) is not refused. The column's type is
  a rigid "some type", opened fresh at each rule goal and each citation, as 0RRQP opens what a
  citation leaves unfixed — TypeScript's `unknown`: a value of it goes where any type is taken
  and nowhere one type is asked. This is a relation's column only; an operation body's arms
  with no common type stay refused.
- *Narrowing.* In a clause a TEST narrows such a variable to `T`, wherever the test stands:
  `domain(?v, T)` — the run-time type test, which decides every ground value of a sort, a
  primitive and a parametric sort — `<=>` against a construction or a literal, and a head's
  bound (the same test). A DEMAND — a call's argument, a dot, a field read — needs the
  variable typed, by a test or by any other position. Narrowing to an arrow waits on
  WI-20261021-VF8GT (a closure carries no type); narrowing in an operation body
  (`holds.head.x`) is not part of C1.

Over `entity pt(x: Int64, y: Int64)`, `sort Hold { entity holder(h: pt) }`, `fact holds(1)`,
`fact holds("a")`, `fact holds(pt(x: 1, y: 2))`, `px(p: pt) -> Int64` (its `x`):

| written | today | decided |
|---|---|---|
| `fact pt(x: "s", y: 2)`; the body goal `holder(h: pt(x: "s", y: 2))` | refused | refused |
| `fact holder(h: pt(x: "s", y: 2))`; `rule hh(pt(x: "s", y: 2)) :- true` | loads | refused |
| `?r <=> pt(x: "s", y: 2)`; `?r <=> pt(x: wrap(v: 1), y: 2)` | binds it | refused |
| `holds(pt(x: "s", y: 2))` | loads, no answer | refused |
| `holds(?r)` | the three values | the three values; `?r` at "some type" |
| `holds(?v), ?r <=> U.ilen(?v)`, `ilen(n: Int64) -> Int64 = n` | loads; `1`, `"a"` and the `pt` — `ilen` hands back what it is given | refused, the demand un-narrowed |
| `holds(?v), domain(?v, Int64), ?r <=> U.ilen(?v)` | `1` | `1` |
| `holds(?v), ?v <=> pt(x: ?a, y: ?), ?r <=> U.px(?v)` | `1` | `1`, from the `pt` solution |

**Decision 3 — the new load errors.**

- *The enclosing sort's parameter is rigid in a clause's typing*, as in an operation body: a
  citation fixes it, the body may not. `Self` is this instance (070), so in `sort Box3[T] {
  entity b3(v: T) }` `rule prSelf(?x: Self) :- ?x <=> b3(v: 5)` is refused ("b3.v expected T,
  got Int64"), while `rule prBare(?x: Box3) :- ?x <=> b3(v: 5)` — a bare sort is an open slot
  — loads, a relation of `Box3[T = Int64]` values. `sort Sat[C]`'s `rule model(vs: C) :- vs <=>
  [?p, ?q, ?r], …` is refused ("expected C, got List[T = Bit]"); its repair is SHED7's
  `PersistentCollection[C = C].fromList([…])`. A variable the clause writes (`?x: Wrap[T =
  ?t]`) or leaves unwritten stays flexible. Today all of these load: `Box3[T = Int64].prSelf`
  answers `b3(v: 5)`, `Box3[T = Colour].prSelf` nothing, `Sat[C = Bag[T = Bit]].model` 0 models.
- *By class, and the part that builds it*:

  | class | example | part |
  |---|---|---|
  | a construction's argument against its field, in a body, a head or a fact | `?r <=> pt(x: "s", y: 2)` | C1b |
  | a variable whose positions disagree | `pt(x: ?a, y: 2), U.slen(?a)`; `rule twoTypes(x: Bit, y: Bag[T = Bit]) :- x <=> y` | C1b |
  | a head's bound against the body | `rule concrete(vs: Bag[T = Bit]) :- vs <=> [t(), f()]` | C1b |
  | a rule goal's argument against the callee's column | `c("a")` over `rule c(?x: Int64) :- true` | C1b |
  | a demand on an un-narrowed "some type" | `holds(?v), U.ilen(?v)` | C1b |
  | a member missing on a typed receiver | `?c.nosuch()` | 0RRQP (constructors), C1b |
  | the sort's parameter fixed by the body | `prSelf`, `Sat.model` | C1b |
  | a call's argument list and types in a value slot | `Util.sub2(1, 5, 9)`; `List.length(vs)` over `vs: Bag[T = Bit]` | C1c |
  | a function value no bare reference can supply | `app(dbl, 2)` | C1c |
  | an effectful application, by its typed row | `now(?r)`, `hofWR` (7D48J's 2026-10-16 row) | C1c |

- *The count is taken during the build*: each part counts its classes on §1.2's corpus and on
  the suite with the check reporting and refusing nothing, records the count here, and builds
  against it. C1c's starts from GGXCX's 2026-10-13 measurement: on the corpus 7 newly typed
  sites and 0 reports; on the suite 29 + 21 rows, the shapes decision 2 excludes.

**Decision 4 — equations are on in a fragment's typing**, as in an operation body. A fragment
(an operation application or a binder form) is typed as an operation body is, equations
included, and the stored fragment is the rewritten one, as an operation body's is. `@[simp]`
still never fires inside §1.1's evaluation, and `ResolveConfig { simplify }` governs only the
resolver's own run-time rewriting. Against 068 §3's grounds for turning them off: WI-1058's
`holds(ite(true, 10, 20))` was a rewrite of data, which decision 2 never rewrites; "one call,
one answer" holds, with the answer the operation-body twin gives; and the 2026-09-26 row (a
`@[simp]` law whose right side leaves `conv(…)` unpinned) is a defect in typing the rewrite's
result, which C1c owes — the rewritten node is typed, as the operation-body typer types it.
Rejected: refusing at load a rule-body call to an operation whose only definition is its
equation (the two texts would differ; `Float.recip`, `Relation.where` / `join` uncallable in a
rule body; stricter than `simplify: true`), and the evaluator running a defining equation as a
body (a backing kind at run time — WI-885's open question). Over `operation dbl(n: Int64) ->
Int64`, `rule dbl(?n) <=> ?n + ?n @[simp]`, `app(f: (Int64) -> Int64, x: Int64) -> Int64 =
f(x)`:

| written | today | decided |
|---|---|---|
| `?x <=> dbl(2)` | conditional, residual `unify(?_, dbl(2))` | `4` |
| `?x <=> app(lambda (y: Int64) -> dbl(y), 2)` | `4` | `4` |
| the goal `dbl(2, ?x)` | no answer, silently | `4` |
| `dbl(2) = 4` | holds | holds |
| `?x <=> app(dbl, 2)` | residual, incomplete | refused, as in an operation body |
| the operation-body twins | `4` | `4` |

**The rows each part owes.**

- *C1b (WF14Z)* — decision 1's table; decision 2's construction, "some type" and narrowing
  rows; decision 3's C1b classes, each with its count. Flips in
  `wi_0rrqp_clause_typed_through_constructor_test`: `a_body_that_fixes_a_sorts_parameter_is_read_as_before`
  (refused), `a_constructor_that_does_not_fit_its_position_pins_nothing` (refused, `b: "s"`
  against `Int64`), `a_slot_the_arguments_own_type_says_is_not_read` (`-4`; §6.7), and
  `a_column_nothing_types_is_read_at_any_type` (refused once a rule goal and a goal-position
  call type their columns; 0RRQP's 51 rows are its measurement). SHED7's `Sat.model` refused,
  with its repair loading.
- *C1c (R1W5A)* — decision 4's table; its own rows (the three spellings of `Box.open`, the
  argument list in a value slot, `()` left by an equation); the 2026-09-26 `twice` row answers
  `14`; decision 3's C1c classes, each with its count. Controls, green before and after: the
  rows the 2026-10-13 equations-off measurement reddened (`wi_rm247` ×2,
  `kernel_mint_address`, `wi939`, `wi_p7vp4`, `wi_3hn0n` ×4).
- *C1d (RYDNV)* — unchanged by C1a: the classification it makes the inference's one input is
  read off the clause typing C1b and C1c build.
- *VF8GT* — narrowing to an arrow; a tuple type written as a value in a data slot.

### 6.3 C1b, decision 1 as built (WI-20261013-WF14Z, first part, 2026-10-22)

`kb/typing/rule_constraints.rs` (`LatePosition`, `settle_late_positions`),
`kb/typing/relation.rs` (`rule_goal_columns`, `same_rule_goal_cycle`). Rows in
`wi_wf14z_clause_typed_as_a_whole_test`, its back-out ledger at its head. Decision 1's table
answers as decided, all but its last row (`-4`, the routing of a named requirement's slot).

- **One substitution, the walk's positions first.** The walk reads what it read before — an
  operation's and an entity's declared parameters, a constructor's application — and leaves
  the rest for after it: the head's written bound (the enclosing sort's parameters it names
  rigid), an operation call's result in a slot that declares a type, the result column of
  `f(args, ?r)` (`functional_relation_goal`, the resolver's own reading of the goal), a rule
  goal's columns and a dot's value. Each is read on a copy of the clause's typing and kept
  where it fits; where it does not it pins nothing and is recorded with its class
  (`ClauseDisagreement`), so this part refuses nothing new — decision 3's classes are counted
  off those records before they refuse. A dot and a result whose type is computed from its
  operands (`field_access`'s `FieldOf`, `head`'s `s.T`) are read last, once what they depend
  on is typed; a call's written type arguments instantiate its parameters. Only a goal the
  clause commits to types: one in a `|` branch, under `not` or in a quantifier's body reads
  nothing outside it.
- **A rule goal's columns are generalized across the callee's clauses**, not joined as a
  citation's are: the most specific type each clause's column is an instance of, so a tie two
  clauses make differently is dropped. Joined, `description_view(some(?d), ?d)` beside
  `description_view(none, none)` made the second column an `Option`, and github-todo's
  `open_item` answered nothing (measured on the first cut). A clause whose column is a variable
  it names nowhere else holds no type there and takes the others' — which is how a relation
  that calls itself reads its columns as one type. A goal on another relation of its own cycle
  reads nothing (Tarjan's numbering over the goals), so neither relation's columns depend on
  which is asked first. Read once per typer run and per clause stored (`rule_goal_columns_memo`).
- **The parameter form's dotted path is a field read** (`clause_param_field_read`,
  `clause_param_method_call` in the loader): `p.t`, `(p.t).abs()` and `p.t.abs()` on a
  sigil-free head parameter lower to the dot the `?p` spelling does.
- **A stamp's sort parameter is opened per citation** (`ClauseTypes::at_citation`): a head's
  bound now reaches the stamps, and a sort's parameter is no variable a citation's pin binds.
- **Inferred bounds stay as written** (user, 2026-10-22): a column the new positions type at a
  data sort with a variable gets the check a written bound gets, so rows moved as their written
  twins already did on the parent — an undecided call's `Result` column filled with an `ok` and
  an `err` (9WVT7's clock, reify and scoped-KB rows), `headOption(…) = ?r` at a filled `Option`
  answering nothing (`wi818`, whose row now counts the call off a body variable), and a z3 proof
  through an inlined rule with an `Option` column refused, "no SMT sort" (FHEEK's `leafVar`,
  KF2SD's `claim_a` and `chosen`). The same claims over an option sort with no parameter,
  whose column is no bound, read as before (`leafN`, the `framesn` fixture).
- **Found and fixed:** a typed head's domain check refused a value whose part its bound fixes
  and the value does not carry — `?r: Result[T = Int64, E = ?e]` over `err(error: 5)` — on the
  parent too (`read_unknowns_from_bound`).
- **Stated limits:** a goal on another relation of a cycle reads nothing (`od` over `ev`); a
  construction passed where a spec's carrier is declared (`head(cons(7, nil))`) is read at the
  spec's own parameter, which the provider does not unify with; a column whose whole type is a
  variable is read at the type its use asks for
  (`a_column_whose_whole_type_is_a_variable_is_read_at_any_type`).

Left to C1b: decision 2; decision 3's classes, each counted and then refused, with three of
the four flips of `wi_0rrqp_clause_typed_through_constructor_test` and SHED7's `Sat.model`;
decision 1's `-4` row; and closing a column whose whole type is a variable. The fourth flip is
made: `a_column_nothing_types_is_read_at_any_type`'s program is refused once its rule goal types
the column, and the row is `a_column_a_rule_goal_types_is_read_at_its_type`.

### 6.4 C1b, the clause typing made exact (WI-20261013-WF14Z, second part, 2026-10-22)

Still refusing nothing. What the first part recorded on the suite — 213 disagreements in 113
tests — was read shape by shape, and each shape the operation-body typer accepts, and whose
clause answers at run time, no longer records anything. Rows in
`wi_wf14z_clause_typed_as_a_whole_test` after `recorded`, each backed out alone in its
ledger.

- **An argument meets a position as an operation's argument does**, with its conversions. A
  `Term` position admits every value and types nothing (`nonvar(?g)`'s parameter: `takes(5)`
  recorded `Term against Int64`). An `Option[T]` parameter is the call's placeholder, as a
  parameter of the callee's own type is: a bare `T` meets it by the some-coercion, and a
  position that says what the variable is takes over (`?a: Int64` passed to `len(o:
  Option[T = Int64])`). The call is not wrapped at run time in a rule body — C1c's (a note on
  WI-20261013-R1W5A).
- **A type written as a term is no data**: a `TypeExtractor` construction, an arrow, a type
  face. `p.E` in `require[Desc[T = p.E]]` typed the head parameter at `ExprCarried.value`'s
  `NodeOccurrence`.
- **A collection literal is its collection**, a tuple of its components' types or a list or
  set of one element type — not the reflect entity it is stored as. A fact's `(x: 1)` was a
  `TupleLiteral`, so `?t.x` on a value read out of it was refused, a member the entity does
  not have.
- **A bound the loader refuses is read as unwritten**: one naming a sort that does not resolve
  (as an annotation is), and one at a spec over its parameter (`check_rule_sort_uses`).
- **A clause says nothing of a column only where the column's variable is an argument of a goal
  that read nothing** — on its own relation or another of its cycle (`GoalColumn::unread`). One
  nothing in the clause names is of every type: `classify(?x, ?c) :- ?c <=> 2` beside
  `classify(?x: Colour, ?c)` was read at `Colour`, and `classify(5, ?r)`, which answers `2`,
  disagreed. kernel-language §5.3's sentence is corrected to say so.
- **A position that fits once the sort's parameters vary is counted as fixing one**, whichever
  position read it (`bx(?x)` under `pr(?x: Box2[T = T])` was a rule-goal disagreement).
- **A column of occurrences quotes its argument** (user, 2026-10-22), as a `Term` position
  does: `synth_int(42, ?n)` over `synth_int(?e, 1) :- occurrence_term(?e, int_lit(value: ?))`
  reads `42`'s occurrence. The operation-body twin `q(42)` at `e: NodeOccurrence` stays
  refused.

Two shapes were taken for false positives and are not: a refining sort (`sort Sub requires
Leaf`) against `?x: Leaf`, and two carriers under one rule-bracket introducer (`both[A](?x: A,
?y: A) :- Desc[A], seed(?x), seedo(?y)`). Each clause answers nothing at run time, so each
disagreement is real and stays.

**The count**, by `ANTHILL_CLAUSE_DISAGREEMENTS_TO=<file>` (one line a disagreement: class,
test, place, source), with nothing refused:

- *The corpus of §1.2*: the stdlib and every project 0, but `lf1`: 4 rule-goal disagreements,
  one cause — `excursion_distance_bound` multiplies `PostArmedExcursionBound.max_ticks`, an
  `Int64`, by `transponder_step_distance_bound`'s `Float` (`?excursion = ?n * ?delta_t`), which
  the operation-body twin refuses, "type mismatch in mul.b: expected Int64, got Float"; the
  three callers then read the column at the wrong type.
- *The suite* (gate 10328 / 0): 89 records in 47 tests — rule goal 79, head bound 4, sort
  parameter fixed 4, call result 1, result column 1. By shape:

  | shape | tests | records |
  |---|---|---|
  | `lf1` loaded (the corpus's one cause) | `lf1_real_spec_test` 3, `wi995`, `wi1075`, the CLI's | 40 |
  | a run-time fault reached through an ill-typed clause: `fact tag("a")`, `tag(?x), PartialOrd.gt(?x, 1)` | `resolver_error_channel` 4, `wi_8y5be` 7, the reflect bridge's 4, `wi879`, the CLI's `resolve_errors` | 24 |
  | a run-time guard over a clause that can never hold: a bound no row meets (`pw9a0`'s lists under an arrow or a tuple bound, `wi582`'s `src(1, 10)` under an arrow, `wi742`'s `named_bad(?x: String) :- ?x <=> 5`), a value of the wrong sort (`shed7`'s `inc(?x, ?), ?x <=> 2.5`), `qmfc5`'s refining carrier and two carriers under one introducer | `pw9a0` 2, `qmfc5` 2, `wi742` 2, `wi582`, `shed7` | 11 |
  | an SMT fixture comparing an `Int64` with a `Float` (`kf32`'s `mode(0, ?r)` beside `lt(?k, 0.5)`), or ordering a construction (`fheek`'s `wrap(P(x: 1.0), ?y)`) | the CLI's | 6 |
  | already refused for another reason, or built to disagree | `0rrqp`'s owed flip and `n4`, `wi1104`, `9wvt7`'s error tag, `two_across`, this file's `n1` / `n2` and `fixedbygoal` | 8 |

Decided with the user, 2026-10-22, for the part that refuses:

- *`lf1`*: `entity PostArmedExcursionBound(max_ticks: Float)`, its fact `max_ticks: 6.0` — the
  SMT documents read every number as a real already.
- *A test whose subject is the run time over a clause the load refuses* reaches that path
  through a goal built at run time, so the program loads clean and the fault channel or the
  guard is still driven; the written clause's refusal is its row.
- *A column typed `NodeOccurrence` or `Expr` is a quote*, as a `Term` position is (built above;
  it took `wi1099`'s 6 tests and `typing_test`'s 6, 19 records, off the count).
- *The §5.3 sentence* on a column a clause says nothing of stands as corrected.

### 6.5 C1b, decision 2 as built (WI-20261013-WF14Z, third part, 2026-10-22)

Recorded, refusing nothing; rows in `wi_wf14z_clause_typed_as_a_whole_test` under "Decision
2", each part backed out alone in its ledger.

- **Every construction is typed against its fields**, in a rule body, a head and a fact: a
  literal or a nested construction is checked against the field it fills, with the argument
  conversions (a `Term` field admits every value, an `Option[T]` field a bare `T`, a field at
  a bare spec a value of a sort that provides it), and a mismatch is recorded at the argument
  (`construction field`). Facts are read by the clause walk — those a source writes, of a load
  no seal holds; a fact the loader makes carries no place and is not read. The table's rows
  that loaded record now: a fact's nested field, a head, a `<=>` side, a nested construction,
  a relation goal's argument.
- **An equation's head is a rewrite pattern, not data**: its constructions are not checked,
  and the reflect syntax its sides are stored as types nothing. Found on the way and fixed:
  a guarded `@[simp]` equation reading a field on its right — `peek(?b) = ?b.v :- gt(1, 0)` —
  was refused, "contradictory variable types", on the tree before WF14Z too: the stored
  `dot_apply(receiver: ?b, …)` typed `?b` at its `receiver` field beside `peek`'s `Box`. It
  loads and rewrites.
- **A rule goal's column whose clauses give it types with no join is of some type**
  (`ColumnType::Some`): a goal's argument there is a filter. A variable it takes that only
  demands type — a call's argument at a parameter of a stated type, a dot — is recorded
  (`some type demand`); a test (`domain(?v, T)`, `<=>` against a construction or a literal, a
  head's bound) or any other position types it, wherever it is written. A parameter of the
  callee's own type is no demand: a spec's carrier is dispatched by the value, and
  `Desc.describe(?x, ?r)` over `item`s of two sorts answers each.
- **Not yet, the citation's side.** A citation of such a column reads as before — a fact
  relation's column a variable read at any type, two rule clauses' refused at the relation,
  "disjoint types for column" —; reading it at some type is an operation-body refusal, made
  with decision 3's, where it closes a column whose whole type is a variable.

**The count**: the corpus records nothing of either class. The suite (gate 10334 / 0): 72
records in 48 tests —

| shape | tests | records |
|---|---|---|
| a fixture built to be refused (`typing_test`'s field rows, `wi928`, `wi1056`, `szkv7`, `d0sd4`, `wi946`, `jb6rs`, `wi830`, `wi849`) | 38 | 46 |
| `KB.fields` compared with `FieldInfo(name: "x", …)`, a `String` at the `Symbol` field — the clause answers at run time, the operation-body twin is refused, "expected Symbol, got String" (`wi_9r5hn`) | 3 | 12 |
| a `cons` pattern at a `Set` field, a negative control whose clause never holds (`wi936`, `wi1096`, `declared_field_type_readers`) | 4 | 5 |
| `docs/proposals/typing_pass_spec.anthill`'s `check_args`, `union_effects` over a column of no common type | 1 | 1 |
| this file's | 2 | 8 |

Decided with the user, 2026-10-22: a field's name is a `String` in every `FieldInfo` —
`KB.fields`'s, as it was at run time, and the loader's own `EntityInfo` / `OperationInfo`
records, which held the field's symbol; the signature reader resolves a parameter's symbol as
`<operation>.<name>`. `wi_9r5hn`'s 12 records go with it.

### 6.6 C1b, decision 3's refusals (WI-20261013-WF14Z, fourth part, 2026-10-22)

Every position the clause typing records as not fitting is a load error at its place, named by
the position, with both types as the whole clause leaves them (`ClauseDisagreement`,
`rules.rs`'s `push_clause_disagreements`). The count of §6.4 and §6.5, taken again on the
tree before this part (FieldInfo's `String` in), was 147 records in 80 tests and 29 in the
CLI's spawned binaries, the corpus none but `lf1`'s; each became a refusal or a rewritten
row. The record tally (`ANTHILL_CLAUSE_DISAGREEMENTS*`, `clause_disagreements_by_this_thread`)
is gone with it. Rows in `wi_wf14z_clause_typed_as_a_whole_test`, the ledger at its head.

| class | the error |
|---|---|
| a construction's argument against its field | `pt.x (entity-field): expected Int64, got String` |
| a rule goal's argument against the callee's column | `c._1 (rule-column): expected Int64, got String` |
| a head's bound against the body | `named_bad.x (rule-bound): expected String, got Int64` |
| the enclosing sort's parameter the body fixes | `Box3.T (sort-parameter): expected T, got Int64`; `Sat.C … got List[T = Bit]` |
| a call's result, a result column | `sign.return (op-return): expected Int64, got String`; a spec operation's result column is WI-1104's refusal, once |
| a dot's value | `<dot projection>.t (dot-projection): expected Int64, got String` |
| a demand on a value of some type | `ilen.n (op-arg): expected Int64, got a value of some type`, naming the column (`holds._1`) and the test that narrows it (`domain(?v, T)`) |
| a variable whose positions disagree | the walk's contradiction, "contradictory variable types", now in every rule: a namespace-level rule's went unreported |
| a member missing on a typed receiver | the dispatch walk's, as 0RRQP built it, at a receiver any position types |

A construction's field that an earlier check refused at the construction holding it — an
entity fact's own fields (`check_entity_facts`), a construction the dispatch walk types (an
entity goal's argument, an `=` operand) — is that check's one error; the fact sweep reads only
what the entity-fact check does not, a construction inside an argument and a relation fact's
arguments, so a refused file's facts and a hand-driven typer call over sorts alone are as before.

Found on the way, and fixed:

- *A construction is read at its position's parameters before its fields*, as an operation
  body reads an expected type into it: `h(inner: w2(a: ?x, b: "s"))` over `inner: W2[A = E, B
  = Int64]` is refused at `w2.b`; checked at parameters of its own it loaded (0RRQP's owed flip).
- *A sort's parameter written by its name in a bound* (`Wrap[T = T]` in a sort nested in the one
  that declares `T`) is the parameter, rigid; read as a name, `Outer.Inner`'s clause loaded.
- *A rigid parameter takes over a call's placeholder of a sort only by the some-coercion*: the
  argument check answers `Ok` for a pair it cannot decide, `List[T = e]` with `e` open against
  `C`, and `Sat.model`'s `vs <=> [?p, ?q, ?r]` loaded where `[1, 2]` was refused.
- *A field is read through the clause's substitution before the provider question*: a `cons`
  at a `List[T = Sp]` slot holds `Car`s and `Van`s.
- *A refused load's clauses are not refused again* (`KnowledgeBase::refused_load_clauses`,
  written at both error exits of a load). Its clauses stay in the knowledge base and a later
  load types every rule a seal does not hold, so they refused its corrected retry; a later load
  is held to every other clause, as one load over everything is — a fact it adds can leave an
  earlier clause's column of no common type, and that clause is refused there.
- The resolver's warning on two literal sorts said the typer cannot see a variable a predicate
  binds; it says a goal built at run time, or a value read through a column that says nothing
  of its type.

The rows, as decided (§6.4, §6.5, and with the user 2026-10-22 for the last):

- `lf1`'s `PostArmedExcursionBound.max_ticks` is a `Float`; the SMT fixtures that wrote an
  integer in a head beside a real (`wi_1kf32`'s `mode(0, ?r)`) write `0.0`, which their
  documents already read.
- A row whose subject is the run time over a clause now refused asks the goal at run time, a
  query (`common::pattern_hits`), and the written clause's refusal is a row beside it: the
  `cons` pattern at a `Set` field (`wi936`, `wi1096` ×2, `declared_field_type_readers`), the
  typed head's guards (`wi742`, `shed7` ×2, `qmfc5`, this file's `n1` / `n2`), the run-time
  refutation of a tie (`wi_5g28a`, `wi_80zv8`), `wi879`'s cross-sort pair and the CLI's
  `resolve_errors`.
- A fault row that reads the fault's written place or a relation over the faulting clause
  reads the value through a `Term` field, which says nothing of its type (user, 2026-10-22):
  `wi_8y5be`, the reflect bridge, `resolver_error_channel`.
- `fheek`'s claims compare `?y` with itself (`related` ties its columns, so `?y` is a `P`); the
  SMT translation's refusal of a construction is what they still reach. `zz7ph`'s application
  across two carriers is refused at load, "Scope.U … expected U, got T".

The flips owed: `a_body_that_fixes_a_sorts_parameter_is_refused` (with the bare-sort repair
loading), `a_constructor_that_does_not_fit_its_position_is_refused`, and SHED7's `Sat.model`
refused. Its repair, `vs <=> PersistentCollection[C = C].fromList([…])`, waits on the stdlib's
`fromList` (SHED7's step 3); with a stand-in spec it loads, and the relation flounders on the
call with no argument at its carrier parameter, which WI-20261013-RYDNV (C1d) supplies.

Left to C1b: decision 1's `-4` row (`a_slot_the_arguments_own_type_says_is_not_read`); the
citation's side of "some type", which closes a column whose whole type is a variable (0RRQP's
51 rows its measurement).

### 6.7 C1b, a named slot read off the citation (WI-20261013-WF14Z, fifth part, 2026-10-22)

Decision 1's last row. A citation routes each requirement read of the cited clauses
(`citation_requirement_routes`); a read whose witness the clause's own typing puts at a type a
named slot of one of its variables' types states is now answered by that slot as the citation
fixes it (`carried_slot_reading`), the way a call reads the slot off its argument's type
(`selections_from_slot_bindings`). In `sort Box { sort T = ?; requires O: WeakOrd[T]; entity
box(a: T, b: T) }`, `rule order(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y,
?c)` types `?p` as `Box[T = t, O = o]` and the read as `WeakOrd[T = t]`, which is `O` at those
bindings; cited as `Box.order(mk()).head.c` with `mk() -> Box[T = Int64, O = Ascending]`, `o`
is `Ascending`, and the read is resolved with `Ascending` selected for it (`resolve_route_pinned`).
Whether the read is the slot's is asked of the clause's typing before the citation fixes
anything (`ClauseTypes::stamped_type`), so a read at another type is not: `WeakOrd.compare(1, 5,
?c)` in the same clause answers `Int64`'s own, as the operation-body twin does. Rows in
`wi_0rrqp_clause_typed_through_constructor_test`, each beside its operation-body twin:

| cited | answers | twin |
|---|---|---|
| `Box.order(mk())`, the description's row (`a_slot_the_arguments_own_type_says_is_read`) | `-4` (was `-1`) | `Box.directOf(mk())`, `-4` |
| the witness a column, cited with and without its argument; a `Self` bound; positional fields; an alias `AscBox = CBox[T = Int64, O = Ascending]` | `-4` | `-4` |
| through `let b = desc()` and through a parameter `b: CBox[T = Int64, O = Descending]` | `4` | `4` |
| `WeakOrd.compare(1, 5, ?c)` | `-1` | `-1` |
| from `Holder`, which holds `W: WeakOrd[T = Int64]` selected `Descending` | `-4` (was `4`) | `-4` |
| `Pair2`'s `OK` and `OV` read off one argument, from outside the sort, at one element type and at two, and both in one clause | `4`, `-4`, `7` | — |
| `requires C: Conv[A = T, B = Int64]`, the read `Conv.conv(?x, ?c)` deciding `A` and leaving `B` | `11` (floundered) | `11` |

A read leaves open an element its witnesses do not decide (`witness_sort_goal`'s wildcard, the
spec's own parameter), so it is the slot's where every element it decides is the slot's
(`slot_states_the_read`), and the goal resolved is the slot's at the citation's types: the open
element against a provision that binds it is refused. A witness the slot is fixed to that does
not answer that goal is refused at the citation, as the member operation's call refuses it:
`mk() -> Box[T = String, O = Descending]` cited as `Box.order(mk())`, "Descending provides
WeakOrd, but not at the bindings this call to Box.order needs" — it loaded and the read derived
`String`'s own. A slot fixed to the caller's own parameter beside one fixed to a witness routes
nothing, as two witnesses do. These three were found by /code-review.

Not read, and routed as before: a slot the clause's bound writes (`?p: CBox[T = Int64, O =
Descending]` answers `Int64`'s own, `-1`, as the operation-body twin with that parameter type
does); a slot the citation leaves open or fixes to the caller's own type parameter, which the
caller's frame answers. A slot fixed to the caller's parameter (`cite[A](b: Box[T = A])`'s
`b.O`) is read from that parameter's own slot of the caller's frame. Two slots that state the
read and that the citation fixes to two providers were a stated limit here — routed nothing,
`-1` — and are refused since the seventh part (§6.9).

MEASURED: the full gate with the reading in and before the rows were written, 10343 / 1, the
description's row — nothing else moved. Backed out over `wi_0rrqp`, `wi_wf14z`, `wi_p7vp4`,
`wi_5g28a`, `wi_x9pb4`, `wi_ee0ep`, `wi1094` and `wi_shed7`, the six rows that hold a moved
answer fail, by the answer they had; the `Conv` row fails with each of its two halves backed
out alone too.

Left to C1b: the citation's side of "some type", which closes a column whose whole type is a
variable (0RRQP's 51 rows its measurement).

### 6.8 C1b, some type at a citation (WI-20261013-WF14Z, sixth part, 2026-10-22)

Decision 2's citation side. Rows in `wi_wf14z_clause_typed_as_a_whole_test` under "The
citation's side of some type", and the row that was its stated limit; the ledger at its head.

- **A column of some type is an unknown at each citation** (`ClauseColumn::some`,
  `some_type_columns_at_citation`): a fresh rigid in an operation body, a variable in a rule
  body's citation, as that keeps the relation's own. A column is of some type where the
  relation's clauses give it types with no join — two rule clauses at `Int64` and `String`,
  refused at the citation until now, "disjoint types for column" — or where a clause's
  variable is one a column of some type gives and nothing else types: `rule anyHolds(?x) :-
  holds(?x)` over `fact holds(1)` and `fact holds("a")`, read at the type its use asked for
  until now. A value of it goes where any type is taken (`mix.takeN(5).length()`), and a use
  that asks one type is refused there: `mix.head.v` returned as an `Int64`, "expected Int64,
  got ?v". An argument at such a column is a filter (`mix("a")`).
- **A relation that passes a column of some type on is of some type there too**, for a rule
  goal as for a citation (`clause_goal_columns`): `g(?r) :- anyHolds(?v), ?r <=> U.ilen(?v)`
  is refused as the goal on `holds` is, naming `anyHolds._1`, and `domain(?v, Int64)` narrows
  it. It was a column of every type, and `ilen` took the `String` as an `Int64`.
- **A column nothing in its clause names stays of every type** (kernel-language §5.3), read at
  the type its use asks for. Closing every column whose whole type is a variable, as the
  nested one is closed (`close_unfixed_clause_vars`), was measured on the full gate: it
  refused `wi730`'s negation over such a column, which a citation reads as a `String`. The 51
  rows 0RRQP measured on 2026-10-21 for it refuse nothing now — the clause typing reads a
  call's result — so the closing is the some-type columns', and no more.
- **Found and fixed: a later load reads a woven call as its call** (`clause_call_parts`). A
  clause's calls that owe a dictionary are stored woven (`apply_within`), and a later load
  types the stored clause again — its citations, its rule goals, its own re-check. The clause
  walk read only `Apply`, so the result column of `WeakOrd.compare(?a, ?b, ?r)` typed `?r` at
  the clause's own load and nothing at a later one: `sgn(1, 5).head.r` returned as a `String`
  loaded and answered the `Int64` `-1`, and `?r.abs()` in a later load's rule was data. The
  closing measurement above found it, through 0RRQP's two later-load rows.

- **A rule goal reads two clauses of different sorts with no join as some type**, a variable in
  either (`generalize_columns`): `k(?l) :- ?l <=> nil` beside `k(?l) :- isInt(?l)` was
  generalized to a column of every type, so a demand on `k`'s value loaded where the citation
  refuses it (found by /code-review).
- **A relation written at two arities gives its goals no columns** (`relation_goal_columns`):
  the load is refused for the arities, and a clause of one arity answers no goal of the other.
  Joined slot by slot, a later load's `fact reaches(1)` beside the library's two-argument
  `reaches` made library bodies read another way, which the typer oracle reported on
  `wi_6wvjb`'s row.
- **Not closed, and for a decision** (measured on the tree before this part too, with the typer
  oracle): a later load's clause at the right arity on a library relation that leaves a column
  of some type changes how sealed library bodies are read, and nothing refuses it — `fact
  reaches("a", "b")` makes `reaches._2` of some type, and the oracle reports `keep_modify`'s
  sealed body; with this part's passing-on the same fact reaches four of them through
  `origin._2`. The load is accepted and the sealed bodies are not typed again.

Rows moved: WI-714's guard rows over a genuinely disjoint pair (`wi714`'s
`wi714_disjoint_concrete_column_types_still_reject`, `wi741`'s two, `wi_9c2pz`'s
`the_inherited_type_reaches_the_published_schema`) are refused at the read that asks one
type, `expected List[T = (x: String)], got List[T = (x: ?x)]`, where they were refused at the
citation; the column is an unknown of the citation's, not `Term`, so WI-714's "never a silent
widen" holds. Their back-out claims that named the citation's refusal were not measured again,
and say so at their sites.

### 6.9 C1b, two providers refused and a dot through a slot (WI-20261013-WF14Z, seventh part, 2026-10-22)

Decided with the user, 2026-10-22, over this program (`CBox` declares `requires O:
WeakOrd[T]`):

```anthill
rule two(?p, ?q, ?c) :- ?p <=> cbox(a: ?x, b: ?y), ?q <=> cbox(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
operation cited() -> Int64 = CBox.two(asc(), desc()).head.c
operation twoOp[A](p: CBox[T = A], q: CBox[T = A]) -> Int64 =
  match q case cbox(a, b) -> WeakOrd.compare(a, b)
```

`?p`'s `O` and `?q`'s both state the read at their shared element, and `asc()` and `desc()`
fix them to `Ascending` and `Descending`; `twoOp`'s read is stated by `p`'s and `q`'s slots
alike. The citation answered `Int64`'s own, `-1`; the operation answered `p`'s order, `-4`,
comparing `q`'s values — by parameter order, `twoOp(desc(), asc())` gave `4`. Decided: **a read
two requirement slots may answer with two providers, and that names neither, is a load error**,
at the citation and in the operation body alike. The second is EE0EP's decision of 2026-09-22
(two parameters of one carrier are refused), which a call needing the second parameter's slot
already met (`AmbiguousWithFrame`) and a read answered from the first escaped.

- **The citation** (`carried_slot_reading`) classifies each slot that states the read: a
  witness the argument's type names, a parameter of the caller (`b.O`), the caller's type
  parameter (`O = P` written), or open. Two that differ are refused, naming both ("fix two
  requirement slots that state it, to `Ascending` and to `Descending`"; "to `Ascending` and to
  the caller's `?P`"). A parameter of the caller is read from its own slot of the caller's
  frame, so `first[A](b1: Box[T = A], b2: Box[T = A]) = Box.order(b1)` reads `b1`'s; one whose
  slot the collision screen dropped (`Box.order(b2)` there) is refused, as the call naming it
  is ("the frame holds one slot for both, `b1`'s"). A read no slot states, answered by the
  caller's frame, is refused where that frame's slot is contested (`contested_cover`).
- **The operation body**: the collision screen of `op_requires_chain_rc` still keeps the
  first parameter's slot and drops the second's, and now marks the kept one contested
  (`SupplySource::FromParam`'s `contested`). A call classified onto a contested slot is refused
  once per body, on the stored tree (`contested_slot_read`, "`p`'s slot `O` and `q`'s answer
  it, two parameters of one carrier, and the read names neither"), and so is an anonymous
  requirement forwarded through one (`build_dep_projection`, `Util.cmp(a, b)` with `cmp[A]
  requires WeakOrd[T = A]`). A callee's named slot read off an argument is not —
  `CBox.direct(p)` reads `p`'s, and the call naming `q` is refused as before.

**A dot through another variable's slot is that spec's call** (`find_spec_op_for_clause_slot`):
in `orderDot(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), ?c <=> ?x.compare(?y)`, `?x` is typed `t`
and `?p`'s `O` states `WeakOrd[T = t]`, so the dot is `WeakOrd.compare(?x, ?y)`, as
`a.compare(b)` is in a member of `Box` through `requires O: WeakOrd[T]`. It was data — the
citation handed back the term `1.compare(5)` declared an `Int64`. In a value slot the call
answers as its written twin there does, by the values, `Int64`'s own `-1`: the inference that
gives a goal-position call its condition (P7VP4's `inferred_demand`) declines an unpinned
body-less operation in a value slot, and retiring that refusal is WI-20261013-RYDNV's (C1d,
its description). Once it is retired the dot answers `4` / `-4` as the goal does, and the
two-box program's dot form is refused as the written one is.

MEASURED: each part backed out alone fails its own row (the ledger at the head of
`wi_wf14z_clause_typed_as_a_whole_test`).

### 6.10 C1b, a later clause on a sealed relation (WI-20261013-WF14Z, eighth part, 2026-10-22)

Decided with the user, 2026-10-22. A goal on a relation reads its columns from its clauses
(§6.3, §6.8), so a clause a later load adds to a relation the sealed standard library wrote
can change what the library's sealed bodies read, and those are not typed again. Measured
with the typer oracle: `fact reaches("a", "b")` beside the library's `reaches(?from, ?to)`
(both `Symbol`) left both columns of some type, and `keep_modify`'s `provenance(?r, input)` a
demand on one — refused in one load over both, loaded clean behind the seal. It predates
WF14Z (the oracle reported one body on the parent), and the sixth part's passing-on of some
type made it four.

The rule is kernel-language §8.3's fourth way a later load could reach a sealed body: a
clause, not a sealed load's, for a relation a sealed load wrote is refused where the
relation's columns over every clause are not those over the sealed load's clauses alone
(`sealed::clauses_that_change_a_sealed_relation`, `relation_columns_over`,
`first_column_read_apart`). A sealed load's relation is one with a clause in a sealed source,
whose bodies are typed once: the seal's clause mark also holds a program loaded in the standard
library's call, sealed only in part, whose readers are typed at every load and refuse a clause
that changes them themselves (found under `ANTHILL_TEST_FRESH_LOAD=1`, by
`a_refused_loads_clause_does_not_refuse_its_corrected_retry`, refused twice). A clause at the
columns' own types adds rows and loads; a relation at two arities is the arity check's. Rows in `wi_9bkz4_sealed_bodies_test` (its
library `tagged`/`doubled`): the clause refused in two calls, the library's reader refused in
one call over both, the control loading; the check backed out, the two-call half loads. The
gate's other rows were green with the check in: no test and no bundled program adds such a
clause.

### 6.11 C1c, a call typed as an operation body (WI-20261013-R1W5A, first part, 2026-10-23)

Decision 4, and decision 3's first two C1c classes. `kb/typing/rule_dispatch.rs`
(`CallDispatch::Fragment`, `rewritten_functional_goal`), `TypingEnv::as_fragment`
(`RuleText::Fragment`); rows in `wi_r1w5a_call_typed_as_an_operation_body_test`, the ledger at
its head.

- **An operation's application is typed whole**: in a value slot, and as the goal that is its
  call — `f(args)` of a `Bool`, `f(args, ?r)` on an operation no clause defines. The walk
  hands it to the typer as it hands a dot, equations on, and stores the typed node. Before it
  was a data term the walk only name-checked. A goal `f(args, ?r)` whose call an equation
  rewrites is stored as `?r <=> <the rewritten call>`. A dotted name (`field_access`) is no
  call (§5.1), a comparison's operands are the rule's own term, and a goal of another shape
  is the goal check's to refuse.
- **What it is typed in is the operation body's text** (`RuleText::Fragment`), and so is every
  call the walk types whole — a dot and a defaulted spec operation anywhere, a body-less spec
  operation in a value slot — and the clause typing's reading of a dot: a literal, a `()` an
  equation leaves and a bare operation name (`Ref`, hinted as `VarRef` is) read as an
  operation body reads them. A comparison goal (`=` and its family as a goal) keeps the rule's
  text: its operands are data.
- **A callee's own `requires` there is the clause's condition**, as it was: the fragment's
  typing neither stamps the operation's slots nor refuses one, and the clause's inference
  (`infer_rule_body_requirements`) weaves it as before. Stamped, the slot read as known and the
  inference declined it: `Util.isLess(x: ?a, y: ?b)` answered under `Int64`'s own order
  where the caller's `Descending` was selected. Making the typer's classification the
  inference's input is C1d's.
- **Decided with the user, 2026-10-23**: a `cons`/`nil` spine at a position that declares its
  element type is checked as the literal it is lowered from, in both bodies (kernel-language
  §4.6; `spine_field_expected`, the seed in `check_constructor_iter`); and a type written in a
  call's argument — a dotted sort path, a sort's bracket — is the type value it denotes, as in
  an operation body (`Loader::written_type_in_call_argument`). For a call in a value slot and
  a dot's: a goal's arguments stay the rule's own term, since whether a goal on an operation is
  its call or a relation its clauses define is known only once every clause is loaded, and a
  goal holding such a type keeps the reading it has as a goal (`holds_a_type_as_the_rules_term`).
  Found by `/code-review`: with the goal's arguments built as a call's, `f(Outer.Inner)` over
  `rule f(Outer.Inner) :- true` stopped matching its own clause. Typed field by field, the rule
  body's `total([car(n: 1), van(n: 2)])` was refused (`cons.tail: expected List[T = Car], got
  List[T = Van]`) where the operation body's literal loads; and `which(Outer.Inner)`, today 0
  (the chain), was refused, a plain reference to the sort.
- **Found and fixed:** the clause typing read a call's positional arguments only, so a
  labelled argument typed nothing (`constrain_application`); its typer stamp then read as a
  known type to the inference above.

| written | before | now |
|---|---|---|
| `?x <=> dbl(2)`; the goal `dbl(2, ?x)` | residual; nothing | 4; 4 |
| `?x <=> Box.open(Box.mk(4))` beside the dot and the parametric sort's call | residual | 4, as both |
| `?r <=> Tw.twice(m(v: 3), "km")`, a law over `Conv.conv` | residual | 14 |
| `?r <=> takes(Box.mk(4).nothing(), 4)` (7G99A's program 5) | refused, `expected Unit, got ()` | 4 |
| `viaHead(3, ?r)`, `?a: Int64` at `Option[T = Int64]` | `match_failed` | 3 |
| `isPos(3)` over `rule isPos(?n) <=> ?n > 0 @[simp]` | nothing; `not(isPos(3))` held | holds |
| `?c <=> sub2(1, 5, 9)`, `sub2(1, 5, bogus: 9)`, `sub2(1)`, `sub2("a", 5)`, the goal `rep(3, 3, ?c)` | -4, -4, residual, fault, `3` | refused, as in an operation body |
| `?x <=> app(dbl, 2)` | residual | refused, as in an operation body |
| `?r <=> named_match((1, 2))` at `(a: Int64, b: Int64)` | 3 | refused, as in an operation body |

**The count** (with the refusals recorded and nothing refused): the corpus of §1.2 records
nothing. The suite (gate 10567): 30 records in 26 tests, every one a row built to be refused —
this file's 3, the other checks' refusals this typing now gives too (`wi1056` ×2, `wi1104`,
`wi710` ×2, `wi839`, `wi753`, `wi756` ×2, `wi_wf14z`, `wi_mhrn1`'s labelled goal ×2,
`wi_nr6fj`, `wi_2sz88` ×2, `wi_a3fy2` ×4, `wi_fcz3n`), the ones it now owns (`wi_50b2k` ×4,
`wi_fc2x4`), and the two rows that turn (`wi_mhrn1`'s left-over argument, `wi_qqpq2`'s
positional tuple at a named slot), each rewritten to its written clause's refusal beside the
run-time goal it drove. Taken before the readings above were fixed, the first count was 157
records in 83 tests: an operation's own requirement, 63 in 43 (`wi_p7vp4`, `wi_nekr0`,
`wi_prva2`, `wi_gfs6a`, `wi_n31xx`, `wi_nr6fj`); a dotted name or a type written in a call's
argument read as a value, 48 in 11 (`dotted_nullary_op_call`, `wi_4nekz`, `wi_rxt6s`,
`wi_tcsgt`); the spine (`wi_m32c2`); a labelled bare operation reference (`wi_50b2k`); and the
rows built to be refused above.

Rows moved by design: `wi_rxt6s`'s `a_rule_bodys_call_argument_is_the_sort` (21, was 0);
`wi_mhrn1`'s and `wi_qqpq2`'s rows above; `wi_80zv8`'s join and `wi872`'s nested collision now
reach their argument through a `let` or a generic identity, since at a declaring slot the
spine is checked field by field.

Three readings make a rule body's own term inside a call read as an operation body's, each at
its reader: a bare operation name (`Ref`, hinted as `VarRef` is), a written type (built by the
operation-body walk), and the spine (hinted in the Apply arm). Building a call's arguments with
the operation-body walk, as a compound expression is built, would retire all three; readers
that tell `VarRef` from `Ref` and that this part did not reach (`leaf_var_ref`,
`arg_is_bare_operation_name`, `varref_arg_env_type`) still see the rule's spelling.

Left to C1c: decision 3's third class, an effectful application refused by its typed row,
with the run-time half of the 2026-10-21 row (an effectful operation's goal undecided where no
typer sees it); kernel-language §5.3's statement of it. Built in §6.12.

### 6.12 C1c, an effectful call refused by its typed row (WI-20261013-R1W5A, second part, 2026-10-23)

Decision 3's third class, and the run-time half of the ticket's 2026-10-21 row.
`kb/typing/rule_dispatch.rs` (`refuse_performed_effects`, `performed_in_a_rule_body`),
`TypeError::RuleBodyEffect`; `kb/resolve.rs` (`KnowledgeBase::effectful_goal_declined`, the
bridge's `note_bridge_error`); rows in `wi_r1w5a_effectful_call_refused_test`, the ledger at its
head. kernel-language §5.3, "A rule body performs no effect".

- **A call the walk types whose row holds an effect other than `Error` is refused at its
  place**, naming the call and the effect: an operation's application, a dot, a spec
  operation's call, a `let` or a `match`. The row is read as at an operation's boundary: a
  `let`'s own resource is dropped (`external_effects`), and a `Modify` of a fresh region where
  the call's value type cannot carry one (`result_type_admits_region`); `Modify[result]` that
  the value carries out counts. A member that is a row variable or a parameter's projection
  names no effect.
- **A function a rule hands over is held to its own row** (user, 2026-10-23): one in a
  relation goal's argument, or in a value built there, and one handed to an operation whose
  row stays open — a callback that writes its own parameter fixes no row parameter
  (`useVia(?c, lambda (x) -> Cell.set(x, 9), ?u)`; the operation-body twin is refused
  "unconstrained Rho", WI-270), at a parameter the call applies — one whose row names a row
  parameter of the operation's own row (`applied_function_args`); `op2(?f, lambda () ->
  stamp(), ?x)` over `effects {R1}` with `g: () -> Int64 @ {R2}` loads, as in an operation
  body. Its type is the clause's for a rule variable, else the one the walk gave it
  (`value_type_in_clause`); a rule variable whose function the clause does not type names
  nothing, so `applies` itself, `rule applies(?f, ?r) :- applyThunk(?f, ?r)`, loads. Each is
  refused where it is written: two in one goal are two refusals. Before, such a function answered nothing, silently: handed through a relation's
  head it does not reach the call.
- **Once.** A call this walk enters before it types the whole atom — `=`, arithmetic, another
  body-less spec operation — skips an effect a call beneath it reported. A fact pattern
  performs only what its arguments do, each typed first. An equation's guard is the
  effectful-rewrite gate's (`check_simp_effectful_ops`), which refuses every operation it
  names whose row holds any effect.
- **Run time.** A goal on an effectful operation that no clause writes — a query's, or one a
  rule builds at run time — is declined in `step_init` with the fault the bridge reports for
  a declined effect, through the bridge's own disposition of it, and is undecided. It fell to
  candidate selection, found no clause, and failed, so `not(stamp(3))` held.
- **Found and fixed, the first part's:** a goal `f(args, ?r)` dropped the error of typing its
  call `f(args)` and was typed as written, where no equation fires, so a call an equation
  rewrites into a refused one was refused in the value-slot spelling alone. The error is the
  goal's. The call is typed apart from the goal only where an enabled equation's left side is
  headed by `f` (`stored_lhs_functor`); any other goal is typed as written, with its result
  column.
- **Found by `/code-review`, and fixed:** the decline read a goal's `Bool` reading strictly
  where the typer reads a result that may be a `Bool` (`pick(true)` over `pick[T](x: T) -> T`
  failed silently), and named a guarded member by its wrapper (`EffectExpression.guarded`). The
  reading is now one (`KnowledgeBase::operation_goal_reading`), the member read past `X :- g`
  (`typing::declared_member_kind`), and the views and the decline share one eligibility
  (`reducible_operation`).

| written | before | now |
|---|---|---|
| `hofWR(?v)`, `hofRW(?v)` over `mkVia(lambda () -> Cell.new(3), ?c)` | 9, 3 | refused, `mkVia` performs `Modify[result]` |
| `mkVia(lambda () -> Cell.new(3), ?c)` | binds a `<Cell>` | refused |
| `applyThunk(lambda () -> now(), ?r)`, `?r <=> plainStamp()` | conditional, the decline reported | refused, `Clock` |
| `now(?r)` | nothing, silently | refused |
| `not(now("2000"))`, `not(plainStamp("2000"))`, `not(stamp(3))` | hold | refused |
| `localCell(3, ?r)`, the cell kept to itself | 9 | 9 |
| the queries `stamp(3)`, `not(stamp(3))`; `apply2(stampAt, 1, ?r)` over `?p(?x, ?r)` | nothing, holds; nothing | undecided, reported |

**The count** (refusals recorded, nothing refused): the corpus of §1.2 records nothing. The
suite: 66 records in 28 tests, every one a row built around an effectful rule-body call — the
9WVT7 routes (`wi_9wvt7_clock_handler` ×10, `wi_9wvt7_reify_rule_body` ×4, `wi_9wvt7_review5`),
NFXPZ's `clkErr` ×8 (one program), DQD5W's `loud_fires`, NX4FD's `loud_r`, VPEWK's `clk` ×2, and
`wi698`'s `@[simp]` guard, the rewrite gate's, left to it. Each moved row asks a goal no typer
sees — a query's goal or value slot, or a goal a rule builds at run time with `?p(?x, ?r)` over
an operation passed as data — with the written clause's refusal beside it (§6.6's convention).

Not this part's, measured on the way, each the same on 083cb6b8:

- A closure handed to another relation through its head answers nothing, pure or not
  (`pureThunk(?f), thunkVia(?f, ?r)`); in one clause it answers. An effectful one is refused
  where it is handed over (above); a pure one still answers nothing.
- A rule variable bound to a lambda by `<=>` is not typed by it, so `?f <=> lambda () -> now(),
  applies(?f, ?r)` loads, and so does a caller of `rule giveF(?f) :- ?f <=> lambda () -> now()`
  that hands `giveF`'s column on; a rule variable typed as a data sort that holds an effectful
  function (`?b <=> box(f: lambda () -> now()), holds(?b, ?r)`) is not read either.
- `import probe.imp.{c}` resolves to an operation's parameter `c` (`useIt(c: Int64)`) rather
  than the relation `c` the namespace's facts define, so a goal `c(?x)` answers nothing.
- A lambda in a query pattern, and an operation name passed as data and applied as a function
  value, are no function values at run time ("unknown operation: applyThunk.f").
- A query's nullary call is the operation's name as data: `not(plainStamp() = "x")` holds.
- A `let` in a rule body's value slot, also in a call's argument, is bound unevaluated.
- A constraint's goal is not walked by the clause typing (WI-20261023-76KZN):
  `constraint c :- plainStamp() = "2000"` loads.
- A guarded effect on a program's operation is dropped at every literal call: `safe(0)` over
  `effects {Error[Boom] :- eq(n, 0)}` loads in an operation body that declares no `Error`, and
  `stampIf(true)` over `{Clock :- eq(b, true)}` in a rule body; the stdlib's `Int64.div(7, 0)`
  is refused.

## 7. Testing

Per CLAUDE.md: each ticket's rows live in one test module, driven by value with its back-outs run
against that module alone (`scripts/test.sh -p anthill-core --test wi_tests -- <module>`); the
full workspace runs once per increment. The census fixtures of §1.1 are the starting fixtures.

## 8. Open

1. Cost: `run_in_bridge_interp` builds an interpreter per call, and a run-time dictionary
   derivation is re-resolved on every call (WI-20260926-QPC89). Measure before and after K4JGC —
   including D3's scan of every goal bound for candidate selection, which decides whether the
   load-time flag is needed.
2. Precise blockers (D1's later half).
3. Splicing a plain `Term` against 058 §3.10 (068 §7.3) — WI-189's.
