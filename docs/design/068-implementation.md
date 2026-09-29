# 068 implementation — an operation application in a rule body is a computation

## Status: Draft (2026-09-29), owned by WI-20260926-ACG10. The proposal is
[`../proposals/068-rule-body-operation-applications.md`](../proposals/068-rule-body-operation-applications.md);
this document owns HOW. Decided with the user (2026-09-29): D1–D7 (§3).

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
| delay | `delay_goal` | re-evaluates from scratch on every rotation | CYNPE: skip unless a blocker was bound |
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

## 6. 7D48J and DSEXA

Their tickets hold their design questions: 7D48J — the clause environment, how far data is typed
(0RRQP's `<=>`-with-constructor tie), the typer's per-call classification as P7VP4's one input,
the census's typing count, and Y6ZCD's single dispatch decision; DSEXA — `?d` as a blocker, the
retired per-consumer reductions, the unfold threading dictionaries.

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
