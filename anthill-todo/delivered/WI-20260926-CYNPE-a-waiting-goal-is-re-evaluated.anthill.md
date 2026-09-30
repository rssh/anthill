## Attributes

- id: WI-20260926-CYNPE-a-waiting-goal-is-re-evaluated
- created: 2026-09-26T09:48:10Z

- status: Delivered
- status_agent: user
- status_at: 2026-09-30T19:59:56Z

- acceptance: cargo-test

- tags: proposal-068

## Description

A WAITING GOAL IS RE-EVALUATED FROM SCRATCH ON EVERY ROTATION, AND A GOAL THAT CAN NEVER BE DECIDED IS RETRIED AS IF IT COULD — proposal 068 §2.2, the run-time half. Filed from the ACG10 review (step A1 of the 068/060 sequence).

TODAY. `delay_goal` (resolve.rs) moves a delayed goal to the back and counts consecutive delays; every time a sibling makes progress the count resets and the goal is evaluated again from scratch — which can include a bridge run, and `run_in_bridge_interp` builds a fresh interpreter and registers the builtins on every call. `BuiltinResult::Unknown` ("nothing will ever instantiate it") is scheduled exactly as `Delay` ("re-ask me"). And the bridge's three decline reasons — an unbound argument, no supplier, a supplier tie — collapse into ONE fall-through in the WI-938 hook, which then tries ordinary candidate selection and, with no clause written, answers NOTHING, silently (WI-20260924-35E14).

WHAT 068 §2.2 DECIDES. A goal that cannot be evaluated YET is SUSPENDED and carries its BLOCKERS — the variables whose binding could change its answer. On its turn it is skipped WITHOUT re-evaluation unless a blocker has been bound since it suspended; it residualizes, as today, when only waiting goals remain. A goal that can NEVER be evaluated is UNREDUCED: PARKED — it keeps its place behind its siblings (a sibling that fails still refutes the clause, and a refutation must win over an undecided answer), is never asked again, and joins the residual as a NAMED cause. The blockers live on the frame's goal entry, never on the occurrence: occurrences are `Rc`-shared across derivations, and a σ-dependent mark on one would leak into another. Of the three bridge declines, the unbound argument is SUSPENDED (blocker: that variable) and no-supplier / tie are UNREDUCED.

No 060 dependency: a blocker is a variable, whatever will bind it. A woven call's dictionary `?d` as a blocker is step D1.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): 35E14's rows, re-measured on current main first (P7VP4's weaving already moved part of that population): `rule late(x: Colour) :- Score.score(x, 3)` answers `blue`; `rule unbound(?r) :- Score.score(?v, ?r)` ends as a CONDITIONAL answer carrying the call, not "no solutions". A suspended goal whose blockers are never bound is evaluated ONCE, not once per sibling's progress (counted, not timed). An UNREDUCED goal (no supplier) yields an undecided residual naming its cause, and a failing sibling still makes the clause answer 0 definitely. CONTROLS, stated at their sites: WI-519's residual rows unchanged; classic-mini unchanged (tiny-sat 2, alphabet-words 27/12/100, map-colouring 6).

## Changes

### 2026-09-26T13:26:23Z — feedback — user

ROW ADDED FROM THE PRVA2 REVIEW (filed on ACG10 2026-09-26): a rule-body call value dispatch cannot evaluate answers NOTHING, silently — Conv.tag(b: B) has no argument at Conv's carrier parameter A, so ?s <=> "km", Conv.tag(?s, ?r) answers no solutions (the operation-body twin fails at run time, 'operation has no body'); with require[Conv[A = Meters, B = String]] it answers 3. The 35E14 class. Whatever reaches run time here is UNREDUCED or SUSPENDED under 068 §2 — a named undecided residual, never an empty answer; the load-time half (060 §3's anchor rule) is WI-20260926-7D48J's. Joins the acceptance, driven.

### 2026-09-30T19:59:34Z — feedback — user

DELIVERED in 049118a8 (2026-09-30). Frame goals carry their wait state (FrameGoal { goal, wait }, Wait::{Ready, Suspended { blockers, cause }, Parked}), frame-local; ResolverFrame::undecided removed (the gate reads causes off waits). Blockers are D1's coarse ones, computed where the goal waits (BuiltinResult::Delay gains none); a waiting goal whose blockers are unbound is PASSED OVER on its turn, counting toward the gate. UNREDUCED parks unless a call in its arguments still waits on a variable (ABSENT outranks UNREDUCED — found by /code-review: div(1, ?z) = Conv.tag("km"), ?z later 0, must refute). Universal-undecided and faults wait on blockers with their cause. The WI-938 hook answers a stuck call with its state on the goal as written (SUSPENDED/SYMBOLIC delay, UNREDUCED undecided, ABSENT fails) instead of candidate selection; a hypothesis in scope (forall_impl antecedent, Γ fact) still answers it — found by probe, the old fall-through let (forall(?c), score(?c, 3) -: score(?c, 3)) answer 1. Rows: 35E14's late -> blue, unbound -> conditional carrying the call; Conv.tag(?s, ?r) -> UNDECIDED naming Unreduced; a suspended goal asked once among progressing siblings (4 before, counted by ResolveStats::goals_asked); a parked goal behind a failing sibling -> 0 definitely. Supplier TIE: refused at load where the typer sees the carrier; at run time (NAR1X's carrier-less no-require row, two providers) UNREDUCED. Controls: wi519, classic-mini unchanged. Five rows that pinned the silent empty answer now pin UNDECIDED (nar1x, s8cbv, 96ztm, wi1043, anthill-stl exhaustion row). Spec: kernel-language §5.3/§8.3 (user-approved); design 068-implementation §4.1. Recorded, not changed: a recursive clause relying on a stuck call's failure now recurses to max_depth (TRUNCATED instead of a wrong complete 0). Workspace green: 7864 passed.

