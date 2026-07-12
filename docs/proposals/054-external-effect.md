# 054: The `External` Effect

## Status: Proposed — design settled in the WI-437 backend design sessions (2026-07-12); implementation tracked by WI-698.

## Tracks: WI-698, the **umbrella** — split 2026-07-12 into: **WI-699** = §"Declaration" + row surface (scope (a)+(b); the whole critical path to the first consumer); **WI-700** = effect-row conformance and lacks enforcement at explicit row-instantiation shapes (a *general* soundness hole, not `External`-specific — the check the §"Mechanism" gate rests on); **WI-701** = the §"`Branch` and `External`" co-occurrence gate; **WI-702** = the §"Consumers" purity gates (loudness + the `[simp]`-tag formation hole); **WI-703** = the `EffectsRuntime`-import wart (a sibling defect in the WI-320 anchor, not a prerequisite). Where the text below says "WI-698 scope item (c)", read WI-700/701/702. Scope item (d) is this proposal; (e) is a no-op by decision.

## First consumer: WI-437 increment 3 (the `Mirror` carrier of `rustland/anthill-todo/docs/design/backend-github-coordination.md` §8.3) — which depends on **WI-699 alone**, not on the umbrella: the hardening gates are not on its path.

## Relates to: 037 (Modify — tracked-heap mutation; `External` is its complement for state the typer cannot see; 037's branch-interaction contracts are exactly what `External` state cannot offer), 027 + 027.2 + 027.3 (`Branch`, `register_undo`, solvers — §"`Branch` and `External`" below), 045 (effect rows — `External` is an ordinary row member, no new machinery), 047 (effects as monads via reflection — its §8 rank ordering is the table `External` can join at *no* rank), 053 (fact mutability — its eval-side guard family is the shape `External`'s decline-gates join), WI-347 (refine-don't-widen spec rows — the mechanism of §"Faking"), WI-329 (row-discharge typing — what makes the `Branch` gate compositional), `prelude/time.anthill` + `prelude/console.anthill` (the proto-`External` precedents).

## Problem

Bundle code increasingly reaches outside the interpreter. The WI-437 tracker
backend calls a forge to allocate ids and push a mirror; provisional ids need
host entropy; future backends will speak HTTP or a database. The effect
vocabulary today offers two shapes for "outside", and neither is honest for
these cases:

1. **A per-capability ambient effect** — `ConsoleOutput`, `ConsoleError`,
   `Clock`. This does not scale: every new capability mints a new row member,
   every shared spec that admits an external implementation churns through the
   widen/refine dance (WI-347) *per name*, and the typer's row machinery grows
   distinctions that no consumer of the row ever uses. Tellingly,
   `prelude/time.anthill` already states `Clock`'s purpose as identifying
   "which operations are non-deterministic by virtue of consulting external
   state" — that is not a fact about clocks; it is the general concept, spelled
   per-capability. This proposal names the concept once.

2. **Absorption under `Modify[s]` via a carrier** — the persistence pattern:
   `persist`/`retract`/`flush` on an `IndexedFileStore` ride 037's
   reachability transitivity, so store ops need only `{Modify[s], Error}`.
   For genuinely external state this is a fiction (the GitHub issue registry
   is not "state reachable from a handle in the heap"), and the fiction has a
   hole exactly where it matters — **reads**. A read of external state mutates
   nothing in-process, so this convention types it `Error`-only, like
   `WorkItemStore.lookup`. `Error`-only is *honest* for `lookup`: the KB
   changes only through tracked `Modify`, so two successive reads with no
   intervening tracked mutation agree. It is *dishonest* for
   `recent_issues(m)`: another writer changes the registry between two calls,
   with no tracked mutation anywhere in the program. No combination of
   `Modify` and `Error` can say that.

## The effect

One new effect, generic over every outside world:

> An operation is `External` iff its result or behavior depends on, or
> changes, state **outside the tracked heap** — state that can change with no
> `Modify` visible to the typer.

What it revokes is the license package that pure code grants the machine:

| license (pure code) | under `External` |
|---|---|
| re-run / replay (evaluation is unobservable) | never — execution is observable outside the process |
| reorder across other calls | never — order is observable |
| deduplicate / CSE two identical calls | never — `create_issue` twice is two issues |
| drop if the result is unused | never |
| use results equationally (simp, prover) | never — `f(x) = f(x)` does not hold across calls |

Two increments over the existing vocabulary, precisely:

* **Over any non-empty row** (e.g. `Error` alone): sequencing is already
  pinned — any effectful op has an observable position in evaluation order.
  What `External` adds is *external non-determinism*: two calls may disagree
  although no tracked `Modify` intervenes, and no replay is ever sound.
* **Over `Modify`**: `Modify` keeps its job — in-process state, 037
  transitivity, 053's retract guard. Neither effect subsumes the other, and an
  operation may carry both: WI-437's `alloc_id` stashes the pending
  `(id, issue number)` in its state cell (`Modify[s]`) *and* talks to the
  forge (`External`). Note the converse too: the real, forge-backed
  `create_issue` carries **no** `Modify` — it changes the world, not the
  heap, and pretending the registry is heap-reachable is the fiction this
  proposal retires. (Its *spec* row below still carries `Modify[m]` — the
  row over all implementations, because the fake's registry IS heap state;
  §"Faking" / §"Mechanism".)

## Effects carry semantics; carriers carry authority

`External` is deliberately **one effect, not one per capability**. The row
answers the machine's question — *what may I still assume and transform?* —
and every external capability revokes exactly the same licenses, so
distinguishing them in the row adds nothing the machine can use.

The question the distinctions *do* answer — *what may this code reach?* — is
**authority**, and authority lives in **values**: an operation on the forge
takes the `Mirror` carrier, and the bundle cannot touch the registry without
holding it (the `IndexedFileStore` precedent; the WI-402 factory decides which
implementation a run holds — `gh`-backed or fake). A future capability system
refines authority without ever touching the effect vocabulary. That is the
stability payoff: rows like `{Modify[s], External, Error}` cover any backend
we will ever write, and no shared spec churns again as backends multiply.

## Declaration

The `Clock` convention — an effect is a sort plus an `Effect` marker fact —
in a new prelude file (exact enclosing sort is WI-698's call):

```anthill
-- stdlib/anthill/prelude/external.anthill
sort anthill.prelude.Externality
  import anthill.prelude.{Effect}

  -- Effect kind. Resource-less at the effect level, deliberately: WHICH
  -- external resource an operation touches is the carrier argument's
  -- business (authority = possession), not the row's.
  sort External
  end
  fact Effect[T = External]
end
```

Rows in practice (WI-437 §6.2/§8.3):

```anthill
operation create_issue(m: Mirror, title: String, body: String) -> Int64
  effects {Modify[m], External, Error}     -- union over implementations (§Faking):
                                           -- the real carrier refines away Modify[m],
                                           -- the fake refines away External
operation recent_issues(m: Mirror, limit: Int64) -> List[T = IssueInfo]
  effects {External, Error}                -- the load-bearing READ case; the fake
                                           -- refines it to {Error}

operation fresh_token() -> String          -- ambient host entropy
  effects {External, Error}

-- a spec that admits an external impl declares it, so the impl
-- refines rather than widens (WI-347):
operation alloc_id(s: Cell[V = State], summary: String) -> String
  effects {Modify[s], External, Error}
```

No new grammar: `External` is an ordinary member of written rows (WI-375
surface) and of row unification.

## Consumers that must decline it — loudly

The machinery whose soundness is conditioned on purity must decline
`External`-rowed operations. The soundness half of that gate **already
exists, and is blanket**: the defining-equation family
(`op_defining_equations`, `synthesize_op_defining_rule(_at)`, the WI-669
tier) routes through a shared purity gate — "an effectful body is not an
equation" (`body_specialize.rs`, `defining_equations`) — that declines *any*
op with a non-empty effect row or `requires`, with twins on the SLD unfold
path (`folded_call_match`) and the relational-view grant
(`bare_bodied_bool_relation`, `resolve.rs`). An `External`-rowed op is
therefore declined **for free**, and the gate's predicate is already the
principled one — function-hood, not the absence of one named effect: a
`Modify`-carrying body is not an equation either, and the existing blanket
check knows it.

What WI-698 scope item (c) actually changes is therefore **loudness and one
formation hole**, not soundness:

* the existing declines are silent (`return None`) — correct on bulk
  enumeration paths, but where a consumer *specifically requests* equations
  for an op (a proof tactic citing them, a simp-tag on its rule), an
  `External` row must produce a loud diagnostic rather than a quiet absence,
  per the repo's loud-over-silent principle;
* the simp rewriter (`fire_simp`) checks no effect rows at the firing site —
  sound today only because effectful ops never *become* simp equations
  (formation is gated as above). The one real hole is a **user-written**
  `[simp]`-tagged equation rule whose sides mention an `External`-rowed
  operation symbol: firing it would duplicate, reorder, or drop the call by
  rewriting. The gate for that belongs at load-time tag validation, not the
  firing site;
* any future memoization or CSE joins the same decline list.

## `Branch` and `External`: incompatible by construction

Proposal 027 gives nondeterminism as an effect: `Branch` — `branch`/`fail`,
generalized by 027.2's `reflect(stream)` — interpreted as resolver choice
points, with solvers (`all`/`one`/`once`/`beam`/`oracle`, 027.2) as the
handlers that reify a search region into a stream. For state under search,
027/037/047 §8 offer a resource exactly two lawful contracts: ranked **above**
`Branch`, it is snapshotted on entry and rolled back on backtrack
(`register_undo`, 027 §RuntimeAPI); ranked **below**, it survives across
branches (the audit-log reading). Both rest on one premise: *the runtime
mediates every change to the resource*, so it can snapshot it, undo it, or
knowingly let each write stand.

`External` names the state for which that premise fails — so neither contract
is available:

* **Above `Branch` is impossible.** There is no `register_undo` for the world.
  A branch that `fail()`s after `create_issue` cannot be unwound: the issue
  number is burnt, the notification sent, another writer may already have read
  the registry. Search would leave debris in the world on behalf of
  computations that officially never happened — a dangling allocation minted
  by backtracking.
* **Below `Branch` is unsound in practice.** A solver multi-shot-resumes the
  continuation once per solution (027.2's eval↔SLD switch), so an `External`
  call reached after a `reflect` runs **once per branch**: `create_issue`
  inside a ten-solution region mints ten issues. Even pure *reads* break the
  search: `recent_issues` re-executed per branch can answer differently in
  different branches — the branches are then exploring different worlds, and
  the "solutions" are no longer answers to one question.

027 already rules that plain sticky-under-`Branch` is "a soundness hazard,
not a feature" for tracked resources that merely *lack* the snapshot hooks
today. `External` is the state for which the hooks are impossible in
principle; the hazard is permanent. Hence the rule, joining the §"Consumers"
gates (WI-698 scope item (c)):

> **A `Branch` region may not perform `External`.** The typer rejects a row
> that carries both. With WI-329's row-discharge typing (047 §9 step 5) the
> rule is compositional and exact: a solver's reify discharges `Branch` from
> the row, so `External` becomes legal again at precisely the point where the
> search has committed to its solutions.

The sound composition is a sandwich, and it is already this repo's idiom:
**read the world before the search; search over tracked state only; write the
world after the commit.** WI-437 does it twice — the store buffers mutations
and flushes once (its §5.1), and autonomous mode records intent as tracked
facts and lets `sync` perform the external act later (its §6.4).

## Faking an external entity = moving its state back inside the heap

The fake `Mirror` (WI-437 §8.3) looks like a test convenience; under this
proposal it is a **change of effect class**, and that is exactly what makes it
compose with `Branch` — which a test harness wants precisely so it can
*search* over protocol schedules. The typical process for faking an external
entity:

1. **The seam is a carrier** — one abstract sort; authority is possession
   (§"carriers carry authority"), so the code under test cannot tell.
2. **The spec row is the union over implementations** — a mutator declares
   `{Modify[m], External, Error}`, "may mutate the carrier's tracked state
   and/or touch the world" — and each implementation *refines* it (WI-347):
   the real one to `{External, Error}`, the fake to `{Modify[m], Error}`;
   reads union to `{External, Error}`, which the fake refines to `{Error}`.
   (How refinement reaches *call sites* — the union as a row parameter's
   upper bound, refinement as instantiation — is §"Mechanism" below.)
3. **The fake's state is an ordinary tracked resource** — an in-memory
   registry — implementing 037's branch-interaction contract like any other
   `Modify` resource: snapshotted on `Branch` entry, unwound by
   `register_undo` on backtrack.
4. **Therefore the fake composes with `Branch` while the real one cannot.**
   A search explores schedules against the fake registry and every abandoned
   branch rolls it back: `oracle(xs)` (027.2) replays one chosen interleaving —
   WI-437's "the fake can force the lost-race interleavings deterministically"
   is this, said informally; `all` enumerates every interleaving of a finite
   schedule space and checks an invariant (*no duplicate ids*) across the lot;
   `beam` guides longer schedules.
5. **The static gate stays sound on both sides.** Production code is typed
   against the spec, whose row carries `External` — `Branch`-forbidden,
   correctly, because the carrier might be the world. Test code that
   concretely holds the fake gets the refined rows without `External` —
   `Branch`-welcome.

In one sentence: *a fake works exactly because it moves the state back inside
the heap, where the runtime's transaction machinery reaches — `External`
disappears by row refinement, and `Branch`-compatibility appears for the same
reason at the same moment.*

## Mechanism: the spec row is a parameter, not a hand-maintained union

Step 5 needs the *same* protocol code to be `External`-rowed under the real
carrier and `External`-free under the fake. A ground row can never do that —
and impl-row dispatch cannot rescue it: the typer anchors every call to the
spec's declared row and only ever *union-merges* an impl's row in
(`merge_effects_into`; the WI-453 additive-only direction, deliberate). What
does carry it is row **variables tied to the carrier** — the delivered
WI-320 `effects E = ?` anchor, because spec-anchored call rows are taken
*after type-argument substitution* (`substituted_op_effects`). Two variables,
not one: reads and mutators refine independently (§Faking step 2 gives them
different rows), so the carrier's outside-ness splits into a read row and a
write row — precisely the WI-441 decoupled-rows precedent, shipped as
MappedStream's `ES`/`EF` pair:

```anthill
sort Mirror
  sort C = ?
  effects ER = ?                       -- the carrier's READ outside-ness
  effects EW = ?                       -- ...and its WRITE outside-ness (WI-441 split)
  operation recent_issues(m: C, limit: Int64) -> List[T = IssueInfo]
    effects {ER, Error}
  operation create_issue(m: C, title: String, body: String) -> Int64
    effects {EW, Error}

-- carriers INSTANTIATE; WI-347 refinement becomes ordinary instantiation,
-- and §Faking step 2's four rows fall out exactly:
--   gh:    provides Mirror[C = GhMirror,   ER = {External}, EW = {External}]
--   fake:  provides Mirror[C = FakeMirror, ER = {},         EW = {Modify[reg]}]
--   (fake read = {Error}, fake mutator = {Modify[reg], Error} — verbatim)
-- and the store THREADS them, MappedStream-style (its ES/EF are this split):
--   CoordState[M]  provides WorkItemStore[S = CoordState[M], E = {ER, EW}]
--   file backend   provides WorkItemStore[S = WIS,           E = {}]
```

Load-level smoke (2026-07-12, user spec + user effect declared via the Clock
convention) confirms the refinement half is **delivered machinery**: a
consumer holding the fake concretely typechecks at the instantiated row
(`effects {}` loads — the `Iterable.find` / `List E = {}` precedent
reproduced); the real carrier's row reaches the same consumer shape and is
rejected loudly (`got undeclared effect`); param-to-param threading — a
wrapper's own row param bound in its `provides`, the `CoordState[M]` shape —
refines and enforces identically; and dot dispatch on an *abstract* carrier
fails loudly rather than leaking a refined row. (The smoke instantiated `{}`
and a nullary stand-in effect through a SINGLE row param; a
`Modify[…]`-indexed instantiation and the two-param read/write split above
ride the same substitution — MappedStream ships two params today — but were
not separately probed.)

Three consequences. **Step 2's union is reread**: the spec row is the
parameters' *upper bound* — what `ER`/`EW` erase to where the carrier is
unknown — not a declaration anyone maintains per-capability, which also
retires the §Problem-1 churn for good. **The seal moves to exactly the WI-402
factory**: the existential is the one point where `ER` and `EW` erase to
their bounds, so
spec-typed production code is `External`-rowed and `Branch`-forbidden
precisely there, while a test constructing the coordinated store over the
fake keeps the whole store surface searchable — the sandwich, stated
type-theoretically: *searchability ends where the carrier is sealed*.
**The `Branch` gate composes as a lacks-constraint**: a solver's region row
demands `-External` (the `-Modify[x]` surface of `Iterable.find`),
discharged by the fake's instantiation — that is the end-state shape; the
enforcement behind it is WI-698's to wire, next paragraph.

What stays genuinely new, per the same smoke: the `Branch`×`External`
co-occurrence gate has no existing check to ride (WI-701) — and, beneath it,
lacks-constraints and callback-row conformance at higher-order positions
currently **parse but do not enforce** at explicit row-instantiation call
shapes (WI-700). The root cause there is *not* that the validator runs at some
other call shape — `validate_callback_effect_row` (`typing.rs:14393`) **is**
wired into the ordinary call path, at both argument loops (`typing.rs:5983`
positional, `:6011` named). It fails to fire because its open-vs-closed
decision reads a declared row whose tail is a row *parameter* (`{EffP,
-Outside}`) as **open, hence absorbing**, never resolving the explicit `[EffP =
{…}]` instantiation through the substitution first. So WI-700 is one decision
point, not a new check at a new shape — and the hole it closes is not
`External`-specific: a non-empty row escapes into an `effects {}` operation
today for `Modify`, `Error` and `Clock` alike. Two by-catches for the WI: an
effectful callback does not infer into a row parameter — the typer demands an
explicit `op[EffP = …]` instantiation (loud, acceptable, but solver-harness
ergonomics should expect it); and a user-namespace `effects X = ?` needs
`anthill.prelude.EffectsRuntime` imported, else the provider-requires check
misses its anchor exemption and reports a confusing
`does not provide 'EffectsRuntime'` instead of the real cause.

## What stays as-is

* **`Clock`, `ConsoleOutput`, `ConsoleError`** — proto-`External` markers,
  untouched. Folding or aliasing them under `External` is a later decision;
  what this proposal fixes is the *pattern*: new capabilities do not follow
  their per-capability shape.
* **Persistence** — stays absorbed under `{Modify[s], Error}` (037). It works,
  and its store is process-owned in the sense that matters (single writer per
  command, buffered flush). An honest migration to `External` is possible
  later and required by nothing.
* **`Error`** — orthogonal. `External` implies neither raising nor being
  raised at; in practice most external ops also declare `Error`, because the
  outside world fails.

## Out of scope

* A capability/authority system — carriers suffice today; this proposal only
  keeps the row vocabulary from pre-empting that design.
* Handler semantics for `External` (047's territory) — `External` is a
  marker with typer-side consequences, not a new handler protocol.
* Effect subsumption/aliasing machinery (needed only if `Console`/`Clock`
  fold-in is ever taken up).
