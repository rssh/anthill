# A logic monad for anthill — `match` over streams, solvers as `Branch` handlers

> **Purpose.** Design brainstorm for relational search in anthill's *functional* layer, converged on
> one spine: **`match` over a stream.** A relation's solution set is a lazy stream (the resolver's
> `SearchStream`); `match` consumes it; a **`Solver`** value (not a keyword) says how much to take.
> This **realizes proposal [047](../../proposals/047-effects-as-monads-via-reflection.md)**
> (`Branch ↦ Stream`, Filinski reflection) with the API of the author's dotty-cps-async
> `CpsLogicMonad`, and extends it with the one thing that monad lacks — **relational search
> (unification), kept behind ordinary lexical binders** so logic variables never enter functional
> code.
>
> The integration factors into **two layers** (§6): **Layer 1** exposes a relation as a *stream-valued
> operation* — no effect, the `reify` face, buildable now on `SearchStream`; **Layer 2** adds the
> `Branch` effect that *reflects* any stream into nondeterministic branches (the `reflect` face — the
> runtime eval↔SLD switch). The boundary between them is **nesting**: flat stream consumption is
> Layer 1; a search body that re-enters search needs Layer 2.
>
> **Status.** Brainstorm (2026-07-04). **Graduated (2026-07-05) into two proposals along the two-layer
> seam (§6):** Layer 1 → [052 — rules as stream-valued operations](../../proposals/052-rules-as-stream-valued-operations.md)
> (the `reify` face: a relation as `LogicalStream[NamedTuple]`, no effect); Layer 2 →
> [027.2 — branch from streams](../../proposals/027.2-branch-from-streams.md) (the `reflect` face:
> `reflect(stream)` into `Branch`, solvers as handlers, the eval↔SLD switch). This doc remains the
> extended design rationale behind both. Reference model:
> `/home/rssh/packages/io.github.dotty-cps-async/` (`logic` = `CpsLogicMonad`, `rl-monad` =
> `CpsScoredLogicMonad`). Companion to proposals [026](../../proposals/026-expression-evaluator.md) /
> [026.1](../../proposals/026.1-value-integrated-kb-queries.md) (`KB.execute`, `LogicalStream`),
> [027](../../proposals/027-effect-handlers-and-standard-effects.md) (`Branch`, handlers),
> [033](../../proposals/033-resolver-primitives-and-disjunction.md) (`push_choice`), and WI-246
> (`Value`-carrying SLD).

## 1. The spine — everything is `match` over a stream

A relation's solutions form a **lazy stream** — literally the resolver's `SearchStream`, whose
`split_first` pulls the next solution. That is the *same* operation as `Stream.splitFirst` on a data
stream and `msplit` on a LogicT monad. So one abstraction sits under all of it:

| scrutinee | stream of… | length | `case` per element |
|---|---|---|---|
| a **value** | itself | 1 | structural match (today) |
| a **collection** | its elements | finite | match each |
| a **relation/goal** `queens(board)` | its **solutions** (SLD, lazy) | 0..∞ | *solve*-and-bind |

Same `match`, same `case <pattern>` per element. **Structural match is the degenerate case** where
the stream has one element; relational search is the case where the stream comes from the resolver.
The only reinterpretation: under a relation source, a `case` pattern is *solved* (one-sided
unification, multi-shot) rather than *matched* against a value's structure.

Three consequences that the rest of this doc is just detail on:
1. **The consumer is a value.** How much of the stream to take — all, the unique one, the best-scored
   — is a **`Solver`** (§4), which is exactly a `Branch` handler (027) = a LogicT observer.
2. **The binder is lexical.** `case board` binds `board` like `case cons(h, t)` binds `h`/`t`; the
   resolver hands out a concrete value. **Logic variables `?x` never appear in functional code** (§3).
3. **The producer is the `Branch` effect.** What fills the search-stream lazily is the runtime
   eval↔SLD switch (§6).

## 2. The convergence — this is already anthill's design

- **047 says it.** *"Effects as monads, realized by Filinski monadic reflection"*: **`Branch ↦ Stream`**
  (the lazy `LogicalStream`/`SearchStream`, not `List`; `fail ≙ empty`, `choice ≙ multi-yield`),
  **effect-op = `reflect`**, **handler = `reify`/`reset`**, the **`HandlerAction` carrier =
  defunctionalized reflection**, and §4 *"the non-native stack is this proposal's design purpose."*
- **The carrier exists** — `stdlib/anthill/prelude/logical_stream.anthill` ("the logic monad for
  multi-valued computation", `splitFirst` = `msplit`).
- **The API is known** — the author's `CpsLogicMonad` is textbook LogicT (`mzero`/`mplus`/`msplit`,
  `interleave`, `>>-`, `ifte`, `once`, `limit`, `fromCollection`), consumed via `observeN`/`toLazyList`.
  `rl-monad`'s `CpsScoredLogicMonad` adds a scored, priority-queue-backed best-first layer.

So we are *surfacing* an existing design, not inventing one.

## 3. Logic variables stay at the metalevel

The decisive simplification: **`?x` never enters functional code.** Logic variables live only at the
metalevel — in the *rules* that define a relation (`rule queens(?board) :- …`). Functional code binds
search results with the binders it already has — **`case` patterns and `let` patterns**, both
lexical. No `deref(σ, ?x)`, no ambient σ, no "typed logical value in an expression": the resolver
resolves a pattern variable to a concrete value, bound like any `case`/`let` binder. Unification stays
inside the resolver; the functional world only ever sees bound values. anthill already splits its two
`let`s along this seam — goal-level `let ?v = e` (logical) vs. expression-level `let <pattern> = e`
(functional).

## 4. Solvers are values, not keywords

How much of the solution stream to take is a **`Solver`** — an ordinary value, an instance of a
`Solver` sort whose operation *provides the matching*. So the surface needs **no new grammar**: a
solver is just a scrutinee value, and a `Solver` instance **is a reified `Branch` handler** (027 §Branch
already enumerates them):

```
sort Solver
  operation run[T](goal: Goal) -> LogicalStream[T]      -- "provides matching" (consumes the stream)

fact Solver[= all]           -- collect every solution            (default Branch handler)
fact Solver[= one]           -- the unique solution — the ι iota  (undefined if not exactly one)
fact Solver[= once]          -- first-commit (take any one)
fact Solver[= beam(k, score)]-- best-first / scored  ← rl-monad CpsScoredLogicMonad, for free
fact Solver[= oracle(xs)]    -- pre-supplied choices
```

A `Solver` instance = a `Branch` handler = a LogicT observer = a **stream consumer** — four names for
one thing (`all` ≈ collect/`observeAll`, `one`/`once` ≈ `once`, `beam` ≈ priority `first`). Scored
best-first search is therefore *just another instance*, and users can define their own solver with no
grammar change.

## 5. Surface — two duals, reusing `match`/`case` and `let`

### 5.1 Expression form — `match <solver> case <goal>`

```
match v    case cons(h, t)     -> …h…t…    -- scrutinee = a value  → structural (today)
match all  case queens(board)  -> body     -- scrutinee = solver `all` → stream of every solution
match one  case queens(board)  -> body     -- scrutinee = solver `one` → the unique (iota)
match beam(k, cost) case path(?p) -> …     -- scrutinee = a custom solver → best-first
```

Reuses `match <scrutinee> case <pattern> -> <body>` verbatim; `all`/`one`/`beam(…)` are `Solver`
*values* in scrutinee position. `board` is a lexical `case` binder. Multiple `case`s = disjunction.

### 5.2 Statement form — `let <goal> = <solver>`

```
let queens(board) = all       -- board bound per solution (Branch); collect → stream
let queens(board) = one       -- the unique solution                       → value
let member(x, l)  = all       -- chains: x visible to the next let and the body
let member(y, l)  = all
… body(x, y, board) …
```

Reuses `let <pattern> = <expr>`: the goal on the LHS (solved, binding its vars **once**), the `Solver`
on the RHS. `board` appears exactly once. The RHS is a solver *value*, not an assigned datum (a spec
note so `= all` isn't misread as ordinary assignment). This is the sequential face — chained `let`s
are conjunction, each binding vars the next uses, no `?x`.

### 5.3 Naming the relation — rule reference as scrutinee (label, else head)

A relation can be cited **by name** and handed to a solver, rather than inlined as a goal:

```
all(Queen.find)                        -- solver applied to a named rule → stream
match all case Queen.find(board) -> …  -- same, binding board through the case
```

`Queen.find` is a first-class **rule reference**. "If it has no name, use the head" is exactly
anthill's existing rule identity: a labeled rule (`rule find: …`) is cited by its label; an unlabeled
rule by its **head functor** (`rules_by_label` vs `rules_by_functor`). So a rule reference resolves to
a label if present, else the head — no new naming scheme, just surfacing the one that exists. This is
the §5.2 dual (WI-580 "rule as knowledge") made concrete: the solver says *how* to search, the rule
name says *what*. A reified relation value composes the same way — `Queen.find.all` /
`Queen.find.solveWith(beam(…))`, or the `Rule[X]` partial-fill of §6 (`Queen.find.where(board: half)`).

### 5.4 NotFound — the `nil` arm of the stream match

Because the spine is *match over a stream* (`cons(head, tail) | nil`), the **empty solution set is
just the `nil` case** — no special mechanism, the same `nil` you already write matching a list:

```
match one case Queen.find(board) -> found(board)
            case nil             -> notFound          -- zero solutions
```

Uniform across solvers: for **`all`**, zero solutions ⇒ empty stream, and the `nil` arm is the
"found nothing, do X" fallback; for **`one`** (the ι iota), zero solutions ⇒ NotFound, handled by the
`nil` arm — and *more than one* is the other iota degeneracy (an error, or an explicit `case multiple`
arm). Three coherent ways to surface "not found," all falling out of the spine, pick per site:
1. a **`nil` `case` arm** — inline, native to stream-match;
2. **`one` returns `Option[T]`** — `None` = NotFound, the total/safe form (no `nil` arm needed);
3. **`Error[NotFound]`** (027 `Error` effect) — the "should be there" case, dischargeable to pure
   where the typer proves non-emptiness (guarded-effect pattern).

The two `one` degeneracies (`nil` = none, `multiple` = >1) are exactly the `∃!` presupposition from
the Hilbert–Bernays definition of ι — discharged at runtime here (the `nil`/`multiple` arms) instead
of as a proof obligation.

## 6. Two layers — streams (`reify`) and branches (`reflect`)

The integration factors cleanly into two layers, split by whether nondeterminism escapes into control
flow — exactly Filinski's two faces:

**Layer 1 — streams, no effect (the `reify` face).** A relation is a *stream-valued operation*: the
resolver already produces solution bindings, so surface it as
`Queen.find : LogicalStream[{board: Board}]` — each element a **named tuple shaped like the query**
(one field per free `?var`, exactly what a `case`/`let` pattern then destructures). Its type is a
**named-tuple type** — a first-class type form anthill already has (reflected as
`TypeExtractor.NamedTuple` in sort.anthill, `fields: List[NamedTupleElement]`), so nothing new is
needed to *type* a solution. The value is a record over the query's `?vars` — but a `case`/`let`
pattern can bind those fields directly, so the record need not be *materialized* at runtime: the
named-tuple type is the static shape, not a mandatory box. The same
relation reified as a *value* is a **`Rule[X]`** with a partial-fill method
(`Queen.find.where(board: half)` = partial application on a relation, narrowing the stream). Pure
`map`/`flatMap`/`fold`; **no `Branch` effect, no suspend/resume.** This is `fromCollection`/carrier-level
in `CpsLogicMonad` terms and is buildable *directly on the existing `SearchStream`.*

**Layer 2 — branches, the `Branch` effect (the `reflect` face).** `reflect : LogicalStream[T] ⊸ T`
lifts **any** stream into ambient nondeterminism — the computation forks per element. Solvers
(`all`/`one`/`beam`/`oracle`, §4) are the handlers (`reify`/`reset`) that collapse branches back to a
stream or a value. Because it lifts *any* stream, rules aren't privileged: it is
`msplit`/`mplus`/`interleave`/`>>-` over a generic stream.

**The boundary is nesting.** Flat consumption of a relation's solutions (`let queens(board) = all`,
map/fold) stays in Layer 1 — a stream is just a value. The moment a solution's **body itself re-enters
search** (a nested solve, interleaving), you need Layer 2 — the branch must suspend and re-enter the
resolver. So `match`/`let` over a relation is Layer-1 pure-stream *until* a body re-enters search.

### 6.1 The switch — Layer 2's one new runtime piece

`match <solver> case <goal>` and `let <goal> = <solver>` both desugar to:

1. evaluating `<goal>` **performs the `Branch` effect**, which lazily enumerates the goal's solutions;
2. each solution is bound **lexically** through the `case`/`let` pattern;
3. the **`Solver`** consumes the resulting stream (collect / take-unique / priority-pull) — it is the
   `Branch` **handler** / reify boundary. A `Branch` with no enclosing solver is **unhandled ⇒ a loud
   load/type error**; nondeterminism never leaks past a consumer.

The **producer** (step 1) is the one genuinely new runtime piece — the **eval↔SLD switch**: suspend
the concrete evaluator at the goal, drive SLD, and **multi-shot-resume** the continuation once per
solution. The control substrate is nearly free, because the interpreter is *already* suspend/resume-
ready (047 §4): its `ActivationStack` is non-native (`run()` is a trampoline over an explicit heap
stack, so the continuation is reified data). What's missing is small and mechanical:
- a `StepOutcome::Suspend` that returns from `run()` with the stack intact + a resume entry (same
  shape WI-455 already plans for `StepOutcome::Dispatch`);
- `Clone` on `Frame`/`ActivationStack` for multi-shot — **already committed (WI-078 Phase-A/a)**;
- **coordinated** binding: the interpreter keeps its suspended stack, the resolver frame holds only a
  resume handle it calls back — so the resolver never embeds eval types.

Concrete values already flow *into* SLD (WI-246 `Value`-carrying goals); choice points already exist
(`push_choice`/`SearchStream`, 033/WI-075 Verified). The switch is what connects them.

## 7. What anthill adds over the reference monad

`CpsLogicMonad` chooses over **ground collections** (`choices.from(1..8)` → `Int`s; its Agatha-puzzle
solution is brute generate-and-test over tuples — no relations, no unification). anthill's addition is
that the `case`/`let` goal is a **relation solved by the resolver**: `queens(board)` enumerates a
rule-defined relation's solutions, binding `board` by unification. The relation is written *once*, at
the metalevel, as ordinary rules; the functional search consumes its solutions through a lexical
binder. The novelty is **relational search behind lexical binders** — *not* logic variables in
expressions (deliberately avoided), which keeps this strictly simpler than a "typed logical value +
ambient σ" design and needs no new expression-level variable notion.

## 8. Scored / best-first — a `Solver` instance, not a special case

The Dijkstra/minimax/RL references (`rl-monad`) are covered by making one more `Solver`: a scored
carrier over `LogicalStream` with `scoredPure(a, r)` / `scoredMplus(m, r, next)` / `multiScore(seq)`
and `first` = **pop the single best** (priority-queue-backed, so `mplus` is a priority merge); a
`ScalingGroup`/`ScalingRing` score algebra (additive costs vs. multiplicative probabilities, *higher
= better*, costs negated); and an exact-vs-approximate policy knob. `match beam(k, cost) case g` just
names that solver.

## 9. State across branches — 047 §8 effect ordering

Shared mutable state (KB facts, `Cell`s) under backtracking is answered by 047 §8: a resource ranked
**below** `Branch` survives backtracking (an audit log); **above** `Branch` it is undone on backtrack
(a speculative log). `register_undo` is a *ranking*, not bespoke machinery. Read-only search sidesteps
it entirely; it bites only for *mutating* effects performed inside the search.

## 10. Substrate assets (nothing here is a green field)

- **047 §4 non-native, suspend/resume-ready stack** — the design purpose is exactly this.
- **`Clone` on `Frame`/`ActivationStack`** (WI-078/a, committed) — multi-shot resume.
- **WI-246 `Value`-carrying goals** — concrete values flow into SLD natively.
- **`push_choice` / `SearchStream`** (033, WI-075 Verified) — lazy solution stream + choice points.
- **`Stream` / `LogicalStream` / `splitFirst`** — the stream abstraction the whole spine keys on;
  `KB.execute` (026.1) is the `Solver.run` engine; `fresh_var` mints metalevel logic vars.
- **`DelayMonad`** (047 §8, WI-516) — the graded-effect monad precedent for the typeclass shape.

## 11. Open questions

1. **`one` semantics / NotFound** — strict iota (unique; the empty and >1 degeneracies handled per
   §5.4 — `nil`/`multiple` arm, `Option`, or `Error[NotFound]`) vs. the separate first-commit `once`.
   Default: `one` = iota, `once` = first-commit.
2. **Goal syntax in `case`/`let`** — a rule head applied to a pattern (`queens(board)`) is the target;
   how a bare Bool-op or a `&`/`|` compound reads in that position (ties to WI-583, WI-529).
3. **`Solver.run` signature** — `run(goal) -> LogicalStream[T]`; how the `case` pattern's projection
   (`T`) is threaded, and how a solver observes vs. produces (the `Observer` split in `CpsLogicMonad`).
4. **The switch seam (§6)** — the coordinated suspend/resume; how a solution's binding re-enters the
   resumed eval (WI-246 var identity should make it direct).
5. **First-class rules** (§5.2 dual) — reifying a relation as a value (`queens.all`); relation to
   WI-580 (body/rule as first-class knowledge).

## 12. Build path (proposed)

**Layer 1 — streams, no interpreter change (§6):**
1. **`Solver.run(goal): LogicalStream[Solution]` — the value form.** Essentially `KB.execute` with the
   goal written naturally; each element a value of a **named-tuple type shaped like the query**
   (`TypeExtractor.NamedTuple`, one field per `?var`); `all`/`one` as
   ordinary stream consumers; the rule-reference scrutinee (§5.3) and the NotFound `nil`-arm (§5.4)
   live here. Proves the goal/`Solver`/stream spine with **no interpreter change**.
1a. **`Rule[X]` reified relation** — a first-class relation value with partial-fill (§6 Layer 1); the
   ergonomic face of step 1, optional.

**Layer 2 — branches, the `Branch` effect (§6.1):**
2. **The eval↔SLD switch (§6.1)** — `StepOutcome::Suspend` + resume + coordinated binding: the one
   interpreter addition, enabling the direct-style `match`/`let` surface (per-solution eval).
3. **The surface desugar** — `match <solver> case <goal>` / `let <goal> = <solver>` lowering to
   `Branch` + solver-handler, reusing `case`/`let` binders.
4. **Scored solvers** (§8) — best-first for the RL/minimax/shortest-path use-cases.

Layer 1 is buildable now on existing pieces; the eval↔SLD switch is the sole real interpreter change;
each later step adds one capability on the same substrate.
