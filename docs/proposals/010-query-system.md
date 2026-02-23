# 010: Query System

## Status: Brainstorming

## Depends on: 011 (Type Resolution), 012 (Sort-Defined Syntax Sugar)

The query syntax (comprehensions, `?-`, `choose`/`guard`) likely instantiates sort-defined sugar mechanisms (012), which in turn require type resolution (011). Core query semantics (terms + unification, `Stream` as logic monad) can proceed independently, but surface syntax is blocked.

## Motivation

The kernel language has pattern-matching queries as an internal mechanism (rule bodies, constraint guards, discrimination-tree lookup in Rust, `query` function in the Isabelle formalization) but no explicit surface-level query construct. Applications beyond rule evaluation need queries:

- **KB introspection** — find all sorts, operations, facts matching a pattern
- **Realization code** — operation implementations that look up facts
- **Persistence** — `retrieve(store, pattern)` in the persistence module
- **Agent coordination** — agents querying for open obligations, work items
- **Testing/validation** — asserting facts, then querying expected results
- **Reactive triggers** — "whenever a fact matching X appears, do Y"

## Core Principle

Since Anthill is types-are-terms and facts-are-terms, the natural model is **queries-are-terms-with-variables**. An entity constructor with logical variables in argument positions is a query pattern:

```
-- Given:
sort Account {
  entity account(id: Int, owner: String, balance: Int)
}

-- Then this is a query pattern:
account(?id, ?owner, ?bal)
```

Unification against the KB binds `?id`, `?owner`, `?bal` to concrete values for each matching fact.

## Resolved Questions

### R1. Query by sort

**Decision: Yes.** Querying by sort returns facts of that sort and all subsorts (per §8.2 subsorting). If `red <: Color`, then a query for sort `Color` matches `red`, `green`, and `blue` facts.

Syntax TBD — possibly `? : Color` or a dedicated `by_sort(Color)` form.

### R2. Result cardinality control

**Decision: Yes.** The caller should be able to specify how many results they want:
- First match (existence / single lookup)
- First N matches
- All matches

### R3. Result streams

**Decision: Explore.** Query results may be large or even conceptually infinite (forward-chaining derivations). A stream/cursor model avoids materializing all results at once.

Possible approach: a `Stream` sort in stdlib that represents a lazy sequence of results, with operations like `next`, `take`, `collect`. This is analogous to iterators/cursors in databases.

Open: relationship to the `List` sort — is `Stream` a lazy `List`? A separate sort? Can you `collect` a stream into a list?

Note: implicit multiple-return (as in Icon's generators or Prolog's backtracking, where a procedure implicitly yields many results) was considered but an explicit `Stream` sort is likely better for Anthill — it's composable, typed, and doesn't require special evaluation semantics.

### R4. Aggregation is Stream operations

**Decision: Yes.** If query results are `Stream{T = S}`, then aggregation (count, sum, min, max, group-by) is just operations on the `Stream` sort. No special aggregation syntax in the query system:

```
-- count is an operation on Stream, not a query primitive
operation count(s: Stream{T = ?S}) -> Int
operation sum_by(s: Stream{T = ?S}, f: ?S -> Int) -> Int  -- (pending arrow sorts)
```

This keeps the kernel query mechanism minimal (terms + unification) and pushes composition to stdlib.

## Open Questions

### OQ1. Query Contexts — Where Do Queries Appear?

**OQ1.1.** Rule bodies are already conjunctive queries (`rule head :- q1, q2`). Should standalone queries exist as top-level declarations in `.anthill` files? E.g.:

```
query high_balance_accounts {
  account(?id, ?owner, ?bal), gt(?bal, 1000)
}
```

Or are named queries just rules without heads (views)?

**OQ1.2.** Inside operation realizations — can an operation body issue queries against the KB? This seems necessary for any non-trivial implementation. How is this expressed?

**OQ1.3.** Should queries be usable as reactive triggers / subscriptions? "Whenever a fact matching this pattern appears, fire this rule." This overlaps with forward chaining but framed as event-driven.

**OQ1.4.** Are constraint guards (`constraint inv :- guard`) sufficient for the integrity-checking use case, or do constraints need richer query features?

### OQ2. Query Result Shape

**OQ2.1.** What does a query return? Options:
  - A list/stream of **substitutions** (bindings for each variable)
  - A list/stream of **matched terms** (the full fact terms)
  - A list/stream of **fact entries** (term + sort + domain + trust + metadata)

**OQ2.2.** Should queries support **projection** — returning only specific bindings rather than full tuples? E.g., "give me just `?owner` values from `account(?id, ?owner, ?bal)`."

**OQ2.3.** Should query results include **fact metadata** (trust level, fact_id, domain, retraction status)? This matters for trust-aware reasoning.

### OQ3. Query Composition

**OQ3.1.** **Conjunction** is natural: `q1, q2` with shared variables acting as joins. Already exists in rule bodies. Same semantics for standalone queries?

**OQ3.2.** **Disjunction**: `q1 ; q2` — needed as a primitive? Or just use multiple rules/queries?

**OQ3.3.** **Negation**: `not(q)` — negation-as-failure with closed-world assumption? The spec mentions stratified negation (§8.3). How central is negation to queries? What are the stratification requirements?

**OQ3.4.** **Nested queries / subqueries**: Can a query result feed into another query? E.g., "find accounts whose owner appears in VIP-user facts."

### OQ4. Sort-Aware Queries

**OQ4.1.** Syntax for query-by-sort. Options:
  - `? : Color` — typed anonymous variable
  - `by_sort(Color)` — explicit built-in
  - Just use the sort name in a query context: `Color` matches all Color facts

**OQ4.2.** Can you query **by domain** — "all facts asserted in scope X"?

**OQ4.3.** Can you query **by functor** — "all facts whose outermost constructor is `account`" regardless of sort?

### OQ5. Variables and Binding

**OQ5.1.** Scope of shared variables in standalone queries — same as in rule bodies? (Named variables shared within the query, `?` anonymous and distinct.)

**OQ5.2.** **Constrained variables**: In `account(?id, ?owner, ?bal), gt(?bal, 1000)`, the second atom is a condition, not a KB lookup. How does the engine distinguish "look up in KB" from "evaluate as constraint"? Is this just the same as rule body evaluation (all atoms are goals, some resolve to facts, some to computable predicates)?

**OQ5.3.** Can variables have **type annotations** in query patterns? E.g., `?bal : Int` — does this constrain matching to facts where the argument is of sort Int?

### OQ6. Query Sort, Query Syntax, or Both?

Even if queries have dedicated syntax, the reflect module will need a sort to reify/inspect query structure as data — just as `TermRepr` exists alongside the opaque `Term` sort. So at minimum there's a `QueryRepr` in reflect. The question is what the *primary* representation is and whether queries are first-class values in the kernel (not just reflect).

#### Option A: Queries are just terms with variables (minimal)

No new sort. A `Term` containing `Var` nodes IS a query pattern. Conjunction, guards etc. live only in syntax (rule bodies, constraint guards).

```
-- retrieve already takes a Term as pattern:
operation retrieve(store: QueryableStore, pattern: Term) -> List{T = Term}
```

Pro: simplest, consistent with types-are-terms. Con: can't express conjunction, negation, guards, sort constraints as a single passable value. `retrieve(store, pattern)` is limited to single-pattern matching.

#### Option B: Query as a kernel sort (first-class query algebra)

A `Query` sort with constructors for the query algebra:

```
sort Query {
  entity pattern(term: Term)                       -- single pattern
  entity by_sort(sort_name: String)                -- all facts of a sort
  entity conjunction(left: Query, right: Query)    -- AND (shared vars = join)
  entity disjunction(left: Query, right: Query)    -- OR
  entity negation(query: Query)                    -- NOT (negation-as-failure)
  entity guarded(query: Query, condition: Term)    -- filter
  entity limited(query: Query, count: Int)         -- cardinality limit
  entity projected(query: Query, vars: List{T = String})  -- projection
}
```

Pro: queries are composable, storable, passable, optimizable. Persistence backends can receive a full `Query` and translate it (e.g., to SQL). Con: heavy — building a query AST as data. Parallel to the `TermRepr` pattern.

#### Option C: Special syntax only, with `QueryRepr` in reflect

Dedicated query syntax (e.g., `query { ... }` blocks or Prolog-style `?-`) that the kernel understands. For introspection, the reflect module has `QueryRepr`:

```
-- In reflect:
sort QueryRepr {
  entity PatternQ(term: TermRepr)
  entity BySortQ(sort_name: String)
  entity ConjunctionQ(left: QueryRepr, right: QueryRepr)
  entity DisjunctionQ(left: QueryRepr, right: QueryRepr)
  entity NegationQ(query: QueryRepr)
  entity GuardedQ(query: QueryRepr, condition: TermRepr)
  entity LimitedQ(query: QueryRepr, count: Int)
}

operation reify_query(q: Query) -> QueryRepr
  effects (Reads(kb))
```

Pro: clean surface syntax, structural introspection when needed. Con: queries are opaque at the kernel level (like `Term`), only transparent via reflect.

#### Option D: Syntax that desugars into a Query sort

Both syntax AND sort. The surface syntax `query { p1, p2, guard(c) }` desugars into `Query` sort constructors. The `Query` sort is a kernel-level type, not just a reflect concern.

Pro: best of both worlds — nice syntax AND first-class values. Con: two ways to express the same thing (syntax and direct construction).

#### Option E: Queries are operations with `Branches` effect

No `Query` sort or syntax. A "query" is just an operation with `effects (Branches, Reads kb)`. Complex queries are composed by calling such operations. Named queries = named operations returning `Stream`.

```
operation high_balance_accounts() -> Stream{T = Account}
  effects (Reads(kb), Branches(result))
```

For reflect, the "query" is the operation's body — inspected via operation introspection. For persistence, `retrieve` takes a `Term` pattern (simple queries) or calls an operation (complex queries).

Pro: no new sort or syntax — reuses the operation + effect system. Con: can't pass a query as a value to `retrieve` unless you also pass the operation itself (higher-order).

#### Key sub-questions

**OQ6.1.** Which option? They aren't mutually exclusive — e.g., Option D (syntax + sort) + Option E (operations for complex cases) could coexist.

**OQ6.2.** Does persistence need rich queries? `retrieve(store, pattern: Term)` only supports single-pattern matching. If backends (SQL, etc.) need conjunctions/filters, they need either a `Query` sort (Option B/D) or a backend-specific query representation.

**OQ6.3.** Can queries be **stored in the KB as facts**? E.g., "this agent's saved search is Query X." This requires a Query sort or `QueryRepr`.

**OQ6.4.** Can queries be **composed programmatically** at runtime? E.g., a meta-agent that builds a query dynamically based on context. This requires either a `Query` sort (construct values) or `reflect`-level TermRepr manipulation.

**OQ6.5.** Parallel to `Term`/`TermRepr`: should there be an opaque `Query` (kernel handle, like `Term`) and a transparent `QueryRepr` (structural, like `TermRepr`)? Or is one representation enough?

### OQ7. Query vs Rule Body — Same or Different?

**OQ7.1.** Prolog doesn't distinguish: a goal IS a query, rule bodies are queries, `?- goal` is a query. Should Anthill follow this unification?

**OQ7.2.** If queries gain richer features (aggregation, ordering, projection, cardinality limits), do rule bodies gain them too? Or are standalone queries a superset of rule-body queries?

**OQ7.3.** If they diverge, what is the minimal query that rule bodies support vs. the full query language?

### ~~OQ8. Aggregation and Computation Over Results~~

**Resolved — see R4.** Aggregation is operations on the `Stream` sort, not a query primitive. The pattern is: query produces `Stream{T = S}`, stdlib provides `count`, `fold`, `sum_by`, `group_by`, etc. as operations on `Stream`.

Remaining sub-question: is `Stream` expressive enough for group-by (which produces `Stream{T = Pair{fst = K, snd = Stream{T = V}}}` or similar nested structure)? This is a `Stream` design question, not a query question.

### OQ9. Effects and Queries

**OQ9.1.** Are queries **pure** (read-only KB access)? This seems natural but needs to be stated.

**OQ9.2.** Should queries declare `effects (Reads kb)` when used inside operations? Or is KB read access implicit?

**OQ9.3.** Can a query trigger **demand-driven forward chaining** — deriving new facts lazily when a query needs them? This blurs the pure/effectful boundary.

### OQ10. Cross-KB and External Queries

**OQ10.1.** Can you query across **multiple knowledge bases**? Is there a concept of federated query?

**OQ10.2.** The persistence module maps KB queries to external stores (SQL, files). Should the query syntax be the same regardless of backend? (Same pattern, different store.)

**OQ10.3.** Can queries target **remote** KBs (agent-to-agent query)?

### OQ11. Syntax

**OQ11.1.** Minimal approach — a term with variables in a query context IS a query, no new syntax needed beyond defining which contexts accept queries.

**OQ11.2.** Prolog-style directive: `?- account(?id, ?owner, ?bal), gt(?bal, 0)`

**OQ11.3.** Named query declaration:
```
query high_balance {
  account(?id, ?owner, ?bal)
  :- gt(?bal, 1000)
}
```

**OQ11.4.** Comprehension-style (returns projected values):
```
[?owner | account(?id, ?owner, ?bal), gt(?bal, 1000)]
```

**OQ11.5.** Query-as-operation — queries are just operations with `effects (Reads kb)` and the "implementation" is pattern matching:
```
operation high_balances() -> Stream{T = Account}
  effects (Reads kb)
```

**OQ11.6.** Which of these can coexist? Are some sugar for others?

### OQ12. Ordering and Determinism

**OQ12.1.** Are query results ordered? By insertion order? By sort? By trust level? Unspecified?

**OQ12.2.** Can the caller specify ordering? E.g., "accounts ordered by balance descending."

**OQ12.3.** Is query result order **deterministic** across runs? This matters for testing and reproducibility.

### OQ13. Streams, Effects, and the Logic Monad

The connection between query result streams and effects has deep structure. A **logic monad** (Kiselyov et al., Curry, LogicT) represents computations with multiple results — exactly what queries produce. The key insight is that `Stream` is not just "lazy list" but a **logic monad** that composes with effects.

Reference implementations:
- Haskell: `LogicT` monad transformer (Kiselyov et al.)
- Scala: `dotty-cps-async/logic` — `LogicStreamT[F, A]` parameterized over effect monad `F`
- Blog: https://github.com/rssh/notes/blob/master/2024_01_30_logic-monad-1.md

#### Background: Logic Monad Structure

A logic monad `M[A]` represents a computation that may produce zero, one, or many values of type `A`. Core operations:

| Operation | Type | Meaning |
|-----------|------|---------|
| `empty` | `M[A]` | No solutions |
| `pure(a)` | `M[A]` | Single solution |
| `mplus(a, b)` | `M[A] -> M[A] -> M[A]` | Disjunction (try a, then b) |
| `flatMap(f)` | `M[A] -> (A -> M[B]) -> M[B]` | Conjunction (bind/chain) |
| `msplit` | `M[A] -> M[Option[(A, M[A])]]` | Decompose: first result + rest |
| `guard(p)` | `Bool -> M[Unit]` | Succeed if true, fail if false |
| `once` | `M[A] -> M[A]` | First result only (Prolog cut) |
| `interleave` | `M[A] -> M[A] -> M[A]` | Fair disjunction |
| `fairFlatMap` | `M[A] -> (A -> M[B]) -> M[B]` | Fair conjunction |

The crucial primitive is `msplit`: it decomposes a stream into "head + tail" *within the monad*, enabling all other operations to be derived.

#### Direct mapping to Anthill queries

| Logic monad | Anthill query concept |
|-------------|----------------------|
| `empty` | Query with no matches |
| `pure(fact)` | Single known fact |
| `mplus(q1, q2)` | Disjunctive query (OR) |
| `flatMap` | Conjunctive query (AND, shared variables = join) |
| `guard(condition)` | Constraint filtering (`gt(?bal, 1000)`) |
| `once(q)` | First match / existence check |
| `limit(q, n)` | Take first N results (R2 cardinality control) |
| `msplit(q)` | Peek at first result + remaining stream |
| `interleave(q1, q2)` | Fair OR (prevents starvation) |
| `fairFlatMap(q, f)` | Fair AND (prevents starvation in nested queries) |

#### Open questions

**OQ13.1. Is `Stream` a logic monad at the kernel level?** If `Stream{T = S}` is the query result type and it supports `mplus`, `flatMap`, `guard`, `msplit` — then it IS a logic monad. Should this be stated in the kernel spec, or is it a stdlib concern?

**OQ13.2. Effect composition — `LogicStreamT[F, A]`.** The Scala implementation parameterizes the logic stream over an effect monad `F`. In Anthill terms: a query that reads from KB has `effects (Reads kb)`. A query inside an operation might also have `effects (Modifies store)`. How does the logic monad compose with the effect system?

Options:
  - (a) Queries are always pure (`Reads kb` is implicit, no other effects inside stream processing)
  - (b) Streams are parameterized over effects: `Stream{T = S, E = Effects}` — a logic monad transformer
  - (c) Effects are tracked per-element: each result in the stream carries its effect footprint

**OQ13.3. Backtracking and state.** If a computation within a stream modifies state (e.g., `effects (Modifies store)`) and then the stream backtracks to try the next alternative, is the state modification rolled back? This is the classic `LogicT + StateT` interaction:
  - **No rollback**: State is threaded linearly through the stream. Backtracking doesn't undo effects. Simpler but surprising.
  - **Rollback**: Each branch gets its own copy of state. Correct but expensive (copy-on-write? persistent data structures?).
  - **Disallow**: Effectful operations inside streams must be pure. Effects only happen when consuming stream results.

**OQ13.4. Fair vs unfair composition.** Standard `flatMap` (Prolog-style) fully explores the left branch before the right — unfair, can diverge on infinite streams. `fairFlatMap`/`interleave` alternate between branches. Which is the default for Anthill queries?
  - For finite KB fact sets, fairness is less critical
  - For derived facts (forward chaining / recursive rules), fairness prevents divergence
  - Should both be available? Is unfair the default with fair as an explicit combinator?

**OQ13.5. `msplit` as a kernel primitive.** In LogicT, `msplit` is the single primitive from which `once`, `limit`, `interleave`, `fairFlatMap`, `ifte` are all derived. Should Anthill's `Stream` sort have `msplit` as a primitive operation?

```
-- msplit decomposes a stream into first result + rest
operation msplit(s: Stream{T = ?S}) -> Option{T = Pair{fst = ?S, snd = Stream{T = ?S}}}
  effects (Reads kb)
```

**OQ13.6. `guard` and constraint integration.** In the logic monad, `guard(p)` is a zero-or-one-element stream: succeeds if `p` is true, empty otherwise. This is exactly what constraint atoms do in rule bodies (`gt(?bal, 1000)` succeeds or fails). Should `guard` be an explicit `Stream` operation, or is it implicit in the query conjunction semantics?

**OQ13.7. `once` / cut semantics.** `once(q)` takes the first result and discards alternatives. In Prolog this is "cut". In Anthill:
  - Is `once` equivalent to the `first(query)` from R2?
  - Does `once` commit to the first result (no backtracking past it)?
  - How does this interact with constraint checking — if the first result violates a downstream constraint, can we backtrack into `once`?

**OQ13.8. Stream consumers — observation.** The logic monad distinguishes between the *logic computation* (inside the monad, lazy) and *observation* (consuming results, effectful). In the Scala impl, `Observer[A]` is the effect type for consuming results:
  - `mObserveOne(stream)` — get first result (in effect monad)
  - `mObserveN(stream, n)` — get first N results
  - `foldWhile(stream, init)(pred)(op)` — fold until predicate fails

Should Anthill have a similar distinction? Inside a `Stream`, you're in "logic land" (backtracking, variables, unification). To get concrete results out, you "observe" — which is effectful and deterministic.

**OQ13.9. Branching as an effect — direct-style logic programming.** Instead of building streams monadically (`flatMap`/`mplus` chains), can we express logical computation in **direct style** by treating branching as an effect?

The idea: a new effect kind `Branches` (or `Spawns`, `Backtracks`) declares that an operation can produce multiple results via backtracking. Inside such an operation, you write sequential-looking code, and the effect system handles the branching:

```
-- An operation that searches for high-balance accounts
operation high_balance_owners() -> Stream{T = String}
  effects (Reads kb, Branches result)
{
  -- 'choose' picks one element from a stream, branching the computation
  -- for each choice. This is 'reflect' in Haskell/Scala LogicT.
  ?acct = choose(query account(?, ?, ?))

  -- 'guard' filters: if false, this branch dies (backtracks)
  guard(gt(balance(?acct), 1000))

  -- the "return" of each surviving branch contributes to the result stream
  owner(?acct)
}
```

This is analogous to:
- Scala `dotty-cps-async/logic`: `reify[LogicStream] { val x = reflect(stream); guard(p(x)); f(x) }`
- Algebraic effects: `Branches` is a resumable effect where each `choose` forks the continuation
- Prolog: the entire language is implicitly in this mode

Key questions about this approach:

**OQ13.9a.** Should `Branches` be a well-known effect kind (like `Modifies`, `Reads`) recognized by the kernel? Or can it be a user-defined effect whose semantics are provided by a handler/realization?

**OQ13.9b.** What are the primitive operations inside a `Branches` effect?
  - `choose(stream)` — pick one element, fork for each alternative
  - `guard(condition)` — filter current branch
  - `fail` / `empty` — kill current branch
  - Are these sufficient? Or do we also need `interleave` and `fairChoose` for fair branching?

**OQ13.9c.** How does `Branches` compose with other effects? This is the central design question — the monad transformer ordering problem expressed in Anthill's effect system.

**`Branches + Reads`** — branching search over read-only state. Natural and safe. Each branch sees the same snapshot. This is the common case for KB queries.

**`Branches + Modifies`** — the hard case. Three possible semantics:

| Semantics | Meaning | Analogy |
|-----------|---------|---------|
| **Linear threading** | State is threaded through branches left-to-right. Branch 2 sees mutations from branch 1. No rollback. | `StateT` outside `LogicT` |
| **Branch-local copy** | Each branch gets its own copy of state. Mutations are isolated. Merging is the caller's problem. | `LogicT` outside `StateT` |
| **Disallow** | `Branches + Modifies` on the same resource is a static error. Mutations only happen outside `Branches`. | Conservative / safe |

The Scala `LogicStreamT[F, A]` uses the "F outside Logic" pattern — effects are in the observer monad, so state is threaded linearly through stream consumption, not through branching. This is effectively the "linear threading" option.

For Anthill, the safest default may be: `Branches + Reads` is free, `Branches + Modifies` on the *same resource* requires explicit opt-in with declared semantics (linear or branch-local).

**`Branches + Emits`** — each branch can emit events. Two possible semantics:
  - **Collect all**: events from all branches (including dead-end branches that later fail) are emitted. Analogous to `WriterT` outside `LogicT`.
  - **Collect surviving only**: events are buffered per-branch and only committed when a branch produces a result. More principled but requires buffering.

**`Branches + Errors`** — an error in one branch:
  - **Kills that branch** (backtrack to next alternative). This is the natural logic monad behavior — failure = no solution on this path.
  - **Kills the whole computation**. This would be for "fatal" errors that shouldn't be backtracked over.
  - Maybe distinguish: `fail` (backtrack) vs `error` (abort). The Scala impl wraps as `Try[A]` — both `Success` and `Failure` are stream elements, giving the consumer control.

**`Branches + Requires`** — capability checking. If a capability is missing, does the branch fail (backtrack) or error (abort)? Probably fail — "this approach requires capability X, try another approach."

**`Branches + Branches`** — nested branching. This is nested `LogicT` — a stream of streams. Options:
  - Flatten automatically (`flatMap` semantics) — inner branching extends outer branching
  - Keep nested (`Stream{T = Stream{T = S}}`) — caller decides how to flatten
  - Anthill should probably flatten by default (inner `choose` extends the outer search), with explicit `Stream` nesting when needed.

**OQ13.9d.** Is the result type of a `Branches` operation always `Stream{T = R}`? I.e., does `effects (Branches result)` imply that the declared return type `R` gets wrapped into `Stream{T = R}` automatically?

**OQ13.9e.** Can `Branches` be nested? An operation with `Branches` calls another operation with `Branches` — does this produce a stream of streams, or are they flattened (like nested `flatMap`)?

**OQ13.9f.** Relationship to rule bodies. A rule body `rule head :- q1, q2, q3` is already direct-style logic: each `qi` is implicitly a `choose` from matching facts, with shared variables providing the join. Are rule bodies syntactic sugar for an operation with `effects (Branches result, Reads kb)`?

**OQ13.9g.** Connection to algebraic effects / delimited continuations. `Branches` is essentially a multi-shot delimited continuation effect — each `choose` captures the continuation and runs it once per choice. Should Anthill's effect system support this generally (any effect can be multi-shot), or is `Branches` special?

**OQ13.10. Async/concurrent queries.** The Scala impl has `CpsConcurrentLogicMonad` with `parOr` — parallel disjunction where both branches run concurrently. Should Anthill queries support concurrent evaluation? This matters for:
  - Querying multiple KB indexes in parallel
  - Federated queries across remote KBs
  - Long-running derived queries that benefit from parallelism

**OQ13.11. Error handling in streams.** The Scala impl wraps elements as `Try[A]` — a stream can contain both successes and failures without stopping. Should Anthill streams propagate errors as stream elements, or should an error terminate the stream?

### OQ14. Scored Streams and Intelligent Search (RLLogic perspective)

A standard logic monad treats all branches equally — it's a queue. A **scored logic monad** is a **priority queue**: branches carry scores, and the highest-scored branch is explored first. This connects query evaluation to optimization, heuristic search, and reinforcement learning.

Reference implementation: `rl-logic` — `CpsScoredLogicMonad[F, R]` parameterized over score type `R`.
Blog: https://github.com/rssh/notes/blob/master/2026_02_07_scored_logic_monad.md

#### Background: Scored Logic Monad

Extension of the logic monad with scored branches:

| Operation | Type | Meaning |
|-----------|------|---------|
| `scoredPure(a, score)` | `(A, R) -> M[A]` | Single value with explicit score |
| `scoredMplus(m, score, next)` | `M[A] -> R -> M[A] -> M[A]` | Disjunction with scored alternative |
| `multiScore(branches)` | `Seq[(R, () -> M[A])] -> M[A]` | Multiple scored lazy branches |

The score type `R` has a `ScalingGroup` structure defining how scores compose:

| Scaling | `combine(a, b)` | Use case |
|---------|------------------|----------|
| **Multiplicative** | `a * b` | Probabilities, likelihoods |
| **Additive** | `a + b` | Costs, distances (Dijkstra) |

The internal representation uses a **priority queue of streams** — `msplit` always returns the highest-scored result first, enabling best-first search.

#### Direct mapping to Anthill

| Scored logic monad | Anthill concept |
|---------------------|-----------------|
| Scored branch | Fact/rule with associated priority (trust level? relevance score?) |
| `multiScore(branches)` | Query results ranked by relevance |
| Priority queue exploration | Best-first KB search |
| `ScalingGroup` | How scores compose across rule chains |
| RL model scoring branches | Agent learning which KB paths are productive |
| `maxSuboptimalResultPool` | Approximate/anytime query answers |

#### Open questions

**OQ14.1. Should `Stream` support scores?** Options:
  - (a) `Stream{T = S}` is always unscored (standard logic monad). Scoring is a separate `ScoredStream{T = S, R = Score}` sort.
  - (b) `Stream` is always scored, with a default "uniform" score (all branches equal) as the unscored case.
  - (c) Scoring is a parameter: `Stream{T = S, scoring = None}` vs `Stream{T = S, scoring = Float}`.

**OQ14.2. Relationship between scores and trust levels.** Anthill already has trust levels on facts (Proved > Verified > Tested > Empirical > Proposed > Stale). Trust is a scoring mechanism. Should query result ordering use trust levels as scores? E.g., when multiple rules derive the same fact, prefer the one with higher trust.

**OQ14.3. Score sources.** Where do branch scores come from?
  - **Trust levels** on facts/rules — built-in, always available
  - **Explicit annotations** — user-provided scores on rules or facts
  - **Computed scores** — a function that scores each branch (heuristic)
  - **Learned scores** — an RL model (neural network) that assigns Q-values to branches based on experience

**OQ14.4. Search strategy as configuration.** The scored logic monad's behavior depends on the priority queue implementation and search policy. Should Anthill queries support configurable search strategies?
  - **BFS** — standard unscored logic monad (queue)
  - **DFS** — stack-based exploration (Prolog default)
  - **Best-first** — scored logic monad (priority queue)
  - **Beam search** — scored, limited width (`maxSuboptimalResultPool`)
  - **Iterative deepening** — bounded depth, increasing

Could this be an effect parameter? E.g., `effects (Branches(result, strategy = best_first))`.

**OQ14.5. `ScalingGroup` in Anthill.** The score composition law (multiplicative vs additive) determines how scores combine across rule chains. Is this a kernel concern or stdlib?
  - If kernel: the `Stream` sort needs a scaling parameter
  - If stdlib: scoring is an optional layer on top of `Stream`

**OQ14.6. Anytime / approximate queries.** The `maxSuboptimalResultPool` setting in RLLogic enables returning "good enough" results before full exploration. Should Anthill queries support this?
  - A query with a deadline: "give me the best results found within N steps"
  - A query with a quality threshold: "give me results scored above X"
  - This connects to agent systems where bounded computation matters

**OQ14.7. RL-guided KB exploration.** The deepest connection: an agent navigating a knowledge base is doing reinforcement learning — each query/rule application is an action, each derived fact is a state transition, and utility of the result is the reward. Should Anthill's query system support:
  - Agents that **learn** which query strategies work well for a given KB?
  - Model-based scoring where a trained model (neural network, decision tree, etc.) assigns Q-values to candidate rule applications?
  - Training feedback loops where query outcomes update the model?

This is speculative for Stage 0 but architecturally significant — if `Stream` is designed as a scored logic monad from the start, RL integration becomes a natural extension rather than a retrofit.

**OQ14.8. Connection to pheromones.** The Anthill metaphor includes pheromone trails — signals that attract agents. Scored branches are essentially pheromone-weighted paths through the KB. Can the scoring mechanism be unified with the pheromone concept? E.g.:
  - Frequently successful query paths accumulate higher scores (pheromone reinforcement)
  - Rarely used or failing paths decay (pheromone evaporation)
  - New agents follow high-pheromone paths (exploitation) with occasional random exploration

**OQ14.9. MiniMax and adversarial queries.** The RLLogic impl includes MiniMax for two-player games. In an Anthill context, adversarial search could model:
  - Constraint satisfaction (constraints = adversary trying to violate invariants)
  - Multi-agent negotiation (agents with competing objectives)
  - Robustness checking ("what's the worst case for this query?")

Is this relevant to Anthill's design, or too specialized for the kernel?

### OQ15. Sort-Defined Syntax Sugar

Rather than hardcoding query syntax in the grammar, can sorts **declare** what syntactic forms they support? This makes sugar extensible — `Stream` gets comprehension syntax, `List` gets literal syntax, `Query` gets `?-` syntax, and user-defined sorts can opt in to the same mechanisms.

#### Precedent in other languages

| Language | Mechanism | What it enables |
|----------|-----------|-----------------|
| Scala | `for`-comprehension | Sugar for any type with `flatMap`/`map`/`withFilter` |
| Haskell | `do`-notation | Sugar for any `Monad` |
| Kotlin | scope functions, builders | Sugar via lambdas with receiver |
| Maude | mix-fix syntax declarations | User-defined operator syntax |
| Agda | syntax declarations | User-defined notation |

#### How could this work in Anthill?

**Option A: By satisfying well-known spec sorts.** A sort that satisfies certain spec sorts automatically gets access to the corresponding syntax:

```
sort Stream {
  -- By having these operations, Stream qualifies for comprehension syntax:
  operation pure(x: ?T) -> Stream{T = ?T}
  operation flatMap(s: Stream{T = ?A}, f: ?A -> Stream{T = ?B}) -> Stream{T = ?B}
  operation guard(cond: Bool) -> Stream{T = Unit}
}

-- Because Stream satisfies Monad-like interface, this syntax works:
[?owner | ?acct <- query account(?, ?, ?), guard(gt(balance(?acct), 1000)), owner(?acct)]
-- desugars to:
flatMap(query account(?, ?, ?), \?acct ->
  flatMap(guard(gt(balance(?acct), 1000)), \_ ->
    pure(owner(?acct))))
```

The kernel defines which "spec sorts" unlock which syntax forms. Similar to how Rust's `Iterator` trait gives you `for` loops, or Haskell's `Monad` gives you `do`.

**Option B: Explicit syntax declarations on sorts.** Sorts declare their syntax patterns directly:

```
sort Stream {
  -- Declare that Stream supports comprehension syntax
  syntax comprehension [?result | ?bindings]
    where ?bindings desugars via flatMap, guard, pure

  -- Declare that Stream supports for-each
  syntax foreach for ?x in ?stream { ?body }
    where desugars via msplit iteration
}
```

This is more explicit but requires a mini-language for describing desugaring rules.

**Option C: Fact-based syntax activation.** Syntax is activated by KB facts — asserting `fact SyntaxComprehension{T = Stream}` enables comprehension syntax for `Stream`:

```
-- In stdlib:
sort SyntaxComprehension {
  -- Activates [result | generators] syntax for sort T
  -- Requires T to have: pure, flatMap, guard
}

fact SyntaxComprehension{T = Stream}   -- Stream gets comprehensions
fact SyntaxComprehension{T = List}     -- List gets comprehensions too
```

This is the most Anthill-native approach — syntax activation is just a fact in the KB, queryable and modifiable.

#### What syntax forms could be sort-defined?

| Syntax form | Unlocked by | Example |
|-------------|-------------|---------|
| **Comprehension** `[expr \| generators]` | `pure` + `flatMap` + `guard` | `[?x \| ?x <- stream, gt(?x, 0)]` |
| **Builder** `{ items }` | `empty` + `append` | `List { 1, 2, 3 }` |
| **For-each** `for x in coll { body }` | `msplit` or iteration protocol | `for ?acct in accounts { ... }` |
| **Direct-style branching** `choose`/`guard` | `Branches` effect + `msplit` | See OQ13.9 |
| **Pattern destructuring** | constructors | `let cons(?head, ?tail) = list` |
| **Operator** `a + b` | named operation `add` | Numeric sorts |
| **Pipe** `x \|> f` | function application | `stream \|> filter(gt(?, 0)) \|> collect` |

#### Open questions

**OQ15.1.** Which approach (A, B, C, or hybrid)? Option A is simplest; Option C is most Anthill-native.

**OQ15.2.** Is syntax sugar a kernel concern or a tool/IDE concern? The kernel could be syntax-agnostic (everything is terms + operations), with sugar handled by the parser layer. Or the kernel could understand sugar declarations and desugar during loading.

**OQ15.3.** Can sorts define **new infix operators**? E.g., `Stream` defines `|>` for pipe, `Numeric` defines `+` for add. How does this interact with the existing operator parsing in the grammar?

**OQ15.4.** How does sort-defined sugar interact with type inference? In `[?x | ?x <- expr]`, the compiler needs to know that `expr` is a sort supporting comprehensions to desugar correctly. This requires type information during parsing/desugaring, which may conflict with the current parse-then-load pipeline.

**OQ15.5.** Can sugar be **scoped**? E.g., `import anthill.prelude.Stream.syntax.comprehension` enables comprehension syntax only in the importing scope. This prevents global syntax pollution.

**OQ15.6.** Relationship to the `describe` mechanism. Description blocks (`{< text >}`) are already a form of syntax that produces facts. Could syntax sugar declarations follow the same pattern — syntax is metadata that produces desugaring facts?

## Possible Design Sketch (Not a Decision)

### Layered design

The query system can be layered, with each layer building on the previous:

**Layer 0 — Kernel primitives (terms + unification)**
1. A query is a term with variables — no new AST node needed.
2. `match_fact` = unification of pattern against stored fact.
3. `query(kb, pattern)` = scan active facts, collect unifiers.

**Layer 1 — Stream as logic monad (stdlib)**
4. `Stream{T = S}` is a logic monad over sort `S`.
5. `msplit` is the primitive; `mplus`, `flatMap`, `guard`, `once`, `limit` derived.
6. `Branches` is an effect kind: direct-style logic via `choose`/`guard`/`fail`.
7. Aggregation/projection: `map`, `filter`, `fold`, `count`, `collect` on `Stream`.

**Layer 2 — Scored streams (stdlib or extension)**
8. `ScoredStream{T = S, R = Score}` extends `Stream` with priority-queue exploration.
9. `ScalingGroup` (multiplicative/additive) determines score composition.
10. Search strategy configurable: best-first, beam search, bounded.
11. Trust levels on facts can serve as default scores.

**Layer 3 — RL-guided search (extension / future)**
12. Model-based scoring: trained models assign Q-values to branches.
13. Training feedback: query outcomes update the scoring model.
14. Pheromone integration: frequently successful paths accumulate score.

### What's kernel vs stdlib vs extension

| Concern | Layer | Rationale |
|---------|-------|-----------|
| Terms with variables as patterns | Kernel | Fundamental to the types-are-terms principle |
| Unification / match_fact | Kernel | Core reasoning primitive |
| Query by sort, by domain | Kernel | Requires sort/subsort awareness |
| `Stream` sort + `msplit` | Stdlib | Logic monad structure |
| `Branches` effect | Stdlib (well-known) | Direct-style logic programming |
| `guard`, `once`, `limit`, `interleave` | Stdlib | Derived from `msplit` |
| Aggregation (`count`, `fold`, etc.) | Stdlib | Operations on `Stream` |
| Scoring / `ScoredStream` | Stdlib or extension | Priority-queue exploration |
| `ScalingGroup`, search policies | Extension | Configurable search strategies |
| RL model integration | Extension | Learned scoring |
| `Query` sort / `QueryRepr` | Stdlib + reflect | First-class query values + introspection |

**Observation boundary**: consuming stream results is effectful — `observe_one`, `observe_n`, `collect` cross from logic-land to effect-land.

This keeps the kernel minimal (queries are terms + unification), gives `Stream` rich algebraic structure via the logic monad, and leaves the door open for scored/RL-guided search without baking it into the kernel.

## References

- Isabelle formalization: `query` and `match_fact` in `Anthill_Kernel.thy`
- Rust implementation: discrimination-tree queries in `rustland/anthill-core/src/kb/discrim.rs`
- Reflect module: `stdlib/anthill/reflect/reflect.anthill` (typed query operations)
- Persistence module: `stdlib/anthill/persistence/store.anthill` (`QueryableStore`)
- kernel-language.md §8.2 (subsort querying), §8.3 (backward/forward chaining)
- Logic monad: Kiselyov et al., "Backtracking, Interleaving, and Terminating Monad Transformers"
- Scala logic monad: `dotty-cps-async/logic` — `LogicStreamT[F, A]`
- Logic monad blog: https://github.com/rssh/notes/blob/master/2024_01_30_logic-monad-1.md
- Scored logic monad / RLLogic: `rl-logic` — `CpsScoredLogicMonad[F, R]`, `ScoredLogicStreamT`
- Scored logic monad blog: https://github.com/rssh/notes/blob/master/2026_02_07_scored_logic_monad.md
