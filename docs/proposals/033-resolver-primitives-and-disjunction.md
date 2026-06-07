# Proposal 033: Resolver primitives and disjunction

**Status:** Draft
**Depends on:** [026-expression-evaluator](026-expression-evaluator.md), [026.1-value-integrated-kb-queries](026.1-value-integrated-kb-queries.md)
**Related:** [027-effect-handlers-and-standard-effects](027-effect-handlers-and-standard-effects.md)
**Affects:** `rustland/anthill-core/src/kb/{resolve,execute,mod}.rs`, new `stdlib/anthill/kernel/`

## Motivation

`LogicalQuery::disjunction(L, R)` and multi-goal `LogicalQuery::negation(q)` currently return `LowerError::NotYetImplemented` (`kb/execute.rs:382`, `kb/execute.rs:356`). The resolver has no native OR — it iterates `Candidate`s for one head at a time, and any branching on the goal side has to be lifted into a fresh rule.

Inline rule-lifting (synthesize `or_NNN(...) :- L`, `or_NNN(...) :- R` per call site) works for one feature but does not compose. The same primitive is needed for:

- `LogicalQuery.disjunction` (this proposal — the immediate driver).
- The future `Branch` effect from proposal 026 §Effects: a `Branch(a, b)` effect with a "collect all paths" handler is the expression-side analogue of disjunction.
- `cut`, soft-cut, `if-then-else`, `once`, `findall` — all express choice-point manipulation.
- Multi-goal negation (proposal 026.1, deferred): "fail if conjunction succeeds" needs a synthesized goal head; the same lifting story applies.

A standalone synthesis path per feature accretes ad-hoc symbols, fragments tests, and hides the shared mechanism. Instead, expose one resolver primitive — `push_choice` — and rebuild the higher constructs as rewrites over it.

## Requirements

1. `LogicalQuery::disjunction(L, R)` lowers to native resolver branching with no auto-generated rule symbols leaking into the KB.
2. The same primitive is reusable for the eventual `Branch` effect handler (one resolver substrate, two surface syntaxes).
3. Cut / `once` / `findall` should be expressible as further rewrites in `anthill.kernel` without further core changes.
4. Existing `Candidate` machinery (alts iteration, dedup, solution accounting in `FrameState::ChoicePoint`) is reused — disjunction is not a parallel codepath.
5. Resolver primitives live in a clearly-marked namespace, segregated from the user-facing prelude.

## Design

### New top-level namespace `anthill.kernel`

Resolver primitives live in `stdlib/anthill/kernel/`. Rationale:

- They are not for application code. `anthill.prelude` reaches into them only when defining derived combinators (`or`, `once`, `findall`).
- Mirrors the precedent from 026.1 where `anthill.reflect.*` collects KB-introspection primitives. `anthill.kernel.*` collects resolver primitives.
- The qualified-namespace approach replaces any need for sigil prefixes (e.g. `$push_choice`) — discoverability through normal symbol resolution.

Initial contents:

```anthill
namespace anthill.kernel
  export push_choice

  operation push_choice(?a: Term, ?b: Term) -> Bool
end
```

### `push_choice(a, b)` — primitive semantics

`push_choice(a, b)` is **binary**. It succeeds immediately with no bindings; its effect is on the resolver frame, not on the substitution. The continuation (the rest of the goal queue after `push_choice`) is shared between both branches:

- Given a current frame `[push_choice(a, b), c₁, c₂, …]` with substitution σ, let `tail = [c₁, c₂, …]`.
- The frame is converted to a `ChoicePoint` with two alternatives:
  - `cont_a = [a, c₁, c₂, …]` — try `a` followed by the shared tail.
  - `cont_b = [b, c₁, c₂, …]` — on backtrack, try `b` followed by the shared tail.
- Both alternatives carry the same σ. No new rule, no auto-generated symbol, no entry in any KB index.

Algebraically: `push_choice(a, b) ; tail` is equivalent to `(a ; tail)` ∨ `(b ; tail)`. The two branches are symmetric; the shared `tail` is the WAM continuation pointer captured once at the choice point.

### `Candidate::Continuation` variant

`enum Candidate` in `kb/resolve.rs:105` gains:

```rust
enum Candidate {
    Rule(RuleId, Substitution),
    Occurrence(OccurrenceId, Substitution),
    Assumption(Substitution),
    /// Inline goal-list continuation, no associated rule head.
    /// The parent frame's σ is inherited unchanged (no head match
    /// contributes bindings), so the variant carries no Substitution.
    Continuation(Vec<TermId>),
}
```

Continuation is a degenerate "rule" with no head and a body of `goals`. The match-step matches trivially (no head), and the body becomes the new goal queue. All of `FrameState::ChoicePoint`, alts iteration, dedup, and solution accounting remain unchanged.

**Goal list = `Vec<TermId>`, σ inherited from parent.** The variant does not carry a substitution snapshot because push_choice contributes no head-match bindings — the parent frame's σ is identical to what each branch starts with. The implementation simply reads `frame.subst.clone()` when constructing each branch's child frame, instead of storing a redundant copy on the candidate.

The goal list stays `Vec<TermId>` (matching `Frame.goals: Vec<TermId>` at `resolve.rs:207`) for the same reason 026.1 keeps it that way: matching/unification fast-paths over hash-consed structural equality. Bindings continue to live in σ as `Value` (post-Q1) — that storage choice is unaffected by this proposal.

### `BuiltinTag::PushChoice` in `step_init`

`push_choice` is **not** dispatched through `execute_builtin` (which would need a `Substitution`-only effect channel). It is special-cased in `step_init`, alongside `Not` and `HoApply`:

1. Walk `args[0]` and `args[1]` through the current substitution σ to obtain `goal_a, goal_b: TermId`. The walk uses the existing resolver-internal mechanism (the same one used elsewhere in `step_init` to walk goals before dispatch). The walk is unconditionally a `TermId → TermId` rewrite: every binding that can flow into a goal-position var today is `Value::Term(t)`, regardless of source.

   Why every goal-position binding is `Value::Term`:
   - `bind_term` (the resolver-internal binding path) wraps as `Value::Term(t)` by construction.
   - Facts retrieved through proposal 007's queryable-store mechanism enter the KB as TermId-asserted facts, then bind through `bind_term` — also `Value::Term(t)`.
   - `lower_query`'s `alloc_from_value` recursively promotes `Value::Entity{..}` payloads back to `Term::App` and scalars to `Term::Lit`, so any caller-supplied Value crossing the boundary is already a TermId by the time it reaches σ.
   - `Value::Closure | Stream | Substitution | Lazy | Int64 | Float | String | Bool` (raw) are evaluator-only; `alloc_from_value` either wraps them (scalars) or rejects them (`UnsupportedVariant`). They never appear as σ bindings on a KB goal-position var.

   Forward-compatibility note: a future proposal (e.g. 026.1 Q4 *if* the external-stream design is pursued) might introduce a `bind_value`-fed path that surfaces `Value::Entity{..}` directly on goal-position vars, avoiding the row-by-row hash-cons. If that lands, the walk would need to invoke `alloc_from_value` (`kb/execute.rs:179`) to lift non-Term Values into the goal queue. That hypothetical concern is shared by *every* resolver step that walks goals through σ — not specific to push_choice — and is out of scope for proposal 033.
2. Let `tail = goals[1..]`. Compute:
   - `cont_a = { let mut v = vec![goal_a]; v.extend_from_slice(tail); v }`
   - `cont_b = { let mut v = vec![goal_b]; v.extend_from_slice(tail); v }`
3. Replace the frame's `Init` state with `ChoicePoint { candidates: vec![Continuation(cont_a), Continuation(cont_b)], .. }`. Both branches will read the parent frame's σ when they're picked — no per-candidate clone needed.
4. Continue the resolver loop — existing `ChoicePoint` machinery does the rest.

Variables in goal position are already supported because `step_init` walks goals through the substitution before dispatch.

### `or` — first user

Define in `anthill.kernel.kernel`:

```anthill
namespace anthill.kernel
  rule or(?a, ?b) :- push_choice(?a, ?b)
end
```

Expansion of `or(a, b), c`:

```
[or(a, b), c]
  → [push_choice(a, b), c]                    (rule unfold)
  → [a, c]              ∨ [b, c]               (push_choice rewrite — shared tail c)
```

That is the desired semantics: try `a` followed by `c` first; on backtrack, try `b` followed by `c`.

### `LogicalQuery::disjunction` lowering

`kb/execute.rs:382` becomes:

```rust
if Some(functor) == syms.disjunction {
    let l_goals = self.lower_query(/* L */)?;
    let r_goals = self.lower_query(/* R */)?;
    let l = self.wrap_as_single_goal(l_goals)?;   // existing helper used by negation
    let r = self.wrap_as_single_goal(r_goals)?;
    return Ok(vec![self.kb.intern_term(Term::App {
        functor: syms.or.ok_or(LowerError::NotYetImplemented(
            "disjunction without loaded anthill.kernel.or"))?,
        args: smallvec![FnArg::Pos(l), FnArg::Pos(r)],
        names: SmallVec::new(),
    })]);
}
```

`wrap_as_single_goal` is the same conjunction-lifting helper already used by single-goal negation at `kb/execute.rs:351`; this proposal does not add it but does generalize its name.

### Multi-goal negation (closes WI-076)

Multi-goal negation (`kb/execute.rs:356`) is a special case of the same lifting — synthesize an intermediate conjunction-rule head, then `not(head)`. With the helper extracted for disjunction, this becomes a one-line change. Filed as WI-076; closing it as a side effect of WI-075's helper extraction is acceptable.

## Solution semantics under shared-tail branching

A subtle question: if the tail is *not* renumbered when split between branches, and both branches succeed, what does the answer stream look like?

**No VarId collision across solutions.** Each `Candidate::Continuation` carries its own σ clone (same pattern as `Rule(rid, σ)` and `Occurrence(occ, σ)` in `kb/resolve.rs:105`). When branch A succeeds with σ_A binding `?x = 5` and branch B independently succeeds with σ_B binding `?x = 7`, the two σ are physically distinct `HashMap<VarId, Value>` allocations. Same key, different values, in different maps. Anthill's resolver does not use a WAM-style trail; it does not unwind bindings on backtrack — it discards σ_A when iterating to the next candidate and reads the σ snapshot stored in branch B's `Continuation`.

**Projection is resolver-wide, not per-candidate.** The set of caller-introduced query variables (`answer_links` per `rustland/CLAUDE.md` §De Bruijn Variables) is established once at `kb.resolve` entry and stays constant across the whole search. Both branches share the same `answer_links` keys. Solution emit, at frame-empty, walks `answer_links` and resolves each through the current frame's σ:

```rust
Solution {
    bindings: answer_links.iter()
        .map(|qv| (*qv, σ.resolve_with_term(*qv)))
        .collect()
}
```

`Continuation` therefore carries only `(goals, σ)` — projection metadata is not duplicated per candidate.

**Why the shared tail does not cause projection collapse.** The tail is the *work queue*, not the *answer template*. Even though branch A and branch B see the same `?q1` VarId in `tail = [use(?q1)]`, the goals *before* the tail (`a` and `b`) may bind `?q1` to different values along the two resolution paths. By the time the tail runs, σ_A and σ_B carry those distinct bindings; the projection step pulls `?q1` through the branch-local σ, yielding two distinct answers.

**Dedup at projection level.** `FrameState::ChoicePoint`'s existing solution dedup compares projections, not raw σ. If both branches happen to project all `answer_links` to identical values (e.g. `or(p(5), p(5))`), the second solution is collapsed — correct set-of-answers semantics. Internal fresh-Global bindings that differ between σ_A and σ_B but do not flow into `answer_links` cannot prevent dedup, because they are never observed.

**Branch isolation comes from σ-clone, not from goal-list renaming.** Renaming variables in the duplicated tail would break the link between the branching goal (`a` or `b`) and the rest of the work — `or(p(?x), q(?x)), use(?x)` requires both branches to share `?x` so that `use(?x)` operates on whatever was bound. Variable identity in the tail is a *feature*; per-σ binding values is where the branches diverge.

## Resolver invariants preserved

- **Substitution semantics.** `push_choice` introduces no bindings; the `Substitution` cloned into both continuations is identical to the one entering the step.
- **Solution dedup.** The existing alts dedup in `ChoicePoint` already handles the case where `cont_a` and `cont_b` reach the same answer set (the `or(a, a)` degenerate case).
- **Negation-as-failure.** `not(or(a, b))` resolves correctly because `or` is a normal rule head — NAF inspects whether *any* alternative for `or(a, b)` succeeds, which is "does `a` succeed or does `b` succeed."
- **Forall-discharge / `Assumption` candidates.** Continuations carry a `Substitution` like other variants; assumed facts in scope when the choice was created remain in scope along both branches.

## Implementation milestones

**M1 — `Continuation` candidate**

- Extend `enum Candidate` with `Continuation(Vec<TermId>, Substitution)`.
- Update match-step: `Continuation` is treated as a body-only candidate (no head unification).
- All existing tests green (variant unused in this milestone).

**M2 — `anthill.kernel` namespace + `push_choice` builtin**

- Create `stdlib/anthill/kernel/kernel.anthill` with `operation push_choice(?goal: Term) -> Bool` and `rule or(?a, ?b) :- push_choice(?b), ?a`.
- Wire `register_prelude` (or equivalent) to load `anthill.kernel` alongside `anthill.prelude` and `anthill.reflect`.
- Add `BuiltinTag::PushChoice` in `kb/mod.rs:27`; register as `"anthill.kernel.push_choice"` in `register_standard_builtins` (`mod.rs:1656`).
- Handle `PushChoice` in `step_init` per §`BuiltinTag::PushChoice in step_init` above.
- Tests: `push_choice(g)` standalone, `or(a, b)` with both branches succeeding, with one branch failing, with a shared variable.

**M3 — `disjunction` lowering**

- Replace `kb/execute.rs:382` `NotYetImplemented` with the rewrite to `or(L_goal, R_goal)`.
- Extract `wrap_as_single_goal` helper from the negation path.
- Tests: `LogicalQuery::disjunction` basic, nested disjunctions, disjunction inside conjunction (no DNF push-down — falls out of the frame structure), shared variables across branches.

**M4 — multi-goal negation (closes WI-076)**

- Use `wrap_as_single_goal` to lift multi-goal negation to single-goal.
- Tests: `negation(conjunction(p, q))` semantics matches `not(synth_head(...))` where `synth_head :- p, q`.

## Future work (out of scope)

- **`Branch` effect handler.** Proposal 026 §Effects mentions `Branch(a, b)`; the runtime handler raises `push_choice` at the resolver layer, sharing the substrate. Lands with the broader functional-operation effect work.

- **Cut and the barrier mechanism.** Cut commits to the *current rule invocation* — given `a(?x) :- b(?x), !, c(?x)`, when `!` fires it must discard (i) any other clauses of `a` still queued at the parent `ChoicePoint`, and (ii) every `ChoicePoint` created during the resolution of `b(?x)` (including `push_choice`-introduced Continuations and any nested rule unfoldings). Choice points created *after* `!` (during `c(?x)`) are untouched.

  The substrate this requires:

  1. **Per-invocation `BarrierId`.** Allocated on rule entry alongside the fresh-Global VarIds in `with_fresh_vars` — `BarrierId` is to cut what `VarId` is to a query variable: a fresh, monotonic, per-invocation tag.
  2. **`ChoicePoint` gains `barrier_at_creation: BarrierId`.** Tagged at the moment the choice point is pushed (via push_choice, rule unfold with multiple alts, occurrence backtracking, etc.).
  3. **`cut(?barrier)` builtin.** The `!` syntax in a rule body is opened to `cut(B)` where `B` is the rule's barrier (parallels DeBruijn-var opening). Semantics: walk the candidate stack and remove every alternative — `Rule`, `Occurrence`, `Continuation`, `Assumption` alike — whose `barrier_at_creation` is `B` or descended from `B`.
  4. **Disjunction–cut interaction falls out naturally.** A cut inside a rule body that *contains* an `or(...)` invocation prunes the push_choice Continuations of `or`, because they were tagged with the outer rule's barrier (transitively). Conversely, a cut inside the rule body of `or` itself (or any inner rule) only prunes within its own barrier — outer push_choice Continuations are preserved. This is Prolog's "disjunction transparent to outer cut, opaque to inner cut" semantics, achieved without a special case.

  Once cut lands, `once(g)` is `(g, !)` lifted into a synthesized rule, `if-then-else(c, t, e)` is `(c, !, t) ; e`, `findall` is meta-call plus collection. All derived; no further substrate.

  Defer to a child proposal (likely 033.1) once disjunction is in production use. The contract being locked in *now*: `ChoicePoint` will eventually grow a `barrier_at_creation` field, and `with_fresh_vars` will eventually grow a `BarrierId` allocator. Naming and scope-nesting rules can stay unspecified until then, but additions to `ChoicePoint` between now and that proposal should leave room.

- **Long-stream disjunction.** WI-077 covers laziness across long disjunctive streams; orthogonal to the substrate.

## Non-goals

- Changing the surface `LogicalQuery` ADT (proposal 026.1 §Q3). Constructors stay; only `disjunction`'s implementation changes.
- Changing the user-facing prelude. `or` is exported from `anthill.kernel`; whether to re-export it from `anthill.prelude` is a stdlib-curation decision, not part of this proposal.
- Replacing the existing rule-based `not` lowering. Negation continues to lower to `not(g)`; the helper extraction is the only overlap.

## Open questions

1. **Visibility of `anthill.kernel.push_choice`.** Should it be `export`ed at all, or kept as an internal symbol resolvable only from `anthill.kernel.*` rules? Leaning toward exported-but-undocumented: experts can use it for advanced control-flow combinators without grep-fu, but it is not part of the public anthill surface.
2. **Naming.** `push_choice` matches the prolog-implementation literature (a "choice point" is "pushed" onto the trail). Alternatives considered: `branch` (collides with the future effect), `alternate`, `amb` (McCarthy/Scheme tradition; cryptic).
3. **Continuation interplay with `forall_impl` discharge (WI-108).** `Assumption` candidates carry frame-scoped facts; `Continuation` carries a substitution. If a `push_choice` fires inside a `forall_impl` proof, do the assumed facts remain in scope along both branches? Expected yes (assumptions are tracked separately from the candidate substitution), but worth a regression test.
4. **Future Value-goal migration.** Goals stay `Vec<TermId>` in this proposal because that matches `Frame.goals` and 026.1's intentional input-boundary architecture. If a future Q-extension to 026.1 (or a new proposal) migrates `Frame.goals` to `Vec<Value>` — letting external-source goals flow without ever hash-consing — `Continuation`'s goal half follows automatically. The implication for *this* proposal: do not let any new code path key off `goals: Vec<TermId>` as a load-bearing contract beyond what the resolver already does. No special action needed; just a forward-compatibility note.

5. **007 ↔ 026.1 reconciliation — resolved (WI-168).** Proposal 007 (persistence layer) and proposal 026.1 (Value-integrated KB queries) described overlapping concerns in unreconciled vocabularies. WI-168 added [007 §11 "Value integration and ingestion contract"](007-persistence-layer.md#11-value-integration-and-ingestion-contract-post-0261), which defines two ingestion paths (bulk-pull TermId / queryable Value-stream), names the parser as the canonical row-to-Value producer for backends that consume anthill source text, and elevates 026.1 Q4 from "optional" to "required for queryable backends at scale." The §`step_init` forward-compat note above remains accurate: a non-Term Value can reach goal position only via Q4's `bind_value` path, and `alloc_from_value` is the existing transit-hash-cons site that path would reuse. No 033 implementation work depends on Q4 landing.
