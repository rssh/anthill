# Proposal 076: A goal's scope in the search — its call, its exit, and the alternatives it leaves

## Status: Draft, written with the user 2026-11-24. Not approved. Nothing here is implemented, and the spec is not changed by it (§8 says what it would change).

## Tracked by: WI-20261122-P6G1P (commit to the first definite proof of a ground goal), WI-20261122-VT9S7 (dependency-directed backtracking). No ticket of its own.

## Relates to: `docs/kernel-language.md` §8.3 (a query yields answers, a relation yields proofs; depth and fuel; negation); proposal 033 (`push_choice`, `Candidate::Continuation`), 033.1 (cut and the barrier), 068 §2.2 (wait states), 052 (relations count proofs), 075 (`SLDProof`, proof mode); WI-569 (σ is persistent).

## The problem

Both tickets measure the same thing: a goal that FAILS after `k` ground goals that each have two proofs costs `2^k` (P6G1P's table, release build):

```
k                        1    2    4     8      12      16
(1 = 1) | (2 = 2)       15   39  167  2583  40999  655415 steps   (2^k)
(1 = 1) | (1 = 2)       14   27   53   105    157     209
!(!((1 = 1) | (2 = 2))) 13   25   49    97    145     193       (negation commits)
```

That is what every Prolog does on `(true ; true), …, fail`. The search order is not wrong. What is missing is a place to do anything else: **the search does not know when a goal has been proved.**

### What the machine is today (both implementations)

- **A frame holds the whole resolvent.** `ResolverFrame` is (`goals`: every goal still to prove, σ, state). Opening a clause builds `body ++ a copy of the tail` (`frame.goals[1..].to_vec()`, `kb/resolve.rs` in `step_choice_point`; `continue_with_goals` the same). Scala: `ArrayBuffer.from(freshBody…) ++= frame.goals.drop(1)` (`resolve/SearchStream.scala`).
- **Once a body is spliced in, the boundary is gone.** Nothing marks where `g`'s proof ends and its caller's tail begins, so `g` being proved is not an event. The choice points opened while proving `g` sit lower on the stack, and a later failure goes back into them in order.
- **A frame is both a branch's state and a choice point.** Every candidate is pushed ABOVE the frame that offered it. The frame is popped only when its candidates are exhausted, which backtracking finds. There is no last-alternative release (WAM's `trust_me`): a call with ONE candidate leaves its frame on the stack until the search backtracks through it. So a deterministic recursion of depth `n` holds `n` frames.
- **Where a boundary was needed, a marker was added.**
  - `!` is baked into the body as `cut(B)`, and the choice point that opened the body is tagged `B` (033.1).
  - A `forall_impl` discharge splices `__pop_assumption(N)` behind its consequent.
  - Each `FrameGoal` carries its own depth, wait state and proof tag, because the frame cannot say what scope a goal is in.
- **Only negation and a closed `eq` sub-proof give a goal its own stacks.** They run a nested `SearchStream`. That is why `!(!(g))` commits in the table above.

### MEASURED, 2026-11-24

`anthill query --max-depth 100000`, wall time and peak RSS. Two builds: the release binary was built 2026-11-21, before the last three days of commits; the debug binary on 2026-11-24, from a tree at or near HEAD `5e721bf5e`; neither was rebuilt for this. Neither is a gate measurement, and the probes are not committed (they are four one-rule files).

A non-tail recursion, whose resolvent grows by one goal per level (`chain(?n) :- (?n = 0) | (?n > 0, chain(?n - 1), ok(1))`), release:

```
n          250     500     1000     2000
time      0.45 s  0.57 s  1.02 s   3.14 s
peak RSS  125 MB  273 MB  850 MB   3.1 GB
```

The CONTROL, the same recursion with `ok(1)` before the call, so the resolvent stays short:

```
n          250     500     1000     2000     4000
time      0.42 s  0.48 s  0.71 s   1.64 s   6.36 s
peak RSS  102 MB  180 MB  475 MB   1.6 GB   6.2 GB
```

A deterministic recursion with no disjunction (`cnt(0)`, `cnt(?n) :- ?n > 0, cnt(?n - 1)`): release 165 MB / 447 MB / 1.57 GB at n = 1000 / 2000 / 4000; debug 105 MB / 181 MB / 487 MB at n = 500 / 1000 / 2000.

So the cost is quadratic **even when the resolvent is short**, which the tail copy alone does not explain. σ is persistent (`imbl`, O(1) clone, WI-569). What a retained frame holds that grows with the level is **not identified**. Finding it is the first step of §5 Stage B: a heap profile of `cnt(4000)`. No profiler is installed on the machine this was measured on.

## 1. How WAM does it

This is the reference design: Warren's abstract machine, as in Aït-Kaci's tutorial reconstruction.

- **The AND side is a chain of environment frames.** A call pushes a frame linked to its caller's. "What to do next" is a code pointer plus a frame pointer, shared by every branch and never copied. When a body finishes (`proceed`, `deallocate`), control returns to the caller's continuation. That is the EXIT of the goal.
- **The OR side is one global stack of choice points.** Each choice point saves what is needed to resume: the arguments, the continuation, the top of the trail, the top of the heap, and the next clause to try. Bindings live in one store; backtracking undoes the trail down to the saved top.
- **A goal owns its alternatives through a height mark, not a stack of its own.** At the call, the machine records the current choice-point height (`B0`, the cut barrier). The goal's alternatives are exactly the choice points above `B0`.
  - If the height at exit is still `B0`, the goal had one way to succeed and nothing is left to retry.
  - `!`, `once` and `->` cut the stack back to `B0`.
  - A frame cannot be freed while a younger choice point might resume into it.
- **Indexing keeps most calls deterministic.** `try / retry / trust` removes the choice point BEFORE the last alternative runs, so most calls leave nothing.

**Do we come back to a choice point a finished rule pushed?** Yes, but only on a later FAILURE, never because the rule finished. A choice point left by a finished goal is its "give me your next answer". Over

```anthill
rule q(1)
rule q(2)
rule p(?x) :- q(?x), r(?x)
```

`q(?x)` exits with `?x = 1` and leaves a choice point for `q(2)`. Control goes to `r(1)`. Only if `r(1)` fails does backtracking pop that choice point and resume `q` with `?x = 2`. Dropping it when `q` finished would lose that answer. That is why the OR stack outlives the goal and is global, and why the goal is tied to it by a mark.

## 2. The idea: a goal's scope

Each goal that is asked gets a scope, with two ends:

- **Its call.** Recorded when the goal is selected: the choice-point height, whether the goal is ground under σ, and the goal's depth and proof tag.
- **Its exit.** Reached when the last goal of its proof has been proved. At the exit, the choice points above the call's height are the goal's **segment**: its remaining alternatives.

At the exit there are three things to do with the segment:

1. **Keep it** (today, and the default for any goal not covered below). A later failure resumes it in order.
2. **Drop it**: a commit, `once`. This is P6G1P's flag (§4). It changes proof counts.
3. **Guard it**: keep it for redo after an answer, skip it on a dead end (§3). It changes neither answers nor proof counts.

"Return to the top stack when the goal is proved" is the exit: control goes back to the caller. The segment is the part that must not simply be dropped there.

## 3. The ground-goal guard — the default

**Rule.** When a goal `g` that was ground under σ at its call reaches a DEFINITE exit (no goal of its proof is still waiting) with a non-empty segment, a guard is placed above the segment. It records how many solutions the search had reached at that moment. When backtracking reaches the guard:

- **No solution was reached since `g`'s exit:** the search after `g` was a dead end. Every alternative of `g` would rebuild the same state and reach the same dead end. Skip the whole segment: cut back to `g`'s call height.
- **A solution was reached:** remove the guard and backtrack in order, as today. `g`'s next proof gives that solution again, and proof counts stay what they are.

**Why the skip is sound.** A ground goal binds no variable outside its proof: everything its proof binds is a fresh variable of a clause it opened. Its definite exit leaves no goal of its own waiting. So every proof of `g` leaves the same state for what comes after: the same σ on every variable the tail can see, the same goals, the same assumptions, the same depths (a goal's depth is its own, §8.3). The search after `g`'s exit is therefore the same search after each of `g`'s proofs. Between pushing the guard and reaching it, the search explored exactly that subtree, so "no solution reached since" means that subtree has none.

**What it covers.**
- The k = 16 chain: each ground `|` exits definitely with a one-candidate segment. When `(1 = 2)` fails, each guard skips its segment. Linear.
- A ground `some_in` with several witnesses followed by a failing goal: linear.
- P6G1P's WHO NEEDS IT: anthill-traces decides clauses on ground values, and the cost is in the clause that FAILS. A clause that holds is decided at its first definite solution. So the guard answers that need with proof counts intact. P6G1P's commit is then needed only if a caller wants a ground goal's proofs counted once (§4).
- It also applies inside a negation's sub-search, which is the same machine. That is where a failing contract clause is decided.

**What it does not change.**
- **Truncation.** A tail cut by the depth limit inside the skipped segment would be cut again at the same depth, and the `truncated` flag is already set. An undecided verdict stays undecided.
- **Faults.** A fault recorded in the tail would be recorded again. Faults are deduplicated.
- **Residuals.** A residual solution is a solution: the guard then backtracks in order.
- **Fuel.** It only saves steps.

**What "solution reached" counts.** Every solution the drain reached, BEFORE answer dedup. With dedup on, a solution reached again is a duplicate and could be skipped too. That extension is not proposed.

**"Ground" is `value_is_ground` under σ.** A type variable counts as a variable, which is the conservative direction. A `var_ref` under Γ is a symbol, not a σ variable, so the identity argument holds for it. Negation's open-world reading of `var_ref` is a different question.

## 4. Commit — P6G1P's flag, opt-in

The same exit and the same conditions (ground at the call, definite exit). Instead of a guard, the segment is cut immediately: `once(g)`. P6G1P's tests stand as written:
- the k = 16 chain is linear with the flag on and `2^k` with it off;
- `(?x = 1) | (?x = 2), ?x > 1` still answers `?x = 2`;
- a ground goal whose first proof is residual and whose second is definite answers definite;
- relation multiplicities are unchanged with the flag off.

It changes proof counts: a ground `(A) | (B)` with both true is one proof instead of two. So it is off by default, and on `KB.execute` it rides on the options of WI-20261122-96QKW (`ExecuteOptions`).

## 5. Backjumping for non-ground goals — VT9S7's general case

The ground guard is backjumping where nothing depends on the skipped choice points. The general case, `member(?c, [1, …, n])` followed by a failing goal that does not read `?c`, needs to know WHO bound what:

- **Each binding remembers the choice-point height that made it.** σ is persistent, so this is a second persistent map, or a field beside each binding.
- **A goal's reads** are the variables it was written with, chased through σ, and the heights of the bindings met on the way.
- **A dead end** (a subtree that reached no solution) jumps to the highest choice point in its conflict set: the union of the reads of the goals that failed in it. It discards the independent choice points in between and merges the conflict set into the target's, as VT9S7 says.

To settle (VT9S7 lists them):
- a negation's sub-search, and a NAF goal's own reads (its negand's variables);
- a goal woken by a binding: its failure depends on the binding that woke it;
- truncation, which must still read as truncated;
- the step accounting of a jump.

This needs Stage C's scopes to be cheap. In today's machine it would be another marker.

## 6. The machine, staged

Each stage is measured on its own and lands on both implementations.

**Stage A — the exit as a marker, in today's machine.** Enough for §3 and §4.
- **At the call.** When a ground `g` is selected in frame `F` (stack index `h`), splice `[g, __exit(h, s)]` in its place, with `s` a fresh scope id. `g` is then asked as usual. Its rewrites in place (arguments evaluated, a predicate applied) stand in front of the marker.
- **Ownership of waiting goals.** A goal rotated behind the tail is stamped with the innermost open scope: the first `__exit` after it in the resolvent.
- **At the marker, in frame `T` (index `t`):**
  - `t == h`: a deterministic exit, nothing to do;
  - a goal stamped `≥ s` is behind the marker: not definite, keep the segment;
  - otherwise: guard (§3) or commit (§4).
- **The guard is a frame state.** `T` becomes `FrameState::Guard { floor: h, solutions }` and its live continuation is pushed above it. When backtracking reaches it, it either neutralizes `[h, guard)` as `apply_cut` does and pops, or just pops.
- **Cost.** One `value_is_ground` per selected goal, and one marker per ground goal. A frame copy happens only at a non-deterministic exit.
- **The marker must be invisible** everywhere a goal COUNT is read:
  - the delay gate `consecutive_delays >= goals.len()`;
  - `yield_sole_goal`'s "only goal";
  - proof mode;
  - residuals.

  That list is the fragility of markers, and the reason for Stage C.

**Stage B — release a frame at its last alternative.** Fixes the retention measured above, after the heap profile says what is retained.
- When a choice point hands out its last candidate, the child replaces it instead of stacking above it. "Last" has to be known: extent rows are matched lazily, and waiting clauses come after the candidates.
- The cut barrier must then be a HEIGHT, as in WAM, not a tag found by scanning for the frame (`apply_cut`). A barrier frame replaced by its child is otherwise "not found", and `apply_cut` asserts.

**Stage C — scopes as the machine's structure.** The answer to "the machine is built wrong".
- **AND.** The flat copied resolvent becomes a persistent linked continuation. A scope is (its goals, the next one, its caller's scope, its call mark). Opening a clause pushes a scope in O(1); a branch copies at most its innermost scope's remaining goals, never the whole resolvent. The exit is structural: a scope with no goals left returns to its caller.
- **OR.** One live state (continuation, σ) plus a stack of choice points, as in WAM. A choice point holds its continuation pointer and σ, both O(1) to keep.
- **What it retires.** `__exit`, `__pop_assumption` and the baked `cut(B)` become fields of a scope: the assumptions it pushed, its call height. Depth becomes how deeply scopes are nested, which is what §8.3 already defines it as.
- **Delay becomes scoped.** A goal that waits moves to the back of ITS scope. When a scope holds only waiting goals, its exit hands them to the caller's scope: they bubble up. Today a waiting goal goes behind the WHOLE resolvent, outside the scope it came from. The answers should be the same; the order in which goals are asked changes, and so do proof records. That must be measured on the gate before it is decided.
- **Size.** `kb/resolve.rs` is 23.7 k lines and almost every arm reads `self.stack.last()` directly. The migration first puts the arms behind accessors (the current goal, σ, fail, offer alternatives), then swaps the representation behind them.

**Stage D — §5's backjumping**, on Stage C's scopes.

## 7. Related, not in scope: a typed column checks its whole value at every call

Raised by the user during this draft ("maybe the related problem is that sort-domain generates instead of checks"). MEASURED 2026-11-24 (debug binary): membership of the LAST element of a ground list,

```anthill
rule mem(?x: Int64, ?l: List[T = Int64]) :-
  (?l <=> cons(head: ?x, tail: ?)) | (?l <=> cons(head: ?, tail: ?t), mem(?x, ?t))
```

```
n                        100      200      400
?l: List[T = Int64]    0.75 s   2.46 s   20.0 s
                       241 MB   1.1 GB   7.6 GB
?l untyped             0.51 s   0.55 s   0.73 s
                        85 MB    99 MB   145 MB
```

**What happens** (read from the code, not traced; the step counts are not yet taken). The typed head puts `apply_domain` in the clause body. With `?l` ground, `lower_apply_domain` turns it into the provider's `fill(?l)` goal. That goal is proved by the domain's clauses, one per constructor, walking the whole value. It runs at EVERY call of `mem`, including the rule's own recursive call on `?t`, which the typer can know is a `List[T = Int64]` (the `tail: Self` of one). So one membership walks `n + (n−1) + … + 1` cells. Today's machine makes that worse than quadratic (§ The problem): the time above grows about eightfold per doubling.

**So it is check mode, not generation, on a ground value. The fault is that it checks again what is already known.** Two candidate fixes, not decided:
- **Discharge the check statically** where the argument's type is known to conform: the recursive call here, and any caller whose argument is typed. The rule then splits into a checked entry and an unchecked body.
- **Remember conforming ground values per search**, keyed by hash-consed term and type, so a tail already walked as part of its list is not walked again.

A third, recorded on the ticket: with the value ground at the call, run the fill at the guard's place rather than after the body, so no fill is pending across the recursive call. That removes the growing resolvent, but still walks each tail once per level.

It compounds the `2^k` (each skipped or replayed branch re-runs its checks), but it is independent of this proposal. Filed with the user as WI-20261124-YFD7F (2026-11-24), the approach to be chosen there.

## 8. What the spec would say

§8.3, once §3 is implemented: a ground goal's alternatives are not retried on a dead end after its definite exit; answers and proof counts are unchanged. Once §4 is implemented: with the commit option, a ground goal's proofs are counted once. Stage C's scoped delay, if it changes any observable order, is stated there too. Each of these is a spec change to agree with the user first.

## 9. Open questions

1. **Proof mode and the guard.** A refutation record (075) covers "every clause whose head matches, on every branch". A skipped segment's branches are never visited. Either the guard is off in proof mode, or the record gains a step "fails as the branch before it did".
2. **Effects.** The soundness argument assumes a proof has no external effect. An operation applied in a rule body (068) that performs one would run fewer times under the guard or the commit. Are rule-body applications effect-free by the typer's rules? To be checked.
3. **A switch for the guard.** Default on, but a back-out control needs it off: a `ResolveConfig` field, or an environment switch as the other controls are.
4. **Scoped delay (Stage C).** Is the order in which goals are asked part of what the spec promises? §8.3 fixes clause order, not the order in which waiting goals are retried.
5. **Wake-on-bind across scopes (Stage C).** Today a woken goal moves to the front of the whole resolvent. With scopes, a goal waiting in an outer scope, woken by a binding made in an inner one, must run there. Whose scope it belongs to then decides what "definite exit" means for non-ground goals. For a ground goal it cannot arise: nothing outside its proof can name its variables.

## History

1. 2026-11-24 — drafted. The user, on P6G1P and VT9S7: "the AND and OR stack should be bound to the goal, and if we prove the goal, we return to the top stack". Asked how WAM is built (§1). Asked "if we have a global OR stack and add something there in some local rule, will we return to it when the rule finished?" (§1, answered: on a failure, not at the exit). Suggested the sort domain generates instead of checking (§7, measured: it checks, at every call). Suggested persistent data structures: σ already is (WI-569), the resolvent is not (§6 Stage C).
