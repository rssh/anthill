# Proposal 076: A goal's scope in the search — its call, its exit, and the alternatives it leaves

## Status: Draft, written with the user 2026-11-24, revised the same day after a review (History 2). Not approved. Nothing here is implemented, and the spec is not changed by it (§9 says what it would change).

## Tracked by: WI-20261122-P6G1P (commit to the first definite proof of a ground goal), WI-20261122-VT9S7 (dependency-directed backtracking). No ticket of its own.

## Relates to: `docs/kernel-language.md` §8.3 (a query yields answers, a relation yields proofs; depth and fuel; negation); proposal 033 (`push_choice`, `Candidate::Continuation`), 033.1 (cut and the barrier), 068 §2.2 (wait states), 052 (relations count proofs), 075 (`SLDProof`, proof mode); WI-569 (σ is persistent); WI-20261124-YFD7F (a typed column checks its whole value at every call).

## References: Warren's abstract machine (Aït-Kaci's tutorial reconstruction); X. Qi, *An Implementation of the Language λProlog Organized around Higher-Order Pattern Unification* (Teyjus 2; `docs/local/references/lambda-prolog/implementation-ho-0911.5203v1-QI.pdf`), §4.2 and ch. 6; ELPI's `src/runtime/runtime.ml` (`type frame`, `alternative`, `pop_andl`, `cut`).

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

- **A frame holds the whole resolvent.** `ResolverFrame` is (`goals`: every goal still to prove, σ, state). Opening a clause builds `body ++ a copy of the tail` (`frame.goals[1..].to_vec()`, `kb/resolve.rs` in `step_choice_point`; `continue_with_goals` the same; 11 such sites). Scala: `ArrayBuffer.from(freshBody…) ++= frame.goals.drop(1)` (`resolve/SearchStream.scala`).
- **Once a body is spliced in, the boundary is gone.** Nothing marks where `g`'s proof ends and its caller's tail begins, so `g` being proved is not an event. The choice points opened while proving `g` sit lower on the stack, and a later failure goes back into them in order.
- **A frame is both a branch's state and a choice point.** Every candidate is pushed ABOVE the frame that offered it. The frame is popped only when its candidates are exhausted, which backtracking finds. There is no last-alternative release (WAM's `trust_me`): a call with ONE candidate leaves its frame on the stack until the search backtracks through it. So a deterministic recursion of depth `n` holds `n` frames.
- **A goal that waits is rotated behind the whole resolvent.** It is passed over on each of its turns until a blocker is bound (068 §2.2), and the search residualizes when a whole turn of the resolvent has only waited (`consecutive_delays >= goals.len()`). 068 §2.2 says "rotates behind its siblings"; with a flat resolvent the callers' goals are behind the siblings, so the goal leaves the body it was written in. **That was not what was meant** (the user, 2026-11-24: "when I think about delay, I think about delay in the current goal, not global"). §6 Stage B.
- **Where a boundary was needed, a marker was added.**
  - `!` is baked into the body as `cut(B)`, and the choice point that opened the body is tagged `B` (033.1).
  - A `forall_impl` discharge splices `__pop_assumption(N)` behind its consequent.
  - Each `FrameGoal` carries its own depth, wait state and proof tag, because the frame cannot say what scope a goal is in.
- **Only negation and a closed `eq` sub-proof give a goal its own stacks.** They run a nested `SearchStream`. That is why `!(!(g))` commits in the table above.

### MEASURED, 2026-11-24

`anthill query --max-depth 100000` (1000000 for n > 8000), peak RSS. Debug binary built 2026-11-24 09:31, from a tree at or near HEAD; not rebuilt for this. Loading the stdlib is about 103 MB and about 8.2 s of every run, so wall times are not listed. Not a gate measurement. The probes are not committed; they are these rules, each in a namespace of its own:

```anthill
fact cnt(0)
rule cnt(?n) :- ?n > 0, cnt(?n - 1)                             -- deterministic
rule chain(?n) :- (?n = 0) | (?n > 0, ok(1), chain(?n - 1))     -- control: the resolvent stays short
rule chain(?n) :- (?n = 0) | (?n > 0, chain(?n - 1), ok(1))     -- the resolvent grows by one goal per level
```

and the first two again with a typed head, `?n: Int64`.

```
                                 n = 1000   n = 2000   n = 8000 / 16000 / 32000
cnt, untyped                         —       107 MB    137 / 178 / 279 MB
cnt(?n: Int64)                    208 MB     537 MB
control, untyped                  123 MB     145 MB
control, ?n: Int64                498 MB     1.63 GB
growing resolvent, untyped        439 MB     1.41 GB
```

- **An untyped recursion with a short resolvent is LINEAR**, about 4.4 KB a level, in memory and in time (wall 9.0 / 10.0 / 11.9 s at n = 8000 / 16000 / 32000). That is the retained frame per call (no last-alternative release).
- **A growing resolvent is quadratic.** That is the tail copy: each level's frames each hold a copy of a tail one goal longer.
- **A typed head makes the resolvent grow.** `?n: Int64` appends a fill after the body (`install_typed_head_domain_goals`, YFD7F), still pending when the recursion opens the next level. So the typed deterministic recursion and the typed control are the growing-resolvent case.

The first draft of this proposal recorded the control at 475 MB / 1.6 GB (n = 1000 / 2000) and the deterministic recursion at 181 / 487 MB (debug), read them as "quadratic even when the resolvent is short", and left the cause "not identified". Those numbers match the TYPED rows above and not the untyped ones. The draft's probes were not kept, so that they had typed heads is inferred from the match, not read from them. **On that reading there is one quadratic cost, the copied flat resolvent, and one linear one, the retained frame.** No heap profile was needed (`malloc_history`, `heap` and `sample` are on the machine if one is wanted).

Not explained, and not this proposal's: with the base clause written `rule cnt(0)` in place of `fact cnt(0)`, the query `cnt(0)` answers "no solutions".

## 1. How other machines do it

### 1.1 WAM

Warren's abstract machine, as in Aït-Kaci's tutorial reconstruction. Teyjus (Qi, ch. 6) is this machine with additions for λProlog.

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

WAM as a whole does not fit here: it needs clauses compiled to instructions and a trail over destructive bindings. Anthill's goals are occurrences interpreted as written, σ is persistent, a lazy consumer holds an answer's σ while the search goes on, and there are two implementations to keep alike. What is taken from it is the height mark and the release of a choice point at its last alternative.

### 1.2 ELPI — the closest relative

ELPI is an INTERPRETER for λProlog, with hypothetical clauses and suspended goals: the same needs as here. Its runtime (`runtime.ml`):

```ocaml
type frame =
 | FNil
 | FCons of (*lvl:*)alternative * goal list * frame
```

- **The continuation is a linked list of frames.** A frame is (the choice point a cut in it goes back to, its remaining goals, its caller's frame). Opening a clause runs its body with the caller's remaining goals as a new `FCons`; nothing is copied. `pop_andl` is the exit: a body with no goals left continues with the caller's frame.
- **Cut is a pointer comparison.** `cut` prunes alternatives until it meets the frame's `lvl`. No tag is searched for.
- **Each goal carries its own program and depth** (`{depth; program; goal}`), as the thesis's abstract interpreter does (§4.2: a goal is a triple ⟨G, P, N⟩, because an assumed clause parameterizes "particular goals and not the entire set"). Here that is `assumed_facts` with `__pop_assumption`, and the per-goal depth: both belong to the scope.
- **A goal that waits is not in the continuation.** It sits in a constraint store, and is resumed when a variable it waits on is assigned; `pop_andl` at `FNil` resumes what is left. Teyjus does the same with the unification problems it cannot solve yet: a list on the heap (register `LL`), restored on backtracking.

### 1.3 Others, for what they say here

- **Binarization (BinProlog) and success-continuation interpreters; miniKanren, LogicT.** The continuation is a shared value (a term, a closure). miniKanren runs on a persistent substitution, as this resolver does: persistent σ is workable when the continuation is shared and not copied.
- **Teyjus compiles `;` into an auxiliary predicate** (Qi §6.5). A disjunction is then an ordinary clause choice, with an ordinary call and exit. `push_choice` gets a scope in the same way (§2).
- **Independence.** &-Prolog runs goals that share no unbound variable at run time as independent, and fails the whole conjunction when one of them fails without retrying its siblings. Mercury prunes the alternatives of a goal with no outputs. §3's guard is the first, restricted to the sequential search; §4's commit is the second.
- **Tabling (SLG, XSB).** A call met again answers from a table. It is the principled form of YFD7F's "remember conforming ground values". A table here would have to store how many proofs each answer has, because a relation counts proofs (052). A proposal of its own, not this one.
- **Conflict-directed backjumping, nogood learning (CDCL).** §5.

## 2. The idea: a goal's scope

Each goal that is asked gets a scope, with two ends:

- **Its call.** Recorded when the goal is selected: the choice-point height, whether the goal is independent of its continuation (§3), what is waiting (§6 Stage B), and the goal's depth and proof tag.
- **Its exit.** Reached when the last goal of its proof has been proved. At the exit, the choice points above the call's height are the goal's **segment**: its remaining alternatives.

At the exit there are three things to do with the segment:

1. **Keep it** (today, and the default for any goal not covered below). A later failure resumes it in order.
2. **Drop it**: a commit, `once`. This is P6G1P's flag (§4). It changes proof counts.
3. **Guard it**: keep it for redo after an answer, skip it on a dead end (§3). It changes neither answers nor proof counts.

"Return to the top stack when the goal is proved" is the exit: control goes back to the caller. The segment is the part that must not simply be dropped there.

## 3. The guard of an independent goal — the default

**Independent.** A goal `g` is independent of its continuation at its call when no variable free in `g` under σ occurs in anything that is asked after `g` exits. Two cases are cheap to know:

- **`g` is ground under σ.** The first draft's case.
- **Each variable free in `g` is LOCAL to it:** a variable of the clause that occurs in this one body goal and nowhere else in the body or the head (or, at the top, in this one goal of the query). "Occurs in one goal only" is known when the clause is loaded. At the call the variable is fresh and aliased to nothing. The goal's other arguments are checked ground under σ.

The second case is VT9S7's own example: `member(?c, [1, …, n])` followed by a failing goal that does not read `?c`.

**Rule.** When an independent goal `g` reaches a DEFINITE exit (no goal of its proof is waiting) with a non-empty segment, a guard is placed above the segment. It records how many solutions the search had reached at that moment. When backtracking reaches the guard:

- **No solution was reached since `g`'s exit:** the search after `g` was a dead end. Every alternative of `g` would rebuild the same state for what follows and reach the same dead end. Skip the whole segment: cut back to `g`'s call height.
- **A solution was reached:** remove the guard and backtrack in order, as today. `g`'s next proof gives that solution again, and proof counts stay what they are.

**Why the skip is sound.** What `g`'s proof binds is either a fresh variable of a clause it opened or a variable local to `g`; nothing asked after `g` reads either. Its definite exit leaves no goal of its own waiting. So every proof of `g` leaves the same state for what comes after: the same σ on every variable the tail can see, the same goals, the same assumptions, the same depths (a goal's depth is its own, §8.3). The search after `g`'s exit is therefore the same search after each of `g`'s proofs. Between pushing the guard and reaching it, the search explored exactly that subtree, so "no solution reached since" means that subtree has none. A local variable may be an answer variable of the query: with no solution, there is no answer to differ in it.

**What it covers.**
- The k = 16 chain: each ground `|` exits definitely with a one-candidate segment. When `(1 = 2)` fails, each guard skips its segment. Linear.
- A ground `some_in` with several witnesses followed by a failing goal: linear.
- `member(?c, l)` with `?c` local, followed by a goal that fails: linear in the length of `l` where it was the product.
- P6G1P's WHO NEEDS IT: anthill-traces decides clauses on ground values, and the cost is in the clause that FAILS. A clause that holds is decided at its first definite solution. So the guard answers that need with proof counts intact. P6G1P's commit is then needed only if a caller wants a ground goal's proofs counted once (§4).
- It also applies inside a negation's sub-search, which is the same machine. That is where a failing contract clause is decided.

**What it does not cover.** The guard acts on a dead end only. Once the tail has ONE solution, every further proof of `g` runs the whole tail again: `k` independent goals of two proofs each before a tail that holds give `2^k` proofs, each of them found. That is what a relation's proof count is (052); saying it otherwise is §4, or a count that multiplies instead of enumerating, which is not proposed.

**What it does not change.**
- **Truncation.** A tail cut by the depth limit inside the skipped segment would be cut again at the same depth, and the `truncated` flag is already set. An undecided verdict stays undecided.
- **Faults of the tail.** A fault recorded in the tail would be recorded again. Faults are deduplicated.
- **Residuals.** A residual solution is a solution: the guard then backtracks in order.
- **Fuel.** It only saves steps.

**What it does change: a fault of a skipped alternative.** An alternative of `g` that is never run records no fault and no truncation of its own. The conjunction is refuted either way (its tail has no solution), so the verdict is right; but a search that today answers "refuted, and this clause faulted" (which reads as incomplete) answers "refuted" under the guard. To agree with the user (§10).

**What "solution reached" counts.** Every solution the drain reached, BEFORE answer dedup. With dedup on, a solution reached again is a duplicate and could be skipped too. That extension is not proposed.

**"Ground" is `value_is_ground` under σ.** A type variable counts as a variable, which is the conservative direction. A `var_ref` under Γ is a symbol, not a σ variable, so the identity argument holds for it. Negation's open-world reading of `var_ref` is a different question.

## 4. Commit — P6G1P's flag, opt-in

The same exit, for a goal GROUND at its call (not merely independent: a local variable may be an answer variable, and a commit would lose its other answers) with a definite exit. Instead of a guard, the segment is cut immediately: `once(g)`. P6G1P's tests stand as written:
- the k = 16 chain is linear with the flag on and `2^k` with it off;
- `(?x = 1) | (?x = 2), ?x > 1` still answers `?x = 2`;
- a ground goal whose first proof is residual and whose second is definite answers definite;
- relation multiplicities are unchanged with the flag off.

It changes proof counts: a ground `(A) | (B)` with both true is one proof instead of two. So it is off by default, and on `KB.execute` it rides on the options of WI-20261122-96QKW (`ExecuteOptions`).

**If it is needed before §6's machine.** A ground goal can be handed to a nested search, the mechanism `!(!(g))` already uses (193 steps at k = 16 in the table): the sub-search has stacks of its own, and a ground goal has no binding to bring back. That needs no marker in the resolvent. NOT MEASURED: what a sub-search per ground goal costs (each has caches of its own), and whether its verdict reads P6G1P's "first proof residual, second definite" row as that row asks. To be measured before it is chosen; it is an interim, and §6 Stage C replaces it.

## 5. Backjumping for dependent goals — not planned

VT9S7's general case is a dead end that depends on SOME earlier bindings and not others, where the goals in between are not independent of their continuations. It needs to know who bound what:

- each binding remembers the choice-point height that made it;
- a goal's reads are the variables it was written with, chased through σ, and the heights of the bindings met on the way;
- a dead end jumps to the highest choice point in its conflict set, the union of the reads of the goals that failed in it, and merges the set into the target's.

It also has to settle a negation's sub-search, a goal woken by a binding, truncation, and the step accounting of a jump (VT9S7 lists them).

**Why it is not planned.** The bookkeeping is paid on every binding and every read of every search, whether a jump ever happens. §3's independence, known mostly at load, covers VT9S7's motivating example and P6G1P's without it. Run-time intelligent backtracking was worked out for Prolog in the 1980s and, as far as is known here, is in no mainstream system; they rely on determinism (indexing, cut, modes) instead. VT9S7 stays open for a measured case that §3 does not cover.

## 6. The machine, staged

Each stage is measured on its own and lands on both implementations. The first draft's Stage A, an `__exit(h, s)` marker spliced behind each ground goal in today's flat resolvent, is WITHDRAWN: it would be a fourth marker in a machine whose trouble is markers. It had to be invisible everywhere a goal count is read (the delay gate, `yield_sole_goal`, proof mode, residuals), and to know a definite exit it had to stamp each rotated goal with the scope it came from.

**Stage A — the continuation is linked, not copied.** No change of behaviour; it removes the quadratic cost measured above.
- **A branch's state** is (its continuation, σ, what is waiting), each O(1) to keep.
- **The continuation** is a persistent linked list of scopes, as ELPI's `FCons`. A scope is (its remaining goals, its caller's scope, its call height, the assumptions it pushed, its depth, its proof tag). Opening a clause pushes a scope in O(1). A branch shares its caller's scopes and copies nothing.
- **The exit is structural:** a scope with no goals left continues with its caller's.
- **What it retires.** `__pop_assumption` and the baked `cut(B)` become fields of a scope: the assumptions it pushed, its call height. Depth becomes how deeply scopes are nested, which is what §8.3 already defines it as. A `push_choice` branch is a scope like a clause body (§1.3).
- **Size.** `kb/resolve.rs` is 23.7 k lines; 73 sites read `self.stack.last()` or `last_mut()` directly, 8 push a frame, 11 copy the tail. The migration first puts the arms behind accessors (the current goal, σ, fail, offer alternatives, continue with goals), then swaps the representation behind them.
- **Measured by:** the growing-resolvent probe and the typed probes of § MEASURED becoming linear, with the gate unchanged.

**Stage B — a goal waits in the goal it was written in.** This is the delay that was meant (the user, 2026-11-24), not a side effect of the representation: a correction of how 068 §2.2 was implemented.
- **The rule.** A goal that waits goes behind its SIBLINGS: the goals of the scope it was asked in, and no further.
  - **Woken** by a binding of one of its blockers, it is asked next, before any ready goal, wherever the search is then (068 §2.2, decided 2026-10-21, kept: a check must cut a generator while it generates). It is asked as a goal of ITS scope: at that scope's depth, under that scope's assumptions.
  - **When a scope has only waiting goals left**, it cannot finish by itself. It exits and hands them to its caller's scope, where they wait behind the caller's siblings. Its exit is then not definite.
  - **At the query's scope**, what still waits is the residual.
- **What it puts right.** Today a waiting goal is carried out of the body it was written in: past `__pop_assumption`, so outside the assumptions it was written under, and into a resolvent whose length is the residualization gate's measure. A clause that waited on a caller variable (`Candidate::Waiting`) is asked again "once the caller has had its turn": that is this rule, said of one case.
- **The representation.** The continuation is shared, so an inner scope cannot write into an outer one. What waits is therefore a store of the BRANCH, beside σ: a persistent map from a blocker to the goals waiting on it, each with the scope that owns it, as σ's `constraints` already are (WI-502). `Wait::Suspended { blockers }` already carries what it needs; a `Parked` goal is there with no blocker. Handing goals to the caller changes their owner.
- **What it retires.** The rotation, the `consecutive_delays >= goals.len()` gate, and passing a suspended goal over on each of its turns.
- **A definite exit** is a scope that hands nothing to its caller. For an independent goal (§3) that is an O(1) test, the store being the one the scope saw at its call: nothing outside its proof waits on a variable it binds.
- **To check on the gate:**
  - a `Parked` goal "keeps its place behind its siblings, because a sibling that FAILS still refutes the clause": in its own scope that holds as written;
  - where the answers or the proof records of today's suites depend on a waiting goal having left its body. Each such place is either a test of the old behaviour or a defect the old behaviour hid; they are listed for the user, not adjusted silently.

**Stage C — choice points by height.** On Stage A's scopes.
- **One stack of choice points**, each (a continuation, σ, the store, the alternatives left). The live branch is not on it.
- **A choice point is released at its last alternative:** a call with one candidate pushes none. "Last" has to be known: extent rows are matched lazily, and waiting clauses come after the candidates. This removes the linear retention measured above.
- **The cut barrier is the scope's call height**, as in WAM and ELPI, not a tag found by scanning for a frame (`apply_cut`).
- **The guard (§3)** is a choice point of its own kind, (floor: the call height, the solutions reached), pushed at the exit of an independent scope whose height is above its call's and whose store is its call's. Backtracking into it either cuts to the floor or pops it.
- **The commit (§4)** cuts to the call height at the same exit.
- **Cost.** One independence test per selected goal: a flag of the clause's goal, and `value_is_ground` on its other arguments.

## 7. Related, not in scope: a typed column checks its whole value at every call

Raised by the user during the first draft ("maybe the related problem is that sort-domain generates instead of checks"). MEASURED 2026-11-24 (debug binary): membership of the LAST element of a ground list,

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

**What happens** (read from the code, not traced; the step counts are not yet taken). The typed head puts `apply_domain` in the clause body. With `?l` ground, `lower_apply_domain` turns it into the provider's `fill(?l)` goal. That goal is proved by the domain's clauses, one per constructor, walking the whole value. It runs at EVERY call of `mem`, including the rule's own recursive call on `?t`, which the typer can know is a `List[T = Int64]` (the `tail: Self` of one). So one membership walks `n + (n−1) + … + 1` cells. And the fill, appended after the body, is still pending when the recursion opens the next level, so the resolvent grows and today's machine copies it (§ MEASURED): the time above grows about eightfold per doubling.

**So it is check mode, not generation, on a ground value. The fault is that it checks again what is already known.** Two candidate fixes, not decided:
- **Discharge the check statically** where the argument's type is known to conform: the recursive call here, and any caller whose argument is typed. The rule then splits into a checked entry and an unchecked body.
- **Remember conforming ground values per search**, keyed by hash-consed term and type, so a tail already walked as part of its list is not walked again. (Tabling, §1.3, restricted to one relation.)

A third, recorded on the ticket: with the value ground at the call, run the fill at the guard's place rather than after the body, so no fill is pending across the recursive call. That removes the growing resolvent, and with it the quadratic memory of every typed recursion in § MEASURED, without waiting for Stage A; it still walks each tail once per level.

It compounds the `2^k` (each skipped or replayed branch re-runs its checks), but it is independent of this proposal. Filed with the user as WI-20261124-YFD7F (2026-11-24).

**The approach proposed there** (agreed with the user 2026-11-24, recorded on the ticket): the first fix, done through the dictionary channel. The user: "during call we pass dictionaries, so we can look on untyped as on translated typed". Every call is elaborated, so there is no untyped caller, and a typed column's hidden parameter says one of two things: *check with `d`*, or *trusted, `d` for generation only*, the second where the typer has the column's type for the argument at that occurrence. A dictionary says the type has a domain, not that this value is in it, which is why the parameter has two states. It rests on type preservation in rule bodies, to be checked first. The second fix (the memo) is the fallback where no typer elaborates: scaland, and a value from outside.

## 8. What is deliberately kept

- **σ stays persistent.** A trail over destructive bindings is faster per binding, but a lazy consumer holds an answer's σ while the search continues, a sub-search starts from its parent's σ, and Scala has the same structure. To look at when σ is next touched: `Substitution::bind_compressed` scans every binding of σ for each new one (22 call sites in `resolve.rs`). It did not show on the probes above, which are linear in time to n = 32000.
- **The search order.** Depth-first, clauses in order. Nothing here reorders goals except Stage B's wake, which is today's.
- **Goals are interpreted as written.** No compilation to instructions.

## 9. What the spec would say

§8.3, once §3 is implemented: the alternatives of a goal independent of what follows it are not retried on a dead end after its definite exit; answers and proof counts are unchanged; a fault that only such an alternative would raise is not reported. Once §4 is implemented: with the commit option, a ground goal's proofs are counted once. Stage B: a goal that waits, waits behind the goals of the body it was written in, and is handed to the caller when that body has nothing else left; 068 §2.2 is reworded with it. Each of these is a spec change to agree with the user first.

## 10. Open questions

1. **Proof mode and the guard.** A refutation record (075) covers "every clause whose head matches, on every branch". A skipped segment's branches are never visited. Either the guard is off in proof mode, or the record gains a step "fails as the branch before it did".
2. **Effects.** The soundness argument assumes a proof has no external effect. An operation applied in a rule body (068) that performs one would run fewer times under the guard or the commit. Are rule-body applications effect-free by the typer's rules? To be checked.
3. **A fault of a skipped alternative (§3).** Is "refuted" without that fault acceptable, or must a guard that skips say that it did (a flag on the stream, read where `truncated` is)?
4. **A switch for the guard.** Default on, but a back-out control needs it off: a `ResolveConfig` field, or an environment switch as the other controls are.
5. **Delay in the current goal (Stage B): what 068 says.** 068 §2.2 and `docs/design/068-implementation.md` describe rotation behind the resolvent. Stage B needs 068 §2.2 reworded ("behind its siblings" meaning the goals of its body; the hand-over to the caller; the residual at the query's scope), and §8.3 to say it. To write with the user.
6. **A scope that hands waiting goals to its caller: is it proved?** Stage B says it exits, not definitely, and the caller goes on. The other reading: a body with goals still waiting has not been proved until they are, and the caller's later goals should not run first. The first is today's behaviour seen from the caller (its goals run while the callee's wait). To confirm.
7. **A goal woken from an outer scope.** It is asked next, in the middle of an inner scope's proof, and may fail it: today's behaviour, kept (068 §2.2). For an independent goal it cannot arise: nothing outside its proof can name its variables.
8. **Local variables under a bounded quantifier or a `forall_impl`.** "Occurs in one goal only" is read off a clause body. What it is for the instance of a `some_in` or the consequent of a discharge is to be written down with Stage C.

## History

1. 2026-11-24 — drafted. The user, on P6G1P and VT9S7: "the AND and OR stack should be bound to the goal, and if we prove the goal, we return to the top stack". Asked how WAM is built (§1.1). Asked "if we have a global OR stack and add something there in some local rule, will we return to it when the rule finished?" (§1.1, answered: on a failure, not at the exit). Suggested the sort domain generates instead of checking (§7, measured: it checks, at every call). Suggested persistent data structures: σ already is (WI-569), the resolvent is not (§6 Stage A).
2. 2026-11-24 — revised after a review the user asked for ("maybe exists better search architecture, compare with other known solutions for high-performance search", naming Qi's thesis), folded in at the user's word.
   - **MEASURED redone.** The untyped short-resolvent probes are linear; the first draft's quadratic numbers match typed heads, whose pending fill grows the resolvent. "Not identified" is withdrawn: one quadratic cost (the tail copy), one linear (the retained frame).
   - **§1 widened** from WAM to ELPI (the closest relative: a linked continuation, cut as a pointer, a constraint store for waiting goals), Teyjus and the thesis's abstract interpreter (state per goal), independence (&-Prolog, Mercury), tabling.
   - **§3's guard widened** from a ground goal to a goal independent of its continuation (ground, or its variables local to it), which covers VT9S7's example. Added: it acts on a dead end only; a fault of a skipped alternative is not reported.
   - **§4** stays ground-only; an interim through a nested search is noted, not measured.
   - **§5** backjumping with binding provenance: from "Stage D" to not planned.
   - **§6 restaged.** The `__exit` marker stage is withdrawn. A: the linked continuation, no change of behaviour. B: a suspension store in place of rotation (new). C: choice points by height, with last-alternative release, the guard and the commit. Formerly: A marker, B release, C scopes with scoped delay, D backjumping.
   - **§8 added** (what is kept: persistent σ, the order, interpretation). Open questions renumbered; 3 and 8 are new.
3. 2026-11-24 — the user, on revision 2's Stage B: "in 068 was an error — when I think about delay, I think about delay in the current goal, not global". Stage B rewritten from "a suspension store, order to be checked against today's" to the delay that was meant: a goal waits behind the siblings of its own scope, is handed to the caller when the scope has nothing else left, and is the residual at the query's scope; woken, it is asked next (068 §2.2, kept). The branch-level store is its representation, with an owner per goal. Open questions 5 to 7 restated: 068 §2.2 to be reworded; whether a scope that hands goals on counts as proved.
