# Proposal 076: A goal's scope in the search — its call, its exit, and the alternatives it leaves

## Status: Draft, written with the user 2026-11-24, revised the same day after reviews (History 2 to 6), and on 2026-11-27 with Stage D, a fair region, moved here from 077's open question 2 (History 7). STAGE A APPROVED TO BUILD (user, 2026-11-28); the other stages are not approved yet. Nothing here is implemented, and the spec is not changed by it (§9 says what it would change). ORDER with 060.1 §9 and 077 (2026-11-27, stated in full in 077's status): Stage A first of all three; Stages B and C after 077 S3b; Stage D after them (open question 10, decided), its declaration on `Fillable.fill` needing 077 S2.

## Tracked by: WI-20261122-P6G1P (commit to the first definite proof of a ground goal), WI-20261122-VT9S7 (dependency-directed backtracking; the guard's ticket, §5), and WI-20261127-AGR9S (Stage A), tagged `proposal-076`. Stages B, C and D are filed as their predecessors are delivered; P6G1P and VT9S7 depend on AGR9S until Stage C has a ticket.

## Relates to: `docs/kernel-language.md` §8.3 (a query yields answers, a relation yields proofs; depth and fuel; negation); proposal 033 (`push_choice`, `Candidate::Continuation`), 033.1 (cut and the barrier), 068 §2.2 (wait states), 052 (relations count proofs), 075 (`SLDProof`, proof mode); WI-569 (σ is persistent); WI-20261124-YFD7F (a typed column checks its whole value at every call); WI-20260911-09E6M (generation by size, the rounds Stage D replaces); proposal 077, open question 2 (moved here as Stage D).

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

- **An untyped recursion with a short resolvent is LINEAR**, near enough, in memory and in time (wall 9.0 / 10.0 / 11.9 s at n = 8000 / 16000 / 32000). With the stdlib's 103 MB taken off, a level costs about 4.3 KB at n = 8000, 4.7 KB at 16000 and 5.5 KB at 32000: a log factor (σ's path copies, one version per retained frame) is not excluded. That is the retained frame per call (no last-alternative release).
- **A growing resolvent is quadratic.** That is the tail copy: each level's frames each hold a copy of a tail one goal longer.
- **A typed head makes the resolvent grow.** `?n: Int64` appends a fill after the body (`install_typed_head_domain_goals`, YFD7F), still pending when the recursion opens the next level. So the typed deterministic recursion and the typed control are the growing-resolvent case.

The first draft of this proposal recorded the control at 475 MB / 1.6 GB (n = 1000 / 2000) and the deterministic recursion at 181 / 487 MB (debug), read them as "quadratic even when the resolvent is short", and left the cause "not identified". Those numbers match the TYPED rows above and not the untyped ones. The draft's probes were kept in the drafting session's scratch directory and READ there (2026-11-24): every one of them is typed, `chain(?n: Int64)` and `cnt(?n: Int64)`, with `ok(?x: Int64)` beside the chains. So the match is confirmed, not only inferred. **There is one quadratic cost, the copied flat resolvent, and one linear one, the retained frame.** No heap profile was needed (`malloc_history`, `heap` and `sample` are on the machine if one is wanted).

The draft's deterministic probe also wrote its base clause `rule cnt(0)`. A rule with no body DECLARES its predicate and asserts nothing (proposal 061: "No body ⇒ DECLARES. A body ⇒ asserts"; `fact` is a body-less assertion). So `cnt(0)` has no clause, the probe answered "no solutions" at every `n` (read again 2026-11-24), and its row measured a descent that then failed, not a recursion that holds. The probes above write `fact cnt(0)`, which answers `true`.

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
fact q(1)
fact q(2)
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
3. **Guard it**: keep it for redo after an answer, skip it on a dead end (§3). It changes no proof count, and no answer except that a search undecided only for a skipped alternative's sake becomes refuted (§3).

"Return to the top stack when the goal is proved" is the exit: control goes back to the caller. The segment is the part that must not simply be dropped there.

## 3. The guard of an independent goal — the default

**Independent.** A goal `g` is independent of its continuation at its call when no variable free in `g` under σ occurs in anything that is asked after `g` exits. Two cases are cheap to know:

- **`g` is ground under σ.** The first draft's case.
- **Each variable free in `g` is LOCAL to it:** a variable of the clause that occurs in this one body goal and nowhere else in the body or the head (or, at the top, in this one goal of the query). "Occurs in one goal only" is known when the clause is loaded. At the call the variable is fresh and aliased to nothing. The goal's other arguments are checked ground under σ.

The second case is VT9S7's own example: `member(?c, [1, …, n])` followed by a failing goal that does not read `?c`.

**Locality is read off the goal as it is ASKED, not only as it was written.** Two things put goals beside a written one, and either can read a variable that looks local in the source:

- **The typer, at load.** A typed column gets a guard and a fill (`install_typed_head_domain_goals`, YFD7F), and so does a typed variable (C6VN0). So "occurs in one goal only" is read off the body as the resolver opens it, after every pass that adds goals to it, never off the parsed clause.
- **Argument evaluation, at run time.** A call in an argument that cannot be evaluated yet becomes a pending equation SPLICED AFTER the goal, among the caller's goals (`evaluate_goal_arguments`). `q(?y, ?y + 1)` is asked as `q(?y, ?hole), ?hole <=> ?y + 1`, and the equation reads `?y` after `q` exits. MEASURED 2026-11-24 (debug build, from reading the code and one query): over `fact q(1, 3)` and `fact q(2, 3)`, the query `q(?y, ?y + 1)` answers `?y = 2`. `q`'s first proof fails only in the equation, and its second is needed. A guard that read `?y` as local to `q` would skip `q(2, 3)` and answer "no solutions". There is no guard yet, so that wrong answer is argued, not run.

**A goal's pending equations belong to its scope** (open question 9, decided). The scope holds the evaluated goal and its equations, at the goal's depth: a split, not a call, and depth is a field (§6 Stage A). The goal's exit then comes after its equations, and `?y` is local to that scope. The alternative keeps the splice where it is today and counts a variable a pending equation mentions as not local, which is sound and loses independence for every such goal. Open question 9, decided for the scope.

**And no assumption in scope has a free variable.** An assumption is a clause the goal's proof may use, and its variables are the CALLER's. MEASURED 2026-11-24 (review, reproduced):

```anthill
fact hyp(99)
rule pick(0) :- hyp(1)
rule pick(0) :- hyp(2)
rule t1(?x) :- (forall(?n), hyp(?x) -: pick(0))             -- answers ?x = 1 and ?x = 2
rule t2(?x) :- (forall(?n), hyp(?x) -: pick(0), ?x <=> 2)   -- answers ?x = 2
```

`pick(0)` is ground, and each of its proofs binds `?x` through the assumption `hyp(?x)`. In `t2` the continuation of its first proof fails and its second is the only answer: a guard that read "ground" as "independent" would skip it, and a commit would drop it in `t1`. So a goal is independent only if, besides the above, **every assumption in scope at its call is ground under σ**. That is conservative (an assumption whose variables the goal's proof cannot reach would do no harm) and O(1) to know where the scope keeps a count of its non-ground assumptions; a narrower test is not proposed. The same condition binds §4's commit and P6G1P as the ticket words it.

**Rule.** When an independent goal `g` reaches a DEFINITE exit (no goal of its proof is waiting) with a non-empty segment, a guard is placed above the segment. It records how many solutions the search had reached at that moment. When backtracking reaches the guard:

- **No solution was reached since `g`'s exit:** the search after `g` was a dead end. Every alternative of `g` would rebuild the same state for what follows and reach the same dead end. Skip the whole segment: cut back to `g`'s call height.
- **A solution was reached:** remove the guard and backtrack in order, as today. `g`'s next proof gives that solution again, and proof counts stay what they are.

**Why the skip is sound.** What `g`'s proof binds is either a fresh variable of a clause it opened or a variable local to `g` (no assumption it can use has a variable to bind); nothing asked after `g` reads either. Its definite exit leaves no goal of its own waiting. So every proof of `g` leaves the same state for what comes after: the same σ on every variable the tail can see, the same goals, the same assumptions, the same depths (a goal's depth is its own, §8.3). The search after `g`'s exit is therefore the same search after each of `g`'s proofs. Between pushing the guard and reaching it, the search explored exactly that subtree, so "no solution reached since" means that subtree has none. A local variable may be an answer variable of the query: with no solution, there is no answer to differ in it.

**What it covers.**
- The k = 16 chain: each ground `|` exits definitely with a one-candidate segment. When `(1 = 2)` fails, each guard skips its segment. Linear.
- A ground `some_in` with several witnesses followed by a failing goal: linear.
- `member(?c, l)` with `?c` local, followed by a goal that fails: linear in the length of `l` where it was the product.
- P6G1P's WHO NEEDS IT: anthill-traces decides clauses on ground values, and the cost is in the clause that FAILS. A clause that holds is decided at its first definite solution. So the guard answers that need with proof counts intact. P6G1P's commit is then needed only if a caller wants a ground goal's proofs counted once (§4).
- It also applies inside a negation's sub-search, which is the same machine. That is where a failing contract clause is decided.

**What it does not cover.** The guard acts on a dead end only. Once the tail has ONE solution, every further proof of `g` runs the whole tail again: `k` independent goals of two proofs each before a tail that holds give `2^k` proofs, each of them found. That is what a relation's proof count is (052); saying it otherwise is §4, or a count that multiplies instead of enumerating, which is not proposed.

**What it does not change.**
- **Truncation and faults of the TAIL.** A tail cut by the depth limit, or faulting, would do so again after each alternative of `g`; the `truncated` flag is already set and faults are deduplicated. A verdict undecided for the tail's sake stays undecided.
- **Residuals.** A residual solution is a solution: the guard then backtracks in order.
- **Fuel.** It only saves steps.

**What it does change: the verdict where a skipped alternative would have been truncated or would have faulted.** An alternative of `g` that is never run sets no `truncated` and records no fault. MEASURED 2026-11-24 (review, reproduced), `--max-depth 8`:

```anthill
fact g(0)
rule g(?n) :- g(?n + 1)
rule dead(?n) :- g(?n), 1 = 2
```

`!(dead(0))` answers today CONDITIONAL, with the truncation notice: `g(0)`'s fact is followed by `1 = 2` failing, the search goes back into `g`'s recursive clause, and that reaches the depth limit. Under the guard the recursive clause is skipped, nothing is truncated, and `!(dead(0))` answers definitely TRUE. So the guard changes an ANSWER, from undecided to decided, and §3's first-draft claim that it changes neither answers nor proof counts was wrong for a search that today ends truncated or faulted.

**The verdict rule (decided with the user 2026-11-24).** A skip is a refutation of the conjunction, not an unexplored part of it: `g`'s continuation has no solution, and it is the same continuation after every proof of `g`, found or not. `dead(0)` is false in every reading, whatever `g`'s recursion would have done, and the definite answer is the right one. So: **a skipped segment sets neither `truncated` nor a fault; the verdict is the tail's.** It only ever moves a verdict from undecided to refuted, never the other way, and never between refuted and proved. It is a change to §8.3's "truncated means undecided" (§9), which today holds of every branch the search would have entered. Today's "undecided" there is not information about `dead(0)`: the search walks into a branch that could not have held a solution and trips the limit in it. A guard that marked every skip undecided "because it did not look" would be wrong for the same reason, and would decide nothing P6G1P needs decided. The same rule holds for §4's commit, which also leaves alternatives unrun. The spec sentence still has to be changed with the user when the guard lands (§9).

**What "solution reached" counts.** Every solution the drain reached, BEFORE answer dedup. With dedup on, a solution reached again is a duplicate and could be skipped too. That extension is not proposed.

**"Ground" is `value_is_ground` under σ.** A type variable counts as a variable, which is the conservative direction. A `var_ref` under Γ is a symbol, not a σ variable, so the identity argument holds for it. Negation's open-world reading of `var_ref` is a different question.

## 4. Commit — P6G1P's flag, opt-in

The same exit, for a goal GROUND at its call (not merely independent: a local variable may be an answer variable, and a commit would lose its other answers) with a definite exit and no non-ground assumption in scope (§3: `t1` there has two answers through a ground goal). Instead of a guard, the segment is cut immediately: `once(g)`. P6G1P's tests, with two controls corrected (review, 2026-11-24):
- the k = 16 chain is linear with the commit on, and `2^k` with the commit AND the guard off. With the guard on, which is the default, it is linear already: the chain does not tell the commit from the guard;
- what does: a ground goal with two proofs that SUCCEEDS, answer dedup off. Two proofs with the guard alone, one with the commit;
- `((?x <=> 1) | (?x <=> 2)), ?x > 1` still answers `?x = 2`. The ticket writes the branches with `=`, which tests and does not bind: MEASURED, that query answers two conditional answers (`eq(?_, 1), gt(?_, 1)` and its twin), and `<=>` answers the one intended;
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

**Why it is not planned.** The bookkeeping is paid on every binding and every read of every search, whether a jump ever happens. §3's independence, known mostly at load, covers VT9S7's motivating example and P6G1P's without it. Run-time intelligent backtracking was worked out for Prolog in the 1980s and, as far as is known here, is in no mainstream system; they rely on determinism (indexing, cut, modes) instead. VT9S7 stays open, and as the GUARD's ticket (with the user, 2026-11-28): it was filed for the slowdown, and each row of its DONE WHEN is met by §3's guard — the k = 16 chain linear by default, `member(?c, [1, …, n])` before a failing ground goal decided in O(1) retries, `member(?c, [1, …, n]), ?c > n - 1` still answering `?c = n`, a dependency through a negation or a waiting goal still finding its answer, proof counts unchanged (reasoned from the two texts; none run, the guard not existing). The mechanism its description names, backjumping, comes back only on a measured case the guard does not cover. The slowdown does not block anthill-traces today (the user, 2026-11-28: "not blocked (we have workaround)"), so §4's interim through a nested search is NOT built ahead of the machine: the guard and P6G1P's commit both land at Stage C.

## 6. The machine, staged

Each stage is measured on its own and lands on both implementations. The first draft's Stage A, an `__exit(h, s)` marker spliced behind each ground goal in today's flat resolvent, is WITHDRAWN: it would be a fourth marker in a machine whose trouble is markers. It had to be invisible everywhere a goal count is read (the delay gate, `yield_sole_goal`, proof mode, residuals), and to know a definite exit it had to stamp each rotated goal with the scope it came from.

**Stage A — the continuation is linked, not copied.** No change of behaviour; it removes the quadratic cost measured above.
- **A branch's state** is (its continuation, σ, what is waiting), each O(1) to keep.
- **The continuation** is a persistent linked list of scopes, as ELPI's `FCons`. A scope is (its remaining goals, its caller's scope, its call height, the assumptions it pushed, its depth, its proof tag). Opening a clause pushes a scope in O(1). A branch shares its caller's scopes and copies nothing.
- **The exit is structural:** a scope with no goals left continues with its caller's.
- **What it retires.** `__pop_assumption` and the baked `cut(B)` become fields of a scope: the assumptions it pushed, its call height. A `push_choice` branch is a scope like a clause body (§1.3).
- **Depth is a field of the scope, given when it is made, and NOT how deeply scopes are nested.** A branch of a choice is a split at the depth of the goal it splits, and a clause body is one deeper (`Nesting`, WI-20261115-0WT09). MEASURED 2026-11-24 (review, reproduced): `anthill.kernel.push_choice((1 === 1), (1 === 2))` answers true at `--max-depth 0`. Counting scopes would refuse it. That query is a regression test of this stage on both implementations.
- **Size.** `kb/resolve.rs` is 23.7 k lines; 73 sites read `self.stack.last()` or `last_mut()` directly, 8 push a frame, 11 copy the tail. The migration first puts the arms behind accessors (the current goal, σ, fail, offer alternatives, continue with goals), then swaps the representation behind them.
- **Measured by:** the growing-resolvent probe and the typed probes of § MEASURED becoming linear, with the gate unchanged.

**Stage B — a goal waits in the goal it was written in.** This is the delay that was meant (the user, 2026-11-24), not a side effect of the representation: a correction of how 068 §2.2 was implemented.
- **The rule.** A goal that waits goes behind its SIBLINGS: the goals of the scope it was asked in, and no further.
  - **Woken** by a binding of one of its blockers, it is asked next, before any ready goal, wherever the search is then (068 §2.2, decided 2026-10-21, kept: a check must cut a generator while it generates). It is asked in the CONTEXT IT WAS FIRST ASKED IN: that depth, those assumptions, that proof tag.
  - **When a scope has only waiting goals left**, it cannot finish by itself. It exits and hands them to its caller's scope, where they wait behind the caller's siblings. Its exit is then not definite.
  - **A hand-over moves the WAIT, not the context.** The caller becomes responsible for when the goal is asked and for whether its own exit is definite. What the goal is asked under stays what it was: a consequent that waited under a hypothesis is proved under that hypothesis, though the discharge that made it has exited.
  - **At the query's scope**, what still waits is the residual.
- **What it puts right.** Today a waiting goal is carried out of the body it was written in: past `__pop_assumption`, so outside the assumptions it was written under, and into a resolvent whose length is the residualization gate's measure. A clause that waited on a caller variable (`Candidate::Waiting`) is asked again "once the caller has had its turn": that is this rule, said of one case.
- **The representation.** The continuation is shared, so an inner scope cannot write into an outer one. What waits is therefore a store of the BRANCH, beside σ: a persistent map from a blocker to the goals waiting on it, as σ's `constraints` already are (WI-502). An entry is (the goal, its context: depth, assumptions, proof tag, captured when it first waited; its owner: the scope now responsible for it). `Wait::Suspended { blockers }` already carries the rest; a `Parked` goal is there with no blocker. Handing goals to the caller changes the owner and nothing else.
- **Acceptance, besides the gate:** a consequent that waits on a caller variable under a discharge, `(forall(?n), h(?n) -: c(?n, ?y))` with `c` waiting on `?y`, is handed to the caller, the caller binds `?y`, and the woken `c` needs `h` to be proved. It holds; and it fails when the suspension is given its owner's assumptions instead (the control).
- **What it retires.** The rotation, the `consecutive_delays >= goals.len()` gate, and passing a suspended goal over on each of its turns.
- **A definite exit** is a scope that hands nothing to its caller. For an independent goal (§3) that is an O(1) test, the store being the one the scope saw at its call: nothing outside its proof waits on a variable it binds.
- **To check on the gate:**
  - a `Parked` goal "keeps its place behind its siblings, because a sibling that FAILS still refutes the clause": in its own scope that holds as written;
  - where the answers or the proof records of today's suites depend on a waiting goal having left its body. Each such place is either a test of the old behaviour or a defect the old behaviour hid; they are listed for the user, not adjusted silently.

**Stage C — choice points by height.** On Stage A's scopes.
- **One stack of choice points**, each (a continuation, σ, the store, the alternatives left). The live branch is not on it.
- **A choice point is released at its last alternative:** a call with one candidate pushes none. "Last" has to be known: extent rows are matched lazily, and waiting clauses come after the candidates.
- **That alone does not bound memory** (review, 2026-11-24). With no choice point left, each call of a deterministic recursion still links a scope to its caller's: at the base of `cnt(n)`, `n` scopes are live with the choice-point stack empty. A scope is small where today's retained frame is about 4.4 KB, but it is still one a level.
- **A scope whose last goal is called is not kept.** When the goal selected is the LAST of its scope, the callee's scope links to the scope's CALLER, not to it. The two exits are then the same moment, so the scope's duties at its exit ride with the callee. Depth is a field (Stage A), so eliding a scope changes no depth.
  - **Its duties are carried, each in O(1).** A guard to decide (§3): carried as (the scope's call height, the store at its call). Where several elided scopes each have one, the OUTERMOST is kept: its floor is the lowest and skips everything the inner ones would, and it is valid as that scope's own guard at its own exit. The commit (§4) is carried the same way. Assumptions to drop: carried as a count.
  - **The one duty that does not compose is a proof record to close.** In proof mode each scope is a node of the record, so no scope is elided there.
  - **Why carrying is needed** (review of revision 5, 2026-11-24): every ground call is independent and has a guard to decide at its exit. A rule that kept a scope with a duty would keep every such scope, and `cnt(4000)`, ground at every level, would hold 4000 scopes with the guard on, which is its default.

  `cnt` then runs in a bounded number of live scopes; a recursion that is not a last call (`chain` with `ok(1)` after it) keeps one a level, as it must.
- **Measured separately**, with the guard ON: peak live scopes and peak live choice points, on `cnt` (both bounded), the control and the growing chain (scopes linear, choice points bounded).
- **The cut barrier is the scope's call height**, as in WAM and ELPI, not a tag found by scanning for a frame (`apply_cut`).
- **The guard (§3)** is a choice point of its own kind, (floor: the call height, the solutions reached), pushed at the exit of an independent scope whose height is above its call's and whose store is its call's. Backtracking into it either cuts to the floor or pops it.
- **The commit (§4)** cuts to the call height at the same exit.
- **Cost.** One independence test per selected goal: a flag of the clause's goal, and `value_is_ground` on its other arguments.

**Stage D — a fair region: a branch deferred to the next level.** Added with the user 2026-11-27 and moved here from 077's open question 2 (History 7). Generating a value fairly means deciding which branch the search restores next, and that is this proposal's subject.

- **What is there today** (WI-20260911-09E6M, `1437ea4a6`). An `apply_domain` whose fill can generate a case with fields becomes a `FrameState::SizeRounds` choice point. Round `k` asks the fill afresh, with a budget of `k` cases with fields (`SizeBudget`). A case refused for want of budget is DROPPED, and the round is marked as having cut a member short. `__size_round_end(k)` admits only a branch that spent all `k`. So each member comes out once, in the round of its size, and the stream ends after a round that cut nothing short. It has three costs:
  - **It re-walks.** Round `k` builds every smaller member again and discards it. MEASURED 2026-11-27 (077's open question 2: the fewest `--max-steps` giving n answers, debug CLI):

    | n answers | `rule nats(?x: Nat) :- true` (rounds) | the same relation written depth-first |
    |---|---|---|
    | 5 | 90 | 28 |
    | 10 | 305 | 58 |
    | 20 | 1 110 | 118 |
    | 40 | 4 220 | 238 |

    That is quadratic where a type has one member per size. Where members grow geometrically with size (`Tree`), the last round dominates and the overhead is a constant factor (reasoned, not measured).
  - **It belongs to one relation.**
    - Whether a fill opens rounds is read off the per-sort table (`SortDomainEntry::generates_by_size`).
    - Only a case of a derived fill spends the budget (`is_fielded_fill_case`).
    - 077 removes that table. The user's objection stands: rounds make `fill` a rule with a generation of its own, against 077 §2 (a provision's rule has the semantics of a rule in a sort).
  - **A marker, and a gap.**
    - `__size_round_end` is one more marker in the resolvent (§6's preamble: the trouble is markers).
    - A fill that waits inside a round is rotated past the marker and generates after it. It is complete, but not fair against the round (kernel-language §5.3).
- **Deferring a branch is suspending it and restoring it later.** A choice point already is a suspended branch, restored on backtracking. A deferred branch is restored at another moment: when its LEVEL comes.
  - **What is saved** is the branch's own state, together with the clause it was about to open. After Stage A that state is its continuation, σ and the store. On today's machine it is a `ResolverFrame`'s goals (each with its depth, wait state and proof tag), σ, assumptions, proof path and budget. Restoring it is exact.
  - **Three things differ** from a plain suspend and restore:
    - suspending counts as a FAILURE in the current level: the search backtracks and goes on;
    - the branch is restored with its budget one unit higher, so the unit it was refused is now paid;
    - only that one branch is saved. Its siblings stay on the stack and are explored in the current level.
  - **It is not a waiting goal:**

    | | a waiting goal (`Wait::Suspended`, `Wait::Parked`) | a deferred branch |
    |---|---|---|
    | side of the search | AND: one goal inside a branch | OR: a whole branch among branches |
    | the branch meanwhile | runs its other goals | stops |
    | restored when | a variable it waits on is bound | its level comes |

- **The agenda.** A fair region is a choice point of its own kind, standing at the region's call. Inside it the search runs in LEVELS:
  - level `k` is plain depth-first search with a budget of `k` units;
  - a branch that wants unit `k + 1` is deferred to level `k + 1`;
  - when backtracking reaches the agenda, it restores the deferred branches of level `k + 1` as its alternatives, in the order they were deferred;
  - the region is exhausted when a level deferred nothing.

  The agenda has four operations, and none of them knows about domains:
  - `open`: the first goal of a region, selected outside any region, pushes the agenda at level 0;
  - `defer`: save the current branch for the next level, then fail;
  - `next`: at the agenda, restore the next level's branches, or pop when there are none;
  - `close`: a cut that commits past the region drops the agenda.

  `Nat` (`zero | succ(n: Nat)`), asked `fill(?x)`:

  ```
  level 0:  zero → answer zero
            succ wants unit 1 → defer B1 = {?x = succ(?n); goals: fill(?n), …}, fail
  level 1:  restore B1:  zero → answer succ(zero)
                         succ → defer B2
  level 2:  restore B2:  zero → answer succ(succ(zero))
                         succ → defer B3
  ```

  Rounds instead start level 2 again from `fill(?x)`: they build `zero` and `succ(zero)` again and drop them. `Tree` (`leaf | node(l: Tree, r: Tree)`), the recursive fields in order:
  - at level 1, `node` is paid for. `l = leaf, r = leaf` answers `node(leaf, leaf)`. Then `r = node` is deferred as D1, and `l = node` as D2;
  - level 2 restores D1, which answers `node(leaf, node(leaf, leaf))`, then D2, which answers `node(node(leaf, leaf), leaf)`.

  These are the third and fourth rows 09E6M pins. What follows from the agenda:
  - **Each step runs once.** A branch finishes, fails, or is deferred and restored once. So `Nat` is linear where rounds are quadratic, and every proof is found once, so relation counts (052) are unchanged. No "spent exactly `k`" filter is needed, because nothing runs twice.
  - **The order is the rounds' order** (reasoned, not measured; 09E6M's pinned order rows are the measurement).
    - Every derivation that spends `k + 1` units crosses from `k` to `k + 1` at exactly one step.
    - No crossing step lies on the path to another, because a path through one crosses there.
    - Level `k` defers at the crossings in the order depth-first search reaches them, and level `k + 1` runs depth-first from each crossing in that order.
    - So level `k + 1` answers its members in the order round `k + 1` does. Within a size the order is clause order with the recursive fields first (WI-743's two rules), as today.
  - **Memory is the next level's deferred branches.**
    - For `Nat` that is one per level. For `Tree` it grows with the next size class (1, 2, 5, 14, …), about what the consumer receives at that level.
    - A bound value selects one clause per level and defers nothing, so a check costs what it does depth-first.
    - On today's frames each deferred branch copies its goal list, as every choice point does. After Stage A it shares it.
  - **One region at a time in a branch.** A fair goal selected inside a region spends the region's units and opens no region of its own, as a fill inside a round does today. That is what makes two infinite fields fair to each other.
  - **Alternatives considered.**
    - Plain breadth-first (first in, first out within a level) changes the order within a size.
    - Interleaving (miniKanren's `mplus`, LogicT's `interleave`) is complete but does not come out by size.
    - Rounds (today) keep little in memory and re-walk.
- **The policy: who opens a region, and what spends a unit.** The agenda is the mechanism. Generation by size is its first policy.
  - **Who opens one.** A goal of a relation DECLARED fair, selected outside any region.
    - Declared with `@[fair]` on the spec member `Fillable.fill`, where `fill` is declared (`SortDomain` provides `Fillable`; open question 11, decided — an earlier wording here said `SortDomain.fill`). Every provision's fill, derived or written, then inherits it, and no sort is special.
    - The declaration changes the search and not the meaning, as XSB's `:- table p/1` does.
    - A goal form, `fair(g)`, can come later on the same agenda. 077 set it aside as too large; on the agenda it is a flag on a scope.
  - **What spends a unit.** Today it is a case of a derived fill whose constructor has fields, opened over an unbound value; a nullary constructor, a primitive's check, a tuple and a bound part spend nothing. In general terms (open question 12, decided): a clause of a fair relation spends one unit when its head binds an unbound variable of the goal to a constructor of a sort that has at least one field; a tuple is not one.
  - **The region's extent.** Fairness around one goal is not enough. In `pair(a: Tree, b: Tree)` the fill of `a` exits with `leaf`, and the fill of `b` then runs for ever.
    - Today a round spans the fill and the typed-column fills right behind it.
    - Proposed: **from the fair goal to the end of the body it was written in**, which is its scope, the unit Stage B uses for waiting. It covers two fills written in one body with a goal between them, which today's rounds do not.
    - It needs Stage A's structural exit. On today's flat resolvent the end of a body is not known (§ The problem), and the region ends at a marker, as now.
    - Not covered, and stated: a caller's generator after a callee whose answers are infinite.
- **Restoring a branch: two rules for what surrounds it.** The branch's own state is restored exactly. What was below it on the stack when it was deferred is gone: the earlier level explored it and popped it. Two things read what surrounds a branch:
  - **Cut.**
    - A cut in scope `S` drops the stack above `S`'s barrier, as today, and also every deferred branch that came from inside `S`: those are alternatives the cut prunes.
    - In a branch restored at a later level, `S`'s barrier is the height at which the branch was restored.
    - A cut that commits past the region closes it (`close`), as a cut past a fill closes its later rounds today.
    - So inside a region a cut commits to the first proof in the region's order, the smallest member, as it does under rounds.
    - A deferred branch's scope is known on today's frames from the pending `cut(B)` among its goals, which names the scope; after Stage A it is the scope itself.
  - **The guard (§3).** It reads the choice points above a goal's call height, and a goal whose proof deferred a branch has alternatives that are not on the stack. Such a goal gets no guard at its exit, and the region as a whole is guarded as any goal is, seen from outside (open question 13, decided).
- **Not yet a client, and stated.** The agenda suspends branches by a key, which is more general than size:
  - tabling (§1.3) suspends a consumer until its table has more answers;
  - a bounded `forall_in` over a domain (09E6M's note) would range over the region's levels;
  - iterative deepening by depth could be a query option.

  None of these is proposed here.
- **What it retires.**
  - `FrameState::SizeRounds` becomes the agenda.
  - `SizeBudget.remaining` stays as the level's budget, and its `pruned` flag becomes "the next level is not empty".
  - `__size_round_end`'s admission filter goes. The marker itself goes once Stage A gives the region a structural end.
  - `is_derived_fill_relation` and `SortDomainEntry::generates_by_size` give way to the declaration as what opens a region.
  - With Stage B, 09E6M's waiting gap closes: a fill that waits stays in its scope, and so in the region.
- **Measured by:**
  - 09E6M's rows with their answers AND their order unchanged: `an_infinite_domain_is_fair` (the seven lists); a free `Tree` at 1, 1, 2, 5, 14 by size, each once with answer dedup off; `alphabet-words` at 27 / 12 and `tiny-sat` at 2; the cut rows;
  - the `Nat` table above with deferral in place of rounds, which is linear; and its control, deferral replaced by dropping (today's rounds), which is quadratic again;
  - peak deferred branches per level on `Tree`;
  - after Stage A, two fills with a goal between them in one body, fair against each other. They are not today.

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
- **The search order.** Depth-first, clauses in order. Nothing here reorders goals except Stage B's wake, which is today's. The one exception for branches is Stage D's fair region: inside one, branches are taken level by level, and depth-first within a level. Outside a region the order is as before.
- **Goals are interpreted as written.** No compilation to instructions.

## 9. What the spec would say

§8.3, once §3 is implemented: the alternatives of a goal independent of what follows it are not retried on a dead end after its definite exit; proof counts are unchanged, and so are answers except one kind: a search that ended truncated or faulted only because of such an alternative now ends refuted ("truncated means undecided" is then said of the branches a search has to enter). Once §4 is implemented: with the commit option, a ground goal's proofs are counted once. Stage B: a goal that waits, waits behind the goals of the body it was written in, and is handed to the caller when that body has nothing else left; 068 §2.2 is reworded with it. Stage D: §5.3 keeps the order it states for a domain (members by size, and within a size in clause order) and loses its rounds. §8.3 says that inside a fair region branches are taken by level, and that a cut there commits to the first proof in that order. Each of these is a spec change to agree with the user first.

## 10. Open questions

1. **Proof mode and the guard.** A refutation record (075) covers "every clause whose head matches, on every branch". A skipped segment's branches are never visited. Either the guard is off in proof mode, or the record gains a step "fails as the branch before it did".
   **DECIDED (user, 2026-11-28): the guard is off in proof mode.** The record keeps its meaning and its checker is unchanged; a step "fails as the branch before it did" would be a new inference whose justification is the whole of §3's independence argument, more to trust in order to believe a proof. Proof mode gives up speed for completeness already (Stage C elides no scope there). Its cost, stated: a failing chain of `k` ground goals with two proofs each stays `2^k` in proof mode, in steps and in the record's size. The step is the way to shrink such a record later, on a record measured too large to produce or check, designed with 075's checker.
2. **Effects.** The soundness argument assumes a proof has no external effect. An operation applied in a rule body (068) that performs one would run fewer times under the guard or the commit. Are rule-body applications effect-free by the typer's rules? To be checked.
   **ANSWERED by the spec (read 2026-11-28, agreed with the user).** `docs/kernel-language.md` §5.3: "A rule body performs no effect. A call written in one whose row, as the call is typed, holds an effect other than `Error` is refused at load, naming the call and the effect" — over `operation stamp() -> Int64 effects {Clock} = 3`, the clauses `?x <=> stamp()`, `stamp(?x)` and `not(stamp(3))` are refused; a `Modify` that escapes the call and a function handed to a relation are held to the same. The one effect left is `Error`, a raise, and a raise in a skipped alternative is a fault never recorded, which question 3's verdict rule covers. Read in the spec, NOT run on the tree: the three refusals are carried as a control in Stage C's acceptance, since the guard's soundness rests on them.
3. **The verdict of a skip (§3). DECIDED with the user 2026-11-24:** a skip is a refutation; a skipped segment sets neither `truncated` nor a fault, so `!(dead(0))` moves from conditional to true. The same for the commit. Left: the wording of §8.3 (§9).
4. **A switch for the guard.** Default on, but a back-out control needs it off: a `ResolveConfig` field, or an environment switch as the other controls are.
   **DECIDED (user, 2026-11-28): a `ResolveConfig` field, with an environment variable for debugging.** First agreed as the field alone; the user then: "environment can be useful for debug". So the field is the mechanism — proof mode sets it off per search, a back-out row sets it at its own site — and an environment variable (`ANTHILL_NO_GUARD`, the name open) changes the field's DEFAULT for the process, so a run can be repeated with the guard off without touching code. A row that measures the guard does not use the variable. The reasons for the field, as first recorded: The guard is off in proof mode (question 1), which is chosen per search, and a process-wide variable cannot say that. READ the same day: `ResolveConfig` (`kb/resolve.rs`) holds the per-search settings (`max_depth`, the step fuel), and the environment switches of `anthill-core` are process-wide diagnostics and oracles (`ANTHILL_LOAD_TIMING`, `ANTHILL_TYPER_ORACLE`, `ANTHILL_PROVISION_ORACLE`). A back-out row sets the field off at its own site and shows the `2^k` chain exponential again. Both implementations mirror a field. A way to turn it off from the shell, if wanted for measuring, is an option of `anthill query` that sets the field.
5. **Delay in the current goal (Stage B): what 068 says.** 068 §2.2 and `docs/design/068-implementation.md` describe rotation behind the resolvent. Stage B needs 068 §2.2 reworded ("behind its siblings" meaning the goals of its body; the hand-over to the caller; the residual at the query's scope), and §8.3 to say it. To write with the user.
   **SETTLED (user, 2026-11-28): the intent is recorded in 068 now, the rewording comes with Stage B.** The user: "looks like I miss 068 — I mean delay until the end of the current goal". 068 §2.2 now opens with that correction of intent and a pointer here; its text, `docs/design/068-implementation.md` and kernel-language §8.3 are reworded when Stage B is delivered, against the rows it moves, since the spec is not to describe behaviour that does not exist.
6. **A scope that hands waiting goals to its caller: is it proved?** Stage B says it exits, not definitely, and the caller goes on. The other reading: a body with goals still waiting has not been proved until they are, and the caller's later goals should not run first. The first is today's behaviour seen from the caller (its goals run while the callee's wait). To confirm.
   **CONFIRMED (user, 2026-11-28): it exits, not definitely, and the caller goes on.** The other reading would deadlock what waiting is for: a goal usually waits on a variable the caller's later goals bind (`rule later(?l) :- chk(?l), ?l <=> [1, 2]`, measured in 077 §9: definite, the waiting clause run once the later goal bound `?l`). 077's `check` in front of a typed rule's body rests on the same. "Not definite" carries the caution: the guard and the commit act only on a definite exit, and a handed-on goal that later fails still fails the branch.
7. **A goal woken from an outer scope.** It is asked next, in the middle of an inner scope's proof, and may fail it: today's behaviour, kept (068 §2.2). For an independent goal it cannot arise: nothing outside its proof can name its variables.
   Read 2026-11-28 with the user as a note, not a choice: nothing to decide.
8. **Local variables under a bounded quantifier or a `forall_impl`.** "Occurs in one goal only" is read off a clause body. What it is for the instance of a `some_in` or the consequent of a discharge is to be written down with Stage C.
   Left to Stage C, as it says (read 2026-11-28 with the user). Until it is written, such a variable is not counted as local, so no guard is placed on its account.
9. **A goal's pending equations (§3).** Proposed: they belong to the goal's scope, so its exit comes after them. The alternative: they stay spliced among the caller's goals, as today, and a variable they mention is not local. To choose with the user. Either way, the `q(?y, ?y + 1)` query of §3 answering `?y = 2` is an acceptance case of the guard, with its control (the guard reading `?y` as local answers "no solutions").
   **DECIDED (user, 2026-11-28): they belong to the goal's scope.** `q(?y, ?y + 1)` is one goal as written, and the equation is part of asking it. The alternative is sound but gives up the guard for every goal with a computed argument, and `?n - 1` is in every recursive rule. Nothing moves in the order of evaluation: the equation runs right after the goal already, and only the scope's boundary changes, the goal counting as finished after it. An equation that has to wait does so in the goal's scope and is handed to the caller when nothing else is left there (Stage B).
10. **Stage D before or after Stage A.** The agenda's operations do not depend on how a branch is represented.
    - Built first, on today's frames: a deferred branch is a cloned `ResolverFrame` whose goal list is copied, as every choice point copies it, and the region is today's (the fill and the typed-column fills behind it, ended by a marker). It removes the re-walk now, and Stage A makes it cheap later.
    - Built after Stage A: it is built once, on the final representation, with the body as its region from the start.

    **DECIDED (user, 2026-11-28): after Stage A, and after Stages B and C.** Before A it would be built twice: on cloned frames with a marker-ended region, then again on the linked continuation. Its one new capability, two fills in one body fair to each other, needs A's structural end of a body in any case. B closes the waiting gap inside a region, and C gives the cut its barrier by height, which this stage's cut rule reads. What it costs is that 09E6M's rounds, quadratic on `Nat`, stay until then; no program is known to wait on that.
11. **The declaration's form.** How a spec member is declared fair: an attribute on `rule fill` in `SortDomain`, and under which name. And whether `fair(g)` comes with it or later.
    **DECIDED (user, 2026-11-28): the attribute `@[fair]` on the declared member, which is `Fillable.fill`.**
    - **Where the member is.** READ 2026-11-28 in `stdlib/anthill/reflect/reflect.anthill`: `fill` is declared in `sort Fillable` (`rule fill(?x)`), and `sort SortDomain` only `provides Fillable[T = T]`. There is no `SortDomain.fill` to write a declaration on, so Stage D's "declared on the spec member `SortDomain.fill`" is corrected to `Fillable.fill`.
    - **Its reach is every `Fillable`,** a fillable collection of 067 as well as a sort's domain, and that is accepted: a solver that asks a collection to fill itself wants its members by size as a domain's are, and one declaration keeps a provider's `fill` from behaving differently by the spec it was reached through.
    - **Form:** `@[fair] rule fill(?x)`, the attribute form the standard library already writes (`@[simp]`, `@[host_implemented]`); nothing new in the grammar.
    - **Name:** `fair`, the word this stage uses, which names the effect on the search and neither size nor domains.
    - **Inherited, not repeated.** A provision's `fill` is fair because the member it implements is; a provider does not write the attribute and cannot remove it.
    - **`check` (077 §9) is not declared.** It never generates, so it opens no region.
    - **`fair(g)` comes later,** on the same agenda: a second way to open a region, with a question of its own (what spends a unit inside an arbitrary goal), and nothing needs it yet.
12. **What spends a unit, in general terms.** Today's rule names a derived fill's case with fields. A written fill and a provision's fill need a rule that does not name the derivation. One candidate is opening a bodied clause of a fair relation whose head match binds a variable of the goal. It spends where a tuple does not today, so it is checked against 09E6M's tuple and holes rows (a tuple's components; `[?, ?]` at `List[T = Tree]`) before it is chosen. It also spends on a nullary constructor (review, 2026-11-27): under 077 §1 every case is written with a body, `rule fill(red) :- true`, and its head match binds the goal's variable, where a nullary constructor spends nothing today. A size is then constructors with fields PLUS nullary leaves, which reorders sorts whose constructors differ in how many such leaves they hold: `p2(a: Colour, b: Colour)` costs 1 today and 3 under the candidate, `q(n: Nat)` at `q(succ(zero))` 2 and 3, so the two fall in one level where `p2` comes first today (reasoned, not run). So the candidate needs "bodied" said otherwise — a clause whose body has a goal besides `true`, or a head whose constructor has fields — or the order of 09E6M's rows is not kept.
    **DECIDED (user, 2026-11-28): today's rule with the word "derived" removed, stated on the clause's head.** A clause of a fair relation spends one unit when its head binds an unbound variable of the goal to a constructor of a sort that has at least one field.
    - A nullary constructor is free (`fill(red)`, `fill(nil)`), and so is a bound value, whose head binds nothing unbound.
    - A tuple is free, and the rule says so: a tuple is not a constructor of a sort. Charged, `e(p: (Colour, Colour))` would fall in one level with `g(succ(zero))`, where it comes first today (reasoned, not run).
    - A primitive is free: its `fill` has a variable in its head and the outer-type test in its body.
    - A derived fill and a written one are treated alike: both are clauses of a provision's block with the constructor in the head (077 §1).
    - A written fill that binds its value in its BODY (`rule fill(?x) :- ?x <=> box(v: ?v), …`) spends nothing and is not generated fairly. That is the author's to write otherwise, as YR3N7 has it (the head decides the mode); it is documented, not detected.

    Acceptance, when Stage D is built: 09E6M's rows keep their answers and their order, the tuple and the holes rows included.
13. **The guard inside a region.** There are two options. The first is no guard for a goal whose proof deferred a branch (proposed). The second is a guard that also drops that goal's deferred branches with its segment, which is sound by §3's argument and covers more.
    **DECIDED (user, 2026-11-28): the first — no guard for a goal whose proof deferred a branch;** the region as a whole is guarded from outside, as any goal is. It only declines to skip, so at worst it is today's behaviour. The second covers little: the guard is for a goal independent of what follows it, and a goal that defers a branch is generating a value, which what follows normally reads. It stays reachable: this stage's cut rule already has to know which scope a deferred branch came from, so a wider guard can be added on a measured case, with that case as its test.

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
4. 2026-11-24 — six review items the user brought; four reproduced on the binary (1, 2, 4, 5), two are arguments about the text (3, 6); all six accepted.
   - **1. A ground goal binds a caller variable through an assumption** (`t1`, `t2` in §3). Independence, and the commit, now also require every assumption in scope to be ground.
   - **2. A skipped alternative that would have been truncated** (`dead` in §3): the guard moves `!(dead(0))` from conditional to true. Revision 2 had seen this for faults only and called it diagnostics. It is an answer. A verdict rule is proposed and gates the guard (question 3).
   - **3. A handed-over wait keeps its context.** Stage B said both "asked under its scope's assumptions" and "the hand-over changes its owner". The suspension now carries its context; the owner schedules it. Acceptance case added.
   - **4. Depth is not scope nesting.** `push_choice` at `--max-depth 0` is the regression test.
   - **5. Two of P6G1P's controls corrected** in §4: the `2^k` baseline needs the guard off too, and the binding branches are `<=>`, not `=`. A test that tells the commit from the guard added.
   - **6. Releasing a choice point does not bound memory.** Stage C gains the elision of a scope with no duty at its exit, and measures live scopes and live choice points separately.
5. 2026-11-24 — the verdict of a skip decided. The user asked why a skipped alternative would make anything undecided; it does not: today's "undecided" for `!(dead(0))` comes from walking into a branch that could not have held a solution. A skip is a refutation and sets neither `truncated` nor a fault, for the guard and for the commit. Question 3 closed but for §8.3's wording.
6. 2026-11-24 — five corrections from a reading of revision 5, applied at the user's word ("apply them").
   - **The first draft's probes were read**, from the drafting session's scratch directory: all typed (`?n: Int64`), which confirms § MEASURED's inference. Its deterministic probe wrote `rule cnt(0)`, a declaration (061), so it answered "no solutions" at every `n`; the "not explained" note is withdrawn.
   - **§1.1's example** wrote `rule q(1)`, `rule q(2)`, which declare and assert nothing; now `fact`.
   - **§3: locality is read off the goal as asked.** A pending equation from argument evaluation is spliced after the goal and reads its "local" variable: `q(?y, ?y + 1)` answers `?y = 2` today and would answer "no solutions" under a guard that read `?y` as local. Proposed: the equations belong to the goal's scope (question 9). Locality is also read after the typer's added goals.
   - **Stage C: a scope's exit duties ride with its last call.** Kept only for a scope with no duty, the elision would keep every ground call's scope for its guard, and `cnt` would not be bounded with the guard on. The guard and the commit are carried as the outermost elided scope's (call height, store), assumptions as a count; only a proof record pins a scope.
   - **§ MEASURED's per-level cost** is 4.3 to 5.5 KB from n = 8000 to 32000, not a flat 4.4 KB: a log factor is not excluded.
7. 2026-11-27 — Stage D added with the user, moved from 077's open question 2.
   - The user: `SortDomain.fill` needs fair generation, "wide instead of deep". 09E6M's rounds (delivered the same day) re-walk every smaller member, quadratic on `Nat`, and they belong to one relation.
   - The approach moves from 077 to the search machine. A branch over budget is DEFERRED to the next level instead of dropped. The user asked whether that is "suspend execution of branch and then restore": yes, restored by level instead of on backtracking, with three differences and two rules for what surrounds a restored branch (cut, the guard).
   - The user asked for a separate mechanism with an API for it: the agenda, with size-fair `fill` as its first policy.
   - The name was first written "parking" and changed, because `Wait::Parked` is a goal's wait state.
   - §8 and §9 amended. Open questions 10 to 13 added.
   - The name "Stage D" is reused: revision 2 had it for backjumping, withdrawn there (§5).
