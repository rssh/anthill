## Attributes

- id: WI-20261127-AGR9S-resolver-the-continuation-is
- created: 2026-11-27T22:39:50Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-28T12:42:18Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-076

## Description

Resolver: the continuation is linked, not copied (proposal 076 Stage A)
WHAT. docs/proposals/076-goal-scope-in-the-search.md §6 Stage A, APPROVED TO BUILD by the user 2026-11-28 (the proposal's other stages are not approved yet). A branch's state becomes (its continuation, sigma, what is waiting), each O(1) to keep. The continuation is a persistent linked list of SCOPES, as ELPI's FCons: a scope is (its remaining goals, its caller's scope, its call height, the assumptions it pushed, its depth, its proof tag). Opening a clause pushes a scope in O(1); a branch shares its caller's scopes and copies nothing. The exit is structural: a scope with no goals left continues with its caller's. NO CHANGE OF BEHAVIOUR.

WHY. A frame holds the whole resolvent today, and opening a clause builds body ++ a copy of the tail (frame.goals[1..].to_vec() in kb/resolve.rs, 11 such sites; scaland: ArrayBuffer.from(freshBody) ++= frame.goals.drop(1) in resolve/SearchStream.scala). MEASURED 2026-11-24 (076, MEASURED; debug CLI, peak RSS, stdlib about 103 MB of each): a recursion whose resolvent grows by one goal a level is quadratic -- 439 MB / 1.41 GB at n = 1000 / 2000 -- where the untyped short-resolvent control is near linear (123 / 145 MB); the typed rows (cnt(?n: Int64) 208 / 537 MB, typed control 498 MB / 1.63 GB) were the same case, a pending fill growing the resolvent. RE-MEASURE FIRST on the current tree: WI-20261124-YFD7F (delivered 2026-11-27) drops a trusted call's fill, so the typed rows may already have moved; the growing-resolvent row is the one this ticket owns.

WHAT IT RETIRES. __pop_assumption and the baked cut(B) become fields of a scope (the assumptions it pushed, its call height); a push_choice branch is a scope like a clause body.

DEPTH IS A FIELD of the scope, given when it is made, and NOT how deeply scopes are nested: a branch of a choice is a split at the depth of the goal it splits, a clause body one deeper (WI-20261115-0WT09). anthill.kernel.push_choice((1 === 1), (1 === 2)) answers true at --max-depth 0 (measured 2026-11-24); counting scopes would refuse it. That query is a regression row of this ticket on both implementations.

HOW (076's sizing). kb/resolve.rs is 23.7 k lines; 73 sites read self.stack.last() or last_mut() directly, 8 push a frame, 11 copy the tail. First put the arms behind accessors (the current goal, sigma, fail, offer alternatives, continue with goals) and commit that green with no representation change; then swap the representation behind them. Both implementations, rustland and scaland.

NOT IN IT. Stage B (a goal waits in the body it was written in), Stage C (choice points by height, the guard, the commit) and Stage D (the fair region): each is filed when its predecessor is delivered. WI-20261122-VT9S7 (the guard) and WI-20261122-P6G1P (the commit) wait on this ticket.

DONE WHEN. The growing-resolvent probe of 076 (rule chain(?n) :- (?n = 0) | (?n > 0, chain(?n - 1), ok(1))) is linear in peak memory at n = 1000 / 2000 / 4000, and its CONTROL is the same probe before the change, quadratic (the numbers above, re-measured on the tree the work starts from); the push_choice row at --max-depth 0 answers true on both implementations; every existing resolver and relation row is unchanged -- answers, multiplicities and proof records; full workspace via rustland/scripts/test.sh, families, scaland testFull.

## Changes

### 2026-11-28T12:37:17Z — feedback — user

DELIVERED (claude, 2026-11-28, with the user). Stage A built on both implementations, in the ticket's three steps, one commit at the user's word. (1) ACCESSORS: every reader and writer of a frame's goals goes through Goals (kb/resolve.rs); gate 13020 / 0 / 26 = HEAD on that alone. (2) THE CONTINUATION LINKED: Goals is a persistent chain of scopes (rustland Goals/Scope/GoalList, iterative drops; scaland Goals/Scope in resolve/SearchStream.scala). Opening a body links a scope and copies nothing; an empty scope with nothing to do at its exit is elided (a last call); a goal that waits goes behind every scope into a queue that comes round in the order it waited; wake and the size round's end edit by copying only the cells in front. A flag (waited) skips the per-step wake scan where no suspended goal ever entered. Depth stays a field of each goal, given when it is made, never counted from nesting. (3) WHAT IT RETIRES: __pop_assumption is gone (tag, kernel registration, resolver arm, builder, reader): a discharge's scope records the assumptions it pushed and drops them at its exit, and the assumptions ride in the continuation (ResolverFrame.assumed_facts removed). The baked cut(B), the barrier allocator and ChoicePoint.cut_barrier are gone: a clause body with a top-level ! records the call height of the choice point that opened it, and apply_cut cuts to it with no scan; a cut written with an argument is a fault. MEASURED (docs/measurements/076-stage-a/, debug CLI, peak RSS, n = 1000 / 2000 / 4000): growing resolvent 422 MB / 1.36 GB / 5.06 GB before (the CONTROL, re-measured on 22bfbc359), 117 / 141 / 189 MB after = the short-resolvent control's own; typed growing 833 MB / 2.99 GB / 11.6 GB before, 122 / 150 / 207 MB after; wall at 4000 4.22 s (11.06 s before). push_choice((1 === 1), (1 === 2)) at --max-depth 0 answers true on both implementations (rows wi_agr9s_linked_continuation_test::a_side_of_a_choice_is_no_call, LinkedContinuationTest). MOVED, listed: a discharge takes one step fewer (the marker was a step); and one answer, w(?y) :- s(?y), (forall(?n), hyp(5) -: ?y <=> 5) with s a caller goal waiting on ?y, from ?y = 5 (the woken caller goal answered by the hypothesis on the marker's step) to no answer, the right one (pinned). The same leak with the binding mid-consequent remains: 076 Stage B. Tests pinning the marker retargeted: wi878's 1-ary arity row to __size_round_end; wi_j03at's kernel-marker list without __pop_assumption. Rows added: kb::resolve::goals_tests (the scopes against the flat resolvent with markers, 30 000 operations; a 200 000-goal drop), wi_agr9s_linked_continuation_test (8 rows), scaland LinkedContinuationTest (3); back-outs at their sites. Gate: scripts/test.sh full workspace 13030 / 0 / 26; scaland testFull 814 + 51 (2 skipped) + 1, all passing. Families not run: the typer is not touched.

