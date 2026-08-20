## Attributes

- id: WI-20260820-FFPGD-resolver-an-existential-body
- created: 2026-08-20T17:13:07Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-20T21:33:25Z

- acceptance: cargo-test

- tags: resolver

## Description

RESOLVER: an existential body variable MULTIPLIES ANSWERS — `tagged(?t)` returns `ok` twice. Answer dedup does not reach the case it was named for.

MEASURED, through the CLI, not a unit-test artifact (freshly built `anthill`):

  namespace dup.probe
    sort Tag    entity ok    entity fail  end
    sort Row    entity check(t: Tag, witness: Int64) end
    fact check(t: ok(),   witness: 1)
    fact check(t: ok(),   witness: 2)
    fact check(t: fail(), witness: 3)
    rule tagged(?t) :- check(t: ?t, witness: ?)
  end

  $ anthill query --path dup.anthill 'dup.probe.tagged(?t)'
    ?t = fail
    ?t = ok
    ?t = ok
  3 solution(s)

`witness` is written `?` — ANONYMOUS, i.e. existential, "don't care". Two rows that differ only in a field the query never mentions must not be two answers. The intent is not in question: the suite already calls this ANSWER DEDUP (`a_symbolref_binding_does_not_disable_answer_dedup`, `a_structural_binding_keeps_answer_dedup_on`), and `is_duplicate_projection` exists to do it.

WHY IT ESCAPES, and this is the whole ticket. `is_duplicate_projection` (kb/resolve.rs, called at the goals-empty yield) fingerprints the NEAREST ancestor ChoicePoint's goal through σ — its own doc says "nearest", and the implementation `return`s inside the frame walk on the first one it finds. That catches redundancy arising AT a choicepoint, which is exactly the shape the WI-1016/WI-1023 fixtures build: several rules for ONE functor, all yielding the same binding, so the nearest choicepoint's goal fingerprints identically and the dedup fires. Our redundancy arises BELOW: the innermost choicepoint here is the one over `check`'s three rows, which are genuinely distinct (different `witness`), so nothing is a duplicate THERE. It only becomes one once projected onto the outer goal `tagged(?t)`, and by then no frame is looking.

(The call-site comment says "project solution onto EACH ancestor ChoicePoint's goal vars" — stale, and it describes a design that is unsound; see below. `record_solution_in_ancestors` is likewise plural-named and also returns at the nearest, though there it only skews a counter.)

TWO CHEAP FIXES, BOTH WRONG — recorded so they are not re-attempted:
  * SCAN ALL ANCESTORS. Unsound, and it DROPS legitimate answers. For `a(?x), b(?y)` over two facts each, the answers (1,1) and (1,2) both fingerprint `a(1)` at the still-live `a` choicepoint, so the second is discarded. Wrong-direction failure: `value_fact_dedup_key`'s doc names dropping as the unsafe side, which is why both existing guards fail OPEN.
  * TAKE THE OUTERMOST CHOICEPOINT INSTEAD OF THE NEAREST. Fixes a single-goal query, breaks the same conjunctive one for the same reason — for a query that IS a conjunction the outermost choicepoint is `a(?x)`.

THE FIX IS TO PROJECT ONTO THE QUERY'S FREE VARIABLES — the answer set — rather than onto any one choicepoint's goal. That yields `{ok, fail}` here and keeps all four answers for `a(?x), b(?y)`, because the projection is over the whole query goal vector, not a prefix of the proof. `SearchStream` (kb/resolve.rs) already owns the stack, config, `query_cache` and stats, and is constructed once per resolve call, so it is where the original query goals and a `seen_answers` set belong. At the goals-empty yield: fingerprint the query goals under σ with the existing carrier-agnostic `goal_fingerprint`, keep BOTH fail-open guards unchanged (σ-wide `bears_opaque`, and `key.is_opaque_free()`), skip on a repeat. It SUBSUMES the nearest-ancestor check, which can then go.

SIZE: the change is ~30 lines. The WORK is the fallout — this moves observable answer counts for every query with an existential body variable, so an unknown number of the 5278 tests that assert a count will move with it. That is the reason this is a ticket and not an inline fix; the code is small and the re-measurement is not.

ACCEPTANCE — DRIVE IT, do not assert that it loads. (1) The repro above returns 2 solutions, `ok` once, through the CLI. (2) THE CONTROL, and it is the one that matters: `a(?x), b(?y)` over two facts each still returns 4 — the test fails if the fix is implemented by scanning ancestors, which is the tempting wrong version. (3) A same-choicepoint duplicate (the WI-1016 fixture shape) still dedups, so the replacement does not regress what the nearest-ancestor check already bought. (4) An opaque-bearing binding still DISABLES dedup in both directions (the existing fail-open guards), asserted rather than assumed.

FOUND BY: `/code-review` on the WI-1131 warning sweep flagged `anonymous_vars_chain_through_rules` as a test that measures nothing (it did `xs.dedup()` itself, then asserted 2 distinct). Asserting the RAW count to fix that returned 3, not 2 — the test had been masking this. That test now CARRIES THE ASSERTION THIS TICKET OWES, written as `assert_eq!(solutions.len(), 2, ...)` and COMMENTED OUT, with a pointer here. Deliberately not pinned at 3: pinning the wrong number enshrines the defect as expected and makes the eventual fix read as the regression. Uncommenting that line is acceptance clause (1) at the unit level.

## Changes

### 2026-08-20T17:14:15Z — feedback — user

RUSTLAND ONLY — acceptance narrowed to cargo-test on filing. scaland's resolver has no answer-dedup counterpart to mirror: `scaland/core/src/main/scala/anthill/resolve/` holds only Builtins/Config/SearchStream, and nothing there dedups, so there is no `is_duplicate_projection` twin and no scaland test that could move. Do not read the absence as an unported fix.

### 2026-08-20T21:33:28Z — feedback — claude

DELIVERED. Answer dedup projects onto the QUERY's goal vector. The fallout was not only re-baselining: it exposed a SECOND SEMANTICS the ticket did not anticipate, and /code-review then found a real bug in the fix itself.

THE FIX, as specified. `SearchStream` carries `query_goals` (the vector handed to `resolve_lazy_goals`) and `seen_answers: HashSet<Vec<GoalKey>>`. At the goals-empty yield, `is_duplicate_answer` (renamed from `is_duplicate_projection`) fingerprints every query goal under sigma with `goal_fingerprint`, keeps BOTH fail-open guards unchanged, and skips on a repeat. A `Vec<GoalKey>` and not one merged key: `GoalKey` is a token sequence, so concatenating goals would let a differently-split pair collide. The nearest-ancestor check is gone and `FrameState::ChoicePoint::seen_goals` with it.

A RELATION IS A BAG, AND PROPOSAL 052 ALREADY SAID SO. Six of the nine moved tests were the relation layer: "Open questions" 6 pins relation consumption to "the resolver's stream as-is", a zero-column membership relation's `multiplicity = number of proofs`, and "a relation is an unordered bag" -- `union(r, r)` yields its row TWICE by design, with `Relation.set` the explicit collapse. A query-level projection erases exactly that, so the resolver was being asked two questions under one name. Now `ResolveConfig::dedup_answers` (default true), OFF at the bag/existence seams. FIVE producers, and the first census found only one -- /code-review caught the miss because my grep covered `anthill-core/src` only. BAG: `execute_logical_query` (feeding `Relation.splitFirst` and `KB.execute`) and `KbBridge::execute` in anthill-stl, a SECOND producer of `KB.execute`'s semantics that builds goals through its own `query_to_goals` and so never touched the function carrying the decision (that duplication predates this and is noted, not fixed). EXISTENCE, where dedup cannot change a verdict and only costs fingerprints: the NAF sub-search, `prove_rule_predicate`, and anthill-stl's `reflect_not` -- each says so at its site, and says that no control exists because the effect is redundant by construction.

THE OTHER THREE MOVES WERE MINE TO FIX, NOT TO RE-BASELINE. `debruijn_multiple_anonymous_vars_independent` and `wi739_zero_head_param_spelling_still_proves` count PROOFS of a goal with no free query variables, so an answer stream reports 1 and the property under test -- anonymous-var independence, body enumeration -- becomes invisible; both set `dedup_answers: false` with the reason at the site. `wi1046`'s `pipe` row showed a disjunction firing both arms with a count of 2 over two arms that BOTH answered `?x = 1`: one answer reached twice, which dedup collapses, so the row would have read 1 whether the right arm ran or not. Fixed at the FIXTURE (`fact right1046(2)`), which restores `[2,1,1,0]` and makes the row discriminate in a form that survives dedup -- the answer `2` can only come from the right arm. That row is now also a control on THIS ticket: it reports `[3,1,1,0]` under the nearest-ancestor projection.

/code-review FOUND A REAL BUG IN MY OWN CHANGE, and it is driven. Checking dedup BEFORE `record_solution_in_nearest_choice_point` left `child_solutions` at zero for a branch that had definitely succeeded, so the choice point took the `child_solutions == 0 && any_delayed` delay fallback and residualized a FLOUNDERED answer over a proof it already had. The old order was safe only BY CONSTRUCTION and the construction is what this ticket removed: dedup keyed the nearest ChoicePoint's OWN `seen_goals`, so a duplicate implied an earlier solution had passed through that very frame. `seen_answers` is stream-global, so a duplicate now arrives from a different subtree. Counting the proof first is the fix; `a_dropped_duplicate_still_counts_as_this_choice_points_proof` drives it and MEASURES the back-out at 2 solutions with residual lengths [0, 1]. Nothing else in the workspace reddens under that back-out.

ACCEPTANCE, all four driven.
(1) CLI: `anthill query --path dup.anthill 'dup.probe.tagged(?t)'` -> `?t = fail`, `?t = ok`, 2 solution(s). At the unit level the commented-out `assert_eq!(solutions.len(), 2, ...)` in `anonymous_vars_chain_through_rules` is UNCOMMENTED, and its neighbour's `xs.dedup()` is GONE -- the raw count is the assertion now, so a regression that duplicates an answer cannot hide behind it.
(2) THE CONTROL: `a_conjunctive_query_keeps_every_pairing` -- a genuine TWO-GOAL `kb.resolve(&[a, b], ..)`, not a wrapper rule, since the wrong fixes are wrong about the QUERY's shape. 4 pairings. MEASURED under both: SCAN ALL ANCESTORS gives `[(1,1),(2,1)]`, OUTERMOST CHOICE POINT gives `[(1,1),(2,1)]`. Scan-all also reddens four `wi739` rows; OUTERMOST reddens NOTHING ELSE in the workspace, so this test is its only witness.
(3) Same-choicepoint dedup still fires: the WI-1016 / WI-1023 (A) tables are green unchanged, and their fixture docs no longer claim the one-goal shape is FORCED -- it is now merely the cleanest isolation.
(4) Opaque guards RE-MEASURED, AND ONE STATED CONTROL WAS WRONG. Deleting the sigma-wide `bears_opaque` scan reddens 2 tests (1 where 2 is right); making it shallow reddens 1. But dropping the key-side `is_opaque_free` guard reddens NOTHING: `an_opaque_child_inside_a_structural_carrier_disables_dedup` credited that guard, and the tuple it builds lands in the head var, so the sigma scan stops dedup first. The claim was true of a SHALLOW sigma scan and went stale when `bears_opaque` became transitive. Corrected at the site -- that test measures TRANSITIVITY -- and THE KEY-SIDE GUARD HAS NO WITNESS IN THE WORKSPACE. Its domain is real but unreached: an `Opaque` the key picks up from the GOAL with nothing in sigma to scan, which now means an occurrence region `occ_head` declines to decompose, or a duplicate-label goal. Kept (it fails open); STATED rather than credited.

TWO MORE CONSUMERS WHOSE BEHAVIOUR MOVED, both from /code-review, both stated at their sites rather than mitigated. `eval_count_guard` now counts ANSWERS -- a `one_q` whose body has an existential `?` matching two rows flips VIOLATED -> HOLDS, which IS the quantifier's own reading; still not exactly its reading, since the projection covers `condition ++ body`'s whole goal vector rather than `syms.var`, a gap that predates this. Its `max_solutions = max + 1` budget is no longer consumed by duplicates, so declaring VIOLATED needs `max + 1` DISTINCT answers and the search goes further -- more correct, more likely to hit the cap, which the existing `truncated` arm already turns into Undecidable. `extent::read_facts_resolved` returns DISTINCT rows instead of one per derivation, and that is LOSSLESS here rather than a policy choice: it returns the same goal reified through the same sigma that the dedup key fingerprints, and `enumeration_goal` carries the full field set, so two collapsed solutions had byte-identical rows.

TWO NON-SEMANTIC CONSEQUENCES, recorded on the `dedup_answers` field. `max_solutions` bounds ANSWERS, not proofs -- a cyclic reachability query with finitely many answers but unboundedly many proofs no longer stops after N derivations; it stops after N distinct answers and then searches to `max_depth`. And `seen_answers` is retained for the stream's lifetime where the per-frame sets it replaced died with their frames; NOT capped, because a cap would silently stop deduplicating, which is the failure this ticket exists to remove. Unmeasured on a large extent, and said so.

A THIRD BLIND SPOT: the var-keyed residual constraint store (`Solution::residual_constraints`). Two answers agreeing on every query variable but carrying different `lacks`/type constraints key identically and collapse. Inherited from the nearest-ancestor projection, which was equally blind, and currently unreachable -- that store is write-mostly with no consumer. Its first reader owes this predicate a third guard.

FILED: WI-20260820-4KXPD. This ticket's description called `record_solution_in_ancestors` "only a counter"; it is NOT. A choice point whose WINNING candidate has a BODY never sees the credit -- the body goal's own choice point takes it -- so with a delayed sibling it manufactures a floundered answer. MEASURED at 2 spurious residuals with dedup ON and OFF alike, so it predates this ticket. Not fixed inline because deleting the `return` can LOSE REAL SOLUTIONS: the rotation it suppresses is what re-asks a delayed candidate after the caller's tail binds its var. That is a semantics decision in the flounder machinery, with three candidate designs and the control that separates them written into the ticket. The renamed function points at it.

DOCS: kernel spec 8.3 gains "A query yields ANSWERS; a relation yields PROOFS" (the projection, the two fail-open non-collapses, the bag face). Proposal 052 "Open questions" 6 marked SETTLED for the relation face with what changed under it. Proposal 007 and the value-facts design doc had superseded text naming the old predicate; both now say so. Five stale in-tree references to `is_duplicate_projection` / "nearest ancestor ChoicePoint" corrected.

5363 passed, 0 failed, 11 ignored, 35 binaries.

