## Attributes

- id: WI-20260820-FFPGD-resolver-an-existential-body
- created: 2026-08-20T17:13:07Z

- status: Open
- status_agent: user
- status_at: 2026-08-20T17:13:07Z

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

