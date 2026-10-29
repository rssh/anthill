## Attributes

- id: WI-20260913-P9QBF-a-lazy-search-truncated-at-its
- created: 2026-09-13T14:00:36Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-29T22:27:38Z

- acceptance: cargo-test

## Description

A LAZY SEARCH TRUNCATED AT ITS DEPTH CAP ENDS AS A COMPLETE EMPTY RESULT on every stream face. WI-628 made the EAGER drains honest (drain_all / drain_verdict carry 'truncated', so NAF, guards and counts read an incomplete search as undecided), but SearchStream::split_first reports only FAULTS (WI-20260911-8Y5BE) - its exhaustion exit returns Ok(None) whether or not a branch was abandoned at max_depth.

MEASURED (probe, default ResolveConfig, max_depth=100) on 'rule Deep(x: ?x) :- Deep(x: ?x)': resolve_with_stats -> 0 solutions, truncated=true, errors=[]; resolve_lazy + split_first -> Ok(None); interpreter 'splitFirst(execute(kb(), pattern_query(...)))' -> none(). The host bridge and the Relation face go through the same door (not separately probed). A consumer therefore reads 'no more answers' as a refutation - the WI-628 hole on the lazy faces - and a Relation's isEmpty / negate reads it as non-membership.

THE DESIGN QUESTION IS THE WORK, not the plumbing: (1) WHERE it is reported - at the exhaustion exit only, since rows yielded before the cap are true answers and only the 'that was all' claim is false; (2) WHAT it is - not a fault (nothing is wrong with any goal) and not a Solution variant (it is not an answer), so probably its own arm on split_first's Err (e.g. a SearchFault variant or a sibling type) and its own ResolveStreamFailure variant (e.g. search_truncated(depth)) on execute's row, which is a declared-payload change that ripples to callers the way Error[ResolveStreamFailure] did; (3) whether a consumer that wants the partial set can opt out (a raised config, or reading the rows before the end).

WHAT NOT TO BREAK: drain_verdict / drain_all step the stream themselves and must keep their three-way verdict; a truncation inside a NAF sub-search already taints the outer 'truncated' and must not become a raise on a decided outer answer (the faults-vs-errors lesson from 8Y5BE applies to 'truncated' too).

ACCEPTANCE: the Deep fixture above, drained lazily through split_first, execute (interpreter and host bridge) and a Relation, reports truncation rather than an ordinary end; a search that yields rows and then truncates hands out those rows first; a CONTROL whose recursion terminates below max_depth still ends Ok(None); an eager consumer (not(P) over a truncated P) is unchanged; cargo-test green via scripts/test.sh.

## Changes

### 2026-10-29T22:27:37Z — feedback — claude

DELIVERED in 252a59db. DECIDED WITH THE USER (2026-10-29): the payload is a fifth ResolveStreamFailure constructor, search_truncated(max_depth: Int64), one of the runtime's accounts (a program matches it and does not construct one), and inside a rule body a raise of it is a truncation below, not a fault. MEASURED BEFORE, default max_depth 100: splitFirst(execute(Deep)) none(), deep.takeN(10) 0 rows, deep(1).isEmpty() true, some1.takeN(1000) 99 rows and an ordinary end, counted(?n) :- ?n <=> deepCount() answered ?n = 0 definitely; negate(deep(1)) already raised relation_floundered, so the ticket's "negate reads non-membership" did not hold. NOW: SearchStream::split_first answers SearchFailure::Truncated at the exhaustion exit only, when the search is truncated and recorded no fault (a fault outranks it); the interpreter's execute and relation pumps raise search_truncated(max_depth) and park the slot Faulted (a later pull is stream_misused); the host bridge raises SearchTruncated; the bridge reads the account as BridgeDisposition::Truncation (the goal waits, the search is incomplete, no message); kernel.not refuses it loudly. Rows before the cut come out first; a search that ends below the limit ends Ok(None); drain_all / drain_verdict, NAF and guards are unchanged. FOUND ON THE WAY AND FIXED: (1) the host adapter's is_empty answered from the resolver's stack without pulling, so any unpulled search was non-empty, one with no answer too — it pulls now and keeps the answer for the next pull (the adapter's state is one enum: search, peeked, ended, spent, raised); (2) from /code-review: a limited(q, n) query set max_solutions, which split_first never read, so the lazy stream ran past n and now on into the cut's raise — split_first ends after the nth answer; an ended adapter answers the end again whichever reader found it, and iterator() keeps a raised or ended state on both adapters; spec §5.2's "a full drain does not return" for an infinite domain corrected (Nat.domain gives 20-29 rows before the cut, then raises). LEFT: a relation drain over a rule whose body call drained a cut search raises relation_floundered at the waiting goal's residual row, as a nested eq sub-proof's cut already did — naming the cut there needs a cause on the waiting goal; a nullary rule named like the last segment of its namespace (namespace probe.zed, rule zed) is filed under the namespace's symbol probe.zed, not probe.zed.zed (unrelated, reported to the user). ROWS: wi_p9qbf_lazy_truncation_test (10, ledger at its head) and six anthill-stl bridge rows; each part backed out alone in one build — the exhaustion arm, the account, the disposition, the host is_empty pull, the limit.

