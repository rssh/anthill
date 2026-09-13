## Attributes

- id: WI-20260913-P9QBF-a-lazy-search-truncated-at-its
- created: 2026-09-13T14:00:36Z

- status: Open
- status_agent: claude
- status_at: 2026-09-13T14:00:36Z

- acceptance: cargo-test

## Description

A LAZY SEARCH TRUNCATED AT ITS DEPTH CAP ENDS AS A COMPLETE EMPTY RESULT on every stream face. WI-628 made the EAGER drains honest (drain_all / drain_verdict carry 'truncated', so NAF, guards and counts read an incomplete search as undecided), but SearchStream::split_first reports only FAULTS (WI-20260911-8Y5BE) - its exhaustion exit returns Ok(None) whether or not a branch was abandoned at max_depth.

MEASURED (probe, default ResolveConfig, max_depth=100) on 'rule Deep(x: ?x) :- Deep(x: ?x)': resolve_with_stats -> 0 solutions, truncated=true, errors=[]; resolve_lazy + split_first -> Ok(None); interpreter 'splitFirst(execute(kb(), pattern_query(...)))' -> none(). The host bridge and the Relation face go through the same door (not separately probed). A consumer therefore reads 'no more answers' as a refutation - the WI-628 hole on the lazy faces - and a Relation's isEmpty / negate reads it as non-membership.

THE DESIGN QUESTION IS THE WORK, not the plumbing: (1) WHERE it is reported - at the exhaustion exit only, since rows yielded before the cap are true answers and only the 'that was all' claim is false; (2) WHAT it is - not a fault (nothing is wrong with any goal) and not a Solution variant (it is not an answer), so probably its own arm on split_first's Err (e.g. a SearchFault variant or a sibling type) and its own ResolveStreamFailure variant (e.g. search_truncated(depth)) on execute's row, which is a declared-payload change that ripples to callers the way Error[ResolveStreamFailure] did; (3) whether a consumer that wants the partial set can opt out (a raised config, or reading the rows before the end).

WHAT NOT TO BREAK: drain_verdict / drain_all step the stream themselves and must keep their three-way verdict; a truncation inside a NAF sub-search already taints the outer 'truncated' and must not become a raise on a decided outer answer (the faults-vs-errors lesson from 8Y5BE applies to 'truncated' too).

ACCEPTANCE: the Deep fixture above, drained lazily through split_first, execute (interpreter and host bridge) and a Relation, reports truncation rather than an ordinary end; a search that yields rows and then truncates hands out those rows first; a CONTROL whose recursion terminates below max_depth still ends Ok(None); an eager consumer (not(P) over a truncated P) is unchanged; cargo-test green via scripts/test.sh.

