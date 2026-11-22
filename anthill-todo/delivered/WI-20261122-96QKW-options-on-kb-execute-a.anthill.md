## Attributes

- id: WI-20261122-96QKW-options-on-kb-execute-a
- created: 2026-11-22T15:13:49Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-22T15:45:48Z

- acceptance: cargo-test, scaland-sbt-test

## Description

Options on KB.execute: a resolution budget the caller sets (max_depth, max_steps), and the search's statistics
WHO NEEDS IT. anthill-traces (a tool outside this repository; design: its docs/design/high-level-design.md §4.4) evaluates operation contracts on ground values through KB.execute's Rust face, execute_typed_logical_query: a walker turns OperationInfo.requires/ensures into goal terms with the values substituted, and the typed query decides them. Measured 2026-11-22 on 53b1eb32c: holding and violated cases of the shop's cancelOrder, addToCart, releaseCartReservations and checkout all come out definite. The one thing it cannot do is choose the search's budget.

WHAT IS THERE TODAY (read from the code on 2026-11-22). KB.execute(kb, query) (stdlib/anthill/reflect/reflect.anthill:865) -> host builtin kb_execute (eval/builtins.rs) -> KnowledgeBase::execute_typed_logical_query (kb/execute.rs): lower_query, type_query_goals, then resolve_lazy(&goals, &execute_config()), where execute_config() is ResolveConfig::default() with dedup_answers: false — max_depth 100, max_steps 10 000 000, for every caller. The SearchStream it returns has split_first and is_empty; its ResolveStats (steps, goals_asked, truncated, out_of_fuel) are private (drain_all is private, and resolve_with_stats, which returns them, takes goals nobody has typed). The interpreter has no budget setting: in eval/, max_depth and max_steps appear only where a limit that was hit is reported (search_truncated(depth | steps)).

WHY THE DEFAULTS DO NOT FIT (measured, release build). (1) Depth: a membership relation written as a recursive rule over the cons spine (one clause opened per element) needs depth k to find the k-th element of a list and n + 1 to miss in a list of n. At 100 entities per kind, 6 of 9 contract checks ended truncated at depth 100; the 8 of them rerun at depth 250 (through the text path, whose config can be set) were all definite. (2) Fuel: a check that cannot finish runs the full 10 M steps, about 140 s; a checker over a trace of many steps wants a small budget and a fast 'undecided'. (3) Without the statistics the caller can neither report what a check cost nor tune its budget.

WHAT IS ASKED.
- Rust: a variant of execute_typed_logical_query that takes the caller's ResolveConfig (name open, e.g. execute_typed_logical_query_with(q, &config)). execute_typed_logical_query stays, calling it with execute_config().
- SearchStream: a public read of its ResolveStats at any point of the pull (e.g. fn stats(&self) -> &ResolveStats), so a consumer that stops at the first definite solution still gets the steps and the truncation cause.
- anthill: KB.execute with options — at least maxDepth and maxSteps, a field left out keeping the default (e.g. an ExecuteOptions entity of Option fields, or a second operation). A limit hit stays search_truncated(depth(n) | steps(n)), naming the caller's limit.
- dedup_answers is not exposed: KB.execute keeps its bag semantics (proposal 052).

WHAT IS NOT ASKED. Changing the defaults; a budget for Relation.splitFirst or for the relations an operation body drains (they keep execute_config()); an option to commit to the first proof of a ground goal (also measured by anthill-traces, recorded on WI-20261122-3QJ36 — a separate question). This is the budget half of WI-20261122-3QJ36 as that item is narrowed by the spike's feedback there.

DONE WHEN. A test drives the Rust variant on a query over a recursive membership rule and a ground list of 150 elements, with a holding and a failing goal: at the default config both end truncated at depth 100; with max_depth 200 both are definite, and the stream's stats report steps and truncated (true for the default runs). A test drives KB.execute from anthill code with maxDepth to the same outcomes, and one with a small maxSteps ends search_truncated(steps(n)) with the caller's n.

## Changes

### 2026-11-22T15:45:46Z — feedback — user

Implemented 2026-11-22 (uncommitted at the time of writing). Rust: KnowledgeBase::execute_typed_logical_query_with(q, &ExecuteOptions { max_depth, max_steps }) in kb/execute.rs; execute_typed_logical_query calls it at ExecuteOptions::default(). DEVIATION from the ask: it takes kb::execute::ExecuteOptions, the budget alone, not a ResolveConfig, because a config built the usual way (..ResolveConfig::default()) has dedup_answers on and would silently turn the bag of proofs into a set; this keeps dedup_answers unexposed on the Rust face too. SearchStream gains next_solution(&mut self, kb), split_first's pull without consuming the stream, and stats(&self) -> ResolveStats, an owned snapshot with truncated / out_of_fuel / errors as they stand; split_first and drain_all are built on them. Without the non-consuming pull the stats would be lost at the end, where split_first consumes the stream. anthill: entity anthill.reflect.ExecuteOptions(max_depth: Option[T = Int64], max_steps: Option[T = Int64]) and KB.execute_with(kb, query, options), host kb_execute_with; none() keeps the default; a limit hit is search_truncated naming the caller's limit; a limit below 0 is malformed_query (ExecuteOptions::from_limits, the one rule both faces read). The anthill-stl bridge implements execute_with too (the generated KB trait gains it; ExecuteOptions added to build.rs emit_only). Measured depth semantics: the query goal is depth 0, so over a list of 150 the last element is found at max_depth 149 and a miss is refuted at 150 (the description's k / n + 1 is one too high). Tests: anthill-core tests/include/wi_96qkw_execute_options_test.rs (8 rows, back-out ledger in its header) and anthill-stl bridge execute_with_runs_at_the_callers_budget. Gate: scripts/test.sh, 12 556 passed, 0 failed; scaland testFull 811 + 51 + 1 passed.

