## Attributes

- id: WI-20261115-JQ0DG-proposal-010-1-stage-4b-docs
- created: 2026-11-15T06:33:39Z

- status: Open
- status_agent: claude
- status_at: 2026-11-15T06:33:39Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-010.1

## Description

Proposal 010.1, stage 4b (docs/proposals/010.1-query-interfaces.md §4 Q5, Q6): LogicalQuery's limited, projected, quantifiers and aggregations. MEASURED on 8cd01f21 (kb/execute.rs, lower_query_with): limited(q, n) and projected(q, vars) lower to q and drop the count and the projection ('the caller is responsible'), a silent skip; forall_q, some_q, one_q, lone_q, no_q, count_q, sum_q, min_q and max_q are refused as not implemented (pending WI-048). FIRST STEP: limited and projected refused loudly (unsupported_operation) until they are honoured, a row asserting each refusal. THEN, decided with the user: honour them in execute and implement the quantifiers and aggregations, or remove them from LogicalQuery in favour of stream and relation operations (010 R4: aggregation is stream operations).

