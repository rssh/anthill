## Attributes

- id: WI-20261115-TFPME-proposal-010-1-stage-4a-docs
- created: 2026-11-15T06:33:23Z

- status: Open
- status_agent: claude
- status_at: 2026-11-15T06:33:23Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261105-CBRD2-proposal-073-stage-4-no-typed

- tags: proposal-010.1

## Description

Proposal 010.1, stage 4a (docs/proposals/010.1-query-interfaces.md §4 Q4): the shell's query is one goal. MEASURED on 8cd01f21: anthill query -p bank.anthill 'account(?id, ?o, ?b), gt(?b, 1000)' is a syntax error, and so is the same line in a --query-file (each fact there is a query of its own), where the test harness's common::query_goals types several goals together through convert_query_terms. Give the shell a conjunction whose goals are typed together, and the bracket introducer of a typed query (010.1 §3.2: [A] ?a: A, ?b: A, PartialEq[T = A], ?a = ?b, A a named slot filled by the types the query fixes). The surface is decided with the user first: how a pattern separates its goals, and how the introducer is written in --pattern and in a query file. ACCEPTANCE: the conjunction above answers bob and cyd; the introducer's program is refused where A is left open and answers at a bracket that fixes it.

