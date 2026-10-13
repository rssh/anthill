## Attributes

- id: WI-20261013-GGXCX-068-c1a-design-the-clause
- created: 2026-10-13T08:02:58Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:02:58Z

- acceptance: cargo-test

- tags: proposal-068, typing

## Description

068 C1a — DESIGN: THE CLAUSE ENVIRONMENT AND HOW FAR DATA IS TYPED. Part 1 of WI-20260926-7D48J; no code. DECIDE with the user, and write into docs/design/068-implementation.md §6 and docs/design/requirement-channel.md: (1) the clause environment — rule variables typed by unification across goals, both sides of `<=>` and constructor result types, tied to the enclosing sort's parameters (a rule sees its sort's `requires` — user, 2026-09-25, on P7VP4); (2) how far data is typed — what 068 §1's 'never types those' becomes, answering WI-1058's three reasons (lost expectation, lost scope, rewriting) for each data position admitted; (3) which new load errors 068 §3 brings, counted from ACG10's census (068-implementation §1.2); (4) the binder-form case of 7D48J's 2026-10-11 note: with equations off under a lambda, an operation whose only definition is its equation has nothing to run when the lambda is applied, where its operation-body twin runs. Decision 3 of 7D48J (one classification per call) is designed in its own part, C1d. ACCEPTANCE: the four decisions written and agreed with the user, and the rows each later part owes named there.

