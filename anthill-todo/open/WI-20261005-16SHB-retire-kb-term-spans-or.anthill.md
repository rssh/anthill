## Attributes

- id: WI-20261005-16SHB-retire-kb-term-spans-or
- created: 2026-10-05T04:51:01Z

- status: Open
- status_agent: user
- status_at: 2026-10-05T04:51:01Z

- acceptance: cargo-test, scaland-sbt-test

## Description

Retire kb.term_spans or justify its last reader: materialize_from_handle's location fallback for runtime-rebuilt nodes.

CONTEXT. WI-753 removed the loader's node -> TermId -> node round trip: every written rule-body node is built from its parse node, and the few nodes a lowering creates with no parse node of their own (an Option wrapper, a written effect row, a list's terminating nil, a bare entity goal, an omitted field's fill) are materialized with an explicit SITE (node_occurrence::materialize_at / materialize_around), which is asked BEFORE kb.term_span. So on the loader's occurrence path kb.term_spans decides no location any more.

WHAT IS LEFT. kb.term_spans (kb/mod.rs, written by the loader's create_occurrence, load.rs ~23779, first-write-wins) has ONE reader: visit_term's fallback in node_occurrence.rs (ctx.site, else kb.term_span(t), else an empty span). It is reached through the bare materialize_from_handle, called at run time on STORED terms by: the evaluator (eval/eval.rs x5, eval/mod.rs), the resolver (resolve.rs ~12788), execute.rs ~755, kb/mod.rs ~3881, typing/expr.rs ~450, and node_occurrence.rs's Value -> node conversions (~5258, ~5282, ~6453). Each node those build is located by a hash-consed key that every structurally identical subterm in the KB shares, filled first-write-wins across files — so a runtime-rebuilt node can be reported at another site's, or another file's, location.

QUESTION TO DECIDE, per caller: where should a node rebuilt at run time from a stored term point? Options: (a) the site of the operation/rule whose stored body it came from (thread a site through, as materialize_at does); (b) nowhere (an empty span, honestly unlocated) and delete kb.term_spans with its writer; (c) keep kb.term_spans for a caller whose term really is one-site (say which and why at that site).

ACCEPTANCE: either kb.term_spans and its writer are deleted, or every remaining reader states at its site why a first-write-wins, hash-consed key is right for it; a test row per changed caller that drives the rebuilt node's location and FAILS when the change is backed out; cargo-test via rustland/scripts/test.sh.

