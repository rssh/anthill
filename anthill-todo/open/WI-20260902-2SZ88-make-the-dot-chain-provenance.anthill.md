## Attributes

- id: WI-20260902-2SZ88-make-the-dot-chain-provenance
- created: 2026-09-02T18:40:24Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T18:40:24Z

- acceptance: cargo-test, scaland-sbt-test

## Description

MAKE THE DOT-CHAIN PROVENANCE ANSWER EXACT: ASK THE PARSE NODE, NOT A HASH-CONSED KEY.

`Loader::parse_dot_chain_table` answers 'is this node a dot the author wrote' from a `HashSet<TermId>` keyed by the HASH-CONSED KB term. That key is MANY-TO-ONE and cannot answer the question: a minted `ns.rel` and a hand-written `anthill.reflect.field_access(ns, rel)` convert to the SAME term — that identity is the entire premise of WI-20260901-92VA4, which is why the bit exists rather than a shape test.

The first cut stamped both, and the written call was silently ACCEPTED and typed as the relation it does not spell. MEASURED, one entity with two Int64 fields, varying ONLY structural identity:

  `boxedc(v: <written call>, w: 1)`                  -> refused (control)
  `boxedc(v: <written call>, w: zz4n.inner.other)`   -> refused (control, distinct TermId)
  `boxedc(v: <written call>, w: zz4n.inner.rel)`     -> **ACCEPTED, typed Relation**

The shipped repair is a SET DIFFERENCE: a kb id is stamped only if EVERY parse node in the atom mapping to it is a citation. That is conservative in the safe direction — never a wrong acceptance — but it is a real weakening: on a collision the bit is WITHHELD where the exact answer is true, so a citation that shares a term with a written call beside it falls back to the per-leaf 'unresolved name' cascade WI-20260902-4NEKZ removed. A user who writes both spellings in one atom gets the worse diagnostic back, silently.

THE EXACT FIX is to carry the PARSE `TermId` beside the KB one through the materializer — `WorkOp::Visit` currently carries only the term id — so `visit_term` can ask `dotted_citation_name` of the node itself instead of looking up a lossy key. Then the bit is exact, the set difference goes away, and `new_expr_dot_chain`'s doc can go back to claiming the safety property it used to claim.

WORTH DOING WITH WI-20260902-2NXAC, NOT BEFORE IT: that ticket lists three MORE readings the same early return drops (CZJ2N's nullary-operation call, proposal-035 form-(3) receiver types, and `substitute_occurrence`'s `Expr::Apply` arm), and threading the parse id is the one change that answers all of them at once. Doing this alone buys back one diagnostic; doing it as the shared substrate fixes four things.

ACCEPTANCE. `a_citation_beside_a_written_field_access_call_does_not_launder_it` keeps passing on all three rows, AND a new row shows the citation in row three getting the ONE true diagnosis rather than the three-segment cascade — that row fails today by design and is the measurement this ticket exists for.

Found by /code-review on the WI-20260902-4NEKZ follow-up, 2026-09-02.

