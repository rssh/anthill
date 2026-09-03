## Attributes

- id: WI-20260903-FCZ3N-a-simp-rule-s-rhs-is-re
- created: 2026-09-03T05:43:27Z

- status: Open
- status_agent: user
- status_at: 2026-09-03T05:43:27Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `[simp]` RULE'S RHS IS RE-DERIVED FROM ITS TERM, SO A CITATION SPLICED BY A FIRE LOSES ITS PROVENANCE AND ITS SPAN.

THE THIRD TERM->OCCURRENCE ROUND-TRIP. WI-20260902-2SZ88 removed one (entity constructors) and WI-20260902-2NXAC removed another (collection literals), both by building the occurrence where the PARSE NODE is instead of re-deriving it from the KB term. `simp_rewrite::subst_visit` is the same shape in a different walk: it resolves a fired rule's RHS from a TERM (`kb.walk_view(term, subst)`) and rebuilds each node with `NodeOccurrence::synthesized_expr`.

MEASURED, on the delivered 2NXAC tree — `rule trig(?x) <=> sink(zzsimp.inner.rel) [simp]` beside `rule rel(1) :- base(1)`:

  simp rule WITH `operation consumer() -> Int64 = trig(5)`   -> 3 errors, ALL at ONE offset:
      "type mismatch in zzsimp.name: expected resolved name, got unresolved"
      "type mismatch in inner.name:  …"
      "type mismatch in rel.name:    …"
  simp rule with NO consumer                                 -> 0   (so all three come from the FIRE)
  the same expression written directly in an OPERATION body  -> 1, the true one
  the same expression written directly in a RULE body        -> 1
  a ONE-SEGMENT citation in the same simp fire               -> 1   (so the fire does not lose name resolution in general)

TWO LOSSES IN ONE. The three errors are the per-leaf cascade WI-20260902-4NEKZ removed, back because the spliced node arrives with `dot_chain` clear — `loader_chain_dotted_name`'s provenance gate then refuses to read the chain as the name it cites. And they are reported AT THE REDEX (`trig(5)`), where the name `zzsimp.inner.rel` does not appear, because the rebuilt node takes the redex's span.

THE FIX IS NOT `synthesized_expr`. That constructor hardcodes `dot_chain: false` DELIBERATELY and its doc says why: a SYNTHESIS is a new node a pass decided to build — the typer's own `field_access(recv, "field")` rewrite is the case — and it is not the dot the author wrote even when it expands one. Flipping it would re-admit exactly WI-20260901-92VA4's silent acceptance by another door.

THE FIX IS FOR A `[simp]` RULE TO KEEP ITS RHS OCCURRENCE. The RHS was written by an author and loaded as an occurrence with the bit and the span already correct; the rule stores a TERM and `subst_visit` rebuilds occurrences from it. `subst_visit` already has the right instinct in one arm — `Value::Node(occ) => results.push(occ)` reuses a MATCHED child and keeps its identity and provenance — so the shape of the answer exists; what is missing is the RHS's own occurrence being available to reuse the same way.

START BY SETTLING WHERE THE RHS OCCURRENCE WOULD LIVE: the rule already carries body nodes (`KnowledgeBase::rule_body_nodes`), so the question is whether an equational rule's RHS is among them or only in the term, and what `subst_visit`'s callers would have to thread.

ACCEPTANCE. `rule trig(?x) <=> sink(ns.inner.rel) [simp]` with a consumer reports ONE error, naming the relation it cites and located at the NAME rather than at the redex — with the four controls above unchanged (0 with no consumer; 1 for each direct spelling; 1 for the one-segment citation). Say which rows fail when the change is backed out.

RELATED, SAME CLASS, ALREADY SETTLED: `substitute_occurrence`'s five explicit arms had the mirror defect and were repaired in 2NXAC by building with `rebuilt_expr`. That measured 0 of 16 chain nodes actually losing the bit (a citation has no substitutable child) — do not assume this one is inert on that basis. It is NOT: the rows above are the measurement.

Split out of WI-20260902-2NXAC, whose findings (1) (2) (3) are delivered.

