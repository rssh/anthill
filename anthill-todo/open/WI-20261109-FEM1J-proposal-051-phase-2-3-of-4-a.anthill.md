## Attributes

- id: WI-20261109-FEM1J-proposal-051-phase-2-3-of-4-a
- created: 2026-11-09T14:15:49Z

- status: Open
- status_agent: claude
- status_at: 2026-11-09T14:15:49Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261109-5BP39-proposal-051-phase-2-2-of-4

- tags: proposal-051

## Description

PROPOSAL 051 PHASE 2 (3 of 4) — A COMPOSITE'S DERIVED `eq` COMPARES FIELD BY FIELD, EACH FIELD THROUGH ITS TYPE'S `eq` (decided with the user 2026-11-09; 051 amended, the text agreed with the user first). MEASURED on 4067661d, `Pt` providing `PartialEq`/`Eq` with `eq` comparing `x` only, `sort Box { entity box(p: Pt) }`: in an operation body `PartialEq.eq(pt(1, 2), pt(1, 9))` is true, `PartialEq.eq(box(p: pt(1, 2)), box(p: pt(1, 9)))` false and `PartialEq.eq(some(pt(1, 2)), some(pt(1, 9)))` false; in a rule body the last two are UNDECIDED (residual `eq(box(…), box(…))`). The derivation (WI-664/WI-1098, conditional for a parametric sort, WI-20260918-CKD4J) records the provision only, and the host's structural compare does the comparing; kernel-language §8.3 says a nested own `eq` suspends the comparison, and the interpreter's `semantic_equal` doc calls the recursive descent a WI-625 follow-up. WANTED: both are true in both bodies. A composite with no `eq` of its own gets a derived member that compares its constructor and then each field through the `eq` its field type supplies — pinned at a known field type (`Box.p` -> `Pt.eq`), through the parameter's dictionary for a parametric sort (`Option[T]` under `provides PartialEq[Option] :- PartialEq[T]`, so `some(pt(…))` reaches `Pt.eq` through `T`'s dictionary); a recursive composite (`node(l: Tree, r: Tree)`) is one member calling itself. The field-wise `Float` walk (WI-664's `composite_field_wise_eq`) is this rule at a `Float` field and goes with it. A composite whose fields all compare by structure may run the structural compare as its member — the same answer, not a fallback. A field whose equality nothing decides (a function) still derives nothing (§8.3). SPEC: §8.3's sentences on a buried own `eq` and on structural equality being a composite's instance rewritten. ACCEPTANCE: the `Box` and `Option` programs above answer true in both bodies and as typed goals, an apart pair false; a `List[T = Pt]`, a recursive tree and a `Pair` holding a `Pt`; `some(nan)` vs `some(nan)` stays false and `some(TotalFloat(nan))` equals itself; `Set[Set[Int64]]` keeps its membership answers; each part backed out alone failing the rows its header names; full workspace green via rustland/scripts/test.sh; families green on both carriers.

