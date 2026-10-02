## Attributes

- id: WI-20260930-K5KQ9-the-effectexpression
- created: 2026-09-30T12:27:49Z

- status: Open
- status_agent: user
- status_at: 2026-09-30T12:27:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE `EffectExpression` CONSTRUCTORS ARE CLASSIFIED BY NAME IN SEVERAL PLACES THAT CAN DRIFT APART. typing/projection.rs `effect_expr_form` strips the `anthill.prelude.EffectExpression.` prefix and matches merge/present/absent/guarded/open; persistence/print.rs `collect_effect_atoms` matches the full qualified names and ends in a silent `_ => {}`; term_view.rs keys `EffectExprNode` through its own tables (`("guarded", 2)`, `&["label", "guard"]`); the occurrence builders and the lowering spell the forms again. A constructor added to `EffectExpression` would be refused by the projection elimination (it falls to the application arm, which refuses a head that is not a sort), dropped by the term printer without a word, and unknown to the view. FIX: one owner — the forms decoded once from their symbols (as the `TypeExtractor` functors are), every reader exhaustive over the decoded kind, an unknown constructor a loud error. FOUND by WI-20260929-0RP29's second /code-review. ACCEPTANCE: one classification site with every reader exhaustive over it (the printer's silent arm gone); full workspace green via rustland/scripts/test.sh.

