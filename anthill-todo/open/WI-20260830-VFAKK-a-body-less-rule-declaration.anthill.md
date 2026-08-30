## Attributes

- id: WI-20260830-VFAKK-a-body-less-rule-declaration
- created: 2026-08-30T11:55:39Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T11:55:39Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BODY-LESS RULE DECLARATION HAS NO DESCRIPTION TARGET, SO THE ONE CONSTRUCT PROPOSAL 061 ADDED CANNOT BE DOCUMENTED IN THE KB.

MEASURED, both spellings, on `examples/guardians/lib/email.anthill`'s `rule in_org(?a)`:

    {< Which addresses belong to the organisation. >}
    rule in_org(?a)
      -> description block on unlabeled rule has no stable target: descriptions name
         a declaration symbol or citation handle. Add a label where this construct
         permits one, or move the text to a named declaration

    {< ... >}
    rule org_membership: in_org(?a)
      -> the body-less rule `in_org` DECLARES the predicate and stores no clause
         (proposal 061). A citation label on it has nothing to cite.

So §4.1 sends you to the label and 061 sends you back. The 061 diagnostic's own suggestion -- "Add `:- true` to make it an assertion" -- is not available where the declaration's whole point is that it asserts nothing: `in_org(?a) :- true` makes every address internal, which is the safe default inverted.

THIS IS A GAP RATHER THAN A DESIGN CHOICE, and the two refusals were written for different constructs. §4.1's rule is about a CLAUSE: a fact or an unlabeled rule has no stable handle for `DescriptionInfo.target`, and a label gives it a citation handle. 061's rule is about a DECLARATION: a citation label has nothing to cite because no clause is stored. But a 061 declaration DOES have a stable target -- the predicate SYMBOL it brings into existence in scan pass 1, which is exactly the kind of thing every other `DescriptionInfo.target` is (a sort, an operation, an entity). The declaration is the one rule form that names something without storing a clause, and it fell between the two rules.

`kb/load.rs`'s `declaration_clause_carrier` carries a comment stating there is deliberately no `descriptions` arm, on the ground that the case cannot render -- unlabeled the converter refuses first, labeled the label arm answers first. That is accurate about today's code and is the mechanical statement of this gap.

SCOPE. Give a body-less rule declaration a description target of its own: the predicate symbol, with no label required (a label stays refused -- there is still no clause to cite). Touches the converter's §4.1 refusal (which must stop firing for this one item shape) and the loader's declaration path (which must emit `DescriptionInfo` keyed on the declared symbol).

ACCEPTANCE: `{< ... >}` on `rule in_org(?a)` in `examples/guardians/lib/email.anthill` loads, and `the_intent_of_a_declaration_is_a_fact_in_the_kb` (guardians_test.rs) finds `in_org` among the description targets -- that test currently names `in_org` in a comment as the one site it cannot cover, and closing this means moving the name from the comment into the loop. CONTROLS: a description on a body-less rule WITH a label is still refused by 061; a description on an unlabeled BODIED rule is still refused by §4.1; the four sites that work today (`guardians.Text`, `guardians.Message`, `Triage.run`, `Email.send`) still emit theirs.

RECORDED AS: examples/guardians/docs/design/measured.md C12.

