## Attributes

- id: WI-20260830-VFAKK-a-body-less-rule-declaration
- created: 2026-08-30T11:55:39Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-30T21:18:34Z

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

## Changes

### 2026-08-30T21:18:29Z — feedback — user

DELIVERED. A body-less rule declaration now has a description target of its own -- the PREDICATE SYMBOL it declares -- so `{< ... >}` on `rule in_org(?a)` loads and reads back as `DescriptionInfo(target: guardians.in_org, ...)`. `releasable` got the same treatment; both are in `the_intent_of_a_declaration_is_a_fact_in_the_kb`'s list, which is what the ticket's acceptance asked for.

THE SPLIT IS NOT "LABELED OR NOT", and stating it that way is the whole fix. A rule has a description target when it is LABELED (the citation handle) or when it DECLARES (the predicate symbol, minted in scan pass 1 -- the same kind of `DescriptionInfo.target` a sort, an entity or an operation gets). What is left with neither is an unlabeled rule that stores a CLAUSE: a bodied one, the explicit `:- true` assertion, and a body-less EQUATIONAL head, whose clauses index under the connective so its subject declares nothing (WI-898). §4.1 and §5.3 now say that; §5.3's list of what a declaration may not carry lost its `description block` entry and gained the sentence saying why.

WHICH PASS DECIDES, and this was the design question rather than the code. `rule_reading` is the ONE decider of declaration-vs-clause, and it lives in `kb/load.rs`. The converter cannot copy its test -- a second spelling would drift, and the first drift admits a block the loader never emits, which is WI-1072's original silent drop re-entered from the other side. So the converter refuses only what its OWN surface settles, which is `rule_reading`'s literal first line ("a body ⇒ Clause, full stop"), and carries every body-less block to the loader. The loader then leaves no third outcome: `Declaration` emits on the declared symbol, `Clause` refuses, `DeclaresNothing` was already refused. The §4.1 sentence has one owner (`parse::error::description_without_target`) and both passes raise it.

CONSIDERED AND REJECTED: moving `rule_reading` and its six helpers (~400 lines) out of `kb/load.rs` into the parse layer, which is where they belong by dependency (they read only `Rule`/`SymbolTable`/`SimpleTermStore`) and would have let the converter ask the decider directly. Their doc comments carry ~15 intra-doc links to load-private items (`[`scan_rule`]`, `[`rule_head_ladder_answer`]`, `[`Loader::declaration_clause_carrier`]`, ...) which the move breaks silently -- invisible to the compiler AND to the suite. Not worth it for this ticket; the layering note is now written at both sites.

MEASURED -- THREE AXES, THREE DISTINCT FAILING SETS, each neutralized (not deleted) and re-measured against the DELIVERED tree, because the first pass's figures went stale the moment an eighth row was added (/code-review caught it):
  * converter admission (`|| body.is_none()`): `guardians_test` 47 of 47 red -- the example stops PARSING with exactly the two refusals the ticket quotes (`in_org` AND `releasable`) -- and `wi_tests` 5 red / 3914 green. Loudest, least informative: every one of the five panics on the parse failure before reaching an assertion.
  * loader emission: `guardians_test` exactly ONE row red (`the_intent_of_a_declaration_is_a_fact_in_the_kb`), `wi_tests` 3 red / 3916 green, each on its own assertion. THIS is the axis that measures what the ticket added.
  * loader refusal (the `Clause` arm): `guardians_test` 47 green, `wi_tests` 1 red / 3918 green -- `a_bodyless_equation_head_is_refused_at_load` alone, failing by LOADING CLEAN, i.e. with the block SILENTLY DROPPED. That row is what says admitting body-less rules at the converter did not open a hole.

THE POPULATION IS `rule_reading`'s THREE ARMS, not the two the ticket named. `DeclaresNothing` (a qualified or multi-head body-less rule) also now carries a block through the converter; it stays refused by 061 and the block dies with the rule. `a_bodyless_rule_that_declares_nothing_is_still_refused` is that row.

CONTROLS, all green either way: a LABELED declaration is still refused by 061 ("nothing to cite"); an unlabeled BODIED rule's block is still refused by the converter at the block's own span (WI-1072's row, fixture changed from `rule p(1) :- true` to a genuinely bodied rule so the `:- true` case gets its own row); `rule p(1) :- true` -- body-less in intent and the remedy 061's own diagnostic offers -- still reads as a CLAUSE; the four sites that already worked still emit theirs.

ONE THING THE FIX GIVES UP, and it is written at the converter and in measured.md rather than left to be rediscovered: the body-less half's refusal is the LOADER's, so a `ParsedFile` consumer that never loads a KB no longer sees it. MEASURED (found by /code-review): `anthill codegen rust` over `{< ... >} rule twice(?x) <=> ?x` reports `1 file(s), 0 error(s)` where it used to report a parse error, with the bodied control still refused there. A lost DIAGNOSTIC, not a lost fact -- the generators read no `Rule::descriptions`, and `load` / `run` / `check` all still refuse it, located. Buying it back means giving the generator a load pass.

SCALAND: nothing to port. `parse.IR.Rule` has no `descriptions` field and `AnthillParser` skips `{< ... >}` as trivia in its comment lexer, so §4.1 descriptions do not exist on that side at all. `sbt test` is a regression check only.

FILES: `parse/convert.rs` (the carve-out + the shared sentence), `parse/error.rs` (`description_without_target`, one owner), `kb/load.rs` (`LoadError::DescriptionWithoutTarget`, the `Clause` refusal, the `Declaration` emit), `docs/kernel-language.md` (§4.1 x3, §5.3, the `Rule` and `Fact` grammar notes), `examples/guardians/lib/email.anthill`, `examples/guardians/docs/design/measured.md` C12 (defect -> fixed, and the header/table rows that referenced it), `guardians_test.rs`, `wi1072_declaration_description_test.rs`, and the new `wi_vfakk_declaration_description_test.rs` (8 rows).

