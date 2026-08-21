## Attributes

- id: WI-20260821-TTHRK-a-rule-head-inside-a-provides
- created: 2026-08-21T07:53:20Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T07:53:20Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RULE HEAD INSIDE A `provides ... language ... end` BLOCK IS INVISIBLE TO THE SCAN, so
it is neither scoped nor refused -- and WI-980's two guards both miss it.

MEASURED (rustland, WI-980's tree). Two unrelated namespaces, each with a sort and a
`provides <Carrier> language rust ... rule pcap(N) ... end` block, N = 1 and 2:
`anthill check` reports nothing, `query "pcap(?x)"` answers BOTH 1 and 2 -- one shared
uncitable symbol -- and `nsA.pcap` does not resolve. CONTROL: with only one namespace
present, `pcap(?x)` answers 1. Reported by /code-review against WI-980.

MECHANISM: `RuleHeadCollectPass::at_item` (sub-pass 3) matches `Item::Rule` and
`Item::RuleBlock`; `Item::ProvidesBlock` falls into the `_ => {}` arm, so
`ProvidesItem::Rule` / `ProvidesItem::RuleBlock` never become `RuleHeadSite`s. The LOAD
phase still loads them (`load_provides_block` -> `load_rule`), so the clause is stored --
under `remap_name_str`'s bare `intern(name)`, WI-894's one global name.

WHY IT IS NOT A MISSING MATCH ARM. The scope is the problem, not the walk. A provides
block's rules load into `kb.symbols.scope_id(spec_domain)`, where `spec_domain` is
resolved BY THE LOAD PHASE from the block's `TypeExpr` (`load_provides_block`,
kb/load.rs). Sub-pass 3 has no such scope and no resolved spec term. Adding the arm means
answering WHICH scope a provides-block head is written in, at scan time.

THREE CANDIDATE ANSWERS, and picking one is the ticket:
 (a) Resolve the spec domain in the scan. Correct-looking and the most dangerous: it
     duplicates a load-phase resolution, and a second spelling of one question is exactly
     what WI-980 spent its budget undoing (a hand-written twin of the resolver's parent
     walk falsely refused three programs that load clean).
 (b) Refuse a rule head in a provides block that would INTRODUCE, leaving one that names
     something already resolving. Cheap and loud; needs a corpus census first (the stdlib
     realization files carry provides blocks).
 (c) Record the escape and leave it. 059 R3's enforcement site already records that a
     provides block's interior is classified recursively, so the shape is known.

RELATED: 059 R3 classifies the direct content of a secondary entry and recurses into a
host `provides` block's interior, so the classification pass DOES reach these items --
whatever this ticket decides should agree with what pass 1b already does there, and may
be able to reuse its walk rather than mint a third.

ACCEPTANCE depends on the answer chosen. For (a) or (b): two namespaces whose provides
blocks each write a head of one name must NOT share a predicate -- drive both goals and
assert the answers are separate, with the control being today's single shared answer. For
(c): the record goes at the site and in kernel-language.md beside the `<global>` refusal,
which currently reads as though it closes the shape. cargo-test green via
rustland/scripts/test.sh.

