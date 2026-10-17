## Attributes

- id: WI-20261017-WPBXQ-072-constructor-contracts
- created: 2026-10-17T12:46:38Z

- status: Open
- status_agent: claude
- status_at: 2026-10-17T12:46:38Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-037

## Description

072: CONSTRUCTOR CONTRACTS, requires AND ensures ON AN ENTITY DECLARATION — the implementation of docs/proposals/072-constructor-contracts.md, acceptance rows 1-4 (row 5, the memory half, is 037 step 6's ticket). Filed at WI-20261017-T34HP's delivery, by the user's decision (2026-10-17; docs/design/037-implementation.md D6, §2.7). THE CHANGE: (1) Grammar, in both parsers: an EntityClause* after an entity's field list ('requires' Goal, Goal* | 'ensures' RuleBody) — tree-sitter-anthill/grammar.js entity_declaration (742) with corpus rows, and the Scala parser's entityDecl (scaland/core/src/main/scala/anthill/parse/AnthillParser.scala:2668). (2) Loader: the clauses stored with the entity, as an operation's are, and <entity>.result declared per entity (proposal 041's binder). A spec requirement written on an entity is refused, naming the sort-level form (072 §1). (3) Typer: a construction call's requires proved from Γ through the call-site contract machinery (WI-539); the implicit ensures (each requires item with its fields read off result) added to Γ after a construction call, beside assume_call_ensures (kb/typing/effects.rs:1691), which reads only an operation's ensures today; a fact's ground term checked against its entity's requires (a ground refutation is a load error, an undetermined one floats, WI-557/WI-602); the explicit ensures assumed at a construction call, at a pattern matching the entity, and for any value of a sort all of whose entities declare it (072 §3). (4) Spec: kernel-language §5.2's entity grammar and §5.4's paragraph on constructors as calls, the wording agreed with the user first. ACCEPTANCE: 072's rows 1-4, each driving the capability: an unproved construction precondition refused and the proved one building the value; a fact refuting its entity's precondition refused, a satisfying one loading; a spec requirement on an entity refused; 072 §2's use loading, and refused at half_of(m) once positive's requires is removed.

