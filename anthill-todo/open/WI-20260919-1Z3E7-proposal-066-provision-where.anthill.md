## Attributes

- id: WI-20260919-1Z3E7-proposal-066-provision-where
- created: 2026-09-19T17:23:22Z

- status: Open
- status_agent: user
- status_at: 2026-09-19T17:23:22Z

- acceptance: cargo-test, scaland-sbt-test

- tags: modinst

## Description

PROPOSAL 066: PROVISION `where` BLOCKS — a conditional provision's `:- goals` are in scope only for the operations written inside its block. Today every body of a carrier is type-checked as if every provision's conditions were sort-level `requires` (the per-sort `provider_dict_chain` becomes each body's enclosing scope). So a non-member body can use a condition it does not own, and the condition silently becomes that operation's requirement, charged to every caller. MEASURED (CKD4J, 2026-09-19): `sort Box3 { … provides PartialEq[Box3] :- PartialEq[T]; operation inner(b, c) = … eq(x, y) … }` loads, and `Box3.inner(box3(v: fe(1.5)), …)` is then refused with 'requirement `PartialEq[T = FE]` of `Box3` cannot be supplied for call to `Box3.inner`', a requirement stated in no definition. Neither place for the requirement works: on the operation it breaks conformance to the spec signature, and inferring membership leaves the body reading evidence it never states. So the requirement lives on the provision, and its members are written inside it. SYNTAX (user decision): `provides X[S] :- g1, …, gn where … end` or `where { … }`, the two forms of a sort body; the block holds operations only; the one-line clause stays for a provision with no members (CKD4J's derived structural Eq rows). SCOPE: grammar + corpus tests; Rust IR/convert (`ProvidesClause` members); loader (block ops are ordinary carrier ops, with operation → provision clause recorded); typer (a per-body mask over the sort half's condition slots, indices unchanged, auditing the ~18 readers of a body's enclosing requires: resolution skips masked slots, frame forwarding keeps them); scaland parser/converter (it loads the embedded stdlib); migrate pair.anthill (`eq` → PartialEq block, `compare` → WeakOrd block); kernel-language.md §8.7 + 058 §3.8/§4. OPEN, measure first: `Pair.compare` is dispatched through both WeakOrd and Ord — is its WeakOrd[A] slot filled from Ord[A] when dispatched through Ord, or must it sit in both blocks? ACCEPTANCE, driven: a block member reads its condition and answers; a non-member using the condition is a LOAD error (control: it loads today); a sibling block's condition is invisible; both body forms parse; Pair's eq/compare still answer (wi858/wi869 green); cargo-test + scaland testFull green. REF: docs/proposals/066-provision-member-blocks.md; WI-869; WI-822.

