## Attributes

- id: WI-20260919-1Z3E7-proposal-066-provision-where
- created: 2026-09-19T17:23:22Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-19T19:49:37Z

- acceptance: cargo-test, scaland-sbt-test

- tags: modinst

## Description

PROPOSAL 066: PROVISION `where` BLOCKS — a conditional provision's `:- goals` are in scope only for the operations written inside its block. Today every body of a carrier is type-checked as if every provision's conditions were sort-level `requires` (the per-sort `provider_dict_chain` becomes each body's enclosing scope). So a non-member body can use a condition it does not own, and the condition silently becomes that operation's requirement, charged to every caller. MEASURED (CKD4J, 2026-09-19): `sort Box3 { … provides PartialEq[Box3] :- PartialEq[T]; operation inner(b, c) = … eq(x, y) … }` loads, and `Box3.inner(box3(v: fe(1.5)), …)` is then refused with 'requirement `PartialEq[T = FE]` of `Box3` cannot be supplied for call to `Box3.inner`', a requirement stated in no definition. Neither place for the requirement works: on the operation it breaks conformance to the spec signature, and inferring membership leaves the body reading evidence it never states. So the requirement lives on the provision, and its members are written inside it. SYNTAX (user decision): `provides X[S] :- g1, …, gn where … end` or `where { … }`, the two forms of a sort body; the block holds operations only; the one-line clause stays for a provision with no members (CKD4J's derived structural Eq rows). SCOPE: grammar + corpus tests; Rust IR/convert (`ProvidesClause` members); loader (block ops are ordinary carrier ops, with operation → provision clause recorded); typer (a per-body mask over the sort half's condition slots, indices unchanged, auditing the ~18 readers of a body's enclosing requires: resolution skips masked slots, frame forwarding keeps them); scaland parser/converter (it loads the embedded stdlib); migrate pair.anthill (`eq` → PartialEq block, `compare` → WeakOrd block); kernel-language.md §8.7 + 058 §3.8/§4. OPEN, measure first: `Pair.compare` is dispatched through both WeakOrd and Ord — is its WeakOrd[A] slot filled from Ord[A] when dispatched through Ord, or must it sit in both blocks? ACCEPTANCE, driven: a block member reads its condition and answers; a non-member using the condition is a LOAD error (control: it loads today); a sibling block's condition is invisible; both body forms parse; Pair's eq/compare still answer (wi858/wi869 green); cargo-test + scaland testFull green. REF: docs/proposals/066-provision-member-blocks.md; WI-869; WI-822.

## Changes

### 2026-09-19T19:49:32Z — feedback — user

DELIVERED (2026-09-19). Commits 30bf7f8c (where blocks: grammar + corpus, converter, loader ProvisionMemberInfo + block-membership check, typer scoping, scaland parser, pair.anthill + wi869/wi1093/nar1x fixtures migrated) and a92a3b9c (066 §7, decided with the user: a dictionary layout per provision — sort-level requires then that provision's conditions; a block member backs only its own provision, the Twin case refused at load; two clauses of one spec are alternatives decided at dispatch, a where block on such a spec refused for now; a same-carrier call into another provision's member builds its dictionary at the call or is a load error; WI-869's strictness mask, NotThisDispatch and 066 §6's hidden mask removed). Open question 1 answered by measurement (Ord declares no op; compare only dispatches as WeakOrd.compare). Recorded direction: blocks as anonymous instances (member identity per clause; two unconditional blocks of one spec = two morphisms). Tests: wi_1z3e7_provision_where_blocks_test (13), wi869 rewritten arms; cargo-test 7178/0, scaland testFull 577+35+1/0.

