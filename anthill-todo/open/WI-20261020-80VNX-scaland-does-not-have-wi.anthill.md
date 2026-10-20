## Attributes

- id: WI-20261020-80VNX-scaland-does-not-have-wi
- created: 2026-10-20T13:56:02Z

- status: Open
- status_agent: user
- status_at: 2026-10-20T13:56:02Z

- acceptance: cargo-test, scaland-sbt-test

## Description

SCALAND DOES NOT HAVE WI-20260902-JB6RS: a constructor's TYPE and its INSTANCE are one term there, and a bare name keeps its old reading — port the reading rule rustland landed in 142bf20d..a6615e1d (kernel-language.md §4.4, *A name has a reading in each context*; §6; §8.3).

WHAT DIFFERS TODAY (scaland green at 694 + 45 + 1 because none of its suites loads a fixture JB6RS migrated):
  * the parser refuses an EMPTY bracket: AnthillParser.scala:672 is `sortBinding.rep(1, sep = ",")`, so `WorkItem[]`, `covers: [WorkItem[], …]` and `facts_of(kb(), WorkItem[])` do not parse (rustland: tree-sitter `commaSep`, corpus row test/corpus/empty_bracket.txt);
  * a constructor has no TYPE FACE, so `fact held(Foo[X = Int64])` is found by `:- held(Foo(X: ?v))` and `Baz[]` / `Baz()` are one term (rustland: `Symbol` bit 31, `intern::Decl`, `KnowledgeBase::type_context_face`);
  * a bare constructor in a DATA context is still the reference, not its instance (`p(account)` is `p(account())` in rustland; `?t <=> account` binds the all-fields-fresh pattern), and a bracket's binding is not read as a type in a rule body;
  * in an operation body a free-standing entity's bare name is still the type (rustland: the instance, and a construction must supply every non-`Option` field — `LoadError::IncompleteConstruction`);
  * the nullary canon still exempts a sort (rustland: one term for every name but the three collection-literal reflect forms), and `S(…)` over a sort with no constructor or operation of its name loads (rustland: `LoadError::SortAppliedAsData`, in a clause, a rule body and a query);
  * `kind` of a type face, and a `Type` field through the JSON store, where scaland has them.

FIRST, AND THE REASON THIS IS A BLOCK OF ITS OWN: scaland's eponymous entity is TWO symbols (rustland: one, WI-926), so the face cannot be one bit on one declaration until they are merged. Measured during JB6RS planning: ~45–60 dual-role sites in scaland.

The order rustland took, each a gated commit there, is the plan: the Symbol bit and table masking; Decl-keyed declaration tables; predicates read a face as a type; faces minted by every type producer, the nested population then the eponymous one; the reading flip with the migration; the canon and the `S(…)` refusal. Rows to mirror: rustland/anthill-core/tests/include/wi_jb6rs_type_face_test.rs (12) and kb::jb6rs_type_face_reads_the_declaration_tests.

