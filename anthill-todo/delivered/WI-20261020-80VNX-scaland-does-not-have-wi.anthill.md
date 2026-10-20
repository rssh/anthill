## Attributes

- id: WI-20261020-80VNX-scaland-does-not-have-wi
- created: 2026-10-20T13:56:02Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-20T16:47:03Z

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

## Changes

### 2026-10-20T16:42:52Z — feedback — user

PORTED (not yet committed). Scaland now has JB6RS: (1) THE EPONYMOUS MERGE (WI-926): `sort Foo … entity Foo(…) … end` is ONE symbol, the sort's, playing Entity too — no nested Foo.Foo, no parent edge, no entity_of fact (Loader.eponymousSortSymbol, asked by both passes); the ~45–60 dual-role sites measured during planning came to one row that pinned the old shape. (2) THE FACE BIT: TermSymbol bit 31, `index`/`plain`/`isTypeFace`, typeFace private[anthill]; SymbolTable reads mask it, scopeOf keys the plain owner, addKind/addImport refuse a face. (3) DECL-KEYED TABLES: intern.Decl (built only by Decl.of, which drops the face) keys sortInfo/sortEntities/entityParent/entityFields/constructorSymbols/sortBaseSubst/quotedFields; isConstructorSymbol and isQuotedField answer false for a face; isEntityOf compares declarations (an entity is of its own type; a parent is reached by its face); declaration-table writes refuse a face; KnowledgeBase.typeFaceOf is the one mint (every Entity-kinded declaration). (4) THE READING RULE: the parser admits an empty bracket (instArgsList / parameterizedType at rep(0), the dot-callee bracket stays rep(1) as rustland's dot_application), records a WRITTEN bracket (SimpleTermStore.isTypeApplication) and every name it lowers in a TYPE position (isTypeName: a bracket's binding, an arrow's or tuple's component, an effect label, a ctor[…](…) call-site binding); Loader.reallocTerm heads a bracket by the face and reads a type-position name as the face, a bare constructor elsewhere staying its instance. (5) THE CANON AND THE REFUSAL: every nullary Fn is its bare Ref but the three reflect collection-literal forms by qualified name (a face of one canonicalizes too); makeNameTermFromSym builds the bare Ref; `S(…)` over a name that is only a type (KnowledgeBase.namesOnlyAType) is LoadError.SortAppliedAsData in a fact, a rule head and a rule body, not inside a field declared Term or List/Option of Term (Loader.QuotedFieldPass, after pass 2 — scaland has no typer to read the field type from). (6) kind reports a face as `sort` (KnowledgeBase.reflectKind), extract_sort_ref answers the declaration's name, Facts.instanceNamed (optionArg, ScalaProfile) and smt-gen's isKnownEntity read a face as the type, the parser's diagnostic renderer writes a bracket as one. ROWS: EponymousConstructorTest, kb.TypeFaceTest (4), load.TypeFaceReadingTest (7), smtgen.TypeFacePremiseTest (2), SymbolTableTest (2), ParseTest (2), the shared parity case testdata/parser-parity/wi777/accept/empty_bracket.anthill; 4 rows that pinned the sort exemption and 1 that pinned Long.Long inverted. BACK-OUT: 41 parts, each alone, every one failing a row (scratchpad driver; table at each row's site); four parts that failed none were not kept (the Ident arm's binding face, the refusal's minted-node gate, namesOnlyAType counting Operation/Goal — unreachable in scaland, an operation at a sort's address being a DuplicateDeclaration — and the reflect-form exemption's Sort+Entity condition, which would make () mean two things with and without the stdlib). /code-review: 14 findings, 12 applied, 2 declined (checkDeclarations stays keyed on the declaration as written, §5.1's rule; a general field-type registry has no second consumer). NOT PORTED, no scaland subsystem to port into: the operation-body, typer field-check, query-converter and JSON-store rows; a bare fielded constructor as the all-fields-fresh pattern is WI-20260902-T8H1W; positional = named bracket normalization and the unknown-key refusal are cef5913b's (53W12). Gates: scaland 710 + 47 + 1 (was 694 + 45 + 1); rustland workspace 10,135 passed, 0 failed (with the separate document.rs length-diagnostic fix).

