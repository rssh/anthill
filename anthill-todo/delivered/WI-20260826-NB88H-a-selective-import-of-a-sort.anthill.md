## Attributes

- id: WI-20260826-NB88H-a-selective-import-of-a-sort
- created: 2026-08-26T06:04:06Z

- status: Delivered
- status_agent: user
- status_at: 2026-08-26T09:59:23Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a SELECTIVE IMPORT of a sort member over-hits: `import anthill.prelude.Numeric.{List}` binds a SIBLING of Numeric and `…{lt}` binds a member reached only by `requires` — strategy 2 is a full scope walk, so it resolves names the path does not name

## Changes

### 2026-08-26T06:04:35Z — feedback — claude

MEASURED while delivering WI-20260825-X9RRN, as the CONTROL that decided that ticket's design — so the two are related by evidence, not just by topic.

DRIVEN on the delivered tree, both loading clean:

  import anthill.prelude.Numeric.{List}   -> LOADS.  `List` is a SIBLING of `Numeric` in
                                            `anthill.prelude`; the path names `Numeric`
                                            and binds something `Numeric` does not have.
  import anthill.prelude.Numeric.{lt}     -> LOADS.  `lt` is `PartialOrd`'s, reached only
                                            because `Numeric requires PartialOrd[T]`.
  import lib.Cell.{zug}                   -> refused, and so is the qualified twin — the
                                            control that says the over-hit is about the
                                            EDGE KIND and not about imports generally.

THE MECHANISM, LOCATED. `load::process_imports`' `ImportKind::Selective` resolves each name by three strategies; strategy 2 is `resolve_in_scope(short, base_scope)` — a FULL scope walk from the sort's own scope. That walk crosses every parent link and re-enters the enclosing chain, and `requires`, `provides` and the enclosing edge are all `is_enclosing: false` links off the same scope. So the import reaches whatever the SORT can see, where the author wrote a path naming what the sort HAS.

WHY IT SURFACED HERE. X9RRN had to decide whether the qualified spelling `Numeric.add(a, b)` should be repaired by copying this walk. It was not: the qualified rung (`load::dotted_by_provision`) follows `ImportOrigin::Provision` edges only, joining `by_qualified_name` per provided sort, so a sort answers with what it DECLARES. `wi_x9rrn_provided_member_address_test::the_qualified_population_is_contained_in_the_member_imports` asserts the containment and names both witnesses above — so if this ticket narrows the import, that row is what tells you, and it is written to fail loudly rather than to silently agree.

NOT A SILENT DEFECT IN THE OBVIOUS DIRECTION, which is why it is a ticket and not a stop-ship: the import binds a name the author did write down (`List`, `lt`), and using it then works. The hazard is the WI-751 one — `Numeric.{List}` is a legitimate-looking line that documents a membership that does not exist, and the day `anthill.prelude` gains a `Numeric`-shadowing sibling the same line silently binds something else. kernel-language.md §8.6's own lead sentence is the rule it breaks: "`import` introduces visibility into the current scope; it does not by itself add a sort's contents — use `requires` or wildcard for that."

WHAT TO DECIDE: whether strategy 2 should ask a narrower question. The pieces exist — WI-20260825-N2865 added `ImportOrigin::Provision` and X9RRN added `SymbolTable::provision_parents`, so declaration-vs-conversion-vs-requires is finally separable at an edge. The obvious narrowing is "own locals plus provision edges", i.e. exactly `dotted_by_provision`'s population, which would make the two spellings agree outright.

CENSUS FIRST, and it is the reason this is not inline: `import <Sort>.{member}` is written ~43 times for `anthill.prelude.Numeric.{add, sub, mul, neg}` alone plus every `Ord.{gte}`-shaped site, and `load.rs`'s WI-1110 comment records that the `provides` link exists precisely BECAUSE `import anthill.prelude.Ord.{gte}` stopped resolving without it. So the narrowing must be measured against the whole corpus before it is written; a refusal here fails at the IMPORT line, which is loud but is a migration.

### 2026-08-26T09:59:19Z — feedback — user

DELIVERED as WI-1089'S RULE AT THE SITE THAT NEVER APPLIED IT, not as the "obvious narrowing" the ticket proposed. `SymbolTable::resolve_below_import` enters the ordinary walk with `EnclosingLinks::StoppedByImport`, and strategy 2 calls it; the stop is a PATH property, so it also holds past a `requires` hop.

WHY NOT "own locals plus provision edges". WI-1089's own doc on `EnclosingLinks` already states the other half as a rule: "a `requires`, a variant exposure and the imported scope's own imports are contents of the thing imported, and stay reachable". Converging the import onto `dotted_by_provision`'s population would REVERSE that sentence and void WI-1110's load-bearing note, not merely narrow a walk. The user took that call after the census; the two readings are recorded at `resolve_below_import` and at `dotted_by_provision` so the next reader does not re-derive them.

CENSUS, and it decided the shape. Instrumented strategy 2, loaded the corpus and the full fixture suite; the hits separate into four classes with no crossings:
  A  11 rows  namespace base, member of a nested sort   -> strategy 3's job, `NESTED-SAME`
  B   6 rows  `provides`  (Eq.{eq,neq}, Numeric.{add,sub,mul}, Ord.{max})
  C   4 rows  `requires`  (Ord.{gt,gte,lt,lte} -> PartialOrd)   ~55 sites
  D   2 rows  SIBLING via the enclosing chain (Type.{TypeBinding}, Pair.{Pair})
Class D is the headline defect and is closed. Class C is untouched and is the ticket's OTHER witness (`Numeric.{lt}`), left standing deliberately.

MIGRATION, measured rather than grepped: pre- and post-change binaries were both run over all 390 distinct `import anthill.*.{name}` pairs in the tree and the refusal sets diffed. Exactly 6 newly refused, 3 of which are only doc prose. Eight live lines, six files: main.anthill (Option/Pair), wi009 (Pair), wi732 (Relation.{Project}), wi734 x3 (Relation.{Concat,Without}), wi_x9rrn (algebra.{Field} -- the fixture was reaching `anthill.prelude.Field` through the chain), typing_pass_spec (Type.{TypeBinding}). The last three the census did NOT predict; the suite found them, which is why the fixture population is part of the census and not an afterthought.

CONTROLS RUN, not asserted. rustland: back out `resolve_below_import` -> 4 rows fail, 5 controls pass. A SECOND back-out separates this from a weaker repair -- stop the enclosing link at the ENTRY scope only -> 3 rows fail (I first wrote "only one" in the doc; measured, corrected). `the_stop_survives_a_requires_hop` uses a target reachable ONLY out through the `requires` target's own namespace, which is the row that distinguishes them. scaland: 2 fail, 2 controls pass.

DOCS: kernel-language.md 8.6 gains "The selective form's own resolution obeys it"; the selective bullet no longer says `resolve_in_scope`; the X9RRN containment paragraph now says ONE edge kind, not two. Three in-code passages that cited `Numeric.{List}` as live were moved to the past tense rather than deleted -- they are the MEASUREMENT that chose `dotted_by_provision`'s filter.

The X9RRN containment test was written to fail loudly if this ticket narrowed the import. It did; `Numeric.List` moved from its "import is strictly wider" list to a new "both spellings refuse it" list.

FROM /code-review ON THIS DIFF, both fixed inline (mechanism already existed nearby in each case, so neither warranted a ticket):
  1. `type_admissible` (load.rs, XFTC7) asked `kind_of` -- `primary_kind`, whose own doc says DISPLAY-only -- where `has_kind` is the membership test. Source order therefore decided: a `Base` declaring both `operation Inner()` and `sort Inner` refused `Base.Inner` as a type with the operation first and accepted it with the sort first. Byte-identical programs, two verdicts, and a regression against pre-XFTC7. An operation-only member still mints no type.
  2. A variant reaching a constructor field through a TYPE PARAMETER was uninhabitable (JSFHG): the hint reads the DECLARED field type, a type var for `entity box(v: T)`. `variant_field_expected_from_ctor` instantiates against the expected type first, sharing the unify+walk `tuple_field_expected_from_ctor` already performed. JSFHG's header records it as CLOSED rather than as a third known gap.
A third finding was mine: the new test's positive controls filtered errors to "unresolved import", so they were green on any other load failure -- the "it loads clean" evidence this repo refuses. They now demand a wholly clean load, and the driven value asserts `Int(30)` exactly rather than a substring that `Int(300)` satisfies.

ACCEPTANCE: rustland 5782 passed / 0 failed (36 binaries; baseline 5771). scaland 518 passed / 0 failed. Commit 3c0656ec.

