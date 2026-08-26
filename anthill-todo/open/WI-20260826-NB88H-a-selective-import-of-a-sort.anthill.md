## Attributes

- id: WI-20260826-NB88H-a-selective-import-of-a-sort
- created: 2026-08-26T06:04:06Z

- status: Open
- status_agent: user
- status_at: 2026-08-26T06:04:06Z

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

