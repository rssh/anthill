## Attributes

- id: WI-20260826-XFTC7-a-type-reference-does-not-read
- created: 2026-08-26T05:45:40Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-26T07:24:15Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a TYPE reference does not read the dotted ladder: `Mid.Inner` reached through a `provides` conversion is 'type Mid has no member Inner', while the term and citation positions resolve it — the same spelling with two answers, one reader over from WI-752's

## Changes

### 2026-08-26T05:46:10Z — feedback — user

MEASURED, WITH ITS CONTROL, while delivering WI-20260825-X9RRN — and found by a UNIFORMITY row rather than by reading the code. Adding the provision rung to `resolve_dotted_in_kb`, the natural next step was to extend `wi752_dotted_ladder_test`'s "same spelling, every position" claim to it. Two of the three positions passed and the type one did not:

  sort Base { sort T = ?  sort Inner { entity inner(v: Int64) }  operation f() -> Int64 = 41 }
  sort Mid  { sort T = ?  provides Base[T = T] }

  TERM      `Mid.f()`             -> LOADS and answers 41
  CITATION  `Mid.rel.isEmpty`     -> LOADS and binds the relation (extent {7})
  TYPE      `x: Mid.Inner`        -> "type mismatch in Mid.Inner (entity-field): expected a
                                      well-formed type projection, got type 'probe.tp.Mid'
                                      has no member 'Inner'"
  TYPE      `x: Base.Inner`       -> LOADS                          <- THE CONTROL

So the difference is the CONVERSION and not the spelling, and it is not a hole in the rung: a `Sort.Member` in type position never reaches the dotted ladder at all. It is read as a TYPE PROJECTION by a separate check with its own member table, which is why the message is about projection well-formedness rather than about a name.

WHY X9RRN DID NOT ABSORB IT — a different QUESTION, not the same one at a second site. The ladder answers "what does this dotted NAME denote"; a projection asks "does this TYPE have this member". A spec's `provides` is documented throughout as a VALUE-level conversion — "hold a `Mid[T]` and you can obtain a `Base[T]`", `eq.anthill`, 058 §3.4 — and a dictionary is not a claim that a nested SORT is reachable through it. Answering yes is a type-level inheritance claim the language has not made anywhere else.

WHAT TO DECIDE, and it is the whole ticket: whether a conversion conveys a nested sort. If YES, the type-projection reader gains the same provision hop and the two readers agree; if NO, the asymmetry is a RULE and belongs in kernel-language.md §8.6 beside the rung, because "the term position resolves it and the type position does not" is exactly the position-dependence WI-752 exists to abolish and must not be left as an accident.

THE HAZARD IF IT IS WIDENED, stated so it is not rediscovered: the type-member table is where WI-751's field over-hit lived (`data.user.name` capturing a FIELD through head-qualification), and `resolve_dotted_in_kb`'s `not_a_field` gate is the repair. A second reader gaining a member hop needs its own version of that gate, measured, not inherited by analogy.

NOT SILENT, which is why this is a ticket and not a bug: the refusal names the head and the missing member. The cost is that one spelling has two answers.

PINNED: `wi_x9rrn_provided_member_address_test::the_type_position_reads_a_different_table` asserts BOTH halves — the `Base.Inner` control loads, the `Mid.Inner` refusal fires — so whichever way this is settled, the row fails and has to be updated deliberately. `wi752_dotted_ladder_test::wi752_provided_member_resolves_in_every_position` carries the same finding at its doc, and covers the two ladder positions only.

### 2026-08-26T07:24:11Z — feedback — claude

DELIVERED, AND THE TICKET'S OWN QUESTION DISSOLVED RATHER THAN WAS ANSWERED. It framed the decision as "whether a conversion conveys a nested SORT" — a claim about what a type HAS, which would have belonged in `project_type_member`. Reading the code, that is not the branch involved.

`load::try_rigid_type_projection`'s non-param arm carries its OWN qualified-child lookup:

    let child_qn = format!("{sort_qn}.{member_name}");
    if let Some(&child) = kb.symbols.by_qualified_name.get(&child_qn) { … }

— rung 1 of the dotted ladder written a second time, and it had rung 1's gap. Its own comment states its job: deciding that `Outer.Inner` is "a legitimate qualified CHILD reference, not a projection" — a question about what a NAME denotes, which WI-20260825-X9RRN's ladder already answers the same way in every other position. So the fix is the same `dotted_by_provision` hop, SHARED with the ladder so the two readers cannot drift again, and `project_type_member` is untouched: a name that denotes nothing as a type still reaches it and is still refused. Nothing was added to what a type HAS.

DRIVEN TO A VALUE, not to a load: `operation viaMid(x: Mid.Inner) -> Int64 = x.v` called with `Base.Inner.inner(v: 41)` answers 41, with the declared `Base.Inner` twin answering 7 beside it so a failure names which spelling broke. The head's own child still wins (fixture built so the two readings cannot both accept the program), a diamond is one answer, two provided routes are an ambiguity in BOTH clause orders, and a typo stays loud on both spellings.

TWO PRE-EXISTING HOLES IN THE SAME ARM, both measured on the tree this started from, both closed because leaving a NEW gated path beside an UNGATED sibling is an asymmetry with no reason behind it:

  * `internal` WAS ASKED BY NEITHER READING. A declared `internal sort Inner` cited as `Base.Inner` from another namespace LOADED CLEAN — the same bypass WI-369 closes at `process_imports` and WI-752 at the ladder. Closing it cost the corpus nothing (measured: the whole suite, one failure, and it was the row that had recorded the hole). The MESSAGE is the other half: a hidden child that merely fell through was reported by the projection path as "type 'Base' has no member 'Inner'", telling the author their name denotes nothing when it denotes something they may not see. Both readings now report the forbidden access by name.
  * NO KIND WAS ASKED EITHER — found by /code-review, see below.

/code-review (high) FOUND FOUR, and the two that mattered had one fix:

  1+2. A MEMBER THAT IS NOT A TYPE BECAME ONE. `operation Zero()` on `Base` made `x: Base.Zero` load clean, the nonsense type surfacing only at whatever call site happened to be checked ("expected Zero, got Int64"). The conversion path mirrored it exactly, so the hop widened a hole rather than opening one. TWO CORRECTIONS TO THE REVIEW'S OWN READING, both material: it prescribed reusing the ladder's `not_a_field`, and MEASURED, the symbol its second repro reaches is `SymbolKind::Param`, which `not_a_field` ADMITS — the fix had to be a POSITIVE gate (`Sort | Entity`), which settles Field, Param and Operation at once and is the TYPE position's own question rather than a third copy of the ladder's. That also dissolves the review's 4th finding (a duplicated predicate): there is now ONE predicate here. Its second repro needed an eponymous `sort Foo` beside `operation Foo(X: Int64)` — WI-751's shape, where the operation's parameter registers at `Foo.X` — and the positive gate refuses it too.
  3. THE PERMISSIVE RE-READ DISCARDED `Ambiguous`, so two hidden routes to one name fell through to "has no member" — the exact verdict the block exists to avoid. Which candidate is named is immaterial when the scope can reference none.
  4. Dissolved by the positive gate, above.

A TYPE PARAMETER IS DELIBERATELY STILL ADMITTED. Sort parameters register as `SymbolKind::Sort`, so the gate passes them, and that is measured rather than tolerated: `Base.E` through the head's own declaration and `Mid.E` through the conversion behave identically at a call site (both load, both accept an `Int64`). Refusing one would have reintroduced the position-dependence this ticket removes.

FOUND BY A UNIFORMITY ROW, AND THAT IS THE METHOD WORTH KEEPING. This gap was not found by reading the type checker. Adding X9RRN's rung, the next step was to extend `wi752_dotted_ladder_test`'s "same spelling, every position" claim to it; two positions passed and the type one failed. `wi752_provided_member_resolves_in_every_position` now carries all three again, and its doc records that it earned its keep on the day it was written.

A SEPARATE DEFECT SURFACED AND IS FILED: WI-20260826-JSFHG. My test comment had asserted that "an enum constructor yields the ENUM, so a `Colour.red`-typed parameter is a narrowing position with no literal to pass it" — presenting a measurement as the language's rule. The user asked "is red not a type?", and §8.2 answers it: each constructor name IS a sort in its own right, and both halves of `red <: Colour` are implemented. What is broken is that every constructor application types at the PARENT, so NO expression has the variant type — driven through the bare and qualified constructors, a declared return, and a re-construction inside an already-narrowed `match` arm. A signature written with one is unsatisfiable and loads clean. The comment is corrected to name the ticket.

SPEC: §8.6 gains the type position on the rung, the sort-or-entity rule with both repros, and the `internal` paragraph gains the qualified-child reading with the forbidden-vs-absent reason.

FINAL: rustland 5752 passed / 0 failed across 36 binaries (X9RRN's baseline 5744; +9 rows, −1 retired); scaland 538 passed / 0 failed — it has no type-projection reader to mirror (`RigidTypeProjection` / `ExprCarried` are not ported), so there is nothing to keep in step there.

