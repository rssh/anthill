## Attributes

- id: WI-20260825-KD9SW-a-minted-operator-should-name
- created: 2026-08-25T17:07:46Z

- status: Open
- status_agent: claude
- status_at: 2026-08-25T17:07:46Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260824-VT8CF-and-are-capturable-by-a-same, WI-20260825-1WBZT-numeric-is-a-bundle-so-a

## Description

A MINTED OPERATOR SHOULD NAME ITS TARGET OUTRIGHT, the way a desugared node already does, and then TWELVE IMPLICIT-TIER ENTRIES AND THE WHOLE OF `check_rival_spec_operations` CAN GO. This is WI-20260825-5W3RJ's move applied one table over, and it retires WI-20260824-BFB9A's and WI-20260824-VT8CF's repairs rather than extending them: both exist to REFUSE a capture that this makes unrepresentable.

THE DUPLICATION. `parse/pratt.rs` says WHICH form — `("+", InfixEntry { functor: "add", … })` — and `kb/load.rs`'s `PRELUDE_QUALIFIED` says WHERE IT LIVES — `"anthill.prelude.Numeric.add"`. Two encodings of one fact, with nothing keeping them in step, and the second one sits BELOW scope resolution, so a same-spelled name in scope captures the operator. 5W3RJ's `parse::desugar_target` doc states exactly this defect for the converter's 28 synthesized forms and exactly this fix: name the target outright, carrying `intern::ABSOLUTE_PATH_MARKER` (`..`), which is unspellable by any identifier (`_identifier_token` cannot contain `..`) and so can collide with no user declaration. There is then no table, no fallback rung, and no capture to refuse.

THE POPULATION IS THE TWELVE, and it is exactly `check_rival_spec_operations`' own: `add`, `sub`, `mul`, `neg`, `div`, `mod`, `eq`, `neq`, `gt`, `lt`, `gte`, `lte`. VERIFIED against the pratt tables — every one is a minted-operator target (`eq` via the `EQ_FUNCTOR` constant, which a naive grep for `functor: "…"` misses). So under this change that pass has NOTHING LEFT TO REFUSE: its subject was always "a free-standing declaration silences a tier name", and no tier name would remain for these twelve.

CENSUS, DRIVEN, not estimated. All twelve entries commented out of `PRELUDE_QUALIFIED`, rebuilt, and the corpus loaded through the CLI against the EMBEDDED stdlib (loading `stdlib` as a DIRECTORY invents 805 errors — it double-loads with the embedded copy, and that is a measurement trap, not data). 48 sites fail in total:

                          minted (an operator)   written (a bare name)
  stdlib (embedded)              9                       5
  examples/webots-modelling/lf1  1                       9
  rustland/anthill-todo/anthill 21                       1
  anthill-testcases              -                       2
  TOTAL                         31                      17

THE 31 MINTED NEED NOTHING — naming the target outright resolves them by construction. `stdlib/anthill/geometry.anthill:50` is the shape: `Vec3(x: a.x + b.x, y: a.y + b.y, z: a.z + b.z)`, three `+` at columns 15/29/43, reported as "`add` is a member of sorts Numeric, Ring, not in scope as a bare name here". Nothing is WRITTEN there; the name exists only because pratt minted it.

THE 17 WRITTEN ARE IMPORT-FIXABLE, which is the user's own framing and it holds. `platform.anthill:152`'s `gt(?t_in, ?t_out)` in a plain namespace is the clean example; four more are `eq(b, 0)` inside `division.anthill`'s and `field.anthill`'s guarded effect rows.

SO AFTER EXCLUDING WHAT AN IMPORT FIXES, NOTHING IS LEFT — that is this ticket's claim and the reason to file it.

THREE THINGS THAT ARE NOT OBSTACLES BUT MUST BE STATED:

  * `import anthill.prelude.*` DOES NOT DO IT. MEASURED: a namespace wildcard brings in the SORTS, not their members, so a bare `rem` still fails under it, while `import anthill.prelude.EuclideanDomain.*` resolves. The repair per file is one wildcard PER SORT — up to five lines (`Numeric.*`, `PartialOrd.*`, `PartialEq.*`, `Divisible.*`, `EuclideanDomain.*`) — or selective imports.
  * QUERY POSITION IS COVERED. `resolve_name_in_kb` is a real reader (WI-909's census found it the SOLE answering site for `div`/`mod`), and a CLI query has no file to hold an import — but `anthill query -i` exists and "reads exactly as the same `import` line in source does" (WI-1089). `wi863_operator_arithmetic_test`'s written `div(6, 0, ?r)` is the row that needs it.
  * THE COUNT IS A FLOOR. This is a LOAD-level sweep of `.anthill` files. The Rust test fixtures carry source as embedded strings and are NOT in it; WI-061 is the precedent — it counted 20 and the truth was 31 corpus plus 116 fixture sites. Re-census with the fixtures before committing to a number.

ONE THING THAT IS A REAL LOSS, and it needs a decision rather than a repair. The tier DISAMBIGUATES: it is the lowest rung, so where a short name is a member of several sorts and scope finds no single answer, the tier answers deterministically. The nine `geometry.anthill` sites are exactly that — "member of sorts Numeric, Ring" — and today they silently get `Numeric.add` though the enclosing `VectorSpace requires Ring[F]`. Absolute minting fixes the OPERATOR, but a file that wildcard-imports two sorts carrying one short name goes AMBIGUOUS where it used to get the prelude's quietly. That is arguably the right outcome (the silence is the bug), and it is still a behaviour change to state.

AND ONE BEHAVIOUR THIS DELETES, with the row that asserts it. Today `import myapp.Money.{add}` REDIRECTS a minted `+` to `Money.add`, because scope answers before the tier; `wi_bfb9a_rival_spec_operation_test::an_imported_unrelated_add_is_a_capture_not_a_rival` records that as a tolerated capture. Under absolute minting `+` always means `Numeric.add` and dispatches by carrier. Either reading is defensible — "the operator means the operator" versus "an import can retarget it" — but it is a LANGUAGE decision, not a refactor, and that row inverts on it.

`or` / `not` DO NOT FIT, and this ticket must not claim them. They are POSITION-DIRECTED: a resolver primitive (`anthill.kernel.or` / `.not`) in a goal position and a dispatched `Bool.or` / `Bool.not` as a value, chosen by `in_op_body_value` in `remap_name_str` — at LOAD time, which is after the mint. One mint cannot name two targets, so the boolean half keeps WI-20260825-P9Y67's own question. `and` may fit (value-only, single target `anthill.prelude.Bool.and`) and should be measured with the twelve rather than assumed.

FIRST STEP: settle the redirect-by-import decision above, because it decides whether this is implementable at all. Then absolute-mint the twelve, keep the tier entries, and re-run the corpus — that step alone should turn the 31 minted failures green with no import written anywhere, and it is separately valuable (it removes the two-list drift) even if the entries are never dropped.

CONTROL, when it is done: the 31 minted sites load with the twelve `PRELUDE_QUALIFIED` entries REMOVED and no import added — that is the measurement, and it is the one a partial implementation cannot fake. `wi_bfb9a_rival_spec_operation_test::the_refusal_population_is_the_twelve_spec_operations` inverts to EMPTY, and `wi_vt8cf_division_tower_test::a_free_standing_mod_is_refused_now_that_its_tier_target_is_a_spec_op` inverts too — `operation mod(a, b) = 99` becomes legal again and a minted `7 % 2` must still answer 1, which is the row that separates "the capture is refused" from "the capture is impossible".

ACCEPTANCE: a minted operator resolves with no tier entry and no import; the twelve entries are gone from `PRELUDE_QUALIFIED`; `check_rival_spec_operations` is deleted or its population is empty and it says so; the written-bare-name sites carry imports; full workspace green via rustland/scripts/test.sh and scaland sbt test.

## Changes

### 2026-08-25T17:22:42Z — feedback — claude

THE MINT ADDRESS TRACKS THE DECLARING SORT, so a spec SPLIT changes what this ticket must mint — and the ordering advice in the body is backwards because of it.

The body says doing this before WI-20260825-1WBZT is "cheaper", on the grounds that 1WBZT would then be a one-line constant change instead of a table edit, and that it merely "moves the twelve-name census by one". That is the weaker half of the interaction and it misses the load-bearing one.

WHAT THE ADDRESS IS. A minted `+` would name `..anthill.prelude.Numeric.add` because that is where `add` is DECLARED today. The address must name a declaration that exists — WI-20260825-5W3RJ pins exactly that with `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load`. The CARRIER never appears in it, which is why absolute minting does not cost any polymorphism: the address is the SPEC op, the spec op is what dispatches, and `Money(700) + Money(25)` = 725 through `Money.add` today by that very route.

WHAT 1WBZT DOES TO IT. That ticket moves `add` off `Numeric` onto `Additive`, with `Numeric provides Additive[T = T]` — ONE declaration per short name, or `ordered.anthill`'s `sort_ops` HashMap coin flip. So after it, `..anthill.prelude.Numeric.add` names nothing and the mint must say `..anthill.prelude.Additive.add`. Same for any later split of the comparison surface.

IT FAILS LOUDLY, which is the mechanism working rather than an excuse: 5W3RJ's own doc says a rename "surfaces at the USE site rather than as a named orphan", and that is the whole reason to prefer an address over a table. But a loud failure across every `+` in the corpus is still a migration, and it is avoidable by ordering.

SO: DO THE SPEC SPLITS FIRST, then mint. Any ticket that moves where one of the twelve operations is DECLARED — 1WBZT for `add`/`neg`/`zero-val`, and anything similar for the `PartialOrd` four — should land before this one, so the addresses are minted once at their final homes. Raised by the user, who asked why the address said `Numeric` and whether that meant a `Money` carrier would stop working. It does not; but the question is the right one to have asked of the address.

AND A COST THE BODY DOES NOT NAME. After this ticket `+` and `add(…)` become DIFFERENT THINGS in one file: with `import Weird.{add}` in scope, `1 + 2` answers the spec op (3) while `add(1, 2)` answers the import (99). That is measured for the CURRENT behaviour — driven, both arms, `99` and `3` — and it is what this ticket deliberately breaks. kernel-language.md §5.5 currently says "Infix and prefix operators are sugar for function application — `a + b` desugars to `add(a, b)`", which stops being true: `a + b` would desugar to an ADDRESS, and refactoring it to the bare call can change the answer with no diagnostic. Either the sentence is corrected as part of this ticket, or the ticket is refused on it. That is the strongest argument against the change and it belongs in front of anyone deciding.

### 2026-08-25T19:47:45Z — feedback — claude

THE PREREQUISITE IS DELIVERED — WI-20260825-1WBZT landed, so the addresses a mint would bake are FINAL for the arithmetic four. Concretely, the targets to mint are now:

  `+`  ..anthill.prelude.Additive.add          (was ..anthill.prelude.Numeric.add)
  `-`  ..anthill.prelude.Additive.sub          (was ..anthill.prelude.Numeric.sub)
  `*`  ..anthill.prelude.Multiplicative.mul    (was ..anthill.prelude.Numeric.mul)
  neg  ..anthill.prelude.Additive.neg          (was ..anthill.prelude.Numeric.neg)
  `/`  ..anthill.prelude.Divisible.div         (VT8CF, unchanged)
  `%`  ..anthill.prelude.EuclideanDomain.mod   (VT8CF, unchanged)
  `=` `!=` `<` `<=` `>` `>=`  PartialEq / PartialOrd, unchanged

THE TWELVE-NAME CENSUS DID NOT MOVE, which is worth stating because the ordering feedback said it might: `wi_bfb9a_rival_spec_operation_test::the_refusal_population_is_the_twelve_spec_operations` still reads `add div eq gt gte lt lte mod mul neg neq sub` and passed unchanged through the split. The move was between two PARAMETRIC carriers, so nothing about spec-op-hood changed — only the owning sort. `wi_1wbzt_syntax_category_test::the_implicit_tier_points_at_the_syntax_categories` is the row that pins it, and it adds `zero` / `one` to the spec-operation set (both are category members now) while asserting `pow` stays out.

NOTHING ELSE IS PENDING FOR YOU on the declaration-location question. 1WBZT was the last ticket that moved one of the twelve; the `PartialOrd` four were already minimal and are not scheduled to move.

ONE THING THE SPLIT MAKES CHEAPER, and one it makes sharper:
  * CHEAPER — the tier hop this ticket would delete is now a table of six arithmetic/division entries pointing at four category sorts, all of which are minimal specs. `PRELUDE_QUALIFIED` is the single reader (kb/load.rs), and `implicit_target_orphans` already pins that every entry resolves, so a mint that names the address outright has a ready control: that orphan check should stay empty and the twelve-name census unchanged.
  * SHARPER — WI-20260825-X9RRN records that a QUALIFIED `Numeric.add(a, b)` does NOT walk the `provides` chain ("unknown functor"), while `import anthill.prelude.Numeric.{add}` does. A minted `..anthill.prelude.Additive.add` is an ABSOLUTE path, so it is unaffected either way — but the two tickets touch the same question (what a qualified spec-op address denotes) and whoever settles X9RRN should check that a mint's absolute reading is not accidentally routed through the same predicate.

