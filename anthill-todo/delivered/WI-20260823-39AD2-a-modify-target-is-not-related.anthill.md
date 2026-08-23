## Attributes

- id: WI-20260823-39AD2-a-modify-target-is-not-related
- created: 2026-08-23T09:07:15Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-23T11:11:30Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `Modify` TARGET IS NOT RELATED TO A RESOURCE TYPE, so two checks the frame condition needs are both missing. Both want the same relation: given a `Modify[p]` whose target is a PLACE (a parameter, `result`, a computed region), what RESOURCE TYPE does that place denote?

MEASURED while delivering WI-20260822-1TKN0, which closed the comparable half of the override-refinement effects leg (rustland/anthill-core/src/kb/typing.rs, `check_override_refinement`).

GAP 1 — a denoted target facing a spec `Modify` over a TYPE fails open. The stdlib's own shape:

  sort ModifyRuntime
    sort T = ?
    operation set(target: T, value: V) -> Unit effects Modify[T]     -- sigma-bound to Cell
  end
  sort Cell
    operation set(c: Cell, value: V) -> Unit effects Modify[c]       -- a PLACE of that type
    provides ModifyRuntime[T = Cell, V = V]
  end

`Modify[c]` DOES refine `Modify[T = Cell]` -- the place `c` is a resource of that type -- and nothing on the pass says so. `types_compatible` relates two denoteds by EQUALITY (`unify_denoted_view`), which is exact for place-vs-place and wrong here. MEASURED: dropping the guard and comparing anyway refuses `Cell.set` over `ModifyRuntime.set` and nothing else in the corpus (`MutableStack.insert`/`clear` survive, their spec targets being places too). So the fail-open is currently load-bearing for the stdlib. Driven by `wi347_override_refinement_test::a_denoted_target_against_a_resource_typed_spec_modify_fails_open`, which asserts the fail-open and names this ticket; when this lands that row must flip to accepted-BY-COMPARISON, and `a_spec_modify_over_a_type_fails_open_its_row_but_not_its_neighbours` is what separates the two readings.

GAP 2 — no site checks `Modifiable[typeof(target)]` at all. `stdlib/anthill/prelude/effects.anthill` states the rule ("Modifiable: marks a type as admitting `Modify[T]` in effect rows", proposal 037 Rule 8), and `mutable_collection.anthill:17` writes `requires Modifiable[T = C]  -- admits Modify[c] in the mutating rows` as though something enforced it. MEASURED: `is_modifiable_sort` (rustland/anthill-core/src/kb/region.rs) has exactly two readers -- the `anthill.reflect.is_modifiable` builtin and the WI-314 region masking -- and neither is a load-time check on an effect row. `Modify[pattern]` on a `pattern: String` parameter loads clean (measured in WI-20260822-1TKN0's ticket text, independently).

WHY ONE TICKET. GAP 2's check IS "resolve the target's type, then ask `Modifiable`" -- the same first step GAP 1 needs. Splitting them would build the resolver twice.

WHAT IT MUST DECIDE, and none of these is obvious from the code:
  * `Modify[result]` -- `Cell.new`'s allocator shape (kernel-language.md 5.5 / WI-314). The target's type is the op's RETURN type; check `Modifiable` on that.
  * A COMPUTED region -- `Modify[glob(pattern)]` in docs/measurements/guardians/d3_frame.anthill. Recorded as C5 in examples/guardians/docs/design/measured.md as "type position". Decide whether it is admissible at all before deciding its type.
  * An ABSTRACT carrier -- `MutableCollection` writes `requires Modifiable[T = C]` with `C` a spec parameter. The check must be discharged against the requirement, not against a `fact`, or every parametric mutable container is refused.
  * A place whose type is itself parametric.

ACCEPTANCE: `Cell.set` over `ModifyRuntime.set` is ACCEPTED BY COMPARISON (not by fail-open) and the wi347 rows above are re-pointed; `Modify[pattern]` on a `pattern: String` parameter is REFUSED naming `Modifiable`; the stdlib and the corpus stay green; C5 and C9's closing paragraph in examples/guardians/docs/design/measured.md are updated with what was decided about a computed region.

## Changes

### 2026-08-23T09:33:22Z — feedback — user

TWO THINGS THE PARENT TICKET'S REVIEW ADDED, one of which is a DECISION and not an implementation.

1. THE MECHANISM MAY BE SMALLER THAN IT LOOKS, and that is a trap rather than good news. `check_override_refinement` already holds `impl_info.params: Vec<(Symbol, Value)>` -- param symbol to declared TYPE -- and `impl_info.return_type`. So for the two shapes that matter (`Modify[<a parameter>]`, `Modify[result]`) the target's declared type is IN HAND at the site, and the coverage test is one `types_compatible(place_type, spec_target_type)`. That is ~20 lines. It is NOT the reason this ticket exists.

2. THE REASON IT EXISTS: THE DOCS DISAGREE ABOUT WHAT `Modify[X]` DENOTES, and the check cannot be written until that is settled.

   * kernel-language.md 5.6 reads it as a NAME: "`Env` is a partial map from resource NAMES (symbols) to terms", "`Modify[S]` -- the operation may inspect and update `Env(S)`". Under this reading `Modify[Cell]` and `Modify[c]` name two DIFFERENT slots, `Modify[c]` does NOT refine `Modify[T = Cell]`, and `Cell.set` providing `ModifyRuntime.set` is an outright defect in the stdlib rather than a check that fails open.
   * stdlib/anthill/prelude/effects.anthill reads it as a TYPE: "`Modify[T]`: the effect MARKER, keyed by the resource-identity TYPE T". Under this reading `Modify[c]` with `c: Cell` refines it, and the fail-open is a missing implication.
   * The RUNTIME is a third reading again (same file): "one arena keyed by the target's FUNCTOR SYMBOL -- `set(store, v)` and `set(counter, v)` share the same handler but live in separate slots".
   * examples/guardians/docs/design/effects.md:145 sides with the place: "`Modify[a]` and `Modify[b]` coexist in one row because `a` and `b` are distinct resources" -- which is also what WI-20260822-1TKN0 now ENFORCES (granting `Modify[box]` is not granting `Modify[box2]` at the same type).

   So GAP 1 is a question about the LANGUAGE, not about typing.rs, and answering it decides GAP 2's shape too. Settle it in kernel-language.md 5.6 FIRST; the code follows in a few lines either way.

3. A CASE REFUTABLE UNDER EITHER READING, found by /code-review and left open deliberately. Even without settling the above, a place whose DECLARED TYPE is incompatible with the spec's binding is refusable: `Modify[db]` with `db: Database` against a spec `Modify[T = Cell]` is excused today and is wrong on every reading. It is left in this ticket rather than fixed inline precisely because the repair is the same `types_compatible(place_type, spec_target_type)` call as item 1, and running it in only the negative direction would encode half of an unsettled rule.

### 2026-08-23T10:51:01Z — feedback — claude

DELIVERED — THE LANGUAGE QUESTION WAS SETTLED FOR THE PLACE, and settling it dissolved
three of this ticket's four items instead of building the relation they asked for.

THE DECISION (user): `ModifyRuntime.set`'s `effects Modify[T]` is an ERROR; it should be
`effects Modify[target]`. So `Modify[X]` denotes a resource NAME — kernel-language.md
§5.6, `examples/guardians/docs/design/effects.md:145`, and what WI-20260822-1TKN0 already
ENFORCES — and `prelude/effects.anthill`'s "keyed by the resource-identity TYPE T" was the
wrong doc.

CENSUS BACKING IT. Every `Modify[…]` in the tree denotes a place: `Modify[s]`
(store.anthill x20, main.anthill x40), `Modify[c]`, `Modify[self]` (webots x20),
`Modify[kb]`, `Modify[store]`, `Modify[env]`, `Modify[box]`, `Modify[result]`,
`-Modify[x]`. The ONE exception in real code was `prelude/effects.anthill:80`. The new
pass, run over the whole stdlib before the fix, flagged exactly that line and nothing
else.

THE "THREE READINGS" IN THIS TICKET'S OWN FEEDBACK WAS TWO. The runtime note it counted
as a third — "one arena keyed by the target's FUNCTOR SYMBOL; `set(store,v)` and
`set(counter,v)` live in separate slots" — IS the name reading. The type reading had
exactly one home: the file that wrote the defect.

MEASURED (spec x impl, refinement leg):
  Modify[T] (before)      x Modify[c]      -> accepted BY FAIL-OPEN
  Modify[T] (before)      x Modify[value]  -> accepted BY FAIL-OPEN   <- the defect
  Modify[target] (after)  x Modify[c]      -> accepted BY COMPARISON
  Modify[target] (after)  x Modify[value]  -> REFUSED

WHAT DISSOLVED:
 * GAP 1 — nothing to build. The alignment WI-20260822-1TKN0 shipped already rewrites the
   override's own param name into the spec's vocabulary, and `unify_denoted_view` relates
   two places EXACTLY. `place_vs_resource_type` was DELETED, not filled in.
 * FEEDBACK ITEM 1 ("~20 lines, `types_compatible(place_type, spec_target_type)`") — ZERO
   lines. No place-vs-type comparison is called anywhere.
 * FEEDBACK ITEM 3 (`Modify[db]` with `db: Database` against a `T = Cell` binding) — ZERO
   lines, already refused by the WI-20260822-1MAGR parameter-conformance leg, with a
   better message than the effects leg could give: "parameter 1 is `Database` where the
   spec's is `Cellish`".
 * C5 (computed region) — already decided by the GRAMMAR: `Modify[glob(pattern)]` is a
   PARSE error. Only the record needed updating; `measured.md`'s "the region slot is a
   type position" was the misleading half and now says the slot takes a PLACE.

WHAT SHIPPED
 1. `prelude/effects.anthill:80` -> `effects Modify[target]`, plus the header and `sort
    Modify` docs that taught the wrong reading.
 2. `check_modify_targets` (kb/typing.rs) — a `Modify` target must be a PLACE; a sort, a
    sort parameter, an `ExprCarried` projection, or no target at all is a LOAD ERROR.
    Refusal rather than comparison because a type target is unsatisfiable BY CONSTRUCTION
    (sigma binds a type param to a TYPE, never to a place) and, left admissible, it does
    not go unchecked — it DISABLES checking: sigma-bound it refuses the CORRECT program,
    un-bound it fails open the WHOLE effects row.
 3. `place_vs_resource_type` deleted from `check_override_refinement`.
 4. kernel-language.md §5.6 states the rule; `measured.md` C5/C9 updated.

CONTROLS, ALL RUN
 * Neutralize `check_modify_targets` -> exactly 2 rows fall
   (`a_resource_type_in_a_modify_target_is_refused_at_its_declaration`,
   `a_concrete_sort_in_a_modify_target_is_refused_too`), nothing else.
 * Drop the `guarded` arm of `peel_effect_atom` -> exactly 1 row falls.
 * THE DELETION IS NOT SEPARATELY PINNABLE, and that is the point rather than a neighbour
   test being credited: the gate needed a spec `Modify` over a TYPE to fire, and that
   shape no longer loads, so it is dead BY CONSTRUCTION. Measured BOTH ways — restoring
   the two closures beside the refusal leaves wi347 at 37/37 and the stdlib clean,
   unchanged. What IS pinned is the capability it suppressed:
   `a_place_target_naming_the_wrong_parameter_is_refused`.

FOUND WHILE DELIVERING, EACH WITH A WITNESS
 a. ONE RULE, TWO SPELLINGS — a GUARDED atom hid the target. `effects { Modify[Wrapped]
    :- eq(b,0) }` loaded CLEAN while its unguarded twin was refused, because a row element
    is `guarded(label, guard)` with its own functor. Fixed inline (`peel_effect_atom`,
    which peels `guarded` / `absent` / `present`), pinned with its own control
    (`a_guarded_modify_over_a_place_still_loads`), which is what stops the peel from
    passing by refusing every guarded Modify.
 b. THE FIXTURES WERE PART OF THE POPULATION — 15 tests in 3 files wrote `Modify[<a
    sort>]`. `wi329` (`Modify[Res]`) and `wi698` (`Modify[Reg]`) never wanted `Modify`
    semantics — the row arithmetic treats every present label alike — so they now use a
    plain registered effect, which keeps their rows GROUND exactly as the type target was.
    `eval_test`'s three m5 rows are runtime tests and now take the resource as a
    PARAMETER; `m5_modify_two_resources_are_independent` thereby declares two DISTINCT
    places, which is the independence it asserts — the old spelling gave both ops the SAME
    label (`Modify[T = Cells]`), the exact conflation §5.6 forbids.
 c. A PRE-EXISTING RE-KEY HOLE, surfaced not caused. `param_to_arg_sym` /
    `param_to_arg_head` populate from a bare VARIABLE and a field PROJECTION only. An
    APPLICATION argument gets no entry and the callee's own parameter name SURVIVES into
    the caller's row: `Cell.set(mk(), 1)` reports `undeclared effect: Modify[T = c]`,
    naming `Cell.set`'s parameter — measured with this ticket's change BACKED OUT, so it
    predates it. This ticket only made it reachable through a second op, which is why the
    ambient-resource idiom (`set(counter(), n)`, a nullary constructor naming a global
    slot — the shape effects.anthill's runtime note describes) is not writable today.
    Pinned by `wi506_modify_field_coverage_test::an_application_argument_does_not_rekey_
    and_leaks_the_callees_param_name`, which asserts BOTH arms.

SCOPE, WITH REASONS RATHER THAN CAUTIONS
 * AN OPERATION'S OWN ROW ONLY. An effect row nested in a PARAMETER's arrow type
   (`handle(body: () -> Int64 @ {Modify[X], Sig})`) scopes differently — its lawful target
   is the arrow's OWN binder, the `CallbackParam` shape `unify_denoted_view` compares by
   POSITION and `prelude/iterable.anthill` writes as `-Modify[x]`. `wi329` held the one
   witness in the tree and no longer does, so there is nothing to measure a refusal
   against. Recorded at the pass and in §5.6.
 * GAP 2 IS NOT DELIVERED and is now INDEPENDENT. This ticket's "WHY ONE TICKET" was that
   GAP 2 shares GAP 1's first step (resolve the target's type); GAP 1 needed no type
   resolver at all, so the bundling rationale is void. Split out.

GREEN: cargo 5600 passed / 0 failed (36 result lines, exit 0); scaland sbt 514 / 0.

### 2026-08-23T11:11:16Z — feedback — claude

/code-review (high) FOUND TEN, ALL REAL, ALL FIXED. Recorded because three of them are
recurring shapes rather than slips, and one of them made a CLAIM I had already written
into the ticket false.

THE TWO THAT CHANGED BEHAVIOUR
 1. THE REFUSAL LANDED A PASS TOO LATE, so a type target produced TWO errors — first a
    coverage refusal blaming the CORRECT override ("declares effect `Modify[T = target]`,
    which is not covered…"), then the real declaration error. My own pass doc had written
    down that exact failure as the reason the refusal must exist, and then shipped it.
    Fixed at the right site rather than by moving the pass: the effects leg now SKIPS an
    atom whose `Modify` target is not a place, on EITHER side, because the refusal belongs
    to the declaration and a coverage consequence sends the author to a line whose repair
    would not load. Order-independent, which moving the pass would not have been.
 2. A SECOND ARM WAS DEAD AND ITS TEST'S CONTROL WAS STALE. `else if effect_is_modify(..)
    && !spec_grants_modify` could only fire for a `Modify` whose target CONTAINS a type
    param — exactly what the new pass refuses. Its test still claimed "BACK-OUT: … this is
    the only row of the file that flips" and stayed green only because
    `widening_refusals` filters on `"effects must not widen"` while the fixture now earned
    the declaration error too. Arm deleted (the capability it carried a nicer message for
    is still refused by the generic arm); test re-pointed to assert the declaration
    refusal AND that no widening is reported beside it.

THE THREE THAT ARE RECURRING SHAPES
 3. A CLAIM I WROTE INTO THIS TICKET WAS FALSE — "the only `Modify` over a type in the
    tree". The same change had to rewrite five test fixtures, which is the recorded "a
    feature's POPULATION includes the test fixtures" trap, committed while quoting the
    census that should have prevented it. And one survives: `anthill-cpp-gen/tests/
    higher_kinded_arrow_test.rs:85` writes `@ {Modify[Calc]}`. Corrected to "in the
    stdlib" at both sites.
 4. A JUSTIFICATION BUILT ON A WITNESS I HAD JUST DELETED. The arrow-position scope note
    said it was left unchecked because "wi329 held the one witness in the tree … and no
    longer does, so there is nothing to measure a refusal against" — but the cpp-gen file
    above IS one, and the asymmetry is directly measurable anyway. Replaced with a driven
    row (`a_type_target_inside_a_parameters_arrow_row_is_not_checked`) that FAILS the day
    the arrow position starts being checked.
 5. A CONTROL WEAKENED BY A NAME COLLISION. I named the wi329 stand-in effect label `Res`
    — which is also every fixture's PARAMETER TYPE (`operation t(r: Res)`), so three
    `expect_reject` controls asserting `contains("Res")` began passing on any diagnostic
    that merely mentioned the parameter's type. The old `"Modify"` substring had no such
    collision, so the repair silently traded control strength for it. Renamed to `Beep`.

THE REST
 6. `fact Effect[T = Reg]` in wi698 was written with `Effect` MISSING from the namespace's
    import list. An unresolved fact functor loads SILENTLY, so it registered nothing while
    its comment claimed otherwise. Import fixed — and then MEASURED: removing the fact
    entirely leaves wi698 at 38/38 and wi329 at 21/21, so effect registration is not
    enforced at all. Filed as WI-20260823-VM3YB, together with the wider half (a fact
    whose functor does not resolve is admitted silently). Both fixtures now say NOT
    load-bearing, with the measurement, instead of asserting a registration that does not
    happen.
 7. A bare `Modify` (no target) got the message "whose target is a TYPE", which
    misdescribes it — there is no target. Split into its own phrasing; the classifier now
    returns Place / Type / Missing.
 8. The wi506 gap pin asserted `contains("undeclared effect") && contains("Modify")`,
    which its OWN fixture satisfies by another route (`mk()` declares `Modify[result]` two
    lines up). Tightened to `Modify[T = c]` — the leaked symbol the docstring names.
 9. kernel-language.md §5.6 enumerated the lawful place forms as a CLOSED list, but the
    pass admits any `TypeHead::Denoted` — a value-producing zero-arg operation
    (`Modify[kb]`, the ambient accessor) is a fourth form and loads clean. Reworded to
    state the rule as DENOTATION with examples, not a list.

STRUCTURAL RESULT: the place/type question is now asked in ONE place
(`classify_modify_target`) by both readers — the declaration pass, which REPORTS, and the
effects leg, which SKIPS. Two questions of one fact, which is the shape this project keeps
getting wrong when each caller writes its own predicate.

GREEN AFTER: cargo 5602 passed / 0 failed (36 result lines, exit 0); scaland sbt 514 / 0.

