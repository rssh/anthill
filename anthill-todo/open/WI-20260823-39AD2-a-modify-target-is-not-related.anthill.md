## Attributes

- id: WI-20260823-39AD2-a-modify-target-is-not-related
- created: 2026-08-23T09:07:15Z

- status: Open
- status_agent: user
- status_at: 2026-08-23T09:07:15Z

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

