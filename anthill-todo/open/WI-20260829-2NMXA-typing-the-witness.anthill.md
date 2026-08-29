## Attributes

- id: WI-20260829-2NMXA-typing-the-witness
- created: 2026-08-29T17:42:20Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T17:42:20Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPING: the WITNESS admissibility leg cannot reach a DENOTED actual, because a `SortGoal`'s bindings are `TermId`s and a denoted binding has none. Split out of WI-20260829-N01PY, where the leg was delivered for the two term-carried arms and this one measured and left.

MEASURED, a drivable pair differing ONLY in the effect row:

  operation total(c: FiniteCollection) -> Int64 effects c.E = FiniteCollection.size(c)

  f(m: MappedStream[Source = List[T = Int64], …, EF = {}])           LOADS
  f(k: Cell[V = Int64],
    m: MappedStream[Source = List[T = Int64], …, EF = {Modify[k]}])  REFUSED --
      "expected FiniteCollection, got MappedStream[… EF = {Modify[T = k], }]"

WHY THE TWO DIVERGE. `types_compatible` routes to `types_compatible_view_structural`
whenever a side is not a hash-consed term, and a DENOTED effect row is such a side. That
function's `(parameterized, sort_ref)` arm carries the contract "mirror the term dispatch
so provider admissibility stays carrier-symmetric" (WI-405 FACET A / WI-466) — and with
N01PY's witness leg on the term side only, it no longer does.

WHY IT IS NOT A ONE-LINE ADDITION, measured rather than assumed.
`witness_provides_admissibly` asks its question by building a `SortGoal`, whose
`bindings: SmallVec<[(Symbol, TermId); 2]>` cannot hold a `Value`; a denoted binding is
exactly what has no `TermId` (`unwrap_spec_view_value`'s own doc says so, and DROPS such
bindings). Wiring the leg into that arm and reading `walk_view`'s result was TRIED: the
actual comes back a `Value::Node`, the branch never fires, and the verdict does not move
— so it was removed rather than shipped as a path nothing can drive. Substituting a bare
`Ref(<base>)` is NOT the repair: it asks about a different type (the carrier with its
arguments dropped) and could answer for a witness the value does not match.

ALSO MEASURED, and it is what makes this hard to find rather than urgent: instrumented to
print every refusal of that arm, it fires ZERO times across `wi_tests`, `eval_tests`,
`guardians_test`, `builtin_tests`, `resolve_tests` and `algebra_tests`. The corpus has no
such comparison at all, so only a written fixture reaches it. That is a LOWER BOUND on
reachability, not a proof that user code cannot.

FIX DIRECTION: give `SortGoal` a carrier-agnostic binding (the WI-342 `TermView` /
`Value` treatment the subtype and unify relations already had), or a
`Value`-carrying sibling entry point for this one question. Whichever is chosen, it is a
change to the resolver's goal representation and wants its own measurement — every
`SortGoal` producer and every `goals_equal` / `resolve_cache` key reads that field.

CELLS THAT TRACK IT: `n01py_witness_provision_subtype_test::a_denoted_effect_row_is_a_known_gap`
— the refusal AND its ground-row control, which is what says this is a gap and not the
design. The refusal row FAILS when the gap closes and tells its fixer to flip it. The site
is commented at the arm in `types_compatible_view_structural`.

