## Attributes

- id: WI-20260911-3MV2C-a-reify-boundary-decides-on
- created: 2026-09-11T06:05:45Z

- status: Open
- status_agent: user
- status_at: 2026-09-11T06:05:45Z

- acceptance: cargo-test

- tags: effects

## Description

A REIFY BOUNDARY DECIDES ON THE PAYLOAD'S SORT, NOT ITS TYPE ARGUMENTS — so a boundary
typed at `Box[V = Int64]` catches a raised `Box[V = String]`, and the value arrives inside
a `Result[E = Box[V = Int64]]` a caller is about to destructure at the wrong type.

THE TYPER DOES DISTINGUISH THEM. Measured: a boundary at `Box[V = String]` around a body
raising `Error[Box[V = Int64]]` is REFUSED — "expected declared: [], got undeclared effect:
Error[T = Box[V = Int64]]". `labels_match_by_subsumption` holds a parameterized payload to
exact argument match; its own comment says so ("`Error[List[T = X]]` against
`Error[List[T = Y]]` falls back to the exact-match leg above, even where `X` refines `Y`").

THE RUNTIME CANNOT. `enter_reify_boundary` narrows `T1` to a `Symbol` (`payload_sort_of`
takes the `Fn` head), and `runtime_carrier_sort` can only ever answer a bare sort — a value
carries its constructor, not the type arguments it was built at. So the comparison in
`payload_matches` is head-against-head by construction.

DRIVEN by /code-review on the working tree: nested boundaries at `Box[V=Int64]` (inner) and
`Box[V=String]` (outer) around a raise of the STRING box answered "inner-caught", and so did
the mirror image. The control with two distinct payload SORTS answered "outer-caught", so
only the type-argument axis is blind. The corruption is observable — a `Box[V=String]`
delivered inside a `Result[E = Box[V = Int64]]` — and a caller that then uses the field at
its declared `Int64` type answers `no solutions`, the confusion degrading into a silent
failure.

NOT A REGRESSION, AND THAT IS WHY IT IS FILED RATHER THAN FIXED IN PLACE. Before proposal
027.4's narrowing no boundary judged the payload at all, so every boundary caught every
raise; this axis is the part the narrowing did not reach, not a part it broke. The
`Boom`-vs-`Other` case it DID close is the same defect class one type-argument shallower.

WHAT CLOSING IT NEEDS. The raised value's type ARGUMENTS at run time, which the interpreter
does not reconstruct. Three directions, none obviously right:
 * RECONSTRUCT from the value — read the constructor's field values' carrier sorts and match
   them against the sort's declared field types. Total for a fully-applied constructor,
   silent for a phantom parameter no field mentions.
 * CARRY the arguments on the value — a constructor records what it was built at. Changes
   the value representation, which is the expensive option.
 * REFUSE at install — `payload_sort_of` answers `None` for a PARAMETERIZED head, so such a
   boundary catches wide as it did before. Cheapest and honest, and it gives up the
   narrowing exactly where the typer is sharpest.

ACCEPTANCE: a nested pair of boundaries at `Box[V=Int64]` / `Box[V=String]` answers through
the OUTER one for a `Box[V=String]` raise and the INNER one for a `Box[V=Int64]` raise, with
the two-distinct-sorts row as the control that passes either way.

