## Attributes

- id: WI-20260823-TR8CF-nothing-checks-modifiable
- created: 2026-08-23T10:51:46Z

- status: Open
- status_agent: claude
- status_at: 2026-08-23T10:51:46Z

- acceptance: cargo-test

## Description

NOTHING CHECKS `Modifiable[typeof(target)]`, AT ANY SITE. Split out of
WI-20260823-39AD2, which delivered the other half (a `Modify` target must be a PLACE) and
in doing so VOIDED the reason the two were one ticket: that ticket's "WHY ONE TICKET" was
"GAP 2's check IS `resolve the target's type, then ask Modifiable` — the same first step
GAP 1 needs", and GAP 1 turned out to need no type resolver at all. So this stands alone,
and its first step has no other client.

MEASURED (with 39AD2 landed): `operation touch(pattern: String) -> Unit effects
Modify[pattern] = ()` loads CLEAN. `String` is not `Modifiable` and nothing asks.

WHAT STATES THE RULE, AND WHERE IT IS WRITTEN AS THOUGH ENFORCED:
  * `stdlib/anthill/prelude/effects.anthill` — "Modifiable: marks a type as admitting a
    `Modify` over a PLACE OF THAT TYPE in effect rows", proposal 037 Rule 8. 39AD2
    annotated it NOT YET ENFORCED and named this ticket.
  * `stdlib/anthill/prelude/mutable_collection.anthill:17` — `requires Modifiable[T = C]
    -- admits Modify[c] in the mutating rows`. Same annotation, same ticket.
  * `is_modifiable_sort` (kb/region.rs) has exactly two readers — the
    `anthill.reflect.is_modifiable` builtin and the WI-314 region masking — and NEITHER is
    a load-time check on an effect row.

WHERE IT GOES. `check_modify_targets` (kb/typing.rs) already walks every operation's
declared row and has the label's target in hand; it deliberately checks only that the
target IS a place. `all_operation_params` / the op's return type give the place's declared
type for the two common shapes.

THE PART THAT IS NOT MECHANICAL, and it is why this is a ticket rather than an inline
addition — THE DISCHARGE HAS AT LEAST THREE CHANNELS, and reading only one is the
recurring defect:
  * a `fact Modifiable[T = X]` — `Cell` writes `provides Modifiable[T = Cell]`, which is a
    PROVISION, not a fact; `is_modifiable_sort` already reads both, via
    `modifiable_claim_heads`.
  * a REQUIREMENT — `MutableCollection` writes `requires Modifiable[T = C]` with `C` a
    spec parameter. The check must be discharged against the requirement or every
    parametric mutable container is refused. `is_modifiable_sort` does NOT read this
    channel; `build_requires_index` / `check_provider_requires` are the other side.
CENSUS THE CHANNELS BEFORE WRITING THE PREDICATE — and note `is_modifiable_sort` answers
a NEIGHBOURING question (it backs a reflect introspection op and the WI-314 masking, whose
own doc records that the two callers must keep DIFFERENT readings of a head). Borrowing it
by name rather than by predicate is exactly the failure WI-20260822-1MAGR recorded.

SHAPES THE RESOLVER MUST COVER (each already legal today):
  * `Modify[p]`, `p` a parameter — the type is `impl_info.params`'.
  * `Modify[result]` — the type is the op's RETURN type (`Cell.new`, `MutableStack.new`).
  * `Modify[c.rep]` / `Modify[result.a]` — a field path; the type is the FIELD's
    (`wi261_result_in_effects_test`, `wi506_modify_field_coverage_test`).
  * A place whose type is itself parametric — must not be refused for being unknown.
  * `Modify[op]` — the WI-313 ambient-KB accessor, a zero-arg operation read as a value
    place. Its "type" is the op's return type; decide whether it is in scope at all.

ACCEPTANCE: `Modify[pattern]` on a `pattern: String` parameter is REFUSED, naming
`Modifiable`; `MutableCollection` and every stdlib carrier stay green (the requirement
channel is the one that decides this); the corpus stays green; a control says which rows
fall when the check is backed out, and a NON-matching cause is mixed in so a homogeneous
fixture cannot bless a wrong predicate; the two NOT YET ENFORCED annotations 39AD2 left in
the stdlib are removed.

