## Attributes

- id: WI-20260823-TR8CF-nothing-checks-modifiable
- created: 2026-08-23T10:51:46Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-16T16:50:27Z

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

## Changes

### 2026-10-16T15:25:11Z — feedback — user

PARTLY DELIVERED, COMMITTED WITH OPEN REVIEW FINDINGS (user, 2026-10-16: "commit all").

DONE. `check_modify_targets` refuses a `Modify` over a place whose type admits none, naming `Modifiable` (acceptance row: `Modify[pattern]` on `pattern: String`). "Admits" is `region::type_admits_modify`, the same predicate the boundary classifier re-keys with: a sort a `Modifiable` provision names or one that `provides` such a sort (`region::is_region_sort`), a type argument or entity field that admits, a type parameter (lenient). Decided with the user: an abstract carrier says so itself — the stdlib's `Store` and `ExecutionEnvironment` now `provides Modifiable[T = Self]`, and `NonMonotonicStore` inherits through `provides Store`. Census (full suite with the check on, before repairs): 46 failures — the webots example's 7 device sorts and ~15 fixture files, each either a real mutable resource lacking a claim (claimed) or a `Modify[result]` over-declaration on an `Int64`/`Bool` result (label dropped). kernel-language.md §5.6 states the rule; the two NOT YET ENFORCED annotations are gone. Back-outs measured per part (check, path walk, provides closure, type-parameter arm). Rows: wi_tr8cf_modifiable_target_test.

OPEN — /code-review (15 findings, not yet applied):
 1. the predicate rides `region_sorts`, which over-approximates: `provides Modifiable[T = Box[V = Int64]]` makes `Int64` modifiable program-wide (fix: an exact set — the claim's `T` head — closed over provides, computed once; also removes the per-node provider walks, finding 11).
 2. a type-parameter place is admitted, so `touch[T](x: T) effects Modify[x]` called at `Int64` leaves the caller unable to declare `Modify[n]`. USER DIRECTION: drop `Modify[X]` for a non-modifiable X rather than refuse; possibly generalise as an effect kind's default guard (`Modify[X] :- requires ModifyRuntime[X]`, discharged as a proposal-048 guarded atom) — a proposal 071 is said to exist in another session and is not yet visible here.
 3. masking (`result_type_admits_region`) and the check disagree on arrow-typed results (route masking through `admits_modify`).
 4. `Function[…]` with an effect-row binding or a modifiable type argument admits.
 5. `check_written_row_bindings` (rows in type arguments / provides clauses) does not apply the rule.
 6. `Modify[result]` reads the return type from the cached first signature, not the fact being checked.
 7. guardians `wide_row_modify.anthill`: `Mailbox` now refused for a second cause.
 8. `declared_field_type`: positional `_n`, multi-variant same-named fields, bindings not substituted.
 9. unexpected place shapes admit silently (CLAUDE.md: loud over silent).
 10. stale docs on `check_modify_targets` and `type_admits_modify`.
 12. `region_sorts` recomputed and sealed stdlib facts re-walked every load.
 13. duplicated dedup/formatting in `modify_place_not_modifiable`.
 14. the test shows the refused set but not that the accepted ops load clean.
 15. `extract_type` allocation per node in `result_type_admits_region`.

### 2026-10-16T16:50:24Z — feedback — user

DELIVERED (f6829f24, on 44bc04f9). All 15 /code-review findings applied: one exact predicate (`region_sorts` = each claim's `T` head closed over `provides`; masking = `type_admits_modify`, which follows fields and reads a function value through its result only); a `Modify` arising at an instantiation over a non-modifiable place dropped as vacuous (user's direction) while a written one on a concrete type stays refused; written rows judged; per-fact return type; field paths by position, every constructor and bindings; unreadable shapes reported; sealed operations skipped and the region set built lazily. Back-outs measured per fix. Merged tree: workspace 9961 / 0, families green, scaland 692 / 0. Not taken here: the user's generalisation (an effect kind's default guard, `Modify[X] :- requires ModifyRuntime[X]`, discharged as a proposal-048 guarded atom) — a proposal of its own if wanted; proposal 071 is TypePattern (Error), not this.

