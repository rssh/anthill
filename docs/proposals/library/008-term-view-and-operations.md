# Library: reaching a type's structure from a rule

## Status

Draft 2026-08-26. No driver WI yet. Found while trying to write
`examples/guardians/lib/safety.anthill` as a rule over reflection facts.

**This proposal was rewritten once, and the first draft is worth recording
because it was wrong in an instructive way.** It proposed adding a `TermView`
sum type — `TermRepr` plus named arguments — on the premise that nothing could
decompose a term-valued reflection field. That premise is false. Types are
`anthill.prelude.Type`, `Type` already has a complete structural view
(`TypeExtractor`), and `anthill.reflect.extract` is implemented. The real gap is
narrower and sits somewhere else entirely: **that view is unreachable from a
rule, and the one resolver builtin meant to bridge the gap does not bind its
result.**

## What already exists, and works

`stdlib/anthill/prelude/sort.anthill` settled the representation at WI-361:

> `Type` is a bare `sort Type = ?` — an opaque handle like `Term` / `Symbol` —
> and every structural form lives in `TypeExtractor`. […] There is NO stored deep
> ADT inside `Type`; its structure is REIFIED on demand by
> `anthill.reflect.extract(t) -> TypeExtractor`.

`TypeExtractor` is complete, and it covers named arguments:

```anthill
enum anthill.prelude.TypeExtractor
  entity SortRef(name: Symbol)
  entity TypeVar(name: Symbol)
  entity Parameterized(base: Symbol, bindings: List[TypeBinding])
  entity Arrow(param: Term, result: Term, effects: Term, arity: Int64)
  entity Denoted(value: NodeOccurrence)
  entity EffectsRows(effects_expr: EffectExpression)
  entity NamedTuple(fields: List[NamedTupleElement])
  entity Nothing
end
```

`extract` is implemented — `extract_type_builtin` in `eval/builtins.rs`,
registered as `anthill.reflect.extract`, backed by the engine-internal
`extract_type`.

And the two shapes a reader actually meets are exactly `SortRef` and
`Parameterized`. Census over the `examples/guardians` KB, on
`SortProvidesInfo.spec`:

| shape | rows | example |
|---|---|---|
| parameterized | 236 | `SortView(Triage, C: GoodTriage)` |
| bare `Ref` | 7 | `Checker`, `Llm`, `Model`, `Harness`, `Store` |

So: **nothing is missing from the type view.** The library already has the sum
type, the reification operation, and an implementation of it.

## The gap

### 1. `extract` is an eval builtin, so a rule cannot reach it

Measured — this rule yields **no solutions** on a KB whose provisions number in
the hundreds:

```anthill
  rule ext(?view, ?e)
    :- SortProvidesInfo(sort_ref: ?c, spec: ?view), extract(?view, ?e)
```

`extract` is registered in `eval/builtins.rs`, which is the *evaluator's*
registry. The resolver has its own, disjoint one — `BuiltinTag` in
`kb/resolve.rs` — and `extract` is not in it. So a type's structure is reachable
from an operation body and not from a rule body, and nothing says so.

### 2. The rule-level substitute exists, and does not bind

The resolver's registry does carry a bridge, and its documented signature is
right:

```rust
    /// `anthill.reflect.typing.extract_sort_ref(?inst, ?result)` — extract
    /// functor as a nullary Fn (canonical sort-name shape) from
    /// instantiation term.
    ExtractSort,
```

Its implementation is right too: `builtin_extract_sort` reads the head
carrier-neutrally, special-cases `SortView(name, …)` by taking the first
positional child's head symbol, falls through to the functor itself for a bare
`Ref`, and ends in `finish_result(target, ref_term)`. That is precisely the
bare-vs-parameterized union above, handled.

**But as a rule-body goal it succeeds without binding.** Measured:

```anthill
  rule checked(?carrier, ?spec)
    :- SortProvidesInfo(sort_ref: ?carrier, spec: ?view),
       extract_sort_ref(?view, ?spec)
```

```
  ?c = BigInt, ?s = ?_
  ?c = BigInt, ?s = ?_
4 solution(s) shown — more exist, raise --max-results
```

Genuine solutions, not residuals — the query reports no undischarged goals, and
chaining `short_name(?spec, ?name)` afterwards then yields **no solutions at
all**, confirming `?spec` is unbound rather than bound-and-unprintable.

**THIS AREA HAS AN OWNER, AND IT IS NOT THE ONE THIS PROPOSAL FIRST NAMED.**
`WI-20260822-ZJZS7` (*a host-backed operation does not reduce in a rule body*)
**closed as delivered** by `WI-20260826-VPEWK` on 2026-08-27. Confirmed live in
this tree: `:- Bool.and(true, true) = true` answers 1, and the `false` case
answers 0. Neither of the two rows above moved.

They did not move because VPEWK's gate is *interpreter-mapped* **and**
effect-free, and "interpreter-mapped" is built from `operation_map` clauses —
`Bool.{and,or,not}` were **migrated to `operation_map`** to qualify. Nothing in
`anthill.reflect` has such a clause. `docs/kernel-language.md` §5.2 now states
this as one of the three surviving declines, and states it as a soundness
problem rather than an incompleteness:

> An operation whose host function is registered by **hardcoded name** rather
> than by an `operation_map` clause is declined for neither reason but because
> the gate cannot **see** it (WI-884's split) … and — unlike the two above — it
> is *decided false* rather than suspended, so `not(…)` over it answers **1**.
> That last is a soundness gap … and it closes when the remaining hardcoded
> registrations migrate (**WI-880**).

So **WI-880 owns it**, and the reflection surface is a family that ticket's
acceptance does not currently name. Measured in this tree:

| tier | count | reachable from a rule? |
|---|---|---|
| registered by **hardcoded name** (`extract`, `term_field`, `term_as_entity`, `term_functor_name`, `make_fn`, `replace_named_arg`, `as_term`, …) | 29 | **no** — §5.2's hardcoded decline |
| declared with **no implementation at all** (`sort_as_term`, `term_as_sort`, `can_be_sort`) | 3 | no — and not from an operation body either |
| resolver `BuiltinTag` (`nonvar`, `ground`, `extract_sort_ref`, `resolve_sort_instantiation_param`, `qualified_name`, `short_name`, `is_entity_of`, `dispatch_carrier`, …) | — | yes |

The consequence is sharper than "one operation is awkward": **no rule can read a
term at all**, because the entire accessor surface is in tier 1.

### 3. `TermRepr` and `KB.reify` are dead

`KB.reify(kb: KB, t: Term) -> TermRepr` and `KB.reflect` have **no
implementation**. (The `reify_value` occurrences in `kb/resolve.rs` and
`kb/extent.rs` are the resolver applying a substitution — a different operation
sharing a stem.) And `TermRepr.FnRepr(name, args: List[TermRepr])` is
positional-only, so it could not represent `Fn{S, named}` even if it were
produced.

This is now a *deletion*, not a thing to replace: `TypeExtractor` covers types,
and the ~18 `Term` accessors (`term_functor_name`, `term_field(t, name)`,
`term_list_items`, `make_fn`, `replace_named_arg`, …) cover the rest from an
operation body.

### 4. Reflection rows say `Term` where they mean `Type`

```anthill
  entity SortProvidesInfo(
    sort_ref : Term,
    spec     : Term
  )
```

Both are types. Declaring them `Type` says what they are, points the reader at
`extract`, and lets the type lattice (`fact Eq[T = Type]`,
`fact Lattice[T = Type]` in `sort.anthill`) apply to them. The same question
applies to `SortInfo`, `OperationInfo`, `FieldInfo` and `TypeOf`.

`entity SortView(sort: Term)` is the remaining oddity: it declares one field
named `sort`, while the stored term carries the spec positionally plus the
bindings as *named* arguments — matching `spec: SortView(Triage, C: ?c)` in a
rule is refused with `'SortView' has no field 'C' (declares: sort)`. Since
`TypeExtractor.Parameterized(base, bindings)` is the post-WI-361 way to say the
same thing, `SortView` looks like a pre-convergence wrapper that outlived its
reason. Confirming that is phase 0.

## Design

No new sum type, and no typeclass. Three changes, in dependency order.

**A. Make the rule-level bridge bind.** Settle why an arity-2
`extract_sort_ref` goal succeeds without binding, and fix it. Everything else
here is cosmetic by comparison: this one line is the difference between
`safety.anthill` being writable and not.

**B. Decide the rule-level surface deliberately.** The resolver's `BuiltinTag`
list is what a rule may ask about a type, and it is currently an accident of
what someone needed:

| builtin | asks |
|---|---|
| `extract_sort_ref(?inst, ?result)` | the base sort of a bare or parameterized type |
| `resolve_sort_instantiation_param(?inst, ?param, ?value)` | one named binding, by name |
| `dispatch_carrier(?sort_ref, ?spec, ?result)` | the carrier a provision dispatches at |
| `is_entity_of(?sub, ?sup)` | the entity→sort lattice |
| `qualified_name` / `short_name` / `lookup_symbol` / `scope` / `kind` | `Symbol` ↔ `String` |

That set answers "which sort, and what did it bind" — enough for
`safety.anthill` and for most provision queries, and it is *not* the same
surface `extract` offers. Two surfaces is defensible (SLD wants goals that
delay, not values that are constructed); two surfaces *by accident*, with no
document saying which is which, is not. Write it down, and state the rule: **a
rule asks narrow questions about a type; an operation body reifies it.**

**C. Type the columns.** `Term` → `Type` on the reflection records whose fields
are types, and resolve `SortView` (phase 0's answer).

## First consumer

`examples/guardians/lib/safety.anthill` declares a three-tier composition — tier
1 the typer's per-implementation verdict, tier 2 a once-and-for-all theorem,
joined by an ordinary rule — and computes nothing, because tier 1 is a
`String`-keyed entity that nothing asserts. Its comment says the verdict is "NOT
YET EMITTED BY THE TYPER" and awaits a "missing seam".

**There is no missing seam.** The verdict is already in the KB as
`SortProvidesInfo`, and its presence in a *loaded* KB is the certificate: a
failed override-refinement check is a **load error**, so there is no KB to
query. "It loaded" is the proof. Tier 1 is a rule nobody could write, and (A) is
why.

## Interaction with other proposals

* [006](006-reflection-record-schemas.md) made two loader-private metadata rows
  into declared records so they could be *enumerated*. This is the same
  correction one level down: a declared record whose field is a type can be
  enumerated today and still not *decomposed* by a rule.
* WI-361 (representation convergence) is the decision this rests on — a `Type`
  IS an ordinary term, and `TypeExtractor` is its on-demand structure. Nothing
  here reopens it.
* **`WI-880`** — migrate the remaining hardcoded host registrations — owns the
  tier-1 decline, and this proposal **depends on** it. Its own feedback thread
  (WI-884, 2026-07-30) already asks to widen its acceptance to cover
  carrier-owned registrations; the `anthill.reflect` family is 29 more of them.
* `WI-20260822-ZJZS7` closed as delivered by `WI-20260826-VPEWK`; that fix
  covers `operation_map`-mapped host ops only. `WI-20260822-F0HHB` (*what should
  `=` mean in a rule body*) remains the neighbour — a goal that suspends reading
  as a solution.

## Open questions

1. **Why does the arity-2 `extract_sort_ref` goal succeed without binding?** This
   one is NOT WI-880's — it is a resolver `BuiltinTag`, tier 3, so the hardcoded
   decline does not explain it. Suspected: the relational view (WI-938) of the
   arity-1 declaration (`operation extract_sort_ref(inst: Term) -> Symbol`)
   shadows the arity-2 tag and resolves vacuously. Is the fix to declare it at
   arity 2, to have the tag win, or to refuse the ambiguity at load? Unowned as
   far as I can find.
2. **Should `extract` become a resolver builtin too?** It would give rules the
   full view rather than the narrow one, at the cost of constructing a
   `TypeExtractor` value inside SLD. (B) is the decision this depends on.
3. **Is `SortView` still needed?** If `TypeExtractor.Parameterized` says the same
   thing post-WI-361, it is a wrapper to delete — but it is the *stored* shape
   today, so deleting it is a term-encoding change, not a declaration change.
4. **Does `Term` → `Type` on a reflection column change any stored row?** It
   should not (both are opaque handles over the same terms), but a declaration
   the loader reads for schema purposes is exactly where "should not" wants
   measuring.

## Phasing

0. **Confirm `SortView`'s status** — pre-WI-361 wrapper, or load-bearing?
1. **(A)** — the rule-level bridge. Two halves with two owners: the tier-1
   migration is **`WI-880`'s** (and would give rules `extract` itself), while
   `extract_sort_ref`'s unbound result is unowned and is the cheaper of the two
   — it alone unblocks the consumer.
2. **(B)** — document the two surfaces and the rule between them; delete
   `TermRepr` / `KB.reify` / `KB.reflect`.
3. **(C)** — `Term` → `Type` on the reflection records.
4. **`safety.anthill` rewritten** with tier 1 derived, and a test that resolves
   `checked(GoodTriage, Triage)` — the measurement that would make the file live
   rather than aspirational.
