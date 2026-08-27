# Library: reaching a type's structure from a rule

## Status

Draft 2026-08-26, **updated 2026-08-27 after `WI-880` landed**. No driver WI yet.
Found while trying to write `examples/guardians/lib/safety.anthill` as a rule over
reflection facts.

**Its largest finding is already fixed.** WI-880 migrated the whole
`anthill.reflect` surface off hardcoded registration, so a rule can now read a
term and the associated soundness gap is closed. What survives is smaller and is
recorded below with what changed: a relational view that does not bind, a
non-ground spec view that (correctly) suspends, an unowned resolver builtin, and
the `Term`-vs-`Type` column typing.

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

### 1. Closed by WI-880 — a rule CAN now read a term

**`WI-880` landed 2026-08-27** ("the reflection surface is host-mapped, and host
arguments reduce"), migrating all 26 `anthill.reflect` operations off hardcoded
registration onto `operation_map` — twenty of them through a binding block whose
target is the NAMESPACE, since they have no carrier. Its own summary states the
consequence this proposal reported: *"NO RULE COULD READ A TERM … `not(term_as_int(7)
= some(7))` answered 1 DEFINITE — a positive conclusion drawn from a term the rule
never read."*

Confirmed live here:

```
  rule read(1) :- term_as_int(7) = some(7)        ->  1     (was 0, decided false)
  rule bad(1)  :- not(term_as_int(7) = some(7))   ->  0     (was 1, unsound)
```

So §"The gap"'s first item is closed, and the soundness hole with it.

### 2. What is left, measured after WI-880

Three things, and only the first is squarely this proposal's.

**(a) A rule body can TEST a result, not BIND one.** `WI-20260827-2YHZ3`. WI-880
makes a host op REDUCE, and this is about what happens to what it returns —
neither WI-880 nor VPEWK touched it. Measured with a bodied op and a host op side
by side:

| form in a rule body | bodied | host |
|---|---|---|
| `f(3) = 6` — test against a known value | 1 ✓ | 1 ✓ |
| `f(3) <=> 6` — unify against a known value | 1 ✓ | — |
| `f(3) <=> ?r` — unify into a free variable | 1, **unbound** | 1, **unbound** |
| `f(3, ?r)` — relational view (WI-938) | 1, **unbound** | **0** |

**An earlier draft of this proposal told the reader to write `extract(?v) <=> ?e`
instead of the relational view. That is wrong** — it succeeds without binding too.
Only the ground-test row works, and the unbound result then flows onward:
`twice(3) <=> ?r, Int64.gt(?r, 5)` answers 1 DEFINITE.

**(b) A meta-predicate's argument need not be ground, and the bridge insists.**
`WI-20260827-1ZG70`. Measured — the residual names it exactly:

```
residual: unify(term_functor_name(SortView(Iterable,
            E: EffectsRows(effects_expr: merge(left: open(tail: ?_),
                                               right: open(tail: ?_))), …)), ?_)
```

Suspending is right for `Int64.add` — a logic variable is not a number — and wrong
here: the functor of `some(?x)` **is** `some`, whatever `?x` is, which is what a
meta-predicate is for. So after WI-880 the surface is visible to the gate and
still unusable on the population it was migrated for. **`SortProvidesInfo` itself
is not the problem** — it is an ordinary relation and enumerates fine; the
suspension is entirely in the host call downstream of it.

**(c) `extract_sort_ref` still succeeds without binding.** Unchanged by WI-880 —
it is a resolver `BuiltinTag`, not a host registration, so neither that ticket nor
VPEWK touches it. Still unowned. See open question 1.

### 2b. A side effect worth knowing: guardians is no longer CLI-queryable

Now that reflect operations are host-mapped, bridging one builds an interpreter,
which validates the whole binding block. `examples/guardians`' `operation_map`
names host functions the *test harness* registers (`guardians_render_task` &c.),
so any query over that example whose goal bridges a host op now panics:

```
broken binding block: operation_map names host function "guardians_render_task"
for guardians.FileHarness.render_task, which the rust runtime does not provide.
```

`anthill load examples/guardians` is unaffected (loading builds no interpreter),
and the in-test path is unaffected (`register_pipeline` supplies them). The
diagnostic is good — it says outright that it "may surface at a call that has
nothing to do with" the named operation. Recorded because it changes how this
proposal's consumer can be exercised: from the Rust test, not from `anthill query`.

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

**A. Finish the rule-level bridge.** WI-880 did the large half. The rest is three
tickets, and none of them is this proposal's to solve: `WI-20260827-2YHZ3` (a
rule body cannot bind a result), `WI-20260827-1ZG70` (a meta-predicate's argument
need not be ground), and `extract_sort_ref`'s unbound result, still unowned.

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
1. **(A)** — ~~the tier-1 migration~~ **DONE by `WI-880`, 2026-08-27.** The rest
   is `WI-20260827-2YHZ3` + `WI-20260827-1ZG70` (+ `extract_sort_ref`, unowned).
   The consumer needs BOTH: one decides whether the call runs, the other what
   happens to its result.
2. **(B)** — document the two surfaces and the rule between them; delete
   `TermRepr` / `KB.reify` / `KB.reflect`.
3. **(C)** — `Term` → `Type` on the reflection records.
4. **`safety.anthill` rewritten** with tier 1 derived, and a test that resolves
   `checked(GoodTriage, Triage)` — the measurement that would make the file live
   rather than aspirational.
