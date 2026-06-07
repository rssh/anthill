# Written effect rows on cross-sort carriers — implementation design (WI-386)

**Status:** Design (2026-06-04). **Prerequisite for:** WI-380 (the stdlib
threading rewrite), which discharges WI-368 (`length(collect(List.iterator(xs)))`
pure). **Builds on:** WI-375 (written effect rows in operation-return type
positions, delivered), WI-379 (bidirectional inference, delivered), WI-356/WI-325
(provider admissibility + abstract spec-op requires-coverage). **Relates:**
[`expansion-during-unification.md`](expansion-during-unification.md) §5,
[`type-parameter-scoping.md`](type-parameter-scoping.md) §5.

## The problem

WI-380 wants a pure carrier to **write** its observation effect in the type, so
the row is carried structurally rather than reconstructed by a close-to-pure
default (which is unsound for effectful carriers — §5 of the threading docs):

```
operation iterator[Elem](l: List[T = Elem]) -> Stream[T = Elem, E = {}] = l
```

`List` provides `Stream` cross-sort (`fact Stream[T = T]`), and `iterator`'s body
returns a `List` value as a `Stream`. WI-375 already lets `Stream[T = Int64, E = {}]`
be written in an **operation-return** type position. The new difficulty is that
the **carrier** must declare its observation effect, and a *cross-sort* carrier
writing an effect row touches three typer/loader subsystems. Each was probed and
the chain is fully diagnosed below; **WI-368's acceptance is proven achievable in
isolation** (see §"Acceptance"). The remaining blocker is **FIX 3**.

## FIX 1 — the fact-head `{}` loader gap → routed around by `provides`

`fact Stream[T = T, E = {}]` **fails to load**: `unresolved name '{}'`. The empty
row `{}` is handled in convert.rs's **type** path (`convert.rs:462` →
`TypeExpr::EffectRow`) but a fact head is a **term**; the `{}` binding value
becomes a `Term::Ref("{}")` which `convert_term` strict-resolves
(`load.rs:4702` → `remap_symbol_strict` → `UnresolvedName`).

**Resolution — no parse surgery needed.** A `provides` *clause* lowers its spec
bindings through the **type-aware** path: `load_provides_clause` →
`sort_inst_to_value` (`load.rs:6226`), whose `_` arm routes to
`type_expr_to_value` → `lower_effect_row` (`load.rs:6140`), which builds the
canonical `effects_rows` term. So:

```
provides Stream[T = T, E = {}]      -- loads (type path)
fact Stream[T = T, E = {}]          -- does NOT load (term path → Ref("{}"))
```

WI-380 uses the `provides` clause. Making the `fact`-head term path *also* lower
`{}` (for `fact`/`provides` convention uniformity) is a smaller, optional
follow-up — not required.

## FIX 2 — cross-sort provider-view in the subtype check (IMPLEMENTED, INNOCENT)

`types_compatible(List[Elem], Stream[T = Elem, E = {}])` fails because
`parameterized_compatible_view` (`typing.rs:9382`) iterates the *expected*
bindings and, for a param not present in the *actual*'s own bindings, does
`None => return false` (`~9449`). The cross-sort actual (`List`) carries only
`T` (matched because `List` and `Stream` share the short symbol `T`); the
expected `E = {}` has no match on the `List` side → reject. The actual is never
translated through its provider fact into the expected sort's param space.

**Fix:** in the `None` arm, when `actual_base != expected_base` (the actual
provides the expected), consult `provider_spec_view_bindings(actual_base,
expected_base)` for the missing expected param (matched by short name) and check
its supplied value against the expected binding; only a genuinely absent/
incompatible param rejects. This **loosens the cross-sort case only** —
same-base checks keep the strict "actual must carry the param" rule, so it cannot
newly-reject existing code.

**Status: implemented and proven innocent in isolation** — with this fix kept and
the `List` provision reverted, `wi357_element_typing` (all 4) and `wi210_dispatch`
(all 20) pass. (Reverted from the working tree only because it is untested
without FIX 3; re-apply it as the first step of the implementation.)

## FIX 3 — abstract/requires-coverage must treat a provided concrete `E` as covering (THE BLOCKER)

Once `List` *declares* its Stream observation effect (`provides Stream[T = T,
E = {}]`), the WI-325/WI-356 **abstract spec-op requires-coverage** check starts
demanding it of consumers:

```
type mismatch in anthill.prelude.Stream.head.requires:
  expected `requires Stream[…]` covering abstract type parameter,
  got missing `requires Stream[E = …]` on enclosing sort
```

i.e. a Stream spec op (`head`, `splitFirst`) consumed **on a `List`** now needs
the enclosing op to `requires Stream[E = …]`. This **regresses delivered
functionality** — `wi357_element_typing` (element threading) and `wi210_dispatch`
— because the check sees `Stream.E` as an *uncovered abstract parameter* once the
provision mentions it, instead of recognizing that the provision binds it to the
*concrete* empty row `{}`.

**Fix direction:** in the abstract/requires-coverage check, a spec parameter that
the carrier's `SortProvidesInfo` binds to a **ground** value (here `E = {}`) is
**covered** — exclude it from the "uncovered abstract parameter" set that demands
a `requires`. Effect-row params bound to a written row are concrete, not
abstract. This is the sensitive part (WI-325/356 area); it must keep demanding
`requires` for genuinely-abstract params (a `C provides Iterable` walk).

## Acceptance (proven in isolation)

With FIX 2 + the `provides` clause + the written-`E` iterator applied together
(FIX 3 stubbed by the fact that `wi357`/`wi210` were temporarily out of the run),
`wi368_iterator_threading_test` **both cases pass**:

```
operation walk(xs: List[T = Int64]) -> Int64 = length(collect(iterator(xs)))   -- PURE, no ?_
operation gather(xs: List[T = Int64]) -> List[T = Int64] = collect(iterator(xs)) -- List[Int64]
-- and `gather -> List[T = String]` is correctly REJECTED
```

So the element threads and the observation effect closes to `{}` — WI-368's
acceptance. FIX 3 is the only thing standing between this and a green full suite.

## Recommended implementation order

1. Re-apply **FIX 2** (cross-sort provider-view; isolated-innocent).
2. **FIX 3** — abstract/requires-coverage: provided-concrete `E` counts as
   covered. Verify `wi357` + `wi210` stay green.
3. Switch `List` to `provides Stream[T = T, E = {}]` and write
   `iterator[Elem](l: List[T = Elem]) -> Stream[T = Elem, E = {}]`.
4. Wire + un-`#[ignore]` `wi368_iterator_threading_test`; confirm WI-368 pure +
   element threaded; full anthill-core green.
5. WI-380: extend to the other producers (`Stream.iterator`, and confirm
   `collect`/`splitFirst`/`takeN`/`head`/`tail`/`isEmpty` thread from the written
   input rather than needing their own rewrite — they consume via `Stream.T`/`E`).

## Code pointers

- `parameterized_compatible_view` — `typing.rs:9382` (FIX 2 in the `None` arm).
- `provider_spec_view_bindings` — `typing.rs:6327`.
- `sort_inst_to_value` (provides-clause spec lowering) — `load.rs:6226`;
  `lower_effect_row` — `load.rs:6140`.
- fact-head term path that mishandles `{}` — `convert_term` `Term::Ref` arm
  `load.rs:4702`; the `unresolved name` originates at `remap_symbol_strict`
  `load.rs:4390`.
- abstract/requires-coverage (FIX 3) — the WI-325/WI-356 check that emits the
  `requires Stream[…] covering abstract type parameter` diagnostic.
