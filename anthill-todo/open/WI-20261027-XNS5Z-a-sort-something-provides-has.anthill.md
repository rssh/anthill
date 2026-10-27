## Attributes

- id: WI-20261027-XNS5Z-a-sort-something-provides-has
- created: 2026-10-27T20:07:15Z

- status: Open
- status_agent: claude
- status_at: 2026-10-27T20:07:15Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing, reflect

## Description

A SORT SOMETHING PROVIDES HAS NO `TypeValue`, SO AN UNRELATED PROVISION CHANGES A PROGRAM'S VERDICT. Observed on WI-20260908-9WVT7 (2026-10-17), filed from its leftovers with the user, 2026-10-27.

MEASURED 2026-10-27 on e9587427:

    namespace test.collnone
      import anthill.prelude.{Int64, Type}
      import anthill.reflect.{TypeValue}
      sort Coll
        sort T = ?
        operation size(c: Self) -> Int64
      end
      operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = TypeValue.type_value[T = B]()
      operation spec[C](s: Coll[T = C]) -> Type requires TypeValue[T = C] = tyOf(s)
    end

loads. Add a provider beside it,

      sort Bag
        entity bag(n: Int64)
        provides Coll[T = Int64]
        operation size(c: Bag) -> Int64 = 1
      end

and the same `spec` is refused: "requirement `anthill.reflect.TypeValue[T = test.collnone.Coll[T = C]]` cannot be supplied for call to `test.collnone.tyOf`; its carrier is `test.collnone.Coll[T = C]`, and no row of `anthill.reflect.TypeValue` answers here, and none may be written: every instance is derived, one for a sort that is no spec, …".

WHY. `type_value_derive.rs` skips every sort some provision names as its spec, on purpose: a spec's row stood beside a provider's own by subsumption, and `List[T = Int64]` was refused "ambiguous among providers: anthill.prelude.PersistentCollection, anthill.prelude.PartialEq, …" before the filter. kernel-language.md ("Every `TypeValue` instance is derived") says "A sort's instance is the loader's", with no exception for a spec.

QUESTION FOR THE USER, before implementing. (a) Derive a `TypeValue` for every sort, a spec too, and let §8.7's "Which one a call gets" pick a carrier's own row over one it reaches through a spec, so `List[T = Int64]` is answered by `List`'s; the second program then loads as the first does. (b) Keep the exclusion, state it in the spec, and decide it by what the sort declares rather than by whether something provides it, so the two programs have one verdict. WI-20261025-27050 (C5) takes `TypePattern` off `TypeValue` for a spec; that does not give a spec a `TypeValue`.

ACCEPTANCE: the two programs above with one verdict, the decided one, with rows that drive `spec` where it loads; `type_value[T = List[T = Int64]]()` still `List[T = Int64]`; full gate green; families green.

