## Attributes

- id: WI-20261115-32WQJ-bounded-quantifiers-range-only
- created: 2026-11-15T11:45:46Z

- status: Open
- status_agent: user
- status_at: 2026-11-15T11:45:46Z

- acceptance: cargo-test, scaland-sbt-test

## Description

BOUNDED QUANTIFIERS RANGE ONLY OVER A LIST SPINE: A COLLECTION SHOULD PROVIDE A TYPECLASS THAT `forall … in` / `some … in` DISPATCH TO (user, 2026-11-15: "Collection should provide some typeclass for forall_in").

FOUND while modelling a shop's state as a value: `entity ShopState(products: Set[T = Product], …)`, with invariants such as `rule r(ShopState(products: ?ps)) :- (forall ?p in ?ps: ?p.price > 0)`. That cannot be written over a `Set`, so the model uses `List` plus key-uniqueness invariants.

MEASURED on 53a0d453b (anthill CLI of 2026-11-13):
  1 `(forall ?x in {1, 2}: ?x > 0)` answers conditional, residual `(forall ?_ in {1, 2}: gt(?_, 0))`
  2 `(some ?x in {1, 2}: ?x > 1)` answers conditional
  3 `(forall ?x in insert(insert(empty(), 1), 2): ?x > 0)`, the Set algebra's own spine: conditional
  4 `(forall ?x in {1, 2}: ?x > 5)`, a FALSE body: conditional, never refuted
  5 `(forall ?x in [1, 2]: ?x > 0)` answers true (the List control)
  6 `contains({1, 2}, ?x)`: no solutions. Set has no enumerating view, so nothing else can range over it either
  7 a `Set[T = Product]` entity field destructured and quantified over: conditional
And it is silent where it matters most: `constraint c: forall ?n: marker(?n) -: r4`, over row 4's false quantifier, PASSES `anthill check` (exit 0). An undecided quantifier satisfies a quantified constraint.

THE CAUSE. `step_bounded_quant` (kb/resolve.rs) takes the elements from `bounded_list_elements`, which walks a ground `cons`/`nil`/`ListLiteral` spine. Anything else is delayed as floundering (WI-519), so a ground Set is treated like an unbound list. kernel-language §5.3 (WI-027) states the restriction ("any term that evaluates to a ground cons/nil list").

PROPOSED. The quantifier dispatches on the collection's carrier to a typeclass instead of hard-coding the List spine:
- The candidate already exists: `FiniteCollection`, whose `collect(c) -> List[T = Element]` is the stated "finiteness PRIMITIVE". `List` and `Map` provide it (Map with `Pair` elements, `E = {}`); `Set` provides neither it nor `Iterable`.
  Whether it is `FiniteCollection` or a dedicated spec (for example, one whose instance is an enumerating relation, so a symbolic collection need not be materialized) is the design decision to make first. A goal performs no effects, so only an instance whose access effect is empty can serve.
- List's instance is today's spine walk, unchanged. Set provides the typeclass over its `insert`/`empty` normal form, with elements de-duplicated by its own `Eq` (Set equality is extensional, WI-616). Map ranges over its entries.
- A collection whose carrier provides no instance is a LOAD ERROR at the quantifier, naming the typeclass. A collection that is not yet ground is still delayed, as now.
- RELATED: WI-20260911-09E6M notes that a bounded `forall_in` over a derived domain is the future link of the same machinery.

ACCEPTANCE: rows 1-4 and 7 are decided. Row 4 is false, so its constraint FAILS `check`, while the true rows answer true unconditionally. Row 5 is unchanged. A `Map` quantifies over its pairs. A carrier with no instance is refused at load, naming the typeclass. kernel-language §5.3 is updated. Back-out: with the dispatch removed, rows 1-4 return to conditional and the row-4 constraint passes again.

## Changes

### 2026-11-15T13:37:48Z — feedback — user

MEASURED 2026-11-15 on 53a0d453b: another row in the same code path. The collection is not evaluated, so a FIELD ACCESS used as the collection leaves the quantifier undecided, even when the receiver is typed. Over `entity S(products: List[T = Product], orders: List[T = Order])`, `rule total_positive_dot(?s: S) :- (forall ?o in ?s.orders: ?o.total > 0)` answers conditional for a ground S, with residual `(forall ?_ in field_access[Name = "orders"](S(...), "orders"): …)`. The typer has resolved the dot to a typed `field_access`, but `step_bounded_quant` takes the collection as written and `bounded_list_elements` sees no list spine. The workaround is to destructure in the head (`rule r(S(orders: ?os)) :- (forall ?o in ?os: …)`), which is decided. With an untyped `?s`, the dot is not dispatched at all (WI-20261105-MP9C8). When the quantifier dispatches to a collection typeclass, it should evaluate the collection expression first.

