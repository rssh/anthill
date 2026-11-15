## Attributes

- id: WI-20261115-YR3N7-a-typed-column-s-domain-check
- created: 2026-11-15T13:37:28Z

- status: Open
- status_agent: user
- status_at: 2026-11-15T13:37:28Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A TYPED COLUMN'S DOMAIN CHECK OF A GROUND VALUE SPENDS RESOLUTION DEPTH IN PROPORTION TO THE VALUE'S SIZE: a lookup over a small ground state exhausts the default --max-depth and answers nothing (found 2026-11-15, typing the rules of a shop state modelled as a value).

MEASURED on 53a0d453b (anthill CLI of 2026-11-13):

```anthill
namespace ty
  import anthill.prelude.{List}
  import anthill.prelude.List.{cons}
  enum OrderStatus
      entity CREATED
      entity PAID
  end
  entity Product(id: Int64, price: Int64)
  entity Order(id: Int64, status: OrderStatus, total: Int64)
  entity S(products: List[T = Product], orders: List[T = Order])
  fact member(?x, cons(head: ?x, tail: ?))
  rule member(?x, cons(head: ?, tail: ?t)) :- member(?x, ?t)
  rule has_order(?s: S, ?o: Order) :- ?s <=> S(orders: ?os), member(?o, ?os)
  operation st() -> S = S(products: [Product(1, 10), Product(1, 20)], orders: [Order(1, PAID, 5), Order(2, CREATED, 0)])
  rule q_full :- ?s <=> st(), has_order(?s, Order(2, CREATED, 0))
end
```

  1 `q_full` answers "no solutions, search truncated at --max-depth". The answer is true: the state holds that order, and every argument is ground.
  2 With `--max-depth 1000` the same query answers true. So nothing loops; the check is merely deep.
  3 Any of these makes row 1 answer true at the default depth: untype either column (`?s: S` or `?o: Order`); drop S's `products` list; give Order two fields instead of three. Writing the state as a literal instead of `st()` does not help: it still fails.
  4 Controls: a single typed column over a ground value is fine at this size. `rule tc(?v: C) :- true` answers true for `tc(C(1, ON))`, and no solutions for the wrong-type `tc(A(1))`.
So the `domain(?x, T)` goal a typed column prepends to its clause (WI-742) is resolved as a goal chain over the value, and its depth grows with the term. Two typed columns over a modest ground state already exceed the default budget of 100, so a realistic state (a few lists of entities) cannot be passed through typed relations at all. The failure is quiet: "no solutions" plus an UNDECIDED note. Under a negation the answer becomes conditional, and an undecided goal satisfies a quantified constraint without any error (see WI-20261115-32WQJ).

PROPOSED.
- The domain check of a GROUND argument is a structural type test of the term against the column type, and spends no resolution depth. Only an unbound or partly bound argument goes through the derived domain (enumeration, WI-743).
- Where the argument's type is already known at the call (`?s <=> st()` with `st() -> S`, a typed parameter, a typed column of the caller), the guard can be discharged at load and not generated.

ACCEPTANCE: row 1 answers true at the default depth, and so does a state ten times larger. Row 4's wrong-type control still answers no solutions. A partly bound argument (`has_order(?s, Order(id: ?id, status: CREATED))`) still finds ?id = 2. Back-out: with the structural test removed, row 1 is truncated again.

