## Attributes

- id: WI-20261115-YR3N7-a-typed-column-s-domain-check
- created: 2026-11-15T13:37:28Z

- status: Open
- status_agent: user
- status_at: 2026-11-15T13:37:28Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261115-0WT09-resolution-depth-counts-steps

## Description

A TYPED COLUMN'S CHECK OF A BOUND VALUE GENERATES INSTEAD OF CHECKING: a sort's derived domain is ONE clause whose body proposes each constructor to the value in turn, so checking a ground value runs the generator over every piece of it, and a lookup over a small ground state exhausts the default --max-depth and answers nothing (found 2026-11-15, typing the rules of a shop state modelled as a value).

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
The failure is quiet: "no solutions" plus an UNDECIDED note. Under a negation the answer becomes conditional, and an undecided goal satisfies a quantified constraint without any error (see WI-20261115-32WQJ).

MEASURED 2026-11-15 on the CLI of 2026-11-14 (the smallest --max-depth that answers, by bisection):
  5 The cost is per piece of the value: `Int64` 5; an entity of one / two `Int64` fields 9 / 12; `List[T = Int64]` of n elements 7 + 9n; each `Product` in the state +16, each `Order` +21. `q_full`'s 107 is its parts added: the untyped query 6, `?s: S`'s check about 87, `?o: Order`'s about 14 (the depth counts steps on the branch — WI-20261115-0WT09).
  6 The cause is the derived clause's SHAPE (`kb/fill_derive.rs`, `emit_fill_clause`): `S.domain(?x) :- push_choice(push_and(unify(?x, S(…)), …), __refined_domain(?x, S))`, and per list cell `push_choice(unify(?x, nil), push_and(unify(?x, cons(…)), apply_domain(?self, ?t), apply_domain(sub, ?h)), __refined_domain(…))`. Every piece is proposed each constructor: `nil` fails, `cons` matches, and the refined case stays on the search, untried. Written by hand as one clause per constructor, the constructor in the head (`fact ldom(nil)`, `rule ldom(cons(head: ?h, tail: ?t)) :- ldom(?t), pdom(?h)`, `rule pdom(Product(id: ?i, price: ?p)) :- intdom(?i), intdom(?p)`), the same lists cost 2 + 6n (8, 14, 26 for n = 1, 2, 4) against the typed column's 7 + 16n (23, 39, 71), and an unbound list generates the same lists in the same order.
  7 The guard in front of the body does not do the deep part: `domain(?s, S)` accepts `S(products: [1])`, built from a column of mixed types (`fact h3(1)`, `fact h3(Product(1, 2))`, `rule mk3(?s) :- h3(?e), ?s <=> S(products: [?e])`); only the fill refuses it, so the fill cannot simply be skipped for a ground value.
  8 Side anomaly, not explained: an EMPTY list inside `S` built by `st()` costs two elements' worth more than the formula (`products: []` +32, `orders: []` +42); the literal `S(products: [], orders: [])` costs 16, and neither an entity with one list field nor one with two list fields of the same element type, built by an operation, shows it. Recheck it on the new shape.

DECIDED (user, 2026-11-15: "we start generating instead of checking", "we should change generation", "build right architecture at first"; proposal 060 §2.3 "The head decides the mode", kernel-language §5.3, 060-implementation §7.3 "DECIDED 2026-11-15"):
  1 ONE FILL CLAUSE PER CONSTRUCTOR, the constructor in the head, base constructors first. Clause selection decides the mode: a bound value selects its one clause, a check; an unbound one matches every head in clause order, generation in today's order.
  2 Fields are filled in the body, recursive fields first, and every fill call is the dispatching `apply_domain(evidence, v)` — no fill called by name.
  3 THE DICTIONARY NAMES WHOSE FILL RUNS, never the value (user, 2026-11-15: "We created fill() because we have issue, when something is rigid value, we should call fill for rigid value, and mechanism for this is dictionary"). `apply_domain(D, v)` runs the member of the provision `D` names; inside `countAt[X]` the asked type is a rigid `X`, a name, and only the dictionary knows its domain, the sub-domains it carries included. EVERY SUB-DOMAIN BELOW `D` COMES OUT OF ITS SLOTS: a recursive field is handed `D` again, a field typed by a parameter `D`'s condition slot; a type builds a dictionary only at the top, where no caller hands one (user, 2026-11-15: "domain can't accept custom subdomains from dictionaries in rigid types"). REFINEMENT is the one case a DERIVED `impl` adds, applied by the call: where `D`'s `impl` is derived and `v`'s constructor is not one of that sort's own, the call runs the fill of `v`'s own sort with a dictionary put together from `D`'s slots. `lower_refined_domain` does NOT do that today — it keeps only the conditions that are types and drops one held as a dictionary — so moving the case into the call must pass those conditions on. A hand-written or primitive `impl` adds no such case. The `__refined_domain` clause is deleted (indexed, its head would list the refining sorts' values in generation; with a variable head it would be tried and refuted beside every value), and a domain still lists its own sort's constructors.
  4 The dictionary is read only in the clauses that read a condition (`fill(nil)` is a fact).
  5 A primitive keeps its one clause, the waiting type check.
Built on this shape, not here: `Bool`'s literal clauses (WI-20260911-5TK6B), fair interleaving (WI-20260911-09E6M), a hand-written domain's provision (WI-20260911-WT8WG, its item 3). Depth as nesting is WI-20261115-0WT09, which acceptance A's larger state needs.
Withdrawn from this ticket's first proposal: discharging the guard at load where the caller's type is already known.

THE THREADED FORM, on the rigid case (`countAt[X]`, `wrapped()`, a bound `hasAt`): proposal 060 §2.3, "How `fill` is threaded — a rigid variable".

TO VERIFY at the work (060-implementation §7.3, "DECIDED 2026-11-15"):
  - the fill relation's column type rides the typed variable of its head today (`install_rule_type_bounds` in `emit_fill_clause`), and the value face still reads it until WT8WG retires it; with a constructor in the head it comes from the sort's `SortDomain` entry;
  - THE THREADING: (a) each clause that reads a condition has its own dictionary read and `fill(nil)` has none — the marker already lays dictionaries out per clause (`resolve::bind_citation_reads`); (b) the derived path hands ONE dictionary (`fill_goal`: `vec![dict]`), right only while the relation is one clause — it must hand the provision's WHOLE dictionary to each reading clause; the `Written` arm is no model, since it routes the `SortDomain` read alone and hands every other read `__unrouted`; (c) a read's witness is the head's constructor pattern, not `?x`.

ACCEPTANCE (cargo-test; scaland has no typed heads — its loader drops the bound — so scaland-sbt-test only stays green). Every row driven:
  A Row 1 answers true at the default depth; a state ten times larger does too once WI-20261115-0WT09 is in.
  B A typed column over a `List[T = Product]` costs the hand-written clauses' 6 steps per element (row 6), not 16, and a ground check leaves no case untried behind it.
  C Row 4's wrong-type control answers no solutions; row 7's `S(products: [1])` is still refused by the typed column; the partly bound `has_order(?s, Order(id: ?id, status: CREATED))` still finds `?id = 2`.
  D `wi_j9ssg_refined_value_in_domain_test` unchanged — a refining value is in the refined domain, an unbound column lists the sort's own constructors — and generation order unchanged: `an_infinite_domain_is_fair`, alphabet-words 27 / 12, tiny-sat 2, map-colouring 6.
  E The rigid rows unchanged (`wi_5g28a_sort_domain_test`: `countAt[X = Colour]` 3, `[X = Letter]` 2; `wi_shed7_fillable_test`: `countAt[X = Wrap[T = Colour]]` 3, `firstWrapped` one `wrap` around `red`), and new rows for 060 §2.3's bound reading: `hasAt[X = Wrap[T = Colour]](wrap(v: red))` answers 1 through `Wrap`'s one clause and `Colour.fill(red)` alone, and `hasAt[X = Base](other(7))` under `sort Other requires Base` answers 1, filled at `Other`.
Back-out: the disjunctive clause restored reddens B, and row 1 at the default depth.

