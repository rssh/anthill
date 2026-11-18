## Attributes

- id: WI-20261115-YR3N7-a-typed-column-s-domain-check
- created: 2026-11-15T13:37:28Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-18T10:08:26Z

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

## Changes

### 2026-11-18T10:08:20Z — feedback — user

BUILT (claude, 2026-11-18), on the design decided 2026-11-15, with WI-20260911-SXZ3G folded in (user, 2026-11-18).

ONE CLAUSE PER CONSTRUCTOR. `fill_derive::emit_fill_clauses` derives a sort's `fill` under the internal `<Sort>.__fill`, the constructor over fresh fields in each clause's head, base constructors first, each group in declaration order. A clause reads the dictionary only where a field's evidence names it (`Evidence::reads_self`: `fill(nil)` is a fact), its witness the head's constructor pattern. Every field is filled through `apply_domain` — `Evidence::Static`, the fill by name, is gone, and so is it in a typed head's ground bound (`typing::ground_fill_goals`). The `SortDomain` entry records the constructors (`ctors`) and how many clauses read the dictionary (`reads`); `fill_goal` hands that many copies of the WHOLE dictionary, one per slot of the relation's layout.

THE VALUE FACE. A relation citation builds its query from its first clause's head and refuses a compound one, so the cases cannot be `<Sort>.domain`'s clauses: the face is a clause of its own, `face(?x: Self) :- [read,] apply_domain(?self | Self, ?x)`, the bound its column type, recorded as one of the sort's domain relations (`record_domain_value_face`) so the typed-head sweep leaves it alone. A sort whose `.domain` names something else keeps its fill and has no face, as before.

REFINEMENT, the call's. `__refined_domain`, `lower_refined_domain` and `BuiltinTag::RefinedDomain` are deleted. Where `apply_domain`'s provider is a DERIVED domain and the value a constructor of another sort (`refining_sort_of`), `lower_refining_value` matches each instance of the asked sort the refining sort's `requires` give it against the HANDED dictionary's slots (`evidence_admits`): the slot each of its parameters meets is that parameter's condition, a parameter met twice must meet one type, a parameter no slot reaches is a fresh type pinned from the value, and a malformed dictionary is an error. So a dictionary a rigid caller handed is passed on, never rebuilt from the value's type (`instances_through_requires` is `pub(crate)` for it). Observably the same as the type-built one today — every dictionary the language builds names its type's own sort — and different once a provision hands a sub-domain of another provider (WT8WG item 2). A refining sort with no domain is checked by conformance, as before.

COST. The dispatch is asked in the step that lowered it (no depth, no fuel), and a derived fill's read a marker bound runs as no goal (`bind_citation_reads` reports which reads it bound). MEASURED on the CLI (the fewest `--max-steps` that answer; first answer / search exhausted): a typed `List[T = Product]` of n elements 13 + 27n / 25 + 38n before, 8 + 10n / 11 + 14n now; the same domain written by hand a clause per constructor 5 + 10n / 7 + 14n — the same per element. The ticket's state (`q_full`): 177 / 281 before, 73 / 105 now. Row 1 answered at the default depth already since 0WT09 (depth is nesting), so the disjunctive clause does not redden it: its back-out reddens the cost row and the no-case-untried row. Side anomaly 8 (an empty list inside `S` built by `st()` costing two elements more): gone — built by an operation costs the literal plus the call's one step, empty lists or not (`o00` 13 vs `l00` 12, `o11` 35 vs `l11` 34).

ORDER (SXZ3G). An unbound value matches every head of the fill, and the index's walk was in its `HashMap`'s run-to-run order: the first build generated `green, blue, red`. `query_view` now sorts its candidates by `RuleId` inside the facts-first grouping, a derived fill's in clause order alone (so a base constructor with fields declared before a nullary one keeps its place); `query_fact_heads` by `RuleId`; scaland's `KnowledgeBase.query` the same.

SPEC: kernel-language §5.3 (the derived members, the domain's "Not built" note replaced by what is built and its cost), §8.3 (the dispatch costs no fuel; clause order, facts first, a derived domain in clause order alone); proposal 060 §2.3 (the bound rows built and measured); 060-implementation §7.3 "DELIVERED 2026-11-18"; `reflect.anthill`'s `SortDomain` note.

ROWS: `wi_yr3n7_domain_check_test` (8): the state and one ten times larger at the default limits; per-element cost equal to the hand-written clauses'; no goal asked after a ground check's answer; the controls (rows 4 and 7, the partly bound order); generation in declaration order (`tagged` before the nullary `plain`); 060 §2.3's bound rows at a rigid type (`hasAt[X = Wrap[T = Colour]](wrap(v: red))`, `base`, generation counts 3 and 1); refining values filled at their own sort (`hasAt[X = Base](other(7))`, `hasAt[X = Wide[W = Colour]](narrow2(q: green))`); a refinement's instance checked whole (`Twin[Q] requires Pair[A = Q, B = Q]`). `wi_sxz3g_clause_order_test` (3); scaland `ClauseOrderTest` (3).

BACK-OUTS, measured on the final tree over 97 rows (this file, sxz3g, j9ssg, wi743, shed7, wt8wg, 5g28a, atvc1), each at its site: [W] HEAD's sources — 4 (cost, no case untried, SXZ3G ×2); [F] the dispatch charged — 1; [R] a bound read run — 1; [C] refinement off — 5; [T] a parameter's later slot uncompared — 1; [H] the no-domain case unchecked — 0, by design (stated); [N] a typed head's fill by name — 1; [S] the clause-order sort off — 12, the set moving with the seed; [O] facts-first for a fill — 1. Scaland [S]: 2 of 3, the bound-position control passing.

/code-review high: 10 findings, 8 fixed, 2 skipped. FIXED: the no-domain refining case admitted unchecked (now the conformance check of the path before; [H] measures no row, stated); a parameter met twice compared once ([T]); `evidence_admits` reporting a malformed dictionary as an error, and a tuple or arrow slot compared as a type; §5.3's derived-members bullet and the fuel sentence's over-reach; SXZ3G delivered with this, the Γ overlay's candidates left as they are — each is the goal itself up to variable identity, so their order is unobservable; `query_view` skips the lookup and the sort for a single candidate; the bound-read check reads `bind_citation_reads`' report instead of looking the symbol up again. SKIPPED: a memo of the refinement's instances per (sort, refined sort) — the path is taken by refining values only; one dictionary for every read slot instead of `reads` copies — `Rc` clones, `reads` the reading constructors (one or two), and the marker's layout stays one slot per read.

FAMILIES: green, no verdict moved. GATE: 12 272 passed / 0 failed / 17 ignored (36 binaries; the previous 12 261 and the 11 new rows); anthill-core one-shot and two-step 11 195 / 0 / 9 each. SCALAND testFull: 1 + 51 + 810 = 862.

