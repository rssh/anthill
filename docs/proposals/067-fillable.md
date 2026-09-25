# 067: `Fillable` — a type whose logical variables can be filled, through a dictionary

## Status: Draft (2026-09-25). Decided in discussion while designing WI-20260911-5G28A's S3b (`docs/design/060-implementation.md` §7.3). The names are the user's.

## Relates to: [060](060-clause-level-requirements-and-typed-heads.md) §2.2–§2.3 (a sort's domain — an implementation of `Fillable`), [`060-typedomains-implementation.md`](../design/060-typedomains-implementation.md) (the requirement channel), [058](058-modular-instances.md) (dictionaries; §3.8 conditional provisions), [052](052-rules-as-stream-valued-operations.md) (`Relation`), [056](056-variadic-argument-capture.md) (the `...` spelling).

## Tracked by: WI-20260925-SHED7. WI-20260911-5G28A depends on it.

## The problem

MiniSat over `List` works today — tiny-sat (§4) — because the program names the collection's shape
and its element type. A solver written ONCE, for any collection, can name neither: it needs an
interface it can REQUIRE — "a logical variable of this type can be filled with a value" — reached
through the dictionary its caller hands in, as `Eq` is for equality.

Nothing states that interface. The nearest thing, a sort's DOMAIN (060 §2.2), is ONE way to fill
a type — the one derived from the sort's constructors — and a solver must also accept a type
filled some other way: a primitive, which has no constructors, or a collection an author builds.

## 1. The spec

```anthill
namespace anthill.reflect
  sort Fillable
    sort T = ?
    rule fill(?x)          -- fills ?x with a value of T: generates in mode (out), checks in mode (in)
  end
end
```

- **A RULE, not an operation.** It has many answers, and a function returns one value.
- **DECLARED UNTYPED**: typed, it would be a typed head whose generated goal runs `fill` itself
  (060-typedomains §0).
- **Fresh variables come from opening `fill`'s clauses.** A clause that unifies `?x` with
  `cons(head: ?h, tail: ?t)` mints `?h` and `?t` when it opens, as every clause does; no kernel
  operation creates them.
- **Its implementations** are the provisions of it: a sort's derived domain (060 §2.3), a
  primitive's, a collection builder's, or one an author writes.

## 2. `Fillable` is a MONOID — `combine` and `empty`

`combine(f, g)` fills with `f`'s answers, then `g`'s — ordered concatenation; `empty` has no
answers, its `fill` fails (user, 2026-09-25). `combine` is associative and `empty` is its identity.

It is NOT commutative, and the order is semantic: `fill` may have infinitely many answers — a
recursive type's does — and an infinite first operand starves the second. So an author who writes
`combine` states the order, finite operands first; 060 §2.3 derives a sort's domain that way.

It is not a group: an inverse would be a `Fillable` undoing another's answers — a complement, which
cannot be generated.

## 3. A dictionary carries it — and only points

A dictionary never fills a variable. It names WHOSE `fill` runs — its `impl` — and, for a
conditional provision, carries one sub-dictionary per condition, naming the parts'. For example,
with the implementation 060 §2.3 derives for `List`, `D = Dictionary(Dictionary(impl: Bit), impl:
List)` for `List[T = Bit]`:

```
fill ?x with D           impl List → List's fill:  ?x <=> cons(head: ?h, tail: ?t)   ?h, ?t fresh
  fill ?t with D         impl List → List's fill:  ?t <=> nil()
  fill ?h with sub(D, 0) impl Bit  → Bit's fill:   ?h <=> t()
                                                   ?x = [t]
```

`fill` is found from `impl` through the provisions, as an operation member is found through
`SortOpsTable` — which gains rows for a spec's RULE members.

## 4. Worked example — MiniSat over `List`, and the generalization we want

tiny-sat (`examples/classic-mini/tiny-sat/sat.anthill`) is MiniSat over `List`, and it works today
— MEASURED by `classic_mini_test.rs`: exactly two models, both definite.

```anthill
sort Bit { entity t  entity f }
fact neg(t(), f())
fact neg(f(), t())
rule or2(?a, ?)  :- ?a <=> t()
rule or2(?a, ?b) :- ?a <=> f(), ?b <=> t()

rule model(vs: List[T = Bit])
  :- vs <=> [?p, ?q, ?r],
     neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
     or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)
```

It works because the PROGRAM names `List`'s shape. THE GENERALIZATION WE WANT is the same solver
written ONCE, over any collection:

```anthill
sort Sat[C]
  requires Fillable[T = C], <a collection builder>[C = C, Element = Bit]
  rule model(vs: C) :- vs <=> C[?p, ?q, ?r], <the clauses over ?p, ?q, ?r>
end
```

It needs three things this proposal does not yet define (§5):
1. **The shape without naming it** — `C[?p, ?q, ?r]`: three cases that add an element, then the
   empty one, through `C`'s dictionary (`cons(?p, cons(?q, cons(?r, nil())))` for `List`).
2. **Cells that stay FREE while the constraints run** — no `fill` on them until `neg` and `or2`
   have bound what they bind.
3. **Labelling** — `fill` on each cell still free at the end (`t | f`).

(`FiniteCollection` is not a builder: its only door to the elements, `collect(c: C) -> List[T =
Element]`, reads a collection and builds none.)

## 5. Open questions

1. **The collection pattern** (§4, 1): which case is "empty" and which "adds an element" — a
   builder's two cases, for a type shaped like a list — and the spelling, borrowing 056's `...`
   for the rest: `C[?x1, ?x2, ...?rest]`. The stdlib has a builder spec,
   `anthill.prelude.PersistentCollection` (`collection.anthill`: `empty() -> C`,
   `insert(c: C, elem: Element) -> C`), but its two members are OPERATIONS, and a pattern must also
   take a value apart, which a function does not.
2. **Free cells and labelling** (§4, 2–3): holding `fill` back until the constraints have run, and
   where labelling runs — the drain, or a written goal. The resolver can delay a goal on a variable,
   not attach one to run later.
3. **The monoid's home, and `combine` at run time** (§2): the stdlib has no `Monoid` spec
   (`algebra.anthill` has `Ring` and `VectorSpace`) — `Fillable` declares `combine` and `empty`
   itself, or a `Monoid` spec is introduced and `Fillable` provides it; and how a combined
   `Fillable` an author writes is carried by a dictionary.

## 6. Implementation — WI-20260925-SHED7

WI-20260911-5G28A's S3b and later steps depend on it. In order:
1. The spec; `fill` resolved through the provisions (§3); and its first implementations — a
   sort's derived domain and a primitive's (060 §2.3) — what 5G28A's S3b needs.
2. §5's question 3, decided with the user.
3. §4's generalization — MiniSat over a collection builder — as the acceptance, once §5's
   questions 1 and 2 are decided.
