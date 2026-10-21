# A collection-typed variable meets a list pattern — the landscape before 067 §4

## Status: Brainstorming draft (2026-10-21)

Written with the user before SHED7 step 3 (proposal 067 §4: MiniSat written once, over any
collection). Not a proposal. A line marked *measured* was run on `c0883a2e`, with the CLI built
from it; everything else is read from the source it names.

Decided while writing it (the user, 2026-10-21):

- A list literal is never translated to another collection: never built as one, never read
  through `split` in a pattern. kernel-language §4.6 says so now, proposal 019 records the
  withdrawal, and WI-561 is rejected.
- `<=>` stays independent of dictionaries: it unifies terms and never asks a sort.
- THE MAIN OPTION (§4): the solver builds its collection from the list with
  `PersistentCollection[C = C].fromList([?p, ?q, ?r])`, a builder that reads the list's spine and
  never an element, and `<=>` unifies `vs` with what it built.
- That call cannot be written in a rule body today (§4.5). SHED7 depends on
  WI-20261013-RYDNV (068 C1d, part 4 of the clause typing WI-20260926-7D48J), after which it can.

§5 keeps the alternatives still standing (D, F, H) and the record of the withdrawn ones.

## Relates to

[067](../proposals/067-fillable.md) (`Fillable`; §4 the generalization, §5 its questions),
[060](../proposals/060-clause-level-requirements-and-typed-heads.md) §2 (typed heads) and §3 (the
head annotation as an anchor), [060-implementation](../design/060-implementation.md), "The next
case — MiniSat over a collection BUILDER", kernel-language §4.6 (collection literals), WI-561
(collection patterns, rejected), [future/unification-framework](../proposals/future/unification-framework.md)
(WI-382), [constrained-term-substrate](../design/constrained-term-substrate.md), and the clause
typing: WI-20260926-7D48J and its parts WI-20261013-GGXCX, -WF14Z, -R1W5A, -RYDNV.

## 1. The case

```anthill
sort Bit
  entity t
  entity f
end
fact neg(t(), f())
fact neg(f(), t())
rule or2(?a, ?)  :- ?a <=> t()
rule or2(?a, ?b) :- ?a <=> f(), ?b <=> t()

sort Bag[T]
  entity bnil
  entity badd(e: T, rest: Bag[T = T])
end

sort Sat[C]
  rule model(vs: C)
    :- vs <=> [?p, ?q, ?r],
       neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
       or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)
end
```

*Measured:*

| call | models |
|---|---|
| `Sat[C = List[T = Bit]].model.takeN(100).length()` | 2 |
| `Sat[C = Bag[T = Bit]].model.takeN(100).length()` | 0, and nothing reports it |

Wanted at `C = Bag`: the same two models, `vs = badd(e: t(), rest: badd(e: t(), rest: badd(e: f(),
rest: bnil())))` and the one for `f, f, t`; and a call that passes a Bag answers whether it is one.

## 2. Why it fails

At load, the typer stores the rule as

```
model(vs) :- __domain_guard(vs, C), vs <=> [?p, ?q, ?r], <clauses>, fill(vs)
```

— the type test in front of the body and `C`'s `fill` after it. Where that is written: proposal
060 §2.3, "What a typed head means" (`rule p(?x: T) :- body ≡ rule p(?x) :- body,
SortDomain[T].fill(?x)`, "the goal goes AFTER the body"), 060 §2.2 ("the member goal is
APPENDED"), kernel-language §5.3; the code is `install_typed_head_domain_goals`
(`rustland/anthill-core/src/kb/typing/rules.rs`), run by the typer's pass in `typing/sorts.rs`.
With nothing in the body binding `x`, that `fill` enumerates the whole domain, as 060 §2 and
§2.2 intend: *measured*, `rule anyBag(x: Bag[T = Bit]) :- true` answers `bnil`, then every Bag by
length, without end.

- `[?p, ?q, ?r]` is always a `List`: the loader builds the `cons`/`nil` spine. §4.6 used to say
  the typing process builds a literal at another expected type (`Collection.insert`/
  `Collection.empty`); that was never implemented, and the sentence is withdrawn. *Measured:*
  `operation mkBag() -> Bag[T = Bit] = [t(), f()]` is refused, `expected Bag[T = Bit], got
  List[T = Bit]`, and so is a literal at a declared `Set` as a return, a field and an argument.
- So `vs <=> [?p, ?q, ?r]` binds `vs` to a list. A later goal can bind the free cells inside that
  value, but cannot replace it. *Measured:* `?x <=> [?p, ?q], ?x <=> badd(e: ?p, rest: badd(e:
  ?q, rest: bnil()))` has no solutions; `?x <=> [?p, ?q], ?p <=> t()` gives `[t, ?_]`.
- `fill(vs)` receives the list: `vs` is read through the substitution. At `C = List` it fills the
  cells. *Measured:* `rule waitsTyped(vs: List[T = Bit]) :- vs <=> [?p, ?q, ?r], ?p != ?q, ?q !=
  ?r` gives `[t, f, t]` and `[f, t, f]`; its twin without the type gives one answer with two `neq`
  residuals. At `C = Bag`, the type test and Bag's `fill` both refuse a list, and 060 §2 says what
  follows: "bound, refuted → fail this binding". That is the silent 0.
- Nothing says so at load, because the typer does not read a head's bound when it types the body.
  *Measured*, each loading clean: `rule concrete(vs: Bag[T = Bit]) :- vs <=> [t(), f()]` (no
  solutions), `rule callArg(vs: Bag[T = Bit], ?n) :- List.length(vs) <=> ?n`, `rule twoTypes(x:
  Bit, y: Bag[T = Bit]) :- x <=> y`. Typing a rule variable by its head's bound is WF14Z's; which
  of these become load errors is GGXCX's to decide (its note of 2026-10-21).

## 3. What a solution has to give

1. Generic: `Sat` names no constructor of `C`.
2. The cells stay free while the clauses run, and what is still free at the end is filled
   (labelling; 067 §5 q2).
3. The shape comes from the solver: `fill` does not enumerate values of `C` for the body to cut
   ("no sense to generate all universum", the user).
4. `vs: C` holds in every answer: `vs` is a `C`, never a list in a column declared `C`.
5. A lazy `C` is read no further than the answer needs.
6. Both modes: `vs` unbound, and `vs` given.
7. A `C` that cannot do it is refused at load, where `C` is fixed.

## 4. The main option: `vs <=> PersistentCollection[C = C].fromList([?p, ?q, ?r])`

The solver builds its collection from the list, and `<=>` does the rest. The literal stays a
`List`, so the line is a `C` against a `C` and types once WF14Z reads the head's bound; `<=>`
stays plain unification.

### 4.1 Full code

`PersistentCollection` (stdlib, `collection.anthill`) gains one member — nothing of it exists
today:

```anthill
sort anthill.prelude.PersistentCollection
  import anthill.prelude.Iterable
  sort C = ?
  sort Element = ?
  effects Effect = ?
  requires Iterable[C = C, Element = Element, E = Effect]

  operation insert(c: C, elem: Element) -> C
    effects Effect
  operation empty() -> C

  -- new: the collection of the list's elements, in the list's order. It reads the list's
  -- spine and never an element, so the elements may still be unbound.
  operation fromList(xs: List[T = Element]) -> C
    effects Effect
  =
    match xs
      case nil() -> empty()
      case cons(x, rest) -> insert(fromList(rest), x)
end
```

The program, with `Bit`, `neg` and `or2` as in §1:

```anthill
sort Bag[T]
  entity bnil
  entity badd(e: T, rest: Bag[T = T])

  -- walkable: Stream provides Iterable, which PersistentCollection requires
  provides Stream[T = T, E = {}]
  operation splitFirst(s: Self) -> Option[Pair[A = T, B = Stream[T = T, E = {}]]] =
    match s
      case bnil() -> none()
      case badd(e, rest) -> some(pair(fst: e, snd: rest))

  -- buildable; fromList is the default, and Bag's insert reads no element
  provides PersistentCollection[C = Bag[T = T], Element = T]
  operation insert(c: Self, elem: T) -> Self = badd(e: elem, rest: c)
  operation empty() -> Self = bnil()
end

sort Sat[C]
  requires PersistentCollection[C = C, Element = Bit]
  rule model(vs: C)
    :- vs <=> PersistentCollection[C = C].fromList([?p, ?q, ?r]),
       neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
       or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)
end

sort Driver
  operation models() -> Int64 effects {Error} = Sat[C = Bag[T = Bit]].model.takeN(100).length()
end
rule given(1)   :- Sat.model(badd(e: t(), rest: badd(e: t(), rest: badd(e: f(), rest: bnil()))))
rule refuted(1) :- Sat.model(badd(e: t(), rest: badd(e: t(), rest: badd(e: t(), rest: bnil()))))
```

What the typer adds to `model` is what it adds today, and nothing else:

```
rule model(vs) :- __domain_guard(vs, C),     -- the type test: waits until vs is bound, then checks it is a C
                  vs <=> PersistentCollection[C = C].fromList([?p, ?q, ?r]),
                  neg(...), ..., or2(...),
                  Fillable[T = C].fill(vs)   -- C's fill, through the dictionary the caller hands in
```

Wanted: `Driver.models()` is 2, `given` answers 1, `refuted` answers nothing; at `C = List[T =
Bit]` the same (List's `insert` is `cons` and its `empty` is `nil`, so `fromList` gives the list
back).

### 4.2 What it does, in both modes

- `vs` unbound: `fromList` runs at once — it reads only `cons`/`nil` — so `vs = badd(e: ?p, rest:
  badd(e: ?q, rest: badd(e: ?r, rest: bnil())))` before `neg` runs. The clauses choose the cells,
  and `fill(vs)` only checks: no shape is enumerated (requirement 3).
- `vs` given: `fromList` builds the same Bag of free cells, and `<=>` unifies the given one with
  it, so the cells come out of it: `?p, ?q, ?r = t, t, f`. Taking the value apart is
  unification's job, which answers 067 §5 q1's objection that a builder's members are functions
  and "a pattern must also take a value apart, which a function does not".

### 4.3 `fromList` reads no element: measured at a named type

The same moves, written as an operation of `Bag` and called by name (`vs <=> Bag.adopt([?p, ?q,
?r])`), *measured*:

| rule | answer |
|---|---|
| `?vs <=> Bag.adopt([?p, ?q, ?r])` | `badd(e: ?_, rest: badd(e: ?_, rest: badd(e: ?_, rest: bnil())))` — runs at once |
| `model(vs: Bag[T = Bit]) :- vs <=> Bag.adopt([?p, ?q, ?r]), <clauses>` | 2 models; `given` 1; `refuted` nothing |
| `?vs <=> Bag.adopt(?xs)` | a residual: the list itself is unbound, so the call waits |
| `?vs <=> Bag.adopt(?xs), ?xs <=> [?a, ?b]` | `badd(e: ?_, rest: badd(e: ?_, rest: bnil()))` — waits, then woken |

And a builder that does read an element waits for it (068 §2): an `adoptIfOne` that checks the
first element is `1` waits while `?p` is unbound — it does not fall through to its other case —
answers `badd(e: 1, …)` once `?p <=> 1`, and `bnil()` once `?p <=> 2`.

### 4.4 Which dictionary

`Sat` requires `PersistentCollection[C = C, Element = Bit]`; the citation `Sat[C = Bag[T =
Bit]]` hands in Bag's, chosen there and never at run time (058 §3.10). The element type's
dictionary is not `Sat`'s concern: the final `fill(vs)` fills the cells through `C`'s dictionary,
which carries the element's as its sub-dictionary (`Dictionary(sub₀ …, impl: S)`). A provider
reaches its element's instance through a conditional provision (`provides X[T = Bag[T = T]] :-
Y[T = T] where …`, as `TypeValuePattern` in `reflect.anthill` does); a solver that needs one of
its own writes `requires Fillable[T = E]`, and the citation hands it in.

### 4.5 Why it cannot be written today, and what makes it possible

*Measured*, with a stand-in spec `Builder` carrying the same `fromList` (the stdlib's
`PersistentCollection` has none), `Bag` providing it, and `sort Sat[C] requires Builder[C = C,
Element = Bit]`:

| the body writes | at load | at run |
|---|---|---|
| `vs <=> Builder.fromList[C = C]([?p, ?q, ?r])` | refused: "call-site type arguments … are not supported here … a rule-body goal … have no channel for it" | — |
| `vs <=> build([?p, ?q, ?r])`, `build` an operation of `Sat` carrying that bracket (the repair the refusal advises) | refused: "element `C = fl.Sat.C` is unconstrained at this call site; this is a RULE-body goal, and nothing in the clause determines which `fl.Builder` instance it means" | — |
| the same, after `?d = require[Builder[C = C, Element = Bit]]` | refused as above, and: "no head bound of this clause names a sort, so none can provide `Builder`" | — |
| `vs <=> Builder[C = C].fromList([?p, ?q, ?r])` | loads | `relation_floundered`: the call never finds its dictionary |
| `vs <=> Builder.fromList([?p, ?q, ?r])` | loads | `relation_floundered`, the same |

The call has no argument at `C` — `C` is only its result — so nothing in the clause names its
instance. 060 §3 makes the typed head the anchor for exactly this ("`?x: T` on the head is the
second anchor … any `require[Spec[T]]` in the clause compiles against it"), which is not
implemented for a head typed by a sort parameter. The clause typing makes it possible:

- WF14Z (068 C1b): `vs` is typed by its head's bound, tied to `Sat`'s `C`, so the call's result
  type is `Sat`'s `C`;
- 0RRQP: a rule-body condition is routed to its enclosing sort's `requires`, which a rule sees
  (the user, 2026-09-25);
- RYDNV (068 C1d): "a call with no argument at its carrier parameter is refused at typing unless a
  require supplies it" — here `Sat`'s `requires PersistentCollection[C = C, …]` supplies it, from
  the citation's dictionary.

SHED7 depends on RYDNV (and on WF14Z, which RYDNV waits on through R1W5A). 060's own ticket,
5G28A, depends on SHED7, so it cannot be the one.

### 4.6 Limits

- `fromList` reads no element itself; `insert` may. A `SortedSet`'s compares, so its `fromList`
  waits until the body binds the cells: that works in `Sat`, where `neg` binds them, and flounders
  where only the final `fill` would.
- A `Stream` is read, not built — it provides no `PersistentCollection` — so a lazy `C` takes F.
- `PersistentCollection` requires `Iterable`: a `C` that is only built must be walkable too (Bag
  through its `Stream`).
- `vs` given is compared by `<=>`, so a collection whose equal values can differ in shape (a
  balanced tree) fails there; comparing by the sort's own sense is H.

## 5. The alternatives, and the record

### D. `fill` with an input and an output, placed by the typer at the head (the user, 2026-10-21)

```anthill
sort Fillable
  sort T = ?
  rule fill(?in, ?out)    -- replaces fill(?x): ?out, a T, made from ?in; with ?in unbound, any T
end
-- the typer stores rule model(vs: C) :- BODY as
--   rule model(?out) :- __domain_guard(?out, C), BODY with vs renamed ?vs, Fillable[T = C].fill(?vs, ?out)
-- Bag's own fill:
--   rule fill(nil(), bnil())
--   rule fill(cons(head: ?h, tail: ?t), badd(e: ?e, rest: ?r)) :- Fillable[T = T].fill(?h, ?e), fill(?t, ?r)
```

The body keeps `vs <=> [?p, ?q, ?r]`; the typed head converts. A given `vs` is invisible to the
body until `fill` runs, so check mode is generate and test. Open: what type the body gives `vs`.

### F. The solver reads its cells through `Stream` (works today)

```anthill
sort Sat[C]                -- C provides Stream[T = Bit]
  rule model(vs: C)
    :- Stream.splitFirst(vs)  <=> some(pair(fst: ?p, snd: ?r1)),
       Stream.splitFirst(?r1) <=> some(pair(fst: ?q, snd: ?r2)),
       Stream.splitFirst(?r2) <=> some(pair(fst: ?r, snd: ?r3)),
       Stream.splitFirst(?r3) <=> none(),
       neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
       or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)
end
```

*Measured:* `models()` 2 (and 2 at `C = List[T = Bit]`), `given` 1, `refuted` nothing. But
`fill(vs)` builds Bags one constructor at a time for the reads to cut (against requirement 3), and
the end check reads one element past (against 5). It is the option for a lazy `C`.

### H. The solver calls the sort's relation: `unifyWith(vs, [?p, ?q, ?r])` (the user, 2026-10-21)

```anthill
sort Fillable
  sort T = ?
  sort Element = ?
  rule fill(?x)
  rule unifyWith(?x, ?xs)     -- ?x, a T, holds the elements ?xs, in T's own sense
end
-- Bag: rule unifyWith(bnil(), nil())
--      rule unifyWith(badd(e: ?h, rest: ?r), cons(head: ?h, tail: ?t)) :- unifyWith(?r, ?t)
-- Sat: rule model(vs: C) :- Fillable[T = C].unifyWith(vs, [?p, ?q, ?r]), <clauses>
```

A relation: both modes, possibly several answers (a set holds `[?x, ?y]` once per order), and the
sort decides what "holds these elements" means. Needs what the main option needs, and a spec's
rule member called through a dictionary, which exists today only for `fill`; and a member a sort
writes in a `Fillable` is not read (*measured*: a sort providing `Fillable` with its own `fill` —
a typed head still enumerates the derived domain).

### Withdrawn

- A (2026-10-21): the literal built as a `C` by the typer — §4.6's withdrawn sentence. The main
  option is its explicit form.
- B (2026-10-21, with WI-561): the literal read as a pattern through `split`. F is the same
  reading, written by the solver; *measured* through the rewrite now parked (§9): 2 models.
- C (2026-10-21): the sort's own unification placed at `<=>` by the typer or the resolver —
  `<=>` stays independent of dictionaries; H is the same relation, called by the solver.
- G (2026-10-21): `vs <=> adopt([…])` with `adopt` a member of `Fillable` — moved to
  `PersistentCollection` as `fromList` and became the main option.

## 6. Side by side

| | main: `vs <=> PersistentCollection[C = C].fromList([…])` | D: `fill(in, out)` at the head | F: reads through `Stream` | H: `unifyWith(vs, […])` |
|---|---|---|---|---|
| `C` provides | `PersistentCollection` (`empty`, `insert`) | a two-argument `fill` | `Stream` | `unifyWith` |
| what the typer adds | the type test, and `fill(vs)` | the type test on `?out`, and `fill(?vs, ?out)` | the type test, and `fill(vs)` | the type test, and `fill(vs)` |
| `vs` unbound: the shape comes from | the list | the list | `fill`, cut by the reads | the list |
| `vs` given: it is | unified with the built value | generated and tested | read, n + 1 times | the sort's choice |
| waits on | RYDNV | WF14Z, and the head rewrite | — | RYDNV, and rule members through a dictionary |
| works today | at a named type (§4.3) | no | yes | no |

## 7. Questions still open

1. Is "`fromList` reads no element" a law every provider owes — so a `SortedSet` provides no
   `fromList` — or a property a provider has or has not, its `fromList` then waiting on the cells?
2. A default body in `PersistentCollection`, from `empty` and `insert` as in §4.1, or a member
   each provider writes?
3. Is requiring `Iterable` (through `PersistentCollection`) right for a collection the solver
   only builds?

## 8. Later: the size comes from the call

060-implementation's "The next case" records a direction of the user's (2026-09-25) for a
different problem: a solver whose number of cells arrives with the call (n-queens, a SAT problem
read from input). A rule only ever gets the variables written in it, so it cannot write `?p1, …,
?pn`. The direction: "teach the kernel to create fresh logical variables" — a kernel goal that
creates n cells at run time, each carrying its element's `fill` attached and not run, with what is
still free at the end labelled. In made-up syntax (nothing like it exists):

```anthill
rule solve(n: Int64, qs: C)
  :- cells(qs, n),     -- qs becomes a C of n fresh cells; n = 3: badd(?c1, badd(?c2, badd(?c3, bnil())))
     safe(qs)          -- the constraints read the cells through C's API
```

`Sat` writes its three cells, so it does not need this.

## 9. Outside this note

067 §5 q3 (the monoid's home) — the user's answer "c", `Monoid[Fillable]`, read as "a value of
type `Fillable[T = X]` is an instance", waits for confirmation and does not depend on this. The
`Stream.asList` work (B through a list: the rewrite, its test, and its texts for kernel-language
§5.3 and 067 §5 q1) was never committed; it is kept in the local git stash "SHED7 parked
2026-10-21".
