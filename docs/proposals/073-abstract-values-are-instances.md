# Proposal 073: A value of an abstract type is an instance of its sort — no carrier is chosen at run time

## Status: Draft (2026-11-05). Decided with the user while picking up WI-20260923-DK0QJ, point by point: no run-time step chooses a carrier or a provider (058 §3.9 holds everywhere); a sort is a set of operations, and a value of an abstract type is an instance of its sort, its dictionary deduced at load where its sort is known and kept in the requirement channel; a spec's default body is typed once; every call passes what its callee reads (§6.3); where no typed caller exists, the requirement's goal composes the dictionary from the entries load selected, keyed by the value's carried type, as 058 §3.9, 060 and 060.1 §4 already decide (§6.1, §6.2). Reviewed the same day: an operation with two operands at the abstract type is answered by the rule the language already has (§2), and a caller-less call over a conditional provision by 060's (§6.2). A value whose type is open where it is used is not given a type there without a dictionary (060.1), so no type is stored with a value (§6.2). §1–§4 and §6 are decided; §5's text is to be agreed; §7 is the plan.

## Extends: [058](058-modular-instances.md) §3.9 ("Dictionaries are PASSED at run time — instances are never CHOSEN at run time"); [060.1](060.1-written-rule-requirements.md) §4 (load decides where each requirement comes from, run time reads it) and §8.8, both kept in §6.2's words.

## Relates to: kernel-language §5.2 (a construction owes its sort's requirement; "a value carries no dictionary" — replaced here), §5.4, §8.7 (which provider a call gets); [`../design/requirement-channel.md`](../design/requirement-channel.md) §2.1 (run time performs no typing operations; `resolve_bridge_requirements` named there as the one exception); [`../design/requirement-dictionaries.md`](../design/requirement-dictionaries.md) §1–§2 (a dictionary is a run-time value a host can pass, §6.1); [045](045-effect-sets-and-expressions.md) §2 (the `EffectsRuntime` anchor, §6.3); [068](068-rule-body-operation-applications.md) §1, §6 (value-direction kept as the fallback for carriers no typer sees — answered by §6.2); WI-20260923-DK0QJ (a named slot reached with values only — its routes go, §4, §6.1), WI-20261015-ZPETZ (the host entry and the in-body dispatch are two copies), WI-817 (polymorphic recursion).

## The problem

058 §3.9 says no operation selects a dictionary from run-time data. The interpreter does, on every path below, and the spec text describes it as behaviour (kernel-language §5.2: "Value-directed dispatch still serves every call no `requires` in scope licenses — an abstract-spec receiver, a carrier only the runtime value names").

```anthill
namespace p.rel
  import anthill.prelude.{Int64, String, List, Error, Relation}
  import anthill.prelude.List.{length}
  sort People
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)
  fact person(name: "carol", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  const people: Relation[T = (name: String, age: Int64)] = person_row
  operation three() -> Int64 effects Error = length(people.takeN(3))
end
```

`Stream.takeN` is a default body of `Stream`:

```anthill
  operation splitFirst(s: Self) -> Option[Pair[A = s.T, B = Stream[T = s.T, E = s.E]]]
    effects s.E
  operation takeN(s: Self, n: Int64) -> List[T = s.T] effects s.E =
    if gt(n, 0) then
      match splitFirst(s)
        case none() -> nil
        case some(pair(h, rest)) -> cons(head: h, tail: takeN(rest, sub(n, 1)))
    else nil
```

The three `splitFirst(s)` calls of `three()` run `Relation.splitFirst`, then `LogicalStream.splitFirst` twice: `Relation.splitFirst` returns `B = LogicalStream[T = r.T, E = r.E]`. Each is chosen by the interpreter from the value's sort (measured on `62882ef0`). And `length` adds `add(1, length(xs))` at `Int64` the same way: the typer leaves `Additive.add` unclassified because `Int64` reaches `Additive` only through `Numeric provides Additive[T = T]`, and the interpreter finds `Int64.add` from the value `1`.

Measured over the full workspace run on `62882ef0` (11,714 tests), with a trace at each place the interpreter chooses an implementation or builds a dictionary from argument values:

| route | tests that reach it |
|---|---|
| a spec operation the typer left unclassified, dispatched on the argument's sort | 1,527 |
| the SLD bridge builds the callee's dictionaries from argument values | 102 |
| an operation's own requirement slots a call left unfilled, filled from argument values on entry | 73 |
| the resolver classifies a rule-body or query call of a spec operation by value | 20 |
| the host entry dispatches by value (14), and fills an operation's own slots from values (13) | 27 |
| a defaulted spec operation on an abstract receiver redirected to the carrier's member by value | 12 |
| a redirected member's requirements built from argument values | 12 |

## 1. The rule

> No step at run time chooses a carrier or a provider. What every call runs is decided at load: the caller passes the dictionary, it is built from the provisions, or the call is made on a value of an abstract type, which is an instance whose operations were fixed where it was made (§2). Where no typed caller exists — a query, a host call, a rule variable no head column reaches — the requirement's goal composes the dictionary when it runs from the entries load selected, keyed by the value's carried type (058 §3.9, 060's rule, 060.1 §4): reads over decided entries, not a choice (§6.2).

A call at a type the program knows is decided by that type, through any chain of provisions: `add(1, n)` at `n: Int64` is `Int64.add`, reached through `Numeric provides Additive[T = T]`, at load.

## 2. A value of an abstract type is an instance of its sort

A sort is a set of operations. A sort that receives on itself is its own carrier (kernel-language §8.1): `List provides Stream`, a `List` is a `Stream`, and `rest : Stream[T, E]` is a `Stream` at its own arguments (§5.1). A value typed at such a sort is a value of an abstract type, and it is an instance of that sort: the sort's operations as the sort that built the value implements them, holding the value. A call of the sort's operation on it runs the operation the instance holds. The value has nothing else an operation could reach: it is used only through its sort's operations, so code that holds it passes it on and does not learn which sort built it.

The instance is made where the value's sort is known, and which operations it holds is decided there, at load:

- **a member whose result is a concrete sort where the spec operation's is abstract**: `Relation.splitFirst` returns `B = LogicalStream[…]` where `Stream.splitFirst` returns `B = Stream[…]`, so the `B` value a call through `Stream` receives is a `LogicalStream` instance. `List.splitFirst` (`B = List[xs.T]`) returns a `List` instance.
- **a body that uses a value of a known sort at an abstract type** — returned, passed or stored at it: `Map.iterator(m: Self) -> Stream[T = Pair[A = K, B = V], E = {}] = entries(m)` returns a `List` at `Stream[…]`, which is the `List` instance there; `[xs, xs.map(twice)]` at `List[T = Stream[T = Int64, E = {}]]` holds a `List` instance and a `MappedStream` instance.
- **a body that builds a value from one of an abstract type**: `MappedStream.splitFirst` builds `mapped(rest, fn)` over the `rest` its source's `splitFirst` returned; the result is a `MappedStream` instance, and what answers its `Iterable[C = Source]` requirement is `rest`, itself an instance.

What the instance holds is the dictionary deduced there, kept in the requirement channel (§6.4); the value is not read for it.

`takeN` is typed once, in `Stream`: `splitFirst(s)` runs the operation of `s` (`__req_self`), and `takeN(rest, sub(n, 1))` passes `rest`, whose operations at `Relation` are `LogicalStream`'s; `takeN` never sees the name.

A data structure of values of an abstract type holds instances, as many as it has values:

```anthill
namespace p.two
  import anthill.prelude.{Int64, List, Stream}
  import anthill.prelude.Stream.{takeN}
  operation twice(x: Int64) -> Int64 = x
  operation streams(xs: List[T = Int64]) -> List[T = Stream[T = Int64, E = {}]] =
    [xs, xs.map(twice)]
  operation firsts(ss: List[T = Stream[T = Int64, E = {}]]) -> List[T = List[T = Int64]] =
    ss.map(lambda s -> takeN(s, 1)).collect()
end
```

The two elements of `streams(xs)` are a `List` instance and a `MappedStream` instance; each application of the lambda runs the operations of its `s`. (Today the two `takeN` calls run `List.splitFirst` and `MappedStream.splitFirst`, each chosen from the value — measured.)

An operation with several operands at the abstract type runs the instance of its receiver, the parameter dispatch reads (kernel-language §8.7, a member's fit to its spec), and the other operands reach it as instances. A provider's member therefore takes them at the spec's type, as the language already requires: with `merge(a: Bag, b: Bag)`, `Bag provides Mergeable` is refused at load ("parameter 2 (`b: Bag`) takes less than the spec's … type `b` by the spec"). Nothing has to show that two values share a carrier, and no operation is barred from a value of an abstract type:

```anthill
sort Mergeable
  operation size(a: Self) -> Int64
  operation merge(a: Self, b: Self) -> Self
end
sort Bag
  entity bag(n: Int64)
  provides Mergeable
  operation size(a: Bag) -> Int64 = match a case bag(n) -> n
  operation merge(a: Bag, b: Mergeable) -> Bag = match a case bag(n) -> bag(n + Mergeable.size(b))
end
sort Tally
  entity tally(k: Int64)
  provides Mergeable
  operation size(a: Tally) -> Int64 = match a case tally(k) -> k * 100
  operation merge(a: Tally, b: Mergeable) -> Tally = match a case tally(n) -> tally(n + Mergeable.size(b))
end
operation two(x: Mergeable, y: Mergeable) -> Int64 = Mergeable.size(Mergeable.merge(x, y))
```

`two(bag(1), tally(2))` answers `201`, `Bag`'s `merge` given the `Tally` as a `Mergeable`, and `two(tally(2), bag(1))` answers `300`; so do the two elements of `[bag(1), tally(2)]` at `List[T = Mergeable]` (measured on `e4442b16`).

A recursion whose instance grows at each turn (WI-817) needs nothing more: each turn passes the instance the previous one returned.

## 3. A spec's default body

A spec's default body is typed once, and each call in it is fixed at load (`apply_within`): at `Self` it takes the instance the body runs at, on a value of an abstract type it runs that instance's operation (§2), at a known type it takes the dictionary built from the provisions. A defaulted spec operation called on an abstract receiver runs the receiver instance's operation, and is never redirected by the receiver's sort to the carrier's own member.

## 4. What goes

- The interpreter's routes that choose from a value: dispatch of an unclassified spec operation on the argument's sort (`dispatch_resolved_operation` step 3b and its host-entry copy), the carrier-override redirect (step 3), and the resolver's value classification of a rule-body or query call.
- Every dictionary built from argument values where a typed caller exists, or ranked among providers — `resolve_bridge_requirements` and its callers: the SLD bridge, the redirected member's requirements, the fill of an operation's own slots on entry (§6.3), the host entry's op half (§6.1). With them the ranking question of WI-20260923-DK0QJ goes: no value-only route is left to rank. What stays is 060's fetch-and-compose where no typed caller exists (§6.2).
- The run-time slot of an effect row's `EffectsRuntime` requirement (§6.3).
- The resolver's built-in answer standing in front of dispatch for a spec operation (`PartialOrd.gt`, `lt`, `gte`, `lte` and the arithmetic family), and `eq`'s step that reads the operand's constructor when the goal runs (`sem_eq_dispatch_target`), which the census above did not trace. Over a `Point` that provides `PartialOrd` and writes its own `gt = false`, the operation body's `PartialOrd.gt(pt(2, 1), pt(1, 9))` answers `false` and the same goal in a rule body, under a declared `PartialOrd[T = A]`, or as a query, is undecided (measured on `7379c5fd`): the rule-body goal reads the pin the typer stamps, a declared guard supplies its dictionary (060.1), and the built-in comparison stays only as what runs a member it realizes, such as `Int64.gt` (WI-20260909-SM910).
- The typer's deferrals to the interpreter at a known type: the transitive-provision arm (WI-496) and the abstract-spec carrier arm (WI-598) in the spec-operation dispatch.
- kernel-language's sentences that describe value-direction: §5.2 (the paragraph "Value-directed dispatch still serves …", the host-entry and rule-body halves of "every route into an operation fills its op-scoped slots", "resolves it from the value otherwise" in "A value carries no dictionary", "its member and its provider are found from the values"), the named-slot paragraph's "The same holds for value-directed dispatch", §5.1's "value-directed dispatch reaches `Stream.splitFirst` on a `Relation` through it", and §5.4's "reached by value".

## 5. The spec text this asks for (to be agreed)

§5.2, replacing "A value carries no dictionary: an operation reached through it … resolves it from the value otherwise":

> A value typed at a sort that is its own carrier (`rest : Stream[T, E]`) is an instance of that sort: the sort's operations as implemented by the sort that built the value. Its dictionary is fixed where its sort is known — by the member that returns it at a concrete sort, or where a value of a known sort is returned, passed or stored at the abstract type — and kept in the requirement channel. It is used only through the sort's operations, and a data structure of such values holds instances. No operation or dictionary is chosen from a value when the program runs.

§5.3 keeps its sentence on a requirement no caller passes ("found from the carried types when the goal runs, waiting while the value is unbound; where that type provides no instance, the goal fails"), which is 060.1 §4's, and adds the host call to it and the case §6.2 measured:

> A value whose type leaves open a type argument the requirement needs is not given it without a dictionary: over `ListShow provides Show[T = List[T = E]]` under `requires Show[T = E]`, `keep[A](?x: A, ?t) :- src(?x), Show[A], Show.show(?x, ?t)` beside `fact src([])` is refused at load, naming `E`, and answers once the `[]` is written with its element type or the citation passes the dictionary, `keep[A = List[T = Int64]](?x, ?t)`.

§5.4, two sentences:

> An operation used as a function value is the lambda that calls it: `app(useS, a)` is `app(lambda (x: A) -> useS(x), a)`, and the call in it is typed at the instance the value is used at.

> A requirement a call fixes only in part is answered at load as §8.7 answers a dispatch: under `requires Spec2[B = P]`, which leaves `A` unwritten, `useB(wis(n: 4), nosp(n: 5))` takes the one provision that agrees with `B = NoSp`, the more specific of two that agree, or the default, and is refused naming the candidates otherwise.

kernel-language does not mention the `EffectsRuntime` anchor, and it already reads `TypeValue[T]` as a requirement, so §6.3's other two answers change no spec text.

## 6. The first draft's open questions, decided

### 6.1 The host entry

A host call is a call with no typed caller, and it reads its requirements as a query does (§6.2). A dictionary the host passes is a run-time `Dictionary` value (requirement-dictionaries.md §1–§2; `alloc_dictionary`, `call_with_requirements`) and is used as given. A requirement the host does not pass is composed from the argument's carried type, as a query's is:

```anthill
sort Desc
  sort T = ?
  operation describe(x: T) -> Int64
end
sort Leaf
  entity leaf
  provides Desc[T = Leaf]
  operation describe(x: Leaf) -> Int64 = 7
end
operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)
```

`interp.call("gen", &[leaf])` answers `7`: `leaf`'s carried type `Leaf` keys `Leaf`'s `Desc`, as in the query `gen(leaf, ?r)`. A slot the carried type does not hold is refused at the entry, naming it: `has(s, "a")` with `s` built at `O = ByInner[OI = Flat]` needs `O`, which `s`'s carried type does not hold — no type is stored with a value (§6.2) — so the host passes it or the call is refused naming `s.O` (WI-20260923-DK0QJ's half (a)). Nothing is built because only one provider exists. The three entries (`call`, `call_with_witnesses`, `call_with_requirements`) become one: a witness named by its sort is that sort's dictionary, and an operation's own `requires`, which `call_with_requirements` has no spelling for today, is passed the same way.

### 6.2 No typed caller

```anthill
namespace p.q2
  import anthill.prelude.{Int64, Bool}
  sort Marker
    sort T = ?
    operation tag(x: T) -> Int64
  end
  fact src(1)
  fact src(true)
  rule keep[A](?x: A, ?t) :- src(?x), Marker[A], Marker.tag(?x, ?t)
  rule answer(?t) :- keep(?x, ?t)
end
namespace anthill.prelude.Int64
  import p.q2.Marker
  provides Marker[T = Int64]
  operation tag(x: Int64) -> Int64 = 1
end
namespace anthill.prelude.Bool
  import p.q2.Marker
  provides Marker[T = Bool]
  operation tag(x: Bool) -> Int64 = 2
end
```

`answer(?t)` answers `1` and `2`, `keep(1, ?t)` answers `1`, `keep(true, ?t)` answers `2` (measured on `62882ef0`). No caller passes `keep` its `Marker`: the two `keep` goals are queries, and in `answer` the type of `?x` differs from one `src` fact to the next.

058, 060 and 060.1 already decide this place, and 073 keeps their rule. `Marker[A]` compiles to a generated goal (060's rule) whose anchor is the head column `?x: A` (060 §3). When it runs, after `src(?x)` has bound `?x`, it reads `?x`'s carried type and composes the dictionary from the entries load selected (060.1 §4, the one place a dictionary is looked up at run time): "reads over decided entries, not choice" (058 §3.9). `1` keys `Int64`'s entry and `true` `Bool`'s.

A conditional provision composes the same way, its type arguments flowing to the sub-fetches (060's rule):

```anthill
namespace c
  import anthill.prelude.{Int64, List}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort ListShow
    import c.Show
    sort E = ?
    requires Show[T = E]
    provides Show[T = List[T = E]]
    operation show(x: List[T = E]) -> Int64 = match x case nil -> 100 case cons(h, t) -> Show.show(h) + 10
  end
  fact src([1, 2])
  fact src([])
  rule keep[A](?x: A, ?t) :- src(?x), Show[A], Show.show(?x, ?t)
  rule answer(?t) :- keep(?x, ?t)
end
namespace anthill.prelude.Int64
  import c.Show
  provides Show[T = Int64]
  operation show(x: Int64) -> Int64 = 1
end
```

`[1, 2]`'s carried type `List[T = Int64]` keys `ListShow`'s entry, and `Int64` its condition's, `Int64`'s `Show`: `11`. `[]`'s type is `List[T = ?]` where the fact is written, and `keep`'s `?x: A` under `Show[A]` would make it typed with no dictionary, which 060.1 forbids (decided with the user, 2026-11-05): the program is refused at load, naming `E`, as a free type variable a requirement is owed at is. It answers `100` once the `[]` is written with its element type, or when the citation passes the dictionary, `keep[A = List[T = Int64]](?x, ?t)` (060.1 §2). Measured on `e4442b16`: `answer(?t)` answers `11` alone, the `[]` row failing in silence, and `keep([], ?t)` answers nothing.

So no type is stored with a value (decided with the user, 2026-11-05), though 060 calls the carried type "a stored term": a value whose type is open where it is used is not given that type there without a dictionary. A `[]` built at `List[T = Int64]` (`operation noInts() -> List[T = Int64] = []`) that passes through a column nothing types brings its dictionary with it, and nothing recovers `Int64` from the value later; a `MySet`'s `O` is passed or the call is refused (§6.1). `src(1)`, `src(true)` and `src([1, 2])` are complete where the facts are written, and answer as above.

### 6.3 A call that passes nothing today

The 73 tests that reach the fill of an operation's own slots on entry, traced by the slot each call left out (2026-11-05):

| what the call does not pass | tests | decided |
|---|---|---|
| the dictionary of an operation used as a function value: `app(useS, a)` over `useS[P](x: P) -> Int64 requires Show[T = P]` and `app[X](f: (x: X) -> Int64, x: X) -> Int64 = f(x)` | 2 | the function value is the lambda that calls it, `app(lambda (x: A) -> useS(x), a)`; its call is typed at `P = A` and passes `A`'s `Show`, built at load, and under a caller's type variable the closure holds the caller's dictionary (`go3[Q](q: Q) requires Show[T = Q] = app(lambda (x: Q) -> useS(x), q)`) — both traced, neither reads the argument |
| the slot of an effect row: `effects E = ?` is `sort E = ? requires EffectsRuntime[Effects = E]` (045 §2), so `MappedStreamFinite.collect`, declared `effects {SourceEffects, TransformEffects}`, has two | 46 | the effect handlers are installed in the interpreter (`Interpreter.effect_handlers`), and an effect row is typed and has nothing at run time: no slot. Today the slot always holds the same leaf, `Dictionary(impl: EffectsRuntime)`, kept only so the others keep their positions |
| the type of a raised error: `Error.raise("boom")` in `fail(x: Int64) -> Int64 effects {Error[String]}` needs `TypeValue[T = String]`; so do host operations that raise (`Int64.rem` by zero, `KB.loaded`) | 20 | `TypeValue[T]` is an ordinary requirement: the call passes it, built at load; a host operation that raises, at the error type its declaration states |
| a requirement leaving a parameter of its spec unwritten: `useB[P](a: WIS, b: P) -> Int64 requires Spec2[B = P]`, called `useB(wis(n: 4), nosp(n: 5))`; `p[MT](x: MT) requires Pair[P = MT]`; `Box.tagOf2(0)` under `requires Tag[T = V]` | 5 | built at load by §8.7's order over the provisions that agree with what the call fixes: the one that agrees (`Both`, at `A = WIS, B = NoSp`, answers `9`); of two, the more specific (`Both` over `AnyA`, which provides `Spec2[A = X, B = NoSp]` at every `X`), which fixes the unwritten `A`; the default; and otherwise a refusal at load naming them (`Both` beside `Both2` at `A = Int64`) |

Today the last row's two-provider programs load clean and die when the call runs, "`__req_spec2` not bound in caller frame", both the incomparable pair and the nested one (measured).

Found beside it, wrong whatever the answer: with `provides Spec2[A = Int64, B = NoSp]` alone (`both(a: Int64, b: NoSp) -> Int64 = 100`), `useB`'s body still hands `both` the `WIS` value `a`, and `go()` answers `100`. `A` is unwritten, so either the body may not use it at `WIS`, or the call owes `A = WIS` and is refused for want of a provider; which of the two is stage 2's question.

### 6.4 Representation

Where a value of a known type is used at a type class over it — a `List` passed, returned or stored as a `Stream`; values of types `X` and `Y` at `TypeClass[X, Y]` — the dictionary is deduced at load and kept in the requirement channel (requirement-channel.md); nothing reads the value for it. How the channel holds one for each element of a data structure (§2's `[xs, xs.map(twice)]`) is the implementation's, written in the design note beside requirement-channel.md.

## 7. Stages

Filed with the user 2026-11-05, tag `proposal-073`; WI-20260923-DK0QJ depends on stages 3 and 4. WI-20260909-SM910, rewritten the same day to this proposal's method, carries the rule-body ordering family and `eq` (§4), and stage 3 depends on it.

1. Calls at a known type are decided at load (§1): the typer's two deferral arms go, and the 1,527-test route then serves only calls at an abstract type. WI-20261105-C6GK8.
2. Every call passes what its callee reads (§6.3): an operation used as a function value is the lambda that calls it; an effect row's slot is removed; a raise is passed its `TypeValue`; a requirement a call fixes in part is answered by §8.7's order at load; the type hole found beside it. The fill of an operation's own slots on entry goes. WI-20261105-89J6K.
3. A value of an abstract type is an instance (§2, §3, §6.4): `Stream`'s and `Iterable`'s default bodies and the stream combinators run on it, and so does an operation with two operands at the abstract type over two carriers (§2's `two`); the interpreter's value routes and the SLD bridge's dictionaries from values go (§4); kernel-language's text (§5). WI-20260923-DK0QJ's half (b) goes here. Depends on 1 and 2. WI-20261105-P0QGF.
4. No typed caller (§6.1, §6.2): the host entry and a query compose a requirement from the argument's carried type, as 060 decides, and nothing more; a value whose type is open at a requirement is refused at load, naming it, where today the row fails in silence (§6.2's `src([])`); the three host entries become one; `resolve_bridge_requirements` goes with its last caller. WI-20260923-DK0QJ's half (a) goes here. Depends on 3. WI-20261105-CBRD2.
