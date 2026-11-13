# Proposal 074: A typeclass instance is a dictionary, and is written as one

## Status: Draft (2026-11-13); §1 to §4 decided, §5 (stages) drafted, §6 (specs over a type constructor) decided: target set H1–H5, G1–G3; a constructor as a value is the bare sort (H5), a sort fills a constructor slot by its unwritten parameters in order (H4), an operation declares a higher-kinded parameter as a sort does (H2), a row parameter of one is a row by use (G1), no group-three row for now. Decided with the user on 2026-11-13, in the order below: a written form has one reading (§1.1); a spec may have several carriers, so a value typed at a spec is no value of a carrier, and KSSA4's rule stands (§1.2); a user is not made to write a type parameter that the call's types fix (§1.3); type parameters are unrolled at compile time, and dictionaries are passed at run time (§1.4); the target programs every choice must run; a dictionary holds no types, and a type read at run time arrives as its `TypeValue` dictionary (§3, revised after review); `x.T` read as a value is proposal 065's dispatch, as a type parameter is, its clause `requires TypeValue[x.T]` written, and supplied from `x` where `x`'s spec states it (§3, after review); a dictionary is written `Dictionary.instance[Additive[T = Int64]]()`, its `S` fixed by the bracket or the expected type, a built-in with no definition in the language (§2, after review), and a parameter that takes one is typed at the spec, `x: Additive` (§2); a spec with operations and no parameter has a dictionary, refused where two are in scope; the member spelling in a function type is the operation's type parameter, as everywhere in its signature, and a function value applied at several instances takes a dictionary parameter for each (§4; "one instance per arrow", decided first, was withdrawn the same day after review); a constant may hold a dictionary (§2, T12). `Dictionary.instance` names a provider by the spec's short name (§2, T11). The target set confirmed (T1–T9, T11, T12; T10 restored after review), T2 and T3 restated with §4. After review: a call uses, after a provider its bracket names and before §8.7's order, the dictionary its operation is handed at the call's spec and type (§2, T13); a rule body reaches a dictionary through an operation that returns one until TC54R reads the bracket there, and a dictionary constant has no value in a data slot (§2); the classes of "Which sorts have a dictionary" are read off the declaration alone (§2); a sort with constructors is closed, a `requires` naming one refused (§2, stage 5). A gap T11 needs, not a decision: a named instance's type arguments fix its parameters.

## Extends: [073](073-abstract-values-are-instances.md) §2 (a value typed at a spec over a parameter is an instance at the carrier its type fixes; its spelling at a call is replaced by §2 here) and §6.2 (no type is stored with a value).

## Tracked by: the `proposal-074` sequence, one ticket per stage (filed 2026-11-13): stage 1 WI-20261113-2KSAA, stage 2 WI-20261113-24ZZ0, stage 3 WI-20261113-Q2C01, stage 4 WI-20261113-5CZ9F, stage 5 WI-20261113-DY84V, stage 6 WI-20261113-FCMJA, stage 7 WI-20261113-10SN8 (PreOpened), stage 8 WI-20261113-64272. WI-817 depends on stage 1.

## Relates to: kernel-language §4.4 (a quantified type is inferred, never written; §4 keeps it so), §5.4 (the member spelling `Spec.Member`: one instance per signature), §8.2 (a spec over a parameter), §8.7 (which provider a call gets); WI-20261005-KSSA4 (the user's decision of 2026-10-05: `w: Tagger` is not `w: Tagger.C`); WI-20261024-TC54R (a call's bracket read in a rule body; §2, "In a rule body"); WI-817 (one closure applied at several types; its witness is T2, §4's dictionary-parameter program); `stdlib/anthill/realization/runtime.anthill` (`Dictionary[S]`: "S … tracked statically by the typer, never read off the value").

## The problem

A spec over a parameter is a typeclass: `Additive` is a set of operations over a type `T`. A parameter typed at it, `x: Additive`, holds an instance of the typeclass: the dictionary of `Additive`'s operations at one `T`, with `x.T` naming that type.

```anthill
operation add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b
operation ints() -> Int64 = add2(Additive[T = Int64], 2, 3)    -- 5
operation asType() -> Type = Additive[T = Int64]               -- the type
```

Since 073 part 2 the same text, `Additive[T = Int64]`, means the type where a `Type` is expected and the dictionary where `Additive` is expected: `add2(Additive[T = Int64], 2, 3)` loads and answers 5. That is 073 part 2's defect, one written form with two meanings, which §1.1 rules out. The dictionary needs a spelling of its own, and with it come two questions: what a dictionary value holds, and how a function value that is applied at several types receives its dictionaries.

## Target programs

Every choice in §2 to §4 must run these, with the answers given; an option that cannot is excluded. "Today" is measured on the tree of 2026-11-13. The group is §1.4's. A dictionary written `‹Additive at Int64›` is spelled as §2 decides.

| | program | answer | group | today |
|---|---|---|---|---|
| T1 | `add3(x: Additive.T, y: Additive.T) -> Additive.T = x + y` at `(1, 2)`, `(3.0, 4.3)` | 3, 7.3 | 1 | runs |
| T2 | `applyBoth(f: (d: Additive, x: d.T, y: d.T) -> d.T)` calling `f(‹Additive at Int64›, 1, 2)`, `f(‹Additive at Float›, 3.0, 4.3)`, given `lambda (d: Additive, x: d.T, y: d.T) -> x + y` | (3, 7.3) | 1 | runs today only through 073 part 2's defect, removed in stage 1 |
| T3 | `sumWith[X](f: (x: X, y: X) -> X, a: X, b: X) -> X = f(a, b)`, given `let f = lambda (x, y) -> x + y`, at `(f, 2, 3)`, `(f, 1.5, 2.5)` | 5, 4.0 | 1 | runs |
| T4 | `applyMap(f: (p: Additive, q: Additive, x: p.T) -> q.T) = f(‹Additive at Int64›, ‹Additive at Float›, 2)`, given `lambda (p: Additive, q: Additive, x: p.T) -> Additive.zero[T = q.T]()` | 0.0 | 1 | runs today only through 073 part 2's defect, removed in stage 1 |
| T5 | `applyMap[T, S](f: (v: T) -> S, x: T) -> S requires Additive[T = T], Additive[T = S] = f(x + x)`, given `lambda (v: Int64) -> if v > 3 then 1.5 else 0.5` and `2` | 1.5 | 2 | runs |
| T6 | `use(a: Convert.X) -> Convert.Y` and `useWith(c: Convert, a: c.X) -> c.Y`, each `= Convert.conv(a)`, at `2` over a provider `Convert[X = Int64, Y = Float]` answering `1.5` | 1.5, 1.5 | 1 | runs (`useWith` only through 073 part 2's defect, removed in stage 1) |
| T7 | `add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b` at `(‹Additive at Int64›, 2, 3)` | 5 | 1 | runs today only through 073 part 2's defect, removed in stage 1 |
| T8 | polymorphic recursion through a conditional provision, one leg through a lambda (`wi817_polyrec_requirement_test`) | 1, 12, 122 | 2 | runs |
| T9 | `[xs, xs.map(twice)]` at `List[T = Stream[T = Int64, E = {}]]`, `takeN(s, 1)` on each (073 §2) | `[[1], [2]]` | 3 | runs |
| T10 | `tOf(x: Additive) -> Type requires TypeValue[T = x.T] = x.T` at `‹Additive at Int64›`, `‹Additive at Float›`; and, over `sort Num { sort T = ?  requires TypeValue[T = T]  operation add(a: T, b: T) -> T }` provided at `Int64` and `Float`, `tOf(x: Num) -> Type requires TypeValue[x.T] = x.T` mapped over a list of `‹Num at Int64›` and `‹Num at Float›` | `Int64`, `Float`; `[Int64, Float]` | 1; 3 | refused: "`T` is a type member of `Additive`, and the receiver's type leaves it open here, so it is no type value"; written `TypeValue.type_value[T = x.T]()`, the first runs, and the second is refused at `map(tOf)`: "cannot be supplied for `tOf` used as a function value" |
| T11 | an instance derived through an isomorphism (below), used through its name: `Additive.add[Additive = ProjAdditive[X = Int64, Y = Meters]](m(v: 2), m(v: 3))` | `m(v: 5)` | 1 | refused: "construction is cyclic: `Additive[T = Meters]` -> `Additive[T = ProjAdditive.X]` -> …" |
| T12 | `const ints: Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()` and `add2(ints, 2, 3)` | 5 | 1 | refused: "const has a non-foldable body" |
| T13 | `viaParam(t: Tag[T = Leaf]) -> Int64 = Tag.tag(leaf(k: 0))`, handed `Alt`'s dictionary, where `Leaf`'s own provision of `Tag` answers 1 and a second provider `Alt` answers 2 | 2 | 1 | 1: the call is decided at load at `Leaf`, and `t` is not used |

T11's program (the user's, 2026-11-13): `Additive` at `X`, a pair of maps between `X` and `Y`, and the instance at `Y` they give, `ya + yb = fxy(fyx(ya) + fyx(yb))`:

```anthill
sort Meters
  entity m(v: Int64)
end
sort Iso
  sort A = ?
  sort B = ?
  operation to(a: A) -> B
  operation from(b: B) -> A
end
sort MetersIso
  provides Iso[A = Int64, B = Meters]
  operation to(a: Int64) -> Meters = m(v: a)
  operation from(b: Meters) -> Int64 =
    match b
      case m(v) -> v
end
sort ProjAdditive
  sort X = ?
  sort Y = ?
  requires Additive[T = X]
  requires Iso[A = X, B = Y]
  provides Additive[T = Y]
  operation add(a: Y, b: Y) -> Y = Iso.to(Iso.from(a) + Iso.from(b))
  operation neg(a: Y) -> Y = Iso.to(Additive.neg(Iso.from(a)))
  operation zero() -> Y = Iso.to(Additive.zero[T = X]())
end
```

The declarations load today; every call that reaches `ProjAdditive` is refused, named or not, because nothing fixes `X` where `Additive[T = Meters]` is built, and `Additive[T = X]` at an open `X` reaches `ProjAdditive` again. It needs two things: a named instance's type arguments fix its parameters (`X = Int64` from `ProjAdditive[X = Int64, Y = Meters]`, after which the construction is `Int64`'s `Additive` and `MetersIso` — finite); a provider whose `provides` leaves `X` unbound chosen only where written (§2, after review), so no other call reaches the cycle; and §2's `Dictionary.instance` naming a provider, since `ProjAdditive` is a provider and not a spec — decided with the user 2026-11-13: by the key a call's bracket names one with, the spec's short name, `Dictionary.instance[Additive[T = Meters], Additive = ProjAdditive[X = Int64, Y = Meters]]()`; without it, the provider is the one §8.7's order selects. The same instance for one concrete `Y`, written as an ordinary provision (`sort MetersAdd provides Additive[T = Meters]` with `add(a, b) = toM(fromM(a) + fromM(b))`), runs today: `m(v: 2) + m(v: 3)` answers `m(v: 5)`.

Kept refused: `direct(w: Tagger) = Tagger.probe(w)` and `x + a` over `x: Additive` (§1.2), `add3(1, 2.5)` (one instance, §1.3); `applyBoth(f: (x: Additive.T, y: Additive.T) -> Additive.T)` calling `f(1, 2)` ("expected Additive.T, got Int64": the arrow's member is `applyBoth`'s type parameter, §4) and `applyBoth[X](f: (x: X, y: X) -> X)` calling `f(1, 2)` and `f(3.0, 4.3)` (one `X` per call of `applyBoth`).

T10 was left out of the first draft, read as needing a type inside a dictionary; it needs none (§3, after review), and is a target again.

## 1. Decided

### 1.1 One written form, one reading

A form means one thing wherever it is written, except in a rare case argued on its own. `Additive[T = Int64]` written as a value is the type `Additive[T = Int64]`.

### 1.2 A spec may have several carriers

`x: Spec` cannot mean "a value of the spec's carrier", because a spec may have more than one:

```anthill
sort Convert
  sort X = ?
  sort Y = ?
  operation conv(a: X) -> Y
end
```

A value is typed at a carrier by naming it — the member spelling, or a type parameter under `requires` — and a value typed at the spec is the dictionary, covering all its parameters:

```anthill
operation use(a: Convert.X) -> Convert.Y = Convert.conv(a)          -- use[P, Q](a: P) -> Q requires Convert[X = P, Y = Q]
operation useWith(c: Convert, a: c.X) -> c.Y = Convert.conv(a)
```

So KSSA4's rule stands: `w: Tagger` is no value of `Tagger.C`, and `x + y` over `x: Additive` is refused.

### 1.3 Type parameters are not written where the call fixes them

A call fixes a type parameter from its arguments and its expected result, and the user does not write it. The member spelling already gives an operation that: `add3(x: Additive.T, y: Additive.T) -> Additive.T = x + y` is called `add3(1, 2)` (3) and `add3(3.0, 4.3)` (7.3); `add3(1, 2.5)` is refused, the two members being one instance. §4 says what this gives a function value.

### 1.4 Compile time and run time

Type parameters are unrolled at compile time; dictionaries are passed at run time. Each construct falls in one of three groups:

| group | example | dictionary |
|---|---|---|
| a call at a known type | `add3(1, 2)` | built at load, a constant of the call |
| a call at a type parameter | inside `applyMap[T, S] … requires Additive[T = T]` | decided at each call site at load, passed at run time |
| a value no type in scope fixes | an element of `List[T = Stream]` | carried by the value (073 §2) |

Only the first is a compile-time constant. The second is passed at run time through the requirement channel, though which dictionary each call site passes is fixed at load; unrolling the type parameters removes it only where the instantiations are finite, and polymorphic recursion (WI-817's witness: each step calls at `Wrap[T]` of the previous one) needs it at run time. The third rides with a value. Every rule below says which group it reaches.

**A host call and the code generators** (decided with the user 2026-11-13, after review). A host call (`interp.call`, an entry point a bundle runs) passes values and writes no bracket. It obtains a dictionary from an operation that returns one, as a rule body does (§2, "In a rule body"), and passes it as a value: `add2(intInstance(), 2, 3)` answers 5 today. A type parameter is fixed by the argument values at the boundary, the one place a value's sort is read, a host having no anthill types: `sum2(2, 3)` over `sum2[X](a: X, b: X) -> X requires Additive[T = X]` answers 5 and `sum2(1.5, 2.5)` 4.0 today. Where no argument fixes it, the call is refused at the boundary, naming the parameter, where today `zeroOf()` over `zeroOf[X]() -> X requires Additive[T = X]` dies with `Internal("DeferToRequirement: requirement param __req_additive not bound in caller frame")`; and an argument that is no dictionary where one is expected is refused naming the parameter, where today `add2(7, 2, 3)` dies with `Internal("… its argument is a Int64, not the instance")`.

The generators gain no dictionary in stages 1 to 6, and that is temporary: C++ and Rust will need them (stage 7). Today C++ turns a type parameter under `requires` into a template, `template<typename X> static X sum2(X a, X b) { return (a + b); }`, so group two needs no dictionary there while its instantiations are finite, and refuses a dictionary parameter loudly ("no C++ mapping for sort 'anthill.prelude.Additive'", and for an `x.T` return "denoted-bearing return type unsupported by C++ codegen"); the Rust generator writes skeletons only and refuses `Additive` ("no Rust mapping for the prelude sort"); the Scala mapping (`docs/scala-forward-mapping.md`) makes a `requires` a `using` parameter and has no row for a parameter typed at a spec. Until stage 7, a dictionary parameter, `Dictionary.instance` and `x.T` read as a value stay loud refusals in each.

## 2. How a dictionary is written (decided)

Where a dictionary is passed explicitly — two independent instances in one function type, which the member spelling cannot say (§1.3 gives one instance per signature):

```anthill
operation applyMap(f: (p: Additive, q: Additive, x: p.T) -> q.T) -> Float =
  f(Additive[T = Int64], Additive[T = Float], 2)                  -- loads today only through 073 part 2's defect, removed in stage 1
operation go() -> Float =
  applyMap(lambda (p: Additive, q: Additive, x: p.T) -> Additive.zero[T = q.T]())   -- 0.0
```

**Which sorts have a dictionary** (decided with the user 2026-11-13; revised after review the same day: read off the declaration alone, never off the provisions). Not "a sort with operations" alone — an enum has operations — but four classes the declaration tells apart:

| the sort declares | its dictionary | examples |
|---|---|---|
| constructors — an entity, an enum, with or without operations | none: its operations are its own members, called on its values; its dictionaries are those of the specs it provides, `Dictionary.instance[PartialEq[T = E]]()`; a `requires` naming it is refused at load | `Box`, `E` with `operation flip(e: E) -> E`, `Leaf` |
| an operation that receives on the sort itself | none of its own: a value of it is a value with its dictionary (073 §2) | `Stream`, `Mergeable` |
| operations, its own or reached through its `provides` or `requires` chain, none receiving on the sort itself | a dictionary of those operations, a provider's bodies, else the sort's own, with the dictionaries its chain reaches as sub-dictionaries; with no parameter, chosen as any dictionary at one type is: the one provider, a default provision, or a named one where several answer | `Additive[T = Int64]`, `Convert[X = Int64, Y = Float]`, `Default[T = Int64]`, `ProjAdditive[X = Int64, Y = Meters]`, `Ticker`, `anthill.prelude.Time`, an example's `Program`; `Ord[T = Int64]`, which declares no operation and reaches `WeakOrd`'s through its `provides WeakOrd[T = T]` |
| no operation in its whole chain | none: a marker; a requirement of it passes nothing at run time | `anthill.cli.Main`, an operation-less `Marker[T = Int64]`, `anthill.logic.Minimal`, `Constructive` and `Classical` (rules all the way down: a rule is answered by resolution, not through a dictionary) |

The classes are read over the whole chain (after review, decided with the user 2026-11-13): `Ord` declares no operation, and `provides WeakOrd[T = T]`, a conversion and so a chain entry, is how a body under `requires Ord[T = X]` reaches `WeakOrd.compare` — `cmp[X](a: X, b: X) -> Int64 requires Ord[T = X] = WeakOrd.compare(a, b)` answers -1, 0 and 1 at `(1, 2)`, `(2, 2)`, `(3, 2)` today — so `Ord` has a dictionary, and only a sort nothing in whose chain declares an operation is a marker. A spec over a parameter is a sort of the third row whose operations mention that parameter: `sort Default { sort T = ?  operation default() -> T }` is over `T` whoever provides it, so `d: Default` holds a dictionary and `Default[T = Int64]` is the type. Today the class is read off the provisions where no operation receives on the parameter (`spec_over_parameter`, `kb/typing/provision.rs`): provided by a sort with values of its own, `d: Default` takes that sort's value and `Default[T = Int64]` is refused as a `Type`; provided by `Int64`, the same program answers 42. That rung goes. `ProjAdditive`, whose operations all have bodies, is of the third row: `Dictionary.instance[ProjAdditive[X = Int64, Y = Meters]]()` is its own dictionary, typed `ProjAdditive[…]`, and handing it on as `Additive`'s is the named form below (T11); written where it is expected it is refused today, "no impl provides ProjAdditive". A module, a sort of the third row nothing provides (`Time`, a `Program`, lf1's controllers), has the dictionary of its own bodies: `Dictionary.instance[Time]()`, and `Time.now()` runs as today. The first version of this table gave an operation-less `Marker[T = Int64]` an empty dictionary; it has none, as `Main` has none, which differs only in `Dictionary.instance[Marker[T = Int64]]()` being refused.

**A sort with constructors is closed** (decided with the user 2026-11-13, after review). Written `sort` or `enum` alike, nothing joins it: not by `provides`, refused today (§5.1), and not by `requires`. Today `sort X1 { requires X  entity e2(j: Int64) }`, over `sort X { entity e1(k: Int64)  operation get(x: Self) -> Int64 = 1 }`, makes `X1` a subtype of `X` (§8.2's refinement): `take(e2(j: 0))` over `take(x: X) = X.get(x)` answers 1, and a match over `X` takes `case e2`, while `e1` is no `X1`. That `requires` is refused at load, so a `requires` names a sort without constructors only, a spec or a marker, and reads one way. A data sort requiring a spec (`requires Eq[T = K]`) is unchanged. The standard library and the examples write no such `requires` (37 clauses read).

For `Ticker`, `c: Ticker` is an instance of `Ticker` — its dictionary — as `x: Additive` is, and its operations carry effects as any operation does (decided with the user 2026-11-13): the dictionary chooses the implementation, and the effect, `Time.Clock` here, says what it does, handled by its handler as anywhere (`anthill run` binds `Clock` to the host's time; a test installs a frozen clock). Measured today (the program written with an effect-free `now() -> Int64`): `use(c: Ticker) = 1` takes a `SysTicker` value (`use(sc())` answers 1), and that is refused under this reading, the call being `use(Dictionary.instance[Ticker]())`; `go() = Ticker.now()` is refused ("no provider can be selected here"); and `use() requires Ticker = Ticker.now()` loads and dies at run time, `OperationBodyMissing("Ticker.now")`, which this reading repairs — the caller passes the dictionary. With two `Ticker`s in scope — two parameters, or a parameter and a clause — a call of `Ticker.now()` names neither, and is refused at load (decided with the user 2026-11-13): `stamps(a: Ticker, b: Ticker) = (Ticker.now(), …)` is refused, where `Additive`'s two are told apart by their types (`Additive.zero[T = b.T]()`). No spelling names a dictionary by a value (`c.now()` stays refused, as `x.zero()` is, and a call's bracket takes a sort, not a value). The last row is the boundary: were operation-less sorts given a dictionary, `requires anthill.cli.Main` would demand a provider no program writes. A provider of `Ticker` is named only where it has no constructors (058 §3.5 unchanged; decided with the user 2026-11-13, after review): over `sort SysTicker provides Ticker  operation now() -> String = …`, `Dictionary.instance[Ticker, Ticker = SysTicker]()` is its dictionary; a provider with constructors, as the measured one with `entity sc()`, may be the one provider or the default, and naming it is refused, though no value of it is ever an argument of `Ticker`'s operations.

**A provider named.** `Dictionary.instance[Additive[T = Meters], Additive = ProjAdditive[X = Int64, Y = Meters]]()` — the key a call's bracket names a provider with (`Additive.add[Additive = …](…)`); without it, §8.7's order selects (decided with the user 2026-11-13; T11). A provider whose `provides` leaves one of its parameters unbound is chosen only where a bracket writes it, with that parameter fixed, and §8.7's order passes over it (decided with the user 2026-11-13, after review): `ProjAdditive`'s `provides Additive[T = Y]` binds `Y` and not `X`. Positional and named type arguments are one, `ProjAdditive[Int64]` being `ProjAdditive[X = Int64]`, and a parameter the bracket leaves unwritten is fixed by the call's type, `Y = Meters` at `Additive[T = Meters]`. Today every call that reaches `ProjAdditive`, written or not, is refused as a cycle, and so is any `Additive` goal no provider answers once it is declared: `Additive.add(true, false)` reports "construction is cyclic: `Additive[T = Bool]` -> `Additive[T = ProjAdditive.X]` -> … no type written at a use changes that", `ProjAdditive` being a candidate at every `Y`.

**Which dictionary a call uses** (decided with the user 2026-11-13, after review; T13). A call of a spec's operation uses the first of: the provider its bracket names; a dictionary its operation is handed at the call's spec and type, as a parameter (`t: Tag[T = Leaf]`, or `x: Additive` at `x.T`) or as a clause (`requires Additive[T = X]`); the provider §8.7's order selects. A call two handed dictionaries answer, two parameters or a parameter and a clause, is refused at load. A dictionary held by a constant or a `let` is used only where it is passed. So `viaParam(t: Tag[T = Leaf]) = Tag.tag(leaf(k: 0))`, handed `Alt`'s dictionary, answers 2, as `viaOpen(t: Tag, x: t.T) = Tag.tag(x)` does today; today `viaParam` answers 1, and so does `viaMember(t: Tag[T = Leaf], x: t.T) = Tag.tag(x)`, the call being decided at load at `Leaf` without using `t`. And `sumM(d: Additive[T = Meters], a: Meters, b: Meters) -> Meters = a + b`, handed `ProjAdditive`'s dictionary, uses it. This is no implicit scope-directed selection (§8.7): what decides is the dictionary the caller passes, not an import or a nearer declaration. It is the rule "Which sorts have a dictionary" states for `Ticker`.

**A constant may hold a dictionary** (decided with the user 2026-11-13; T12): `const ints: Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()`. The dictionary is built at load at known types (group one) and is pure, and a constant is a value computed once. Refused today, "const has a non-foldable body".

**In a rule body** (decided with the user 2026-11-13, after review). A rule body reads no bracket on a call (kernel-language §5.4: "elsewhere it calls an operation whose body carries the bracket"), so it reaches a dictionary through an operation that returns one: over `intInstance() -> Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()`, `rule viaRuleReturned(?r) :- ?r <=> add2(intInstance(), 2, 3)` answers 5. The bracket read in a rule body is WI-20261024-TC54R's. A constant holding a dictionary has no value in a data slot (`fact holds(d: ints)`, a rule body's `add2(ints, 2, 3)`): storing a dictionary in a fact is one of the readers §3 leaves unmeasured.

**The type — decided with the user 2026-11-13: (T1).** A parameter that takes a dictionary is typed at the spec, `x: Additive`, as today, and `x.T` names its member. To add no rule relating two spellings of one type, the built-in is declared `operation instance() -> S` in `sort Dictionary`, so `Dictionary.instance[Additive[T = Int64]]()` is typed `Additive[T = Int64]`: to pass or take a dictionary, user code names `Dictionary` only as the operation's sort and need not write it as a type. Not decided (with the user 2026-11-13): the readers `Dictionary` already has (`impl`, `arity`, `sub`, `resolveOp`, `ops`) receive `d: Self`, a `Dictionary[S = …]`, so they do not take a dictionary `instance` returns, typed `S`: `Dictionary.arity(Dictionary.instance[Additive[T = Int64]]())` is refused. Today they are reached only from the host (`interp.call`) and from rules, so they stay as they are, the reflection layer; the question is taken up when a program needs to read a dictionary it was given. The candidates:

- (T1) keep `p: Additive` — the spec's name as the type of its dictionaries (today);
- (T2) `p: Dictionary[S = Additive]` — the type names the kind of value, its member read through `S` (`x.S.T`), every signature with a dictionary parameter rewritten.

**The value — decided with the user 2026-11-13.** What is passed today as `Additive[T = Int64]` is written `Dictionary.instance[Additive[T = Int64]]()`: a member of `anthill.realization.runtime.Dictionary`, its bracket the spec application — a type, its one reading — and its result the dictionary, typed `Additive[T = Int64]` (the type half, below), built at load at a known type, the clause's own at a rigid one (`Dictionary.instance[Additive[T = X]]()` under `requires Additive[T = X]`). Its `S` is fixed as any type parameter is, by its bracket or by the type its result is expected at (§1.3; decided with the user 2026-11-13, after review), to a spec application with every parameter fixed, or rigid under a clause: `const ints: Additive[T = Int64] = Dictionary.instance()` loads, and `add2(Dictionary.instance(), 2, 3)` is refused as unconstrained, as a call of `mk[X]() -> Additive[T = X]` is today. Its bracket is read by a rule of the built-in: its one positional entry is the spec application, binding `S`, and every key names a provider by the spec's short name (`Additive = ProjAdditive[…]`), as §5.4's second rung names one on a call of that spec's operation. No declaration gives that key a target, and the parameter is never written as a key, so a spec named `S` does not collide with it. Refused at load: a sort with values of its own — an entity's or an enum's type, `Dictionary.instance[Box[V = Int64]]()`, `Dictionary.instance[E]()`, has no dictionary, and the result declared `S` would claim a `Box` or an `E` (the dictionaries such a sort has are those of the specs it provides, written at the spec: `Dictionary.instance[PartialEq[T = E]]()`); a spec that is its own carrier — a value typed `Stream` is a stream with its dictionary (073 §2), not a dictionary; an application leaving a parameter unwritten; and one no provision answers (`Additive[T = Bool]`). A built-in, as `type_value` is, with no definition in the language (after review): a named requirement's name is a type parameter (058 §3.4), which proposal 065 reads as a value as its type — `requires d: Additive[T = Int64] = d` asks for `TypeValue[T = d]` today — so `instance[S]() -> S requires x: S = x` returning the dictionary would read `x` a second way (§1.1). The candidates it was chosen among:

- (V1) a member every spec has, read at the bracket, as `type_value` is: `Additive.instance[T = Int64]()`;
- (V2) an operation from a type to its dictionary, evaluated at load: `dictionary(Additive[T = Int64])`;
- (V3) only the member spelling — no explicit dictionary at all — and two instances in one function type written by type parameters (§4's question). Excluded by T2, T4 and T7: §4 keeps the member spelling the operation's, so a function value applied at several instances takes them as dictionaries.

A dictionary under a clause, `requires Additive[T = X]`, is the clause's own in every option: `Additive.instance[T = X]()` under (V1).

## 3. What a dictionary value holds (decided with the user 2026-11-13; revised after review the same day)

A dictionary holds no types: today's `Dictionary(sub0 .. subN, impl: S)`, the provider sort and its sub-dictionaries, unchanged. One provider may provide several specs, so the witnessed spec is not recoverable from the value, and 073 §6.2 decided that no type is stored with a value. It prints in that shape, `Dictionary(impl: Int64)`, its sub-dictionaries positional before `impl` (decided with the user 2026-11-13, after review); today it prints `Dictionary[impl = Int64]`, the bracket of a type applied. Equality of two dictionaries stays refused, as it is in typed code today: a dictionary holds its provider only, so two of one provider for two specs would compare equal. A fact holds none (§2, "In a rule body").

A type read at run time arrives as a dictionary of its own, `TypeValue` at that type (proposal 065), and the operation that reads it writes the clause, `requires TypeValue[x.T]`, as 065 has it for a type parameter: explicit, not inferred (decided with the user 2026-11-13, after review). Where `x`'s spec itself states `requires TypeValue[T = T]`, `x` holds that dictionary, and a call supplies the clause from it, so a list of such dictionaries mapped through `tOf` answers `[Int64, Float]` (T10); over `Additive`, which states none, the same `map` is refused at load, nothing supplying `TypeValue` at each element's `T`.

Measured today, over `sort Num { sort T = ?  requires TypeValue[T = T]  operation add(a: T, b: T) -> T }` provided at `Int64` and `Float`: `tOf(x: Num) -> Type requires TypeValue[T = x.T] = TypeValue.type_value[T = x.T]()` answers `Int64` and `Float` at a known dictionary, and `[‹Num at Int64›, ‹Num at Float›].map(tOf)` is refused, "requirement `TypeValue[T = x.T]` cannot be supplied for `tOf` used as a function value; its carrier is a projection this call does not ground". Without the clause the same `tOf` loads, `Num`'s own requirement answering it, and the `map` answers `[Int64, Float]`: that loads today and is refused under this rule.

**`x.T` read as a value is 065's dispatch** (decided with the user 2026-11-13, after review). A type with no fixed value read in value position, a type parameter `X` or a member `x.T` alike, is `TypeValue.type_value[T = …]()`: it needs `TypeValue` at that type in scope, and is refused at load otherwise, as `X` is today. So `tOf(x: Additive) -> Type requires TypeValue[T = x.T] = x.T` answers `Int64`; today it is refused, "`T` is a type member of `Additive`, and the receiver's type leaves it open here, so it is no type value", while `tOf[X](y: X) -> Type requires TypeValue[T = X] = X` answers `Int64`.

The first draft asked whether a dictionary should hold its types — (D1) as today, (D2) a slot for its types in `Dictionary`, (D3) a new entity — and chose D1 by leaving T10 out. T10 needs no type in a dictionary, so D2 and D3 answer nothing.

## 4. The member spelling in a function type (decided with the user 2026-11-13)

`Spec.Member` written inside an arrow is what it is anywhere in the signature: the operation's type parameter, one instance per signature (kernel-language §5.4); in the body, a lambda's binder written so names the same instance. An arrow binds no type of its own, and §4.4's quantified type stays inferred, never written. Today's rule, unchanged, measured:

```anthill
operation h(g: (x: Additive.T) -> Additive.T, y: Additive.T) -> Additive.T = g(y)
operation go() -> Int64 = h(lambda (x: Int64) -> x + 1, 2)        -- 3

operation total(x: Additive.T, y: Additive.T) -> Additive.T =
  let f = lambda (a: Additive.T, b: Additive.T) -> a + b
  f(x, y)        -- total(1, 2) answers 3; f(1, 2) here is refused, "expected Additive.T, got Int64"
```

A function value applied at several instances inside an operation takes each as a dictionary parameter, passed as §2 writes it (T2):

```anthill
operation applyBoth(f: (d: Additive, x: d.T, y: d.T) -> d.T) -> (Int64, Float) =
  let ints = f(Dictionary.instance[Additive[T = Int64]](), 1, 2)
  let floats = f(Dictionary.instance[Additive[T = Float]](), 3.0, 4.3)
  (ints, floats)
operation both() -> (Int64, Float) = applyBoth(lambda (d: Additive, x: d.T, y: d.T) -> x + y)   -- (3, 7.3)
```

Two independent instances are two such parameters: `applyTwo(f: (p: Additive, q: Additive, a: p.T, b: q.T) -> q.T) = f(Dictionary.instance[Additive[T = Int64]](), Dictionary.instance[Additive[T = Float]](), 1, 2.5)`, given `lambda (p: Additive, q: Additive, a: p.T, b: q.T) -> b + b`, answers 5.0. One closure handed to an operation at several types needs no dictionary parameter: a `let`-bound lambda is generalized, and each reference takes the dictionary at the type it is used at (§4.4; T3). Where the function is at one type of each, the instances are type parameters of the operation:

```anthill
operation applyMap[T, S](f: (v: T) -> S, x: T) -> S requires Additive[T = T], Additive[T = S] = f(x + x)
operation go() -> Float = applyMap(lambda (v: Int64) -> if v > 3 then 1.5 else 0.5, 2)   -- 1.5
```

Withdrawn the same day, after review: "one instance per arrow", each application of `f: (x: Additive.T, y: Additive.T) -> Additive.T` fixing the member and handing its dictionary (WI-20261113-26390, deleted). Where the signature names the member outside the arrow too, it contradicted §5.4's one instance per signature (`go` above, 3 today, would be refused); it wrote the quantified type §4.4 says is never written; and it left open whose instance a result arrow has, where else the spelling may be written (a field, a `let` annotation, a type argument, a rule head), and how such an arrow converts to and from `(x: Int64) -> Int64`. The dictionary-parameter form says the same with the rules there are.

## 5. Stages

§4 is today's rule and needs no stage. Stage 1 comes first; stages 2, 3 and 4 each depend on it and not on one another; stage 5 depends on none; stage 6 depends on stage 1; stage 7 is parked; stage 8, §6's, depends on stages 1 and 6. §6 was decided before any stage was filed: stage 1 fixes what a dictionary is at run time, and §6's programs fit it (H5). Each stage writes its kernel-language text, agreed with the user before it is committed, and is accepted on its rows driven to their values, its back-outs measured, the full gate, and the families on both carriers.

**Stage 1 — `Dictionary.instance[…]()`, 073 part 2's defect removed, and a call uses the dictionary it is handed** (§2; T2, T4, T6, T7, T13).

- `operation instance() -> S` in `sort Dictionary` (`stdlib/anthill/realization/runtime.anthill`), a built-in as `type_value` is: at a known type the dictionary is built at load (group one); at a type rigid under a clause it is the clause's own (group two).
- Refused at load, a row each: an entity's or an enum's type (`Dictionary.instance[Box[V = Int64]]()`, `Dictionary.instance[E]()`), a spec that is its own carrier (`Stream`), an application leaving a parameter unwritten, one no provision answers (`Additive[T = Bool]`), a sort with no operations (`anthill.cli.Main`, `Marker[T = Int64]`, `anthill.logic.Constructive`), and, until stage 3, a sort with operations and no parameter (`Ticker`, `Time`).
- The class read off the declaration (§2, "Which sorts have a dictionary"): `spec_over_parameter`'s provision rung goes. Rows: `Default` provided by a sort with values of its own, where `d: Default` takes a dictionary, that sort's value is refused there and `Default[T = Int64]` is a `Type`; `Default` provided at `Int64`, 42 as today; `Dictionary.instance[ProjAdditive[X = Int64, Y = Meters]]()`, its own dictionary. The classes read over the whole chain: `cmp[X](a: X, b: X) -> Int64 requires Ord[T = X] = WeakOrd.compare(a, b)` answers -1, 0, 1 (as today), `Dictionary.instance[Ord[T = Int64]]()` is a dictionary, and `Dictionary.instance[anthill.logic.Classical]()` is refused, a marker.
- A spec application where a dictionary is expected is refused: `add2(Additive[T = Int64], 2, 3)`, the message naming `Dictionary.instance[Additive[T = Int64]]()`. Where a `Type` is expected it stays the type (`asType()`).
- Rows: the target programs in one test file, T1 to T9 driven to their answers in §2's spelling, with the kept refusals beside them; stages 2 and 4 add T12 and T11 to it. The rows of 073 part 2 and part 3 that write a spec application at a call are rewritten (`wi_p0qgf_spec_instance_values_test`, `wi_p0qgf_lambda_instance_test`, `wi_dndzf_arrow_parameter_projects_another_test`).
- In a rule body (§2): `viaRule` and `viaRuleDefaulted` are written through an operation that returns the dictionary, as `viaRuleReturned` is. The direct spelling, `?r <=> add2(Dictionary.instance[Additive[T = Int64]](), 2, 3)` answering 5, is a row of whichever of this stage and WI-20261024-TC54R lands second.
- Spec: §8.2's paragraph "Where the spec is expected, the spec application is the instance … where a `Type` is expected it is the type"; §8.2's "How a position asks for a provider", whose rung "or, where it declares no operation that says, one a provision binds a parameter of to the providing sort" goes (§2, "Which sorts have a dictionary"); and `Dictionary`'s doc comment.
- Which dictionary a call uses (§2; T13): `viaParam` and `viaMember`, handed `Alt`'s dictionary, answer 2; a bracket naming `Leaf` outranks the handed dictionary; a call two handed dictionaries answer is refused at load.
- `S` fixed as a type parameter is (§2): `let k: Additive[T = Int64] = Dictionary.instance()` then `add2(k, 2, 3)` answers 5; `add2(Dictionary.instance(), 2, 3)` is refused as unconstrained; a key in the bracket names a provider.
- A host call (§1.4): `zeroOf()` from the host refused at the boundary naming `X`, `add2(7, 2, 3)` naming `x`; `sum2(2, 3)` 5 and `add2(intInstance(), 2, 3)` 5 as today. The Scala emitter measured on a dictionary parameter, and refusing it loudly if it emits anything else.
- A dictionary prints `Dictionary(impl: Int64)` (§3); today `Dictionary[impl = Int64]`.
- WI-817 depends on it: its witness is T2.

**Stage 2 — a constant holds a dictionary** (§2; T12). `const ints: Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()` is folded at load, and `add2(ints, 2, 3)` answers 5. Today: "const has a non-foldable body". A constant at an application stage 1 refuses is refused as there. Its value in a data slot is not part of the stage (§2, "In a rule body").

**Stage 3 — a sort with operations and no parameter has a dictionary** (§2, the third row of "Which sorts have a dictionary", with no parameter).

- `use(c: Ticker)` takes `Dictionary.instance[Ticker]()`, and `Ticker.now()` in its body reads that dictionary.
- `use() requires Ticker = Ticker.now()` reads the dictionary its caller passes. Today it loads and dies at run time, `OperationBodyMissing("Ticker.now")`.
- `go() = Ticker.now()` takes the dictionary as any dictionary at one type is chosen: the one provider, a default provision, or a named one where several answer. Today: "no provider can be selected here".
- Refused at load: `use(sc())`, a provider's value where the dictionary is expected (it answers 1 today); and a call of the spec's operation with two of its dictionaries in scope, two parameters or a parameter and a clause.
- A provider named: `Dictionary.instance[Ticker, Ticker = SysTicker]()` over a `SysTicker` without constructors; naming one with constructors is refused (058 §3.5).
- The operations keep their effects: `now() -> String effects Time.Clock`, run under `anthill run` and under a frozen clock.
- First, a census: every sort in this row in the stdlib, the examples and the fixtures, and every parameter typed at one. Those are the programs whose meaning moves.
- A module has the dictionary of its own bodies: `Dictionary.instance[Time]()`; `Time.now()`, every example's `Program` and lf1's controllers run as today.
- What is new to build (from review): a supply channel for a requirement with no carrier, which has none today (`use() requires Ticker = Ticker.now()` loads and dies); the refusal of a call two dictionaries answer; and the row's change of admissibility, `use(sc())` answering 1 today, which the census measures as KSSA4's did. The class is read by `spec_over_parameter` and `spec_has_carrier_param` at 28 call sites in 11 files (counted 2026-11-13), each of which the declaration-only reading of stage 1 and this row reach.

**Stage 4 — a named provider fixes its parameters** (§2, "A provider named"; T11). `Dictionary.instance[Additive[T = Meters], Additive = ProjAdditive[X = Int64, Y = Meters]]()`, and the call's bracket `Additive.add[Additive = ProjAdditive[X = Int64, Y = Meters]](m(v: 2), m(v: 3))`, answer `m(v: 5)`: the named provider's type arguments fix `X`, after which its construction is `Int64`'s `Additive` and `MetersIso`, finite. Today refused: "construction is cyclic". Rows (§2, "A provider named"): the bracket `ProjAdditive[X = Int64]`, its positional `ProjAdditive[Int64]`, and `ProjAdditive[Int64, Meters]` answer `m(v: 5)`, `Y` fixed by the call's type where unwritten; the bare `Additive = ProjAdditive` is refused, naming `X` to write; the unnamed `m(v: 2) + m(v: 3)`, with `ProjAdditive` the only provider at `Meters`, is refused as no provider chosen there, its message naming `ProjAdditive` and the bracket that chooses it; `Additive.add(true, false)` is refused about `Bool`, not as a cycle; a cycle among provisions that fix every parameter keeps its message, "no type written at a use changes that". `sumM(d: Additive[T = Meters], a: Meters, b: Meters) = a + b`, handed the named dictionary, answers `m(v: 5)` (stage 1's rule). What is new to build (from review): a witness's plain type arguments are discarded today by design — `selection_witness_sym` (`kb/typing/slots.rs`) keeps the head, the witness's parameters being instantiated at the goal's bindings — so the selection keeps them, and they enter `InstanceSelection`, the key of `resolve_cache`, beside WI-870's `slots`; a row: two sites naming `ProjAdditive` at two `X` (an `Iso` from `Int64` to `Meters` and one from another carrier) each answer through their own.

**Stage 5 — a `requires` naming a sort with constructors is refused** (§2, "A sort with constructors is closed"). First, the count: every such `requires` in the test fixtures, by a traced run of the full gate (the standard library and the examples write none). Each is rewritten, its sort without constructors or the refinement removed, or deleted where it tests only that refinement. Rows: `X1 requires X` refused, naming both sorts; a data sort requiring a spec (`requires Eq[T = K]`) and a spec refining a spec (`Classical requires Constructive`) load and run as today. Spec: §8.2's refinement paragraph ("A sort that refines another is a subtype …") and §5.1's data-sort rule, which today names `provides` only.

**Stage 6 — `x.T` read as a value is 065's dispatch** (§3; T10). In value position `x.T` is `TypeValue.type_value[T = x.T]()`, as a type parameter is: under `requires TypeValue[x.T]`, `tOf(x: Additive) -> Type requires TypeValue[x.T] = x.T` answers `Int64` and `Float`; without the clause it is refused at load, naming the clause to add, as for `X`, over `Num` as well (it loads today). Where `x`'s spec states `requires TypeValue[T = T]`, the clause is supplied from `x`'s dictionary, and the list of T10 answers `[Int64, Float]` (refused today at `map(tOf)`); over `Additive` that `map` is refused. Depends on stage 1, whose spelling its rows write. Spec: §8.2 and proposal 065's rule, which today name a type parameter only.

**Stage 7 — dictionaries in the C++ and Rust generators** (§1.4; parked, filed PreOpened). Group one, a dictionary built at load, emitted as a constant; group two passed where a template cannot unroll it (polymorphic recursion, T8); group three, a value with its dictionary (T9), as the host's own form of a value beside its table. Rows: T2, T4, T7, T8 and T9 generated, compiled and run in each.

**Stage 8 — specs over a type constructor** (§6; H1–H5, G1–G3). An operation's higher-kinded parameter, `lift[F[T]]` (H2), fixed by a call's bracket, an argument or the expected type; a sort filling a constructor slot by its unwritten parameters in order (H4), `provides Monad[M = Box]` loading; a requirement's constructor read through it (`requires Monad[M = F]` making `M[T = A]` read `F[T = A]`, refused today); `m.M[Int64]` off a dictionary parameter (H1); §5.4's member spelling at a higher-kinded member (H3, which loads and dies today); a constructor's dictionary a sub-dictionary of a provider over it (H4's `OptionTMonad`); `TypeValue` at a sort with unwritten parameters (H5, with stage 6's value read), one sub-dictionary per declared parameter with an open-slot dictionary for an unwritten one — rows `Pair[A = Int64]` and `Pair[B = Int64]` read back each as written, and `tyOf(none)` answering `Option` as `tv[X = Option]()` does, while `Additive` at a free or unwritten slot stays refused in both spellings; a row parameter by use (G1–G3). Depends on stages 1 and 6. Rows: H1–H5 and G1–G3 driven to their answers.

Not staged: a lambda argument with two annotated binders not fixing a type parameter its slot names (found writing §4), which is WI-20261103-2N4QH's.

## 6. Specs over a type constructor (target set H1–H5, G1–G3 and its decisions taken with the user 2026-11-13)

A spec whose parameter is a type constructor, `sort Monad[M[T]]`, is designed here before stage 1 fixes what a dictionary is at run time: a type argument can reach the run time as a dictionary (`TypeValue`, §3), and a constructor's must fit the same shape. The programs below, over

```anthill
sort Monad[M[T]]
  operation pure[A](a: A) -> M[T = A]
end
sort OptionMonad
  provides Monad[M = Option]
  operation pure[A](a: A) -> Option[T = A] = some(a)
end
sort ListMonad
  provides Monad[M = List]
  operation pure[A](a: A) -> List[T = A] = [a]
end
```

are the targets; each row names the dictionary value it needs at run time. "Today" is measured on the tree of 2026-11-13.

| | program | answer | group | dictionary at run time | today |
|---|---|---|---|---|---|
| H1 | `lift(m: Monad, x: Int64) -> m.M[Int64] = Monad.pure(x)` at `Dictionary.instance[Monad[M = Option]]()` and at `Monad[M = List]`'s | `some(7)`, `[7]` | 1 | `Dictionary(impl: OptionMonad)`, as for `Additive` | refused: "unresolved type name 'm.M'" |
| H2 | `lift[F[T]](x: Int64) -> F[T = Int64] requires Monad[M = F] = Monad.pure(x)`, called `lift[F = Option](7)`, `lift[List](7)`, and `let o: Option[T = Int64] = lift(7)` | `some(7)`, `[7]`, `some(7)` | 2 | the clause's, passed at run time | syntax error near `[T]`: an operation declares no higher-kinded parameter; the sort-level twin, `sort UseM[F[T]] requires Monad[M = F]` with `lift(x: Int64) -> F[T = Int64] = Monad.pure(x)`, refused: "expected F[T = Int64], got M[T = Int64]" |
| H3 | `lift(x: Int64) -> Monad.M[Int64] = Monad.pure(x)` (§5.4's member spelling: H2 with the parameter unnamed), `let o: Option[T = Int64] = lift(7)` | `some(7)` | 2 | as H2 | loads, and dies at run time: "operation has no body: Monad.pure" |
| H4 | a provider over a type constructor: `sort OptionT[F[T]] { sort T = ?  entity optT(run: F[T = Option[T = T]]) }`, `sort OptionTMonad[F[T]] { requires Monad[M = F]  provides Monad[M = OptionT[F = F]]  operation pure[A](a: A) -> OptionT[F = F, T = A] = optT(run: Monad.pure[M = F](some(a))) }`; `Monad.pure[M = OptionT[F = List]](7)` | `optT(run: [some(7)])` | 1, and 2 inside `pure` | `Dictionary(‹ListMonad's›, impl: OptionTMonad)`: the constructor's dictionary a sub-dictionary, as `ProjAdditive`'s | the declarations load; `pure`'s body refused: "`Monad[M = OptionTMonad.F[T = ?]]` cannot be supplied" |
| H5 | a constructor read as a value: `tOf(m: Monad) -> Type requires TypeValue[m.M] = m.M` at `Option`'s dictionary | `Option` | 1 | `TypeValue` at a constructor | refused at `m.M`; and `TypeValue.type_value[T = Option]()` refused: "no impl provides TypeValue … write every type argument of that type" |

**Graded monads** (added with the user 2026-11-13): a monad indexed by an effect row, so that an effectful computation is held as a pure value whose type says the effects it performs when run. The suspension itself runs today, without a higher kind:

```anthill
sort Eff
  effects E = ?
  sort T = ?
  entity eff(run: () -> T @ E)
end
operation force[R, A](m: Eff[E = R, T = A]) -> A effects R =
  match m
    case eff(run) -> run()
operation pureE[A](a: A) -> Eff[E = {}, T = A] = eff(run: lambda () -> a)
operation liftE[R, A](body: () -> A @ R) -> Eff[E = R, T = A] = eff(run: body)
operation bindE[R1, R2, A, B](m: Eff[E = R1, T = A], f: (a: A) -> Eff[E = R2, T = B]) -> Eff[E = {R1, R2}, T = B] =
  eff(run: lambda () -> force(f(force(m))))
operation build() -> Eff[E = ConsoleOutput, T = Int64] =
  bindE(liftE(lambda () -> println(console(), "inside")), lambda (u) -> pureE(1))
```

`build()` declares no effect and performs none; `force(build())` prints `inside` and answers 1 (measured: `built`, printed between the two, comes first). The row union in a bracket is written `{R1, R2}`; `merge(R1, R2)` there is a syntax error today, being admitted after `effects` and `@` only. The spec over it, and its rows:

```anthill
sort GradedMonad[M[E, T]]                 -- E a row parameter of M: its spelling is a decision below
  operation pure[A](a: A) -> M[E = {}, T = A]
  operation bind[R1, R2, A, B](m: M[E = R1, T = A], f: (a: A) -> M[E = R2, T = B]) -> M[E = {R1, R2}, T = B]
  operation lift[R, A](body: () -> A @ R) -> M[E = R, T = A]
end
sort EffMonad
  provides GradedMonad[M = Eff]           -- pure, bind, lift as pureE, bindE, liftE above
end
```

| | program | answer | group | dictionary at run time | today |
|---|---|---|---|---|---|
| G1 | `greet[M[E, T]](name: String) -> M[E = ConsoleOutput, T = Int64] requires GradedMonad[M = M] = GradedMonad.bind(GradedMonad.lift(lambda () -> println(console(), name)), lambda (u) -> GradedMonad.pure(1))`; `let b: Eff[E = ConsoleOutput, T = Int64] = greet("x")`, then `force(b)` | building prints nothing; `force` prints `x` and answers 1 | 2 | the clause's, `Dictionary(impl: EffMonad)` | refused: an operation declares no higher-kinded parameter |
| G2 | `greetWith(m: GradedMonad, name: String) -> m.M[ConsoleOutput, Int64]`, the same body, at `Dictionary.instance[GradedMonad[M = Eff]]()` | as G1 | 1 | `Dictionary(impl: EffMonad)` | refused, as H1 |
| G3 | the grade checked: `greet` declared `-> M[E = {}, T = Int64]` with the same body; and `force(b)` in an operation whose row lacks `ConsoleOutput` | refused at load, naming `ConsoleOutput` | — | — | both refused for the non-higher-kinded `Eff`: `build` declared `Eff[E = {}, T = Int64]`, "expected Eff[E = {}, T = Int64], got Eff[E = {{}, ConsoleOutput}, T = Int64]"; `quiet() -> Int64 = force(build())`, "undeclared effect: ConsoleOutput" |

A row is a type, and none reaches the run time here: the dictionary of `GradedMonad[M = Eff]` has the shape of `Monad[M = Option]`'s.

The decisions the rows need, taken one by one:

- H4, decided with the user 2026-11-13: a sort written at a constructor slot `M[T]` is the constructor over the parameters it leaves unwritten, lined up with the slot's parameters in declaration order, their count the same: `Option` over `T`; `Box` (`sort V = ?`) over `V`, `M[T = A]` being `Box[V = A]`; `OptionT[F = F]` over `T`; `Pair[A = Int64]` over `B`; `Pair`, two unwritten for one, and `Option[T = Int64]`, none unwritten, refused at the provision. Today the slot's parameter is matched by name: `provides Monad[M = Box]` is refused, "the member returns `Box[V = ?A]`, which is not a subtype of the spec's `M[T = ?A]`", and `Option` and `List` fit because their parameter is named `T`. This is H5's reading of a bare sort: its unwritten parameters stay open.
- H5, decided with the user 2026-11-13: a type constructor read as a value is the bare sort, the value `operation t() -> Type = Option` already is today (`t()` equals `Option` and not `Option[T = Int64]`). `TypeValue` at a sort with unwritten parameters is derived as at any sort, with no sub-dictionary for an unwritten parameter, and its value leaves the parameter unwritten: `TypeValue.type_value[T = Option]()` and `tv[X = Option]()` over `tv[X]() -> Type requires TypeValue[T = X] = X` answer `Option`, refused today ("`TypeValue[T = Option[T = ?]]` … no row answers"), and H5 answers `Option`. A dictionary keeps its shape, the provider and one sub-dictionary per written type argument; no slot for a constructor. Revised after review (with the user, 2026-11-13): the dictionary keeps one sub-dictionary per declared parameter in declaration order, the layout `kb/type_value_derive.rs` states and `type_value_of_self` reads by position and counts, and an unwritten parameter's is an open-slot dictionary, `Dictionary(impl: …Unwritten)`, whose `type_value()` leaves the parameter unwritten; so `TypeValue.type_value[T = Pair[A = Int64]]()` is `Pair[A = Int64]` and `TypeValue.type_value[T = Pair[B = Int64]]()` is `Pair[B = Int64]`, which one sub-dictionary per written argument would have made one dictionary. A parameter inference leaves free is one left unwritten (the user: an inferred type and a written one behave the same): `tyOf(none)` over `tyOf[B](x: B) -> Type requires TypeValue[T = B] = B` answers `Option`, as `tv[X = Option]()` does, both refused today. This refines the rule of 2026-11-03 that a type variable free after typing, at which a requirement is owed, is refused at load: written or inferred alike, the requirement is answered where its spec has an answer at an open slot, which `TypeValue` alone has, and refused otherwise — `Additive` at a free or unwritten slot stays refused in both spellings.
- H2, decided with the user 2026-11-13: an operation declares a higher-kinded parameter with the sort's spelling, `lift[F[T]](x: Int64) -> F[T = Int64] requires Monad[M = F]`; the inner name only counts the constructor's parameters (H4 lines them up by order). A call fixes `F` as any type parameter: `lift[F = Option](7)` `some(7)`, `lift[List](7)` `[7]`, `let o: Option[T = Int64] = lift(7)` `some(7)`, `let b: Box[V = Int64] = lift(7)` `box(v: 7)`. Today `[F[T]]` in an operation's bracket is a syntax error.
- G1, decided with the user 2026-11-13: a parameter of a higher-kinded parameter is a row by use, as an operation's row parameter is (`map[Dst, EffP](…, f: … @ {EffP, …})`): `E` of `GradedMonad[M[E, T]]` is a row because the spec writes rows there (`M[E = {}, T = A]`, `M[E = R, T = A]` with `R` in `@ R`); a provider's constructor, lined up by order (H4), agrees in kind (`Eff`'s `effects E = ?`), and a mismatch is refused at the provision; a parameter used nowhere as a row is a type. No new syntax.
- A group-three row, decided with the user 2026-11-13: left out for now. A value of `M[Int64]` at an `M` no type in scope fixes, carried with its dictionary, would be spelled as a tuple carrying both, `(m: Monad, v: m.M[Int64])`, since under §1.2 `x: Monad` is the dictionary and not such a value; and a tuple type whose component reads an earlier one is refused today outside a parameter list (`dbl(p: (x: Additive, a: x.T))`: "unresolved type name 'x.T'"). Whatever its spelling, at run time it is the pair of a dictionary and a value, the pair T9's elements already are, so leaving it out changes nothing in what a dictionary is.
