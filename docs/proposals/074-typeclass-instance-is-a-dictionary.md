# Proposal 074: A typeclass instance is a dictionary, and is written as one

## Status: Draft (2026-11-13); §1 to §4 decided, §5 (stages) to write. Decided with the user on 2026-11-13, in the order below: a written form has one reading (§1.1); a spec may have several carriers, so a value typed at a spec is no value of a carrier, and KSSA4's rule stands (§1.2); a user is not made to write a type parameter that the call's types fix (§1.3); type parameters are unrolled at compile time, and dictionaries are passed at run time (§1.4); the target programs every choice must run; a dictionary holds no types, for now (§3); a dictionary is written `Dictionary.instance[Additive[T = Int64]]()`, and a parameter that takes one is typed at the spec, `x: Additive` (§2); a spec with operations and no parameter has a table, refused where two are in scope; the member spelling in a function type is the operation's type parameter, as everywhere in its signature, and a function value applied at several instances takes a dictionary parameter for each (§4; "one instance per arrow", decided first, was withdrawn the same day after review); a constant may hold a dictionary (§2, T12). `Dictionary.instance` names a provider by the spec's short name (§2, T11). The target set confirmed (T1–T9, T11, T12), T2 and T3 restated with §4. §5 to be written. A gap T11 needs, not a decision: a named instance's type arguments fix its parameters.

## Extends: [073](073-abstract-values-are-instances.md) §2 (a value typed at a spec over a parameter is an instance at the carrier its type fixes; its spelling at a call is replaced by §2 here) and §6.2 (no type is stored with a value).

## Relates to: kernel-language §4.4 (a quantified type is inferred, never written; §4 keeps it so), §5.4 (the member spelling `Spec.Member`: one instance per signature), §8.2 (a spec over a parameter), §8.7 (which provider a call gets); WI-20261005-KSSA4 (the user's decision of 2026-10-05: `w: Tagger` is not `w: Tagger.C`); WI-817 (one closure applied at several types; its witness is T2, §4's dictionary-parameter program); `stdlib/anthill/realization/runtime.anthill` (`Dictionary[S]`: "S … tracked statically by the typer, never read off the value").

## The problem

A spec over a parameter is a typeclass: `Additive` is a set of operations over a type `T`. A parameter typed at it, `x: Additive`, holds an instance of the typeclass: the table of `Additive`'s operations at one `T`, with `x.T` naming that type.

```anthill
operation add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b
operation ints() -> Int64 = add2(Additive[T = Int64], 2, 3)    -- 5
operation asType() -> Type = Additive[T = Int64]               -- the type
```

Since 073 part 2 the same text, `Additive[T = Int64]`, means the type where a `Type` is expected and the table where `Additive` is expected. That is a second reading of one written form, and §1.1 rules it out. The table needs a spelling of its own, and with it come two questions: what a table value holds, and how a function value that is applied at several types receives its tables.

## Target programs

Every choice in §2 to §4 must run these, with the answers given; an option that cannot is excluded. "Today" is measured on the tree of 2026-11-13. The group is §1.4's. A dictionary written `‹Additive at Int64›` is spelled as §2 decides.

| | program | answer | group | today |
|---|---|---|---|---|
| T1 | `add3(x: Additive.T, y: Additive.T) -> Additive.T = x + y` at `(1, 2)`, `(3.0, 4.3)` | 3, 7.3 | 1 | runs |
| T2 | `applyBoth(f: (d: Additive, x: d.T, y: d.T) -> d.T)` calling `f(‹Additive at Int64›, 1, 2)`, `f(‹Additive at Float›, 3.0, 4.3)`, given `lambda (d: Additive, x: d.T, y: d.T) -> x + y` | (3, 7.3) | 1 | runs, in the second reading |
| T3 | `sumWith[X](f: (x: X, y: X) -> X, a: X, b: X) -> X = f(a, b)`, given `let f = lambda (x, y) -> x + y`, at `(f, 2, 3)`, `(f, 1.5, 2.5)` | 5, 4.0 | 1 | runs |
| T4 | `applyMap(f: (p: Additive, q: Additive, x: p.T) -> q.T) = f(‹Additive at Int64›, ‹Additive at Float›, 2)`, given `lambda (p: Additive, q: Additive, x: p.T) -> Additive.zero[T = q.T]()` | 0.0 | 1 | runs, in the second reading |
| T5 | `applyMap[T, S](f: (v: T) -> S, x: T) -> S requires Additive[T = T], Additive[T = S] = f(x + x)`, given `lambda (v: Int64) -> if v > 3 then 1.5 else 0.5` and `2` | 1.5 | 2 | runs |
| T6 | `use(a: Convert.X) -> Convert.Y` and `useWith(c: Convert, a: c.X) -> c.Y`, each `= Convert.conv(a)`, at `2` over a provider `Convert[X = Int64, Y = Float]` answering `1.5` | 1.5, 1.5 | 1 | runs (`useWith` in the second reading) |
| T7 | `add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b` at `(‹Additive at Int64›, 2, 3)` | 5 | 1 | runs, in the second reading |
| T8 | polymorphic recursion through a conditional provision, one leg through a lambda (`wi817_polyrec_requirement_test`) | 1, 12, 122 | 2 | runs |
| T9 | `[xs, xs.map(twice)]` at `List[T = Stream[T = Int64, E = {}]]`, `takeN(s, 1)` on each (073 §2) | `[[1], [2]]` | 3 | runs |
| T11 | an instance derived through an isomorphism (below), used through its name: `Additive.add[Additive = ProjAdditive[X = Int64, Y = Meters]](m(v: 2), m(v: 3))` | `m(v: 5)` | 1 | refused: "construction is cyclic: `Additive[T = Meters]` -> `Additive[T = ProjAdditive.X]` -> …" |
| T12 | `const ints: Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()` and `add2(ints, 2, 3)` | 5 | 1 | refused: "const has a non-foldable body" |

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

The declarations load today; every call that reaches `ProjAdditive` is refused, named or not, because nothing fixes `X` where `Additive[T = Meters]` is built, and `Additive[T = X]` at an open `X` reaches `ProjAdditive` again. It needs two things: a named instance's type arguments fix its parameters (`X = Int64` from `ProjAdditive[X = Int64, Y = Meters]`, after which the construction is `Int64`'s `Additive` and `MetersIso` — finite); and §2's `Dictionary.instance` naming a provider, since `ProjAdditive` is a provider and not a spec — decided with the user 2026-11-13: by the key a call's bracket names one with, the spec's short name, `Dictionary.instance[Additive[T = Meters], Additive = ProjAdditive[X = Int64, Y = Meters]]()`; without it, the provider is the one §8.7's order selects. The same instance for one concrete `Y`, written as an ordinary provision (`sort MetersAdd provides Additive[T = Meters]` with `add(a, b) = toM(fromM(a) + fromM(b))`), runs today: `m(v: 2) + m(v: 3)` answers `m(v: 5)`.

Kept refused: `direct(w: Tagger) = Tagger.probe(w)` and `x + a` over `x: Additive` (§1.2), `add3(1, 2.5)` (one instance, §1.3); `applyBoth(f: (x: Additive.T, y: Additive.T) -> Additive.T)` calling `f(1, 2)` ("expected Additive.T, got Int64": the arrow's member is `applyBoth`'s type parameter, §4) and `applyBoth[X](f: (x: X, y: X) -> X)` calling `f(1, 2)` and `f(3.0, 4.3)` (one `X` per call of `applyBoth`).

Left out for now (the user, 2026-11-13; §3): T10 — `tOf(x: Additive) -> Type = x.T` at `‹Additive at Int64›` answering `Int64`, and over a list of `‹Additive at Int64›` and `‹Additive at Float›` answering `[Int64, Float]` (group 3). It stays refused at load, as today: "`T` … the receiver's type leaves it open here, so it is no type value".

## 1. Decided

### 1.1 One written form, one reading

A form means one thing wherever it is written; a second reading is admitted only in a rare case argued on its own. `Additive[T = Int64]` written as a value is the type `Additive[T = Int64]`.

### 1.2 A spec may have several carriers

`x: Spec` cannot mean "a value of the spec's carrier", because a spec may have more than one:

```anthill
sort Convert
  sort X = ?
  sort Y = ?
  operation conv(a: X) -> Y
end
```

A value is typed at a carrier by naming it — the member spelling, or a type parameter under `requires` — and a value typed at the spec is the table, covering all its parameters:

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

## 2. How a dictionary is written (decided)

Where a dictionary is passed explicitly — two independent instances in one function type, which the member spelling cannot say (§1.3 gives one instance per signature):

```anthill
operation applyMap(f: (p: Additive, q: Additive, x: p.T) -> q.T) -> Float =
  f(Additive[T = Int64], Additive[T = Float], 2)                  -- today: the second reading
operation go() -> Float =
  applyMap(lambda (p: Additive, q: Additive, x: p.T) -> Additive.zero[T = q.T]())   -- 0.0
```

**Which sorts have a table.** Not "a sort with operations" — an enum has operations — but the classes the language already tells apart:

| sort | example | `Dictionary.instance[…]()` |
|---|---|---|
| with constructors — an entity, an enum, with or without operations | `Box`, `E` with `operation flip(e: E) -> E` | refused: its operations are its own members, called on its values; its tables are those of the specs it provides, `Dictionary.instance[PartialEq[T = E]]()` |
| a spec over a parameter | `Additive[T = Int64]`, `Convert[X = Int64, Y = Float]`, an operation-less `Marker[T = Int64]` a provision binds | the table (the marker's empty) |
| its own carrier — no constructors, receives on itself | `Stream`, `Mergeable` | refused: a value of it is a value with its table (073 §2) |
| no parameter, no constructors, operations that receive on nothing (decided with the user 2026-11-13) | `sort Ticker { operation now() -> String effects Time.Clock }` | the table, chosen as any table at one type is: the one provider, a default provision, or a named one where several answer |
| no parameter, no operations | `anthill.cli.Main` | none: a marker; `requires Main` asks for nothing |

For the fourth row, `c: Ticker` is an instance of `Ticker` — its table — as `x: Additive` is, and its operations carry effects as any operation does (decided with the user 2026-11-13): the dictionary chooses the implementation, and the effect, `Time.Clock` here, says what it does, handled by its handler as anywhere (`anthill run` binds `Clock` to the host's time; a test installs a frozen clock). Measured today (the program written with an effect-free `now() -> Int64`): `use(c: Ticker) = 1` takes a `SysTicker` value (`use(sc())` answers 1), and that is refused under this reading, the call being `use(Dictionary.instance[Ticker]())`; `go() = Ticker.now()` is refused ("no provider can be selected here"); and `use() requires Ticker = Ticker.now()` loads and dies at run time, `OperationBodyMissing("Ticker.now")`, which this reading repairs — the caller passes the table. With two `Ticker`s in scope — two parameters, or a parameter and a clause — a call of `Ticker.now()` names neither, and is refused at load (decided with the user 2026-11-13): `stamps(a: Ticker, b: Ticker) = (Ticker.now(), …)` is refused, where `Additive`'s two are told apart by their types (`Additive.zero[T = b.T]()`). No spelling names a dictionary by a value (`c.now()` stays refused, as `x.zero()` is, and a call's bracket takes a sort, not a value). The fifth row is the boundary: were operation-less sorts given a table, `requires anthill.cli.Main` would demand a provider no program writes.

**A provider named.** `Dictionary.instance[Additive[T = Meters], Additive = ProjAdditive[X = Int64, Y = Meters]]()` — the key a call's bracket names a provider with (`Additive.add[Additive = …](…)`); without it, §8.7's order selects (decided with the user 2026-11-13; T11).

**A constant may hold a dictionary** (decided with the user 2026-11-13; T12): `const ints: Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()`. The dictionary is built at load at known types (group one) and is pure, and a constant is a value computed once. Refused today, "const has a non-foldable body".

**The type — decided with the user 2026-11-13: (T1).** A parameter that takes a dictionary is typed at the spec, `x: Additive`, as today, and `x.T` names its member. To add no rule relating two spellings of one type, the built-in is declared `operation instance() -> S` in `sort Dictionary`, so `Dictionary.instance[Additive[T = Int64]]()` is typed `Additive[T = Int64]`: to pass or take a dictionary, user code names `Dictionary` only as the operation's sort and need not write it as a type. The candidates:

- (T1) keep `p: Additive` — the spec's name as the type of its tables (today);
- (T2) `p: Dictionary[S = Additive]` — the type names the kind of value, its member read through `S` (`x.S.T`), every signature with a dictionary parameter rewritten.

**The value — decided with the user 2026-11-13.** What is passed today as `Additive[T = Int64]` is written `Dictionary.instance[Additive[T = Int64]]()`: a member of `anthill.realization.runtime.Dictionary`, its bracket the spec application — a type, its one reading — and its result the dictionary, typed `Additive[T = Int64]` (the type half, below), built at load at a known type, the clause's own at a rigid one (`Dictionary.instance[Additive[T = X]]()` under `requires Additive[T = X]`). Its bracket holds a spec over a parameter with every parameter written, or rigid under a clause. Refused at load: a sort with values of its own — an entity's or an enum's type, `Dictionary.instance[Box[V = Int64]]()`, `Dictionary.instance[E]()`, has no table, and the result declared `S` would claim a `Box` or an `E` (the tables such a sort has are those of the specs it provides, written at the spec: `Dictionary.instance[PartialEq[T = E]]()`); a spec that is its own carrier — a value typed `Stream` is a stream with its dictionary (073 §2), not a table; an application leaving a parameter unwritten; and one no provision answers (`Additive[T = Bool]`). For now a built-in, as `type_value` is. Its definition in the language, `instance[S]() -> S requires x: S = x`, waits on two gaps, both measured refused today: a named requirement read as a value (`requires d: Additive[T = Int64] = d`: "`d` is read as a VALUE and nothing in scope requires `TypeValue[T = d]`"), and a `requires` over a type parameter standing for a spec ("type parameter `S` collides with the head of its own `requires S…` goal"). The candidates it was chosen among:

- (V1) a member every spec has, read at the bracket, as `type_value` is: `Additive.instance[T = Int64]()`;
- (V2) an operation from a type to its dictionary, evaluated at load: `dictionary(Additive[T = Int64])`;
- (V3) only the member spelling — no explicit dictionary at all — and two instances in one function type written by type parameters (§4's question). Excluded by T2, T4 and T7: §4 keeps the member spelling the operation's, so a function value applied at several instances takes them as dictionaries.

A dictionary under a clause, `requires Additive[T = X]`, is the clause's own in every option: `Additive.instance[T = X]()` under (V1).

## 3. What a dictionary value holds (decided 2026-11-13: D1, for now)

Decided with the user: T10 is left out for now, so a dictionary holds no types (D1). `x.T` is a type only, and a read of it as a value is refused at load. (D2) or (D3) is taken up again if a target program needs a type at run time.

Today: `Dictionary(sub0 .. subN, impl: S)` — the provider sort and its sub-dictionaries. Its types are static only: one provider may provide several specs, so the witnessed spec is not recoverable from the value, and 073 §6.2 decided that no type is stored with a value.

Measured: `x.T` used as a type needs no type in the value — T7's `a + b` is checked against `x.T` at load and dispatched through the provider the dictionary holds — while `x.T` read as a value is refused at load (T10). So the question is T10's: whether a type member of a dictionary is readable as a value. (D1) excludes T10; (D2) and (D3) admit it.

In group one (§1.4) the compiler knows every type, and nothing needs them in the value. In group two the caller knows them at load and the callee does not: a callee that reads its type parameter as a value asks for it as a requirement of its own (`TypeValue[T = T]`), passed beside the dictionary. In group three a reader that needs `x.T` at run time has nowhere to read it. The options (the user's):

- (D1) as today: a dictionary holds no types; a reader that needs one is refused at load;
- (D2) `Dictionary` gains a slot for its types;
- (D3) a new entity, represented by a symbol or by a dictionary with a types slot.

To measure before choosing, on the tree: which run-time readers ask a dictionary for its types — printing, equality of two dictionaries, storing one in a fact, `x.T` read as a value — and which of them are reached in group three.

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

To be written once §2 to §4 are decided. §4 is today's rule and needs no stage; §2 replaces 073 part 2's reading of a spec application at a call, and with it the rows of `wi_p0qgf_spec_instance_values_test` and `wi_p0qgf_lambda_instance_test` that write one.
