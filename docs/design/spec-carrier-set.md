# The sort carrier and the operation carrier

## Status: design, measured 2026-11-22 on `1a58f1e48` (code `88e83f4ae`); §6's decisions taken with the user the same day. Reviewed the same day from another session: a8 moved from §3 A to §3 B (it was a first match, not a selection), decision 1 reopened on that account and then decided with the user (the carrier belongs to the operation, §3 D), decision 3 and §5's scope corrected, decision 5 added and decided (the reflect relation's carrier is the substituted sort) (History, at the end). Second review the same day: decision 1's rule restated, so it no longer refuses d8, which runs today; the vocabulary of sort carrier and operation carrier taken from the user. §5.4's wording approved by the user the same day. Decision 4 measured and decided the same day (the sort carrier is all the type-vars, `Self` being the spec at all of them). Third review the same day: a call that names its provider (d11–d13), and an amendment to §5.4's wording, approved by the user. Decision 6 decided the same day, reopened by a fourth review, and decided again: every binding counts (rule 1). A fifth review the same day found two cases decision 5's correction left open. §1's table was then reworked with the user from `Self`'s definition, decision 5 confirmed against it, and decisions 7 (refused at load) and 8 (a spec with both shapes is self-representing) follow from it. No decision is open. That review also had decision 5 corrected with the user: for a self-representing spec the carrier is the provider at its own type-vars (`List[T = T]`). Scope decided the same day: JE2MT is stage 1, and stage 2 is WI-20261122-CXR5B (§5). For WI-20261121-JE2MT.

The MODEL is the type system's own, so this corrects the implementation to it. Proposal 074
§1.2 (decided): "a spec may have several carriers … a value typed at the spec is the
dictionary, covering all its parameters". [`path-dependent-types.md`](path-dependent-types.md)
§5.4 (decided 2026-06-13): a sort's type-vars identify what a provision of it provides, and what is not
part of it is an operation's type parameter (§1.1 below). The implementation never followed
either. It computes ONE parameter per spec, by an inference `kernel-language.md` §5.1 itself
calls "the rule as implemented", and about 120 sites read that one parameter. JE2MT found two
of the ways it is computed disagreeing.

Some CONSEQUENCES of the correction move verdicts a program sees: what decision 1 admits,
what decision 3 refuses, b5's first match, and the shape of a reflect relation (decision 5).
Each is listed in §6 and decided with the user; none is taken silently.

This document says where a provision is and what a call fixes, measures where the single
parameter answers wrongly, and lays out the correction. (The file keeps its first name,
`spec-carrier-set`, so that the links to it stay valid.)

The probes and the script that reruns them are in [`spec-carrier-set/`](spec-carrier-set/).
The full list of readers is [`spec-carrier-set/readers.md`](spec-carrier-set/readers.md).

## 1. The model (with the user, 2026-11-22)

**Vocabulary (the user, 2026-11-22).** Every reuse of a word says which definition it
means. The terms:

- **Substituted sort**: a sort with type substitutions, its type-vars bound, such as
  `Eq[T = Set]` (a spec's) or `List[T = T]` (a provider's). It is not called an "instance"
  in that meaning, because an instance can be read as an element of a sort.
- **Sort carrier**: ALL the type-vars of a spec (decision 4). It belongs to the sort, and it
  is what a substituted sort of the spec binds. (The user first put the model as "the
  carrier of a typeclass is a set of type-vars in sort".)
- **A provision's carrier**: the type of the values the provision is for, a substituted
  sort (decision 5). For a spec with a dictionary it is the SPEC with its sort carrier
  substituted (`Eq[T = Set]`). For a self-representing spec it is the PROVIDER at its own
  type-vars (`List[T = T]`).
- **Operation carrier**: the type-vars an operation's signature mentions. It belongs to the
  operation, and it is what a call can fix. (The user, deciding decision 1: "carrier is
  more applicable to operation, not to sort".)

A bare "carrier" in this document is one of the last three by its context. Quotations of
the spec, of proposals and of messages keep their own words. §2 to §4 keep the
implementation's "carrier parameter", the single parameter they measure. (Corrected after
the fifth review: "substituted sort" was defined as the spec's alone, which `List[T = T]`
is not.)

**The sort carrier is ALL the type-vars of the spec, for every spec** (decision 4). It often
has one type-var; not always: `Eq[T]`, `SortDomain[T]`, `TypeValue[T]`, `Monad[M]` have one,
and `Iterable[C, Element, E]`, `VectorSpace[V, F]`, `Convert[X, Y]`, `Stream[T, E]` several.
`Self` is not a further member of it. By §5.2's definition `Self` is the sort at all its own
type-vars (`Cell[V = V]`), one per signature, fixed by the call. A type-var an operation
writes is that `Self`'s projection: in `Cell.get(c: Self) -> V`, `V` is what this cell holds.

**The carrier, from `Self`** (the table reworked with the user, 2026-11-22). In a spec,
`Self` is the spec at all its type-vars (`Holder[C = C, Element = Element]`). Every type-var
an operation writes is `Self`'s projection: `peek(c: C)` is `peek(c: Self.C)`. A provision
`P provides S[…]` says what `Self` denotes for the values the provision is for. That is the
provision's **carrier**. What `Self` denotes depends on the spec's CLASS (074 §2): whether a
value of type `Self` exists.

| | spec with a dictionary | self-representing spec |
|---|---|---|
| **test** (074 §2) | no operation takes a value of type `Self` | some operation takes a value of type `Self` (`splitFirst(s: Self)`, `joinTwo(a: Self, …)`) |
| **a value of type `Self` is** | a dictionary | a value of a provider's sort |
| **the carrier** (what `Self` denotes) | the spec at the provision's bindings: `Set provides Eq[T = Self]` → `Eq[T = Set]` | the provider at its own type-vars: `List provides Stream[T = T, E = {}]` → `List[T = T]` |
| **a type-var `Self.T`** | the provision's binding | read off the provider: `Stream.T` is `List`'s `T`, `E` is `{}` |
| **one provider, two provisions differing in a type-var** | two carriers; admitted, and decision 1 picks per call | one carrier with two readings of `Self.C`; refused at load (decision 7) |
| **provides for itself** | its sort is the head of a binding (decision 6) | always, the provider being the carrier's head; a witness cannot exist |
| **a call with no `Self` value** | decision 1 reads the rest off the provisions at what it fixes | the same; with several providers it is refused until the provider is written (g3): there is no default "any `Stream`" |
| **default rows keyed by** | the carrier: the spec's substituted sort | the carrier: the provider, so different providers never collide (decision 5) |
| **examples** | `Eq`, `Coll`, `Dflt`, `NonEq`, `Convert` | `Stream`, `Src`, `Holder` |

A spec with both shapes is not a third kind. `wi1076`'s `Holder` has `peek(c: C)`, which is
`peek(c: Self.C)`, beside `joinTwo(a: Self, …)`. So it is self-representing, and its `C` is
read off the provider (decision 8). From the table:

- **Two provisions are at the same carrier** where their carriers unify. A binding can be
  an effect row (`Iterable`'s `E`), so the unification is over rows too.
- **A provider provides a spec for itself** where its sort is the head of the carrier (a
  self-representing spec: `List` at `List[T = T]`) or the head of one of the carrier's
  bindings (`Set` at `Eq[T = Set]`). Every binding counts (decision 6). Otherwise it is a
  **witness**. For a self-representing spec, both shapes included, a witness cannot exist.
- **"Add this provision unless one is written"** (the derivations) asks whether a written
  provision is at a carrier that unifies with the one to be added.
- **What a call fixes** is a question about its OPERATION. The **operation carrier** is
  the type-vars its signature mentions, directly or inside an application (`m: M[A]`
  mentions `M`). The call's arguments fix those in its parameters, the type expected at
  the call fixes those in its result, and a bracket or a `requires` fixes any type-var of
  the spec. What the call leaves unfixed is read off the provisions at what it fixes
  (decision 1, §6).

A proper subset of the type-vars ("`Element` is decided by `C`") is NOT in the language.
The implementation neither enforces one nor tells two such provisions apart: it takes the
first one declared (§3 B, b5–b8). Adding a subset would be a language extension. The
correction does not need it.

### 1.1 The same model, read as path-dependent members

[`path-dependent-types.md`](path-dependent-types.md) already has this model in other
words. Read through it, the question "which sort is this provision for" disappears.

- **A spec's type-vars are members.** `d.T` over `d: Additive` (074),
  `C.Elem` over a type receiver (§5.3), `s.provider.K` over a provider's value (§1). The
  β law `F[T = A].T ≡ A` (§5.4) is the reading of a written binding: `W provides
  Eq[T = C]` provides the substituted sort `Eq[T = C]`, whose member `T` is `C`.
- **The type-vars ARE what identifies a provision.** §5.4 (decided 2026-06-13): "`CpsMonad`'s
  only parameter is its type constructor `F[T]`. The element types `A` / `B` are
  per-operation type params … not part of the monad's identity", and the fixtures that
  declared them as sort type-vars were migrated to per-operation ones. So a type-var of
  the sort is part of what identifies a provision of it, and what is not must be an operation's type
  parameter. That is the carrier set of §1.
- **A self-representing spec is the path case.** In §1's example the members are read off
  the PROVIDER's value: `s.provider.K` is `SubscriberStore`'s `K`, which its provision
  binds to `String`. The tests that drive that example today give `DataProvider` a
  self-receiving `pick(p: Self)` (`wi1082_self_return_tie_test`), which puts it in that
  class: a value of `DataProvider` is a value of a provider's sort, and `K` is one of its
  members.
- **So two provisions are at one substituted sort when their members agree**, and nothing needs to
  name one member as "the" carrier. A reader that picks one type-var reads one member of
  the substituted sort and ignores the others. That is what every row of §3 B does.

## 2. What the implementation computes instead

ONE parameter per spec. Five ladders compute it (L1–L5); two more rules read something else
in its place, a set per operation (L6) and a label (L7):

| ladder | rule | where |
|---|---|---|
| L1 | the first declared type-var that some operation takes as a BARE parameter type | `spec_carrier_param`, provision.rs:133 |
| L2 | L1, else the sole type-var if the spec is not self-representing | `spec_carrier_param_or_sole`, provision.rs:187 |
| L3 | for a spec with a dictionary: L1, else the FIRST type-var | `spec_over_parameter`, provision.rs:243 |
| L4 | L1, else the first type-var, with no class gate | `clause_carrier_param`, carrier.rs:2594 |
| L5 | L1, else the sole type-var, with no self-representing gate | inline in `check_rule_sort_uses`, provision.rs:812 |
| L6 | any type-var any parameter of the operation is typed at (a SET); the spec itself if self-representing | `op_has_spec_carrier_param`, value_type.rs:1301 |
| L7 | `Effect`'s `T` binding, by label | `registered_effect_kinds`, signature.rs:5877 |

L1 is under the witness criterion (`witness_dispatch_carrier_value`, coherence.rs:2888), so
dispatch, the coherence groups, the member checks and the derivations of `SortDomain` and
`TypeValue` read it. L2 is under `provisions_about`, the equality derivation (since
TV0PA), the goal keys, and the default rows. [readers.md](spec-carrier-set/readers.md) lists
114 call sites: 106 read L1–L3 and their wrappers, and 8 read L6
(`op_has_spec_carrier_param`). Two further wrappers have 9 callers.

L1 and L2 disagree only on a spec with exactly one type-var that is not self-representing
and that no operation takes as a bare parameter type. In the standard library that is
`Eq`, `NonEq`, `Effect`, `Modifiable`, `SortDomain`, `Fillable`, `TypeValue`, `Monad`,
`DelayMonad` and others (the doc of `spec_carrier_param_or_sole` counts fourteen).

L1 is also wrong on its own terms: `declared_type_param_vid` (carrier.rs:380) pins arity 0,
so `Monad.flatMap(m: M[A], …)` does not count as taking `M`, and `Monad` lands on L2 for
the wrong reason.

## 3. Measured

`spec-carrier-set/run.sh` reruns every row. "Answers" is what the program prints.

### A. A call already selects by all the bindings

| probe | program | answers |
|---|---|---|
| a1 | `Dflt[T]` with `dflt() -> T` (no operation takes `T`); `W1 provides Dflt[T = Int64]`; `Dflt.dflt[T = Int64]()` | 1 |
| a2 | the same with two witnesses, called `Dflt.dflt[Dflt = W1]()` | 1 |
| a3 | the two witnesses, the call naming neither | refused at the call, "they may coexist, so say which: write `[Dflt = …W1]`" |
| a4 | `Dflt2[A, B]`, `dflt() -> A`, one witness at `[A = Int64, B = String]` | 1 |
| a5 | two witnesses at `A = Int64` that differ only in `B`; the call binds `B = Bool` | 2 |
| a6 | `Rel[A, B]`, `relate(a: A, b: B)`; two witnesses that differ in `A`; `Rel.relate(red, 5)` | 2 |
| a7 | the same, the witnesses differing in `B`; `Rel.relate(5, red)` | 2 |

Every one is right, and none depends on which single parameter is "the carrier". In each,
what tells the provisions apart is a bracket (a2, a5) or an argument (a6, a7); a5–a7 pick the
SECOND-declared witness, so they are not first matches. Where only the expected result type
could tell them apart, the selection is not by bindings at all: b5–b8 below.

### B. Where the single parameter answers wrongly

**b1: a written `SortDomain` is not seen by its derivation (L1).**

```anthill
sort Colour
  entity red
  entity green
end
sort W
  provides SortDomain[T = Colour]
  rule fill(?x) :- ?x = red
end
sort Q
  requires SortDomain[T = Colour]     -- something asks, so the loader derives rows
end
```

| question | answer |
|---|---|
| `SortProvidesInfo` rows of `SortDomain` | `W` at `T: Colour`, **and** `Colour` at `T: Colour` (derived) |
| `anthill.reflect.typing.provision_carrier` (L2) | `W`'s row is at `Colour` |

`sort_domain_derive`'s `already` set reads L1 (`provision_carriers_of_spec`), finds no
carrier parameter, files `W`'s row under `W`, concludes that nothing provides `SortDomain`
at `Colour`, and derives a second one. The reflect relation reads L2 and says `W`'s row is
at `Colour`. One program, two answers about the same row. A sort's own provision
(`provides SortDomain[T = Self]`) is seen, and nothing is derived for it. TV0PA measured
the same defect for `Eq`: the derived structural equality answered, `W.eq` was never
called. TV0PA fixed it by moving that one reader to L2.

**b2: the `TypeValue` refusal is right only by accident.** `sort W { provides
TypeValue[T = C] }` is refused: "'…W' writes `provides …TypeValue[…]`, but every
`TypeValue` instance is DERIVED and none may be written". The sentence is about who WROTE
the provision, so the right reader is the provider (`providers_of_spec`). It reads L1 and
gets `W` only because L1 misfiles the witness. With the witness criterion switched to L2
(experiment, reverted), the message named `C`, who wrote nothing.

**b3/b4: the carrier moves when two lines are swapped.**

```anthill
sort Bag2
  sort T = ?          -- b4: these two lines swapped
  sort C = ?
  operation put(c: C, x: T) -> C
end
sort MyBag
  entity bag
  provides Bag2[T = Int64, C = Self]
  operation put(c: MyBag, x: Int64) -> MyBag = c
end
```

| | `provision_carrier(MyBag, Bag2, ?c)` | so `MyBag` is |
|---|---|---|
| b3, `T` declared first | `Int64` | a witness for `Int64` |
| b4, `C` declared first | `MyBag` | its own provider |

`put` takes values of both type-vars, so L1 takes the first one declared.

**b5–b8: two provisions that differ in a type-var no argument fixes are a first match.**

```anthill
sort Coll
  sort C = ?
  sort Elem = ?
  operation first(c: C) -> Elem
end
sort W1
  provides Coll[C = Foo, Elem = Int64]
  operation first(c: Foo) -> Int64 = 1
end
sort W2
  provides Coll[C = Foo, Elem = String]
  operation first(c: Foo) -> String = "two"
end
```

| probe | the call | answers |
|---|---|---|
| b5 | `to_string(Coll.first(foo))`: `Int64` expected, `W1` declared first | 1 |
| b6 | the same with `W2` declared first | refused: "expected Int64, got String" |
| b7 | `println(console(), Coll.first(foo))`: `String` expected, `W1` first | refused: "expected String, got Int64" |
| b8 | `let x = Coll.first(foo)`: nothing fixes `Elem` | runs, no ambiguity reported |

The expected type selects nothing: the first-declared witness answers, and a call that
expects the other one is refused as a type mismatch. Where nothing fixes `Elem` (b8), the
call is not refused the way a3 is. L1 makes `C` the carrier, both rows are filed at
`C = Foo`, and the first is taken. This is the one wrong answer driven by a CALL for a spec
with several type-vars; b3/b4 read a reflect row.

**The standard library is read right by declaration order.** A load of the standard library
alone has 585 provision rows. Three bind two or more sorts: `Map provides
Iterable[C = Map[…], Element = Pair[…]]`, the same for `FiniteCollection`, and `Vec3
provides VectorSpace[V = Vec3, F = Float]`. They read as `Map`'s and `Vec3`'s own because
`C` is declared before `Element` and `V` before `F`. `VectorSpace.vec_scale(c: F, v: V)`
takes `F` too, so with `F` declared first `Vec3`'s provision would read as a witness for
`Float`.

### C. Not decided here (recorded so they are not mistaken for one of §3 B)

| probe | program | answers | why it is kept apart |
|---|---|---|---|
| c1 | `sort BoxM { provides Monad[M = Box]; … }` with its own `pure`/`flatMap`/`map`; `Monad.flatMap(box(v: 41), …)` | refused: "no impl matches" | moving L1 to L2 does not fix it (both experiments, reverted). That does NOT show it is independent of the V question: the readers that find the argument at the carrier match a bare type-var (`declared_type_param_vid`'s arity pin), so `m: M[A]` may be missed there too. A stage 2 row; its cause is to be named when stage 2 reaches the V readers |
| c2 | control: `Box` providing `Monad[M = Self]` with the same members | 42 | |
| c3 | two data sorts each `provides Dflt[T = Int64]` | refused, and no bracket is accepted: "each is a CONCRETE provider, where … the VALUE decides" | the bracket rule asks whether the provider has constructors (`is_value_directed_provider`, dispatch.rs:426), not which parameter is the carrier. Known since wi822 (`TieRepair::ValueDirected`) |

c3 is a separate defect. Neither c1 nor c3 is filed.

### D. What a call fixes: the probes behind decision 1

The rule a call is held to is `kernel-language.md` §5.4's last case of "A body-less
operation must have something that can run it" (around line 3542). In plain words: take what
the call fixes; look at the provisions at that; if they agree on everything else, take it from
them; if they disagree, refuse and have the substituted sort written at the call. As written, "what the call
fixes" is the spec's single carrier parameter, fixed by "an argument, bracket, expected
result or requirement in scope". So its own example has `A` as the carrier of
`Conv.tag("km")` when `Conv` declares `conv(a: A, b: B)`, and `B` when it declares only
`tag(b: B)`.

| probe | program | answers |
|---|---|---|
| d1 | `Dflt[T]`, `dflt() -> T`; witnesses at `Int64` and `String`; `to_string(Dflt.dflt())` | 1 |
| d2 | the same; `println(console(), Dflt.dflt())` | two |
| d3 | `Conv[A, B]`, `tag(b: B) -> Int64`; `Meters` and `Feet` at `B = String`; `Conv.tag("km")` | refused: "it leaves `A` open, and `Meters` and `Feet` provide `Conv` at what it fixes, naming different types for it. Write the instance" |
| d4 | the same, `Conv[A = Feet].tag("km")` | 2 |
| d5 | ONE provider writing both of b5's provisions (`first = WB.f1` at `Elem = Int64`, `first = WB.f2` at `Elem = String`) | refused at load four times, among them "conflicting provisions: … the first provision written would silently win" (§8.7) |
| d6 | b6 (`W2` declared first), `Coll[Elem = Int64].first(foo)` | 1 |
| d7 | b6, `Coll.first[Coll = W1](foo)` | refused: "W1 provides Coll, but not at the bindings this call … needs" |
| d8 | b8 with `W2` deleted: ONE provider, `let x = Coll.first(foo)` | runs (`Elem` read off the one provision) |
| d9 | a1 with `let x = Dflt.dflt()`: one witness, nothing expected | refused: "missing `requires Dflt[T = …]`" |
| d10 | d1 with `let x = Dflt.dflt()` then `to_string(x)` | refused: "ambiguous dispatch … the call selects none" |

The expected type already fixes a type-var (d1, d2), and the rule's refusal works (d3, d4).
b5–b8 break the rule even as written: the provisions at `C = Foo` give `Elem` different
types, and the first declared answers. d7 is a defect of its own: naming the witness is
refused against the first match's bindings. It is a stage 2 row.

## 4. The readers, by the question each one has

From [readers.md](spec-carrier-set/readers.md), 114 sites:

| question | sites | under the model |
|---|---|---|
| D: add a provision unless one is written | 4 | is a written provision at a carrier that unifies with the one to be added (decision 5) |
| S: select the provision a goal asks for | 39 | the goal's substituted sort: all its bindings, for a dictionary spec |
| V: which argument fixes the substituted sort | 17 | the operation carrier (decision 1): the type-vars its signature mentions, directly or in an application. L6 reads a set, but of the parameters only and of a bare type-var only |
| P: projection, left-out bindings | 12 | a binding of the carrier set, read by name; "except the carrier" becomes a decision, §6 |
| K: a refusal decided by the parameter | 10 | per refusal (§6 for `ProvisionNamesNoCarrier`) |
| SC: the spec's class | 9 | unchanged: these ask whether the spec has a dictionary, not which parameter |
| X: diagnostic text | 6 | names the substituted sort, or the provider |
| W: witness or own | 5 | the provider is neither the head of the provision's carrier nor the head of one of its bindings (decision 6) |
| O: overlap, defaults, specificity | 5 | provisions whose carriers unify; default rows keyed by carrier, which for a self-representing spec is the provider (decision 5) |
| M: member checks | 4 | the provision's substituted sort; the receiver per operation, as §8.7 already says |
| other | 3 | `EqProviders::of` (load.rs:23438) reads the stage 1 helper; the seal's re-judging (signature.rs:3070) moves with W; the layer test (layer.rs:877) lists `Eq`'s providers and keeps asking that |

The `Eq` family's K and X rows (eq_derive.rs:600, :652, :1348) are stage 1 with D.

## 5. The correction

**One owner.** `sort_carrier(kb, spec) -> SortCarrier`, read off the declaration and
memoized per canonical spec:

```rust
struct SortCarrier {
    /// Every type-var of the spec, in declaration order (decision 4: every spec, both classes).
    type_vars: SmallVec<[Symbol; 2]>,
}
```

Decision 4 left it a list of type-vars and nothing else. Whether a value of type `Self`
exists is the spec's class (`sort_class`, 074 §2), and it stays a question of its own.
(The shape with a `self_sort` flag that this paragraph had until decision 4 was taken is in
the History.)

It replaces L1–L5 as the answer to "where is this provision". Two questions stay apart from
it, under names that say what they answer: the operation carrier (L6, per operation,
extended to the result and to an application of a type-var), and the spec's
class (`sort_class`, 074 §2). Nothing reads "the first" of anything.

**Stage 1: the owner and the derivations.** `sort_carrier` is written first. One helper,
"the written provisions of `S` at a substituted sort that unifies with `t`", is built ON it, not on
L2, so it is not one more reader of the single parameter to migrate later. It replaces
`provisions_about` and `provision_carriers_of_spec` in:

- `eq_derive` (`spoken_for`, `equality_signatures`, `equality_reaching_no_eq`, `written_spec_of`)
- `load.rs` `EqProviders::of`
- `sort_domain_derive`'s `already`
- `type_value_derive`'s `already`. `HandWrittenTypeValue` reads the PROVIDER.

Every spec these read has one type-var, so stage 1 moves ONE verdict: b1. b2 names `W`
before and after stage 1 (the witness criterion does not move in it), so b2 is a GUARD for
stage 2, when the criterion moves, not a stage 1 row.

**Scope, decided with the user 2026-11-22.** JE2MT asks for a row per reader that answers
wrongly for a one-parameter spec, and one owner. It delivers stage 1:
[WI-20261121-JE2MT](../../anthill-todo/open/WI-20261121-JE2MT-two-readings-of-which-sort-a.anthill.md),
whose note of that day says so. Stage 2, the change of about 114 sites on the per-call
path, has its own ticket:
[WI-20261122-CXR5B](../../anthill-todo/open/WI-20261122-CXR5B-the-readers-of-the-single.anthill.md),
which depends on JE2MT.

**Stage 2: everything else**, by question, in the order W, O, S, V, P, M, K, with the two
indexes that are keyed by the single parameter: `ProvidesIndex`'s witness carriers memo
(rule_requirements.rs:3205) and the eq-dispatch index's witness filing
(`provision_supplier`). WI-20261121-DBR8V's (b) is a consequence of the latter. This is
the size of the work, and it touches the per-call path, where speed was measured before
(the provider index removed a scan that was 39 % of a later load).

**Spec text.** These passages describe the single parameter as the rule. Each is
corrected to describe the set, as 074 §1.2 has it:

- §5.1: "One owner decides this for every reader" (around line 1356); "Which parameter is
  the carrier is read off the operations … The rule as implemented …", with the
  sole-parameter sentence (around 1476–1491); `ProvisionNamesNoCarrier` (around 1495);
  "Where a spec genuinely has no carrier parameter, a witness for it cannot exist" (around 1570).
- §5.2: a left-out parameter is `?` "the spec's carrier parameter excepted" (around 2143);
  and `Self` "in a spec it is the spec, and does not become each carrier (a spec's carrier
  parameter is what stands for the carrier)" (around 2135). The parenthesis is the single
  parameter again; `Self` is the spec at all its type-vars (decision 4). The wording is for
  the user's approval.
- §5.4: the last case of "A body-less operation must have something that can run it"
  (around 3542), reworded per decision 1. The wording is approved (§6, decision 1), and it
  lands with stage 2.
- §8.3: "a provision being about the sort it binds to its spec's carrier parameter, or to
  the sole one" (around 6266).
- §8.7: "One carrier declaring one spec twice" (around 7272); the member receiver "the
  first typed by a spec parameter the provision binds to the carrier" (around 7325).
- 058 §3.6 keeps its rule. A note says its "carrier" is the substituted sort.

## 6. Decisions (taken with the user 2026-11-22; after review, 1 reopened and decided, 4 decided, 5 added, decided and corrected, 6 added, decided, reopened and decided again; 7 and 8 from §1's table)

1. **What a call fixes, for every provider. DECIDED 2026-11-22**, after it was reopened. It
   began as "§8.7, one provider declaring one spec twice" (d5, refused at load), decided
   "admit them, as a8's two providers already are". That premise was wrong (a8 is now
   b5–b8, a first match), so the rule that tells two such provisions apart had to be stated
   first. Taken with the user:

   **What a call fixes is decided by the OPERATION CARRIER**: the type-vars the
   operation's signature mentions, its parameters and its result. `first(c: C) -> Elem`
   mentions `C` and `Elem`; `tag(b: B) -> Int64` mentions `B` alone, whatever else `Conv`
   declares. A call fixes what it can of them: the parameters by its arguments, the result
   by the type expected AT THE CALL, and any type-var of the spec by a bracket or a
   `requires` in scope. Whatever the call leaves unfixed, in the operation carrier or not,
   is read off the provisions at what it fixes. The call is refused in two cases only:
   - it fixes no type-var at all and names no provider, even with one provision (d9);
   - the provisions at what it fixes disagree on a type-var it leaves unfixed (b8, d3).

   Then the substituted sort is written at the call. One provider and several are held to
   the same rule, for every spec (decision 4 removed the self-representing exception).

   **Why a call that fixes nothing is refused even with one provision (d9), while one that
   fixes something reads the rest off it (d8).** A call that fixes no type-var is open in
   all of them. The operation it is written in must then require the spec at them, as
   today's message says ("missing `requires Dflt[T = …]`"). Taking the one provision that
   happens to exist would let any later provision change the call. A call that fixes `C`
   reads the rest off the provisions at `C`, as `Iterable.find(xs)` reads `Element` off
   `List`'s. A later load can still add a provision at `C = Foo` that disagrees; that is the
   open-world limit of every such reading, today's included.

   Corrected after the second review: the first statement of this rule refused a call
   whenever a type-var of the operation carrier was fixed by nothing. That would have
   refused d8, which runs today with one provider and must keep running.

   **Two providers at the SAME substituted sort** (a3: `W1` and `W2` both at
   `Dflt[T = Int64]`) are not this rule's case. They agree on every type-var, so there is
   nothing to read off. That is 058's tie, which a bracket naming the provider, or a
   default (decision 5), settles.

   **The expected type is the one at the call.** A type a later use of the call's value
   expects does not reach back: d10 is refused today and stays refused. It is a limit a
   user will meet, and the repair is the bracket.

   | probe | today | decided |
   |---|---|---|
   | b5 | 1 | 1 |
   | b6 | refused, type mismatch | 1 |
   | b7 | refused, type mismatch | two |
   | b8 | runs, first declared | refused; the substituted sort is written at the call (`Coll[Elem = Int64].first(foo)`) |
   | d5 | refused at load | loads; its calls answer as b5–b8 |
   | d7 | refused | 1 |
   | d8: one provider, `let x = Coll.first(foo)` | runs | runs (`Elem` read off the one provision) |
   | d9: one witness, `let x = Dflt.dflt()` | refused, "missing `requires Dflt[T = …]`" | refused (it fixes nothing) |
   | d10: two witnesses, `let x = Dflt.dflt()` then `to_string(x)` | refused, ambiguous | refused (the expected type is at the call) |
   | d1, d2, d3, d4, d6 | 1, two, refused, 2, 1 | unchanged |

   **d5 is refused by three checks today, and all three move for it to load:**
   - "ambiguous dispatch of `Coll.first` on carrier `Foo`: 2 implementations are supplied
     for that carrier". This is the supplier tie, keyed by the single carrier parameter.
   - "ambiguous instance: 2 distinct instance facts provide `Coll` for carrier `WB`". This
     is the coherence grouping, keyed by the PROVIDER.
   - "conflicting provisions: `WB` declares `Coll` twice", twice: once binding `first` and
     once binding `Elem`. This is §8.7's "one carrier declaring one spec twice".

   Declaration order decides nothing, and a call's verdict does not depend on which other
   operations the spec declares. Option (b) of the reopening (refuse such pairs at load) was
   not taken: it would refuse d3's program, whose repair d4 runs today and is the one §5.4
   itself prints.

   For a SELF-REPRESENTING spec, one provider's two provisions that differ in a type-var are
   one carrier with two readings of `Self.C`, so they are refused at load (decision 7, from
   §1's table). That is §8.7's rule, kept for that class. This paragraph kept it first;
   decision 4 removed it on a premise that decision 5's correction reversed, and decision 7
   restores it.

   **A call that names its provider** (found by the third review, measured on `409250372`).
   A bracket naming the provider selects provisions without fixing any type-var:

   | probe | program | today |
   |---|---|---|
   | d11 | one witness `W1` at `Dflt[T = Int64]`; `let x = Dflt.dflt[Dflt = W1]()`, nothing expected | refused at load: "… `Dflt.dflt.dispatch`: expected matching impl for per-call bindings, got no impl matches — unresolved: `Dflt` (the call selected `W1` …" |
   | d12 | a spec with NO type-vars, `sort Greeter { operation greet() -> Int64 }`, and `W1 provides Greeter` with `greet() = 7`; `to_string(Greeter.greet[Greeter = W1]())` | LOADS, then fails at run: "operation has no body: `Greeter.greet` — nothing this runtime can run is registered for it" |
   | d13 | d12 without the bracket | refused at load: "no provider can be selected here …" |

   d11 should answer 1: the provider is named, and `T` is read off its one provision. d12
   loads clean and fails when it runs, which is exactly what §5.4 exists to refuse. It is
   a defect of today, independent of the single parameter, and it is a stage 2 row.

   **Amendment, approved by the user 2026-11-22**, and merged into the wording below. A
   bracket naming a provider fixes that provider's provisions. The first refusal reads "and
   names no provider". With it the decision also says "`Self` mentions them all", which
   writes decision 4 into the rule. So d11 answers 1, and d12 answers 7, where today it
   loads and then fails at run.

   **Wording for §5.4, approved by the user 2026-11-22, with its amendment.** It goes into `kernel-language.md`
   with the stage that implements decision 1 (stage 2), so that the spec never describes
   behaviour the implementation does not have yet. It replaces the case's first part, up to
   "the call's receiver"; the paragraph after it ("A rule written in a sort that requires
   `S` …", with `Sat` and `Two2`) stays as it is:

   > - At the call, in an operation body or a rule body, of a body-less member `op` of a
   >   spec `S` whose substituted sort the call does not fix. The **operation carrier** of
   >   `op` is the type-vars of `S` its signature mentions, in a parameter or in the result,
   >   directly or inside an application (`m: M[A]`); `Self` mentions them all. The call
   >   fixes what it can of them: a parameter's by the argument, the result's by the type
   >   expected at the call itself (not one a later use of its value expects), and any
   >   type-var of `S` by a bracket or a `requires` in scope. Whatever the call leaves unfixed, in the operation carrier or
   >   not, is read off the provisions at what it fixes, as `Iterable.find(xs)` reads
   >   `Element` off `List`'s and `let x = Coll.first(foo)` reads `Elem` off the one
   >   provision at `C = Foo`. A bracket naming a provider (`Dflt.dflt[Dflt = W1]()`) fixes
   >   that provider's provisions, and what the call leaves unfixed is read off them. A spec
   >   with no type-vars (`Greeter.greet()`) is fixed only that way, or by a `requires`.
   >   Whether one provider or several provide `S`, the call is refused when:
   >   - it fixes no type-var of `S` at all and names no provider: `let x = Dflt.dflt()`,
   >     with nothing expected, even where one provision exists;
   >   - the provisions at what it fixes give a type-var it leaves unfixed different types:
   >     `Conv.tag("km")` over `Meters` and `Feet` at `B = String`, whether or not `Conv`
   >     declares `conv`; `let x = Coll.first(foo)` over provisions at `C = Foo` that
   >     disagree on `Elem`.
   >
   >   The substituted sort is then written at the call: a bracket (`Conv[A = Meters].tag("km")`,
   >   `Coll[Elem = Int64].first(foo)`) or a `requires` on the operation; in a rule body, on
   >   the call's receiver. Two providers at the same substituted sort are not this case: a
   >   bracket naming the provider, or a default, chooses between them (§8.7).
2. **A written provision that overlaps the one a derivation would add without covering
   it** (`Eq[T = Box[T = Int64]]` against the derived `Eq[T = Box[T = T]]`). Today `Box`
   gets no derived equality at all. Decided: keep that (any overlap skips). §8.3's "Closed
   by the load" assumes it.
3. **A left-out type-var** (§5.2, `ProvisionNamesNoCarrier`). Today a left-out binding is
   `?`, except the carrier parameter, which a written provision must bind
   (`LiveLlm provides Llm[E = {External}]` is refused). Under the model every left-out
   type-var is `?`. Decided: keep the refusal, restated as "a provision binds each type-var
   an operation of the spec takes a value of". It is per operation. Corrected after
   review: it refuses MORE than today. Today the refusal itself depends on declaration
   order: over `Bag2 { put(c: C, x: T) }`, `provides Bag2[C = Self]` is refused as naming
   no carrier with `T` declared first, and passes that check with `C` first (where, in the
   probe, the member check refuses it for `put`'s narrower `x`). Restated, it is refused
   in both orders. "Takes a value of" means the PARAMETERS, on purpose: a type-var only an
   operation's result mentions may be left out (`?`), and the member check then judges
   whether the member returns every type there. The standard library is unaffected: every provision of
   `PersistentCollection`, `MutableCollection` and `VectorSpace` binds both type-vars. The
   test fixtures are not measured.
4. **The sort carrier is all the type-vars, for every spec. DECIDED 2026-11-22**, after
   measuring. The question was whether a spec where one operation takes `Self` and another
   a type-var (`spec_carrier_param`'s doc: "a spec declaring BOTH a carrier parameter and
   a self-receiving operation") has `Self`, or `Self` and its type-vars, as its sort
   carrier.

   The user resolved it from `Self`'s definition, `kernel-language.md` §5.2: "**`Self` — the
   sort a declaration is written in, at its own parameters** … in `sort Cell` with
   `sort V = ?` it is `Cell[V = V]` … every `Self` of one signature is one instance — the
   one the call fixes". So `Self` already is all the type-vars, and it is not a member of
   the sort carrier beside them. A type-var an operation writes is that `Self`'s projection
   (`Cell.get(c: Self) -> V`: "returns what this cell holds"). So "an operation that takes
   `Self`" and "an operation that takes a type-var" are not two kinds: both are about the
   one `Self` the call fixes.

   What remains different between specs is their class: whether a value of type `Self`
   exists (§1).

   **Census** (a temporary unit test over the standard library, run on `409250372` and
   removed): 146 self-representing sorts, of which 9 also have a type-var an operation takes:
   `List`, `Cell`, `MappedStream`, `FilteredStream`, `Function`, `Map`, `MutableStack`,
   `Set`, `SortedSet`. All 9 are data sorts that nothing provides (zero provisions), so this
   decision moves nothing in the standard library. The test fixtures were not censused. The
   one behind the doc's note is `wi1076_self_representing_spec_carrier_test`'s `Holder`.

   **Probes** over that `Holder` (`sort C`, `sort Element`, `peek(c: C) -> Int64`,
   `joinTwo(a: Self, b: Self) -> Int64`):

   | probe | program | today | decided |
   |---|---|---|---|
   | e1 | `BoxHolder` (no constructors) at `C = Box`; `Holder.peek(box(n: 5))` | 2; filed at `Box` | 2 |
   | e2 | witnesses at `C = Box` (2) and `C = Crate` (7) | 9 | 9 |
   | e3 | ONE provider (no constructors) writing both provisions | refused at load, "ambiguous instance … for carrier `TwoHolder`" | refused at load, as today: one carrier, two readings of `C` (decision 7) |
   | e4 | `Bag` with constructors at `C = Box`; `joinTwo(bag, bag) * 10 + peek(box)` (`joinTwo`'s second parameter takes any provider, `b: Holder`, per §8.7) | 32; but filed at `Box`, so `Bag` counts as a witness although `joinTwo` dispatches on its values | 32; `Bag` provides `Holder` for itself (§1) |
   | e5 | `Bag` at `C = Box` and at `C = Crate` | refused at load, three times | refused at load, as today: one carrier, two readings of `C` (decision 7) |

   Two of e5's three refusals today are a separate defect. A `joinTwo` bound by name
   (`joinTwo = Bag.join`) has its receiver `a: Bag` refused as incompatible with
   `Holder[C = Box, …]`, while the same receiver written as a member passes (e4). It is a
   stage 2 row.

   Consequences, each written where it applies:
   - §1's table is now about the class, not the carrier.
   - Decision 1's self-representing exception is removed.
   - Decision 5's `?c` for `Stream` was first rewritten to `Stream[T = T, E = {}]` here. The
     fourth review showed that this collides, and the user corrected it to `List[T = T]`, the
     provider at its own type-vars (decision 5).
   - "Provides for itself" holds for a self-representing spec's provider, because it is the
     head of the carrier (decision 5). Otherwise the stdlib's `Stream` provisions would lose
     their inferred default rows, the loss WI-1076 once measured.
   - `SortCarrier` holds type-vars only.
   - §5.2's "a spec's carrier parameter is what stands for the carrier" joins the spec text
     to correct.
5. **The reflect relation's `?c` is the provision's carrier. DECIDED 2026-11-22, and
   confirmed with the user the same day against §1's table** (added
   after review). `anthill.reflect.typing.provision_carrier(?p, ?s, ?c)`, "sort P provides
   spec S at dispatch carrier C", answers ONE sort per provision. b1, b3 and b4 are
   measured through it. It is the join under 058 §3.6's two rules, `self_provides(C, S)`
   and `default_provider(S, C, W)`, which the loader materializes (`kb/defaults.rs`, an
   index bucketed by that one sort, and the `one_default` load check). With two type-vars,
   one sort cannot say where a provision is, and the answer moves with declaration order
   (measured on `bc5f30f1e`):

   | | `provision_carrier` | `self_provides` | `default_provider` |
   |---|---|---|---|
   | b3, `T` declared first | `MyBag, Bag2, Int64` | none | none |
   | b4, `C` declared first | `MyBag, Bag2, MyBag` | `MyBag, Bag2` | `Bag2, MyBag, MyBag` |

   So whether `MyBag`'s own provision is its default depends on which of two lines comes
   first. Decided, of three shapes (one row per type-var; the substituted sort; one sort
   for one type-var and the substituted sort for several): **`?c` is a substituted sort**,
   one compound carrier, a type like any other, with the operation bindings
   (`pure = optionPure`, `eq = cEq`) left out.

   **Which substituted sort: the type of the values the provision is for** (corrected with
   the user after the fourth review). The spec's class picks it:
   - For a spec with a dictionary, the values are dictionaries, so `?c` is the SPEC at all
     its type-vars. It is not new data: the provision fact's `spec` field already holds it
     (`SortView(Bag2, T: Int64, C: MyBag)`), and today the relation throws it away to answer
     one sort.
   - For a self-representing spec, the values are the provider's, so `?c` is the PROVIDER at
     its own type-vars, its `Self` (`List[T = T]`). The spec's type-vars are read off it.

   | provision | `?c` today | `?c` decided |
   |---|---|---|
   | `sort Set provides Eq[T = Self]` | `Set` | `Eq[T = Set]` |
   | `sort W provides SortDomain[T = Colour]` | `Colour` | `SortDomain[T = Colour]` |
   | `MyBag provides Bag2[T = Int64, C = Self]` | `Int64` or `MyBag`, by order | `Bag2[T = Int64, C = MyBag]` in both orders |
   | `W1`/`W2` over `Coll` (b5) | `Foo`, `Foo` | `Coll[C = Foo, Elem = Int64]`, `Coll[C = Foo, Elem = String]` |
   | `Option provides Monad[M = Self, pure = optionPure, …]` | `Option` | `Monad[M = Option]` |
   | `List provides Stream[T = T, E = {}]` (self-representing) | `List` | `List[T = T]` |
   | `FiniteStream provides Stream[T, E]` (self-representing) | `FiniteStream` | `FiniteStream[T = T, E = E]` |
   | `Bag provides Holder[C = Box]` (e4; self-representing, has values) | `Box` | `Bag` |
   | `BoxHolder provides Holder[C = Box]` (e1; self-representing, no constructors) | `Box` | `BoxHolder` |

   **Why not the spec for `Stream` too** (the fourth review's finding 1, worked through with
   the user; probes g1–g4). The loader writes inferred default rows by itself: rule (2) of
   `default_provider` in `reflect/typing.anthill`, `default_provider(?S, ?C, ?C) :-
   self_provides(?C, ?S)`, gives every sort that provides a spec for itself a row "this
   sort is its own default". `one_default` (§8.7's "at most one default per carrier",
   `check_one_default`, kb/defaults.rs:798) refuses two default rows of one spec at
   overlapping carriers with different providers. g1 shows it doing that rightly:
   `Show[T = Box[T = ?]]` beside `Show[T = Box[T = Int64]]`.

   A self-representing spec has no default in that sense, and needs none:
   - a call's argument value picks the provider (g2: `Src.next(ones)` reaches `Ones`, answers 12);
   - a call that names no value cannot pick one among many (g3, refused today; its members
     return `Self`; written `-> Ones`, they were refused on their own, since a bare `Ones`
     is `Ones[T = ?]`, a fix found by the fifth review);
   - so there is no "default `Stream`".

   With the spec's substituted sort in `?c`, rule (2) would WRITE one, six times:
   "`List` is the default for `Stream[T = T, E = {}]`", "`FiniteStream` … for
   `Stream[T = T, E = E]`", and so on. Those carriers unify, so `one_default` would refuse
   the standard library. With the provider at its own type-vars, rule (2)'s rows stay at
   `List[T = T]`, `FiniteStream[T = T, E = E]`, … and do not overlap, as today's rows at
   `List`, `FiniteStream` do not. No special comparison rule is needed. (A first answer to
   the finding proposed one: compare the provider beside the substituted sort. This
   replaces it.) It also settles the third review's "two shapes of `?c`": there is one
   definition, and the class picks which sort.

   The rules then read:
   - `self_provides(C, S)`: the provider is the head of `?c` (`List` at `List[T = T]`) or the
     head of one of its bindings (`MyBag` at `C`, in both orders); every binding counts
     (decision 6).
   - `default_provider(S, I, W)`: a call whose substituted sort is `I`, tied between
     providers, takes `W`. That is what decision 1's call fixes.
   - `one_default` compares two rows by unifying their substituted sorts, as it already
     unifies `List[T = E]` with `List[T = Int64]`.

   Every answer of the relation changes shape, one-type-var ones included (`Set` becomes
   `Eq[T = Set]`). That is visible, and it is made once. Its readers move with it:
   `self_provides`, `default_provider`, the loader's index and `one_default`, and the tests
   that assert the rows (`wi860_default_provider_relations_test` among them).
   `examples/guardians` has an operation of its own named `provision_carrier`, which reads
   `SortProvidesInfo` directly. It is not this relation. The key of the loader's default
   index under a compound `?c` is stage 2's to choose, and it is on the per-call path.
6. **"Provides for itself": every binding counts. DECIDED 2026-11-22**, after it was decided
   once, reopened by the fourth review, and discussed with the user. The rule, one sentence
   with no exception: **a provider provides a spec for itself when its sort is the head of
   the carrier, or the head of one of the carrier's bindings.** Otherwise it is a witness.
   With decision 5 this covers both classes. A self-representing spec's provider is the head
   of its carrier (`List` at `List[T = T]`); a dictionary spec's provider is found among the
   bindings (`Set` at `Eq[T = Set]`). It feeds the inferred default rows (rule (2) of
   `default_provider`), the supply route and the member checks.

   | probe | provision | today | decided |
   |---|---|---|---|
   | f1 | `Num provides Coll[C = Foo, Elem = Self]` (`Elem` only in `first`'s result) | witness; 42 | `Num`'s own, so it gains an inferred default row, used only on a tie at `Coll[C = Foo, Elem = Num]`; 42 |
   | f2 | `Foo provides Dflt[T = Self]` over `dflt() -> T` | its own; default row | unchanged |
   | f4 | `Num provides Coll[C = Foo, Elem = Self]` AND `Foo provides Coll[C = Self, Elem = Num]` | runs, 1: `Foo` its own and the default, `Num` a witness | refused at load: both are their own, so `one_default` sees two defaults at one carrier, until one is marked `default provides` |
   | | the nine stdlib `NonEq` providers (`nonEqRefl() -> T`) | their own; default rows | unchanged |

   **Two rules were weighed**, each one sentence:
   - **Rule 1, every binding counts.** Taken. Its one refusal (f4) is loud and is repaired
     by one mark. It changes nothing in the standard library.
   - **Rule 2, a binding at an output-only type-var never counts.** Not taken. It takes
     away a sort's own provision of every spec whose type-vars are all output-only: f2, the
     nine `NonEq` providers, `Default`- and `Bounded`-like specs. Their uses would need
     rewriting with `default provides` marks. It also makes a phantom type-var that is
     bound only in a result second-class.

   The first decision, option (b), was rule 2 with an exception (where no operation takes
   any type-var, every binding counts), so that f2 and `NonEq` kept their own provisions.
   The user did not want a rule with variants. No single rule was found that keeps both f4
   and f2: "the provider is at every type-var an operation takes" breaks `MyBag provides
   Bag2[T = Int64, C = Self]` (`put(c: C, x: T)` takes both).

7. **One provider writing two provisions of a self-representing spec: refused at load.
   Follows from §1's table** (2026-11-22; the fifth review, finding 2). Under decision 5
   both provisions are at ONE carrier, the provider (`Bag`). The spec's type-vars are
   `Self`'s projections, read off that carrier, so `Bag`'s `Self.C` would have two readings
   (e3, e5: `C = Box` and `C = Crate`). Refused, as today, by §8.7's "one carrier declaring
   one spec twice", kept for this class. The alternative, admitting them and having
   decision 1 refuse the `Self`-only calls (`joinTwo(bag, bag)`), was not taken: a value's
   type-var is a member of its type, and the language already refuses a member that two
   provisions of one sort bind differently (§8.7's projection rule).
8. **A spec with both shapes is self-representing. Follows from §1's table** (2026-11-22;
   the fifth review, finding 3). `Holder`'s `peek(c: C)` is `peek(c: Self.C)`, and
   `joinTwo(a: Self, …)` takes a `Self` value, so `Holder` is self-representing. Its
   provisions are at the provider: `BoxHolder` at `BoxHolder` (today a witness at `Box`),
   `Bag` at `Bag`. Its `C` is read off the provider.

   e1 (2) and e2 (9) answer as today: `peek(box)` fixes `Self.C = Box`, and decision 1
   finds the one provision with `C = Box`. Several providers at the same `C` are refused at
   the call until the provider is written, as g3 is: there is no default "any `Holder` at
   `C = Box`". A `default provides` mark cannot settle that tie, because its row is keyed
   by the provider. The alternative, provider-keyed rows for the `Self`-taking operations
   and spec-keyed rows for the rest (two per provision), was not taken.

   Caveat: where the tied providers all have constructors, today's c3 rule also refuses
   naming one in a bracket, so no call works. That is the c3 defect (§3 C), unfiled.

## 7. Acceptance

The stage 1 rows are JE2MT's; the stage 2 rows are WI-20261122-CXR5B's.

- **Stage 1 rows:** b1 derives no second row, with its back-out. The equality rows of
  `wi_tv0pa_eq_gives_partial_eq_test` stay green.
- **Stage 2 rows:**
  - b2 still names `W` once the witness criterion moves.
  - b3 and b4 agree: `MyBag`'s own provision in both orders, `?c` is
    `Bag2[T = Int64, C = MyBag]`, and `self_provides` and `default_provider` answer the same
    in both orders.
  - Decision 5's `?c` table holds, `Stream`'s row included.
  - b5–b8, d5 and d7–d10 answer as decision 1's table says; d1–d4 and d6 as they do today.
  - d11 answers 1, and d12 answers 7 (the approved amendment); d13 stays refused.
  - e1 answers 2, e2 9 and e4 32; e3 and e5 stay refused at load (decision 7). `?c` is
    `BoxHolder` and `Bag` (decisions 5, 8).
  - The bound-`joinTwo` receiver defect (§6 decision 4) gets a probe of its own, with ONE
    provision, since e5 is refused by decision 7 anyway.
  - `VectorSpace` declared `F` first still reads `Vec3`'s provision as its own.
  - c1 answers 42, or its cause is named.
  - The diagnostics the X readers print ("Write the instance: …") use the substituted sort.
  - f1, f2 and f4 answer as decision 6's table says: f4 is refused at load until one
    provision is marked `default provides`.
  - The stdlib's `Stream` providers keep their inferred default rows, at `List[T = T]` and
    the others (decision 5), and `one_default` passes. g1 is still refused, g2 answers 12,
    and g3 and g4 answer as decision 1 and c3 decide.
  - Each of §6's decisions has its driven row.
- **The a-rows** pass before and after, by design.
- **Gates:** families green; full workspace via `rustland/scripts/test.sh`; scaland
  `testFull`.

## Reproduce

```bash
docs/design/spec-carrier-set/run.sh                     # rustland/target/debug/anthill
docs/design/spec-carrier-set/run.sh path/to/anthill
```

The two experiments of §3 were edits to the tree, measured and reverted. Each was run over
a1–a3, b2 and c1–c3 only. a4–a7, b1 and b3–b8 were not run under them.

- `witness_at_param(kb, spec_carrier_param(…)?, …)` → `spec_carrier_param_or_sole` in
  `witness_dispatch_carrier_value`: unchanged except b2, which then named `C`.
- the same fallback inside `spec_carrier_param` itself: unchanged, so c1 still refused.

## History

- **2026-11-22, written.** The model taken with the user; §6's four decisions taken with
  the user, each as proposed. Committed in `182cc7154`.
- **2026-11-22, reviewed from another session** (anthill-6d), which reran `run.sh` on
  `182cc7154` and confirmed every row and every citation, `clause_carrier_param`'s line
  aside (2594). Taken from it, each checked here first:
  - a8 is a first match by declaration order, not a selection by the expected type. Its
    three variants were reproduced, and it moved to §3 B as b5–b8.
  - Decision 1's premise was a8, so decision 1 was reopened with two selection rules.
  - b2 is a stage 2 guard, not a stage 1 row; stage 1 moves one verdict.
  - Decision 3 refuses a superset. The order-dependence of today's refusal was measured
    here.
  - The `SpecCarrier` shape (now `SortCarrier`) no longer presupposes decision 4.
  - The reflect relation became decision 5.
  - The opening no longer says "not a change of the language" of the consequences.
  - c1 is no longer called independent of the V question.
  - The stage 1 helper is built on the owner (then `spec_carrier`, now `sort_carrier`).
  - Scope: stage 2 is proposed as its own ticket.
  - Smaller: five ladders compute one parameter, not seven; the 114 sites include L6's 8;
    §4 has its "other" row; rows unify; a witness reads each binding's head sort; the
    experiments' coverage is stated.
- **2026-11-22, decision 1 decided with the user.** d1–d7 measured on `182cc7154` (§3 D).
  The user's point: the carrier belongs to the operation, not to the sort. `first`'s
  signature mentions `Elem` in its result, so the expected type fixes `Elem` as an argument
  fixes `C`. That is the rule for every provider. Option (b) was not taken. The §5.4
  wording is proposed, not yet approved.
- **2026-11-22, decision 5 decided with the user**: the reflect relation's carrier is the
  substituted sort. b3/b4's `self_provides` and `default_provider` measured on
  `bc5f30f1e`. Vocabulary taken from the user: a spec with its type-vars substituted is a
  substituted sort, not an "instance" in that meaning; the document's own prose changed
  to it.
- **2026-11-22, second review from the other session** (anthill-6d), on `bc5f30f1e`. It
  reran `run.sh` and every row printed what the tables say. Taken from it, each measured
  here first:
  - Decision 1's first refusal over-refused: d8 (one provider, nothing fixes `Elem`) runs
    today and would have been refused. The rule is restated as "refused when it fixes
    nothing at all, or when the provisions at what it fixes disagree", and d8–d10 are
    added.
  - Two providers at the same substituted sort are 058's tie (a3), not this rule.
  - The expected type is the one at the call (d10).
  - d5's three refusing checks are named.
  - Decision 3's "takes a value of" means the parameters, on purpose.
  - The status line names decision 4.
  - §7 says where the stage 2 rows go.
  - For the review's finding that "carrier" had two definitions, its suggestion of
    "instance" was NOT taken: the user had just ruled that word out in that meaning. The
    user's terms were taken instead: **sort carrier** and **operation carrier**. The title
    changed to them, and the owner became `sort_carrier` / `SortCarrier`.
- **2026-11-22, §5.4's wording approved by the user**, as restated after the second review.
  It lands in `kernel-language.md` with stage 2, the stage that implements it.
- **2026-11-22, decision 4 decided with the user.** A temporary census of the standard
  library (removed): none of the 9 sorts with both shapes is provided. Probes e1–e5 over
  `wi1076`'s `Holder`. The user's point: `Self` is by definition the sort at all its
  type-vars (§5.2), so a type-var an operation writes is that `Self`'s projection, and the
  sort carrier is all the type-vars for every spec. Decision 1's self-representing
  exception and decision 5's `List[T = T]` sentence were corrected; `SortCarrier` lost its
  `self_sort` flag (it was `{ self_sort: bool, type_vars }`).
- **2026-11-22, third review from the other session** (anthill-6d), on `c3f0cd4e5`, before
  the §5.4 approval and decision 4. Taken from it, each measured here first:
  - A call that names its provider is not covered by the approved wording. d11 is refused
    though it should answer, and d12 loads clean and fails at run. An amendment is
    proposed for the user's approval.
  - The two shapes of `?c` (its finding 2) are resolved by decision 4.
  - "Provides for itself" through a result-only binding (its finding 3) is decision 6, open.
  - The d8/d9 asymmetry has its reason stated.
  - §7 lists d8–d13, e1–e5, decision 5's shapes, and the X readers' message.
  - The default index's key under a compound `?c` is noted as stage 2's to choose.
- **2026-11-22, the amendment to §5.4's wording approved by the user**, merged into the
  approved wording: a bracket naming a provider fixes its provisions; the first refusal
  reads "and names no provider"; "`Self` mentions them all" (decision 4).
- **2026-11-22, decision 6 and the scope decided with the user.** Decision 6, option (b): a
  binding at a result-only type-var does not make a provision the provider's own (probe
  f1, measured on `aa4e60674`). Scope: JE2MT delivers stage 1, and stage 2 is filed as
  WI-20261122-CXR5B, depending on it.
- **2026-11-22, fourth review from the other session** (anthill-6d), on `0a3f0acb8`. Taken
  from it, each measured here first:
  - Finding 1, the stdlib `Stream` default rows colliding under decision 5. Worked through
    with the user (probes g1–g4), who corrected decision 5: for a self-representing spec
    `?c` is the provider at its own type-vars (`List[T = T]`), so the rows stay apart. A
    first answer, comparing the provider beside the spec's substituted sort, was replaced
    by this.
  - Finding 2: decision 6's (b) takes away `Foo`'s own `Dflt` (f2) and the nine stdlib
    `NonEq` self-provisions. Decision 6 is reopened.
  - Finding 3: §7's stale scope sentence is fixed.
  - Finding 4: WI-20261122-CXR5B restates decisions 5 and 6, and gets a note when they
    settle.
- **2026-11-22, decision 6 decided again with the user: rule 1, every binding counts.**
  Probe f4 (measured on `0a3f0acb8`) was the case where the candidates differ. Rule 2,
  where output-only bindings never count, was weighed and not taken, because of `NonEq`,
  `Default`-like specs and phantom type-vars.
- **2026-11-22, fifth review from the other session** (anthill-6d), on `78c02aca1`. Taken
  from it, each checked here first:
  - The vocabulary is restated for both classes: a substituted sort is any sort with type
    substitutions, and a provision's carrier is the type of the values it is for.
  - §4's D, W and O rows are brought to decisions 5 and 6.
  - g3 and g4 were refused a second time, because their members returned a bare `Ones`
    (`Ones[T = ?]`). The members now return `Self`, and only the call's refusal remains.
    This was the probe's fault, not a defect.
  - Two open decisions are added: one provider writing two provisions of a
    self-representing spec (7, which also undoes decision 4's removal of that refusal),
    and a spec with both shapes (8).
- **2026-11-22, §1's table reworked with the user from `Self`'s definition** (§5.2): a
  provision's carrier is what `Self` denotes for the values it is for. Decision 5 is
  confirmed against it, `?c` being the provision's carrier. Decisions 7 and 8 are recorded
  as following from it: refused at load, and a spec with both shapes is self-representing,
  `peek(c: C)` being `peek(c: Self.C)`.
