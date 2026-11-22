# The carrier of a spec is a set of its type-vars

## Status: design, measured 2026-11-22 on `1a58f1e48` (code `88e83f4ae`); §6's decisions taken with the user the same day. For WI-20261121-JE2MT.

This is a CORRECTION of the implementation, not a change of the language. The type system
already says what a spec's carrier is. Proposal 074 §1.2 (decided): "a spec may have several
carriers … a value typed at the spec is the dictionary, covering all its parameters".
[`path-dependent-types.md`](path-dependent-types.md) §5.4 (decided 2026-06-13): a sort's
type-vars are the instance's identity, and what is not part of it is an operation's type
parameter (§1.1 below). The implementation never followed either. It computes ONE parameter per spec, by an inference
`kernel-language.md` §5.1 itself calls "the rule as implemented", and about 120 sites read
that one parameter. JE2MT found two of the ways it is computed disagreeing. This document
says what the carrier is, measures where the single parameter answers wrongly, and lays out
the correction.

The probes and the script that reruns them are in [`spec-carrier-set/`](spec-carrier-set/).
The full list of readers is [`spec-carrier-set/readers.md`](spec-carrier-set/readers.md).

## 1. The model (with the user, 2026-11-22)

The carrier of a typeclass is a SET of the sort's type-vars. Often it has one element; not
always.

| the spec | its carrier | examples |
|---|---|---|
| a spec with a dictionary: no operation takes the spec itself | all its type-vars | `Eq[T]`, `SortDomain[T]`, `TypeValue[T]`, `Monad[M]` (one); `Iterable[C, Element, E]`, `VectorSpace[V, F]`, `Convert[X, Y]` (several) |
| a self-representing spec: an operation takes the spec itself | the providing sort itself (`Self`); its type-vars are read off the provider | `Stream[T, E]` (`splitFirst(s: Self)`), so `List provides Stream[T = T, E = {}]` is at `List` |

A provision `W provides S[p₁ = t₁, …]` is AT the instance its bindings at the carrier
name: the whole binding list for a dictionary spec, the provider for a self-representing
one. From that:

- **Two provisions are at the same instance** where those bindings unify.
- **A witness** is a provider that is none of the sorts bound at the carrier.
- **"Add this provision unless one is written"** (the derivations) asks whether a written
  provision is at an instance that unifies with the one to be added.
- **Which argument of an operation fixes the instance** is a question about THAT OPERATION:
  its parameters typed at a type-var of the carrier. It is not a property of the spec, and
  it is not "the carrier".

A proper subset of the type-vars ("`Element` is decided by `C`") is NOT in the language,
and the implementation does not enforce one (§3, `a8`). Adding it would be a language
extension. The correction does not need it.

### 1.1 The same model, read as path-dependent members

[`path-dependent-types.md`](path-dependent-types.md) already has this model in other
words. Read through it, the question "which sort is this provision for" disappears.

- **A spec's type-vars are the members of an instance.** `d.T` over `d: Additive` (074),
  `C.Elem` over a type receiver (§5.3), `s.provider.K` over a provider's value (§1). The
  β law `F[T = A].T ≡ A` (§5.4) is the reading of a written binding: `W provides
  Eq[T = C]` is an instance whose member `T` is `C`.
- **The type-vars ARE the instance's identity.** §5.4 (decided 2026-06-13): "`CpsMonad`'s
  only parameter is its type constructor `F[T]`. The element types `A` / `B` are
  per-operation type params … not part of the monad's identity", and the fixtures that
  declared them as sort type-vars were migrated to per-operation ones. So a type-var of
  the sort is part of the instance's identity, and what is not must be an operation's type
  parameter. That is the carrier set of §1.
- **A self-representing spec is the path case.** In §1's example the members are read off
  the PROVIDER's value: `s.provider.K` is `SubscriberStore`'s `K`, which its provision
  binds to `String`. The tests that drive that example today give `DataProvider` a
  self-receiving `pick(p: Self)` (`wi1082_self_return_tie_test`), which puts it in that
  class: the provider is the carrier, and `K` is one of its members.
- **So two provisions are one instance when their members agree**, and nothing needs to
  name one member as "the" carrier. A reader that picks one type-var reads one member of
  the instance and ignores the others. That is what every row of §3 B does.

## 2. What the implementation computes instead

ONE parameter per spec, by one of seven ladders:

| ladder | rule | where |
|---|---|---|
| L1 | the first declared type-var that some operation takes as a BARE parameter type | `spec_carrier_param`, provision.rs:133 |
| L2 | L1, else the sole type-var if the spec is not self-representing | `spec_carrier_param_or_sole`, provision.rs:187 |
| L3 | for a spec with a dictionary: L1, else the FIRST type-var | `spec_over_parameter`, provision.rs:243 |
| L4 | L1, else the first type-var, with no class gate | `clause_carrier_param`, carrier.rs:2595 |
| L5 | L1, else the sole type-var, with no self-representing gate | inline in `check_rule_sort_uses`, provision.rs:812 |
| L6 | any type-var any parameter of the operation is typed at (a SET); the spec itself if self-representing | `op_has_spec_carrier_param`, value_type.rs:1301 |
| L7 | `Effect`'s `T` binding, by label | `registered_effect_kinds`, signature.rs:5877 |

L1 is under the witness criterion (`witness_dispatch_carrier_value`, coherence.rs:2888), so
dispatch, the coherence groups, the member checks and the derivations of `SortDomain` and
`TypeValue` read it. L2 is under `provisions_about`, the equality derivation (since
TV0PA), the goal keys, and the default rows. 114 call sites read L1–L3 and their wrappers
directly ([readers.md](spec-carrier-set/readers.md)), plus 9 callers of two wrappers.

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
| a8 | `Coll[C, Elem]`, `first(c: C) -> Elem`; `W1 provides Coll[C = Foo, Elem = Int64]`, `W2 … Elem = String`; `to_string(Coll.first(foo))` | 1 |

Every one is right. None of them depends on which single parameter is "the carrier", and
a8 shows the carrier is the whole set: two instances at `C = Foo` coexist and the expected
`Int64` picks one.

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

**The standard library is read right by declaration order.** A load of the standard library
alone has 585 provision rows. Three bind two or more sorts: `Map provides
Iterable[C = Map[…], Element = Pair[…]]`, the same for `FiniteCollection`, and `Vec3
provides VectorSpace[V = Vec3, F = Float]`. They read as `Map`'s and `Vec3`'s own because
`C` is declared before `Element` and `V` before `F`. `VectorSpace.vec_scale(c: F, v: V)`
takes `F` too, so with `F` declared first `Vec3`'s provision would read as a witness for
`Float`.

### C. Not this question (recorded so they are not mistaken for it)

| probe | program | answers | why it is not the carrier |
|---|---|---|---|
| c1 | `sort BoxM { provides Monad[M = Box]; … }` with its own `pure`/`flatMap`/`map`; `Monad.flatMap(box(v: 41), …)` | refused: "no impl matches" | unchanged with the witness criterion on L2 and with `spec_carrier_param` itself on L2 (both experiments, reverted) |
| c2 | control: `Box` providing `Monad[M = Self]` with the same members | 42 | |
| c3 | two data sorts each `provides Dflt[T = Int64]` | refused, and no bracket is accepted: "each is a CONCRETE provider, where … the VALUE decides" | the bracket rule asks whether the provider has constructors (`is_value_directed_provider`, dispatch.rs:426), not which parameter is the carrier. Known since wi822 (`TieRepair::ValueDirected`) |

c1 and c3 are separate defects. Neither is filed.

## 4. The readers, by the question each one has

From [readers.md](spec-carrier-set/readers.md), 114 sites:

| question | sites | under the model |
|---|---|---|
| D: add a provision unless one is written | 4, and the `Eq` family's K/X/other rows (6) | is a written provision at an instance that unifies with the one to be added |
| S: select the instance a goal asks for | 39 | the goal's bindings at the carrier, all of them for a dictionary spec |
| V: which argument fixes the instance | 17 | the operation's parameters typed at a type-var of the carrier (L6 already reads this) |
| P: projection, left-out bindings | 12 | a binding of the carrier set, read by name; "except the carrier" becomes a decision, §6 |
| K: a refusal decided by the parameter | 10 | per refusal (§6 for `ProvisionNamesNoCarrier`) |
| SC: the spec's class | 9 | unchanged: these ask whether the spec has a dictionary, not which parameter |
| X: diagnostic text | 6 | names the carrier's type-vars, or the provider |
| W: witness or own | 5 | the provider is none of the sorts bound at the carrier |
| O: overlap, defaults, specificity | 5 | provisions whose instances unify; default rows keyed by instance |
| M: member checks | 4 | the provision's instance; the receiver per operation, as §8.7 already says |

## 5. The correction

**One owner.** `spec_carrier(kb, spec) -> SpecCarrier`, read off the declaration and
memoized per canonical spec:

```rust
enum SpecCarrier {
    /// An operation takes the spec itself: the provider is the carrier.
    SelfSort,
    /// A spec with a dictionary: these type-vars, in declaration order.
    TypeVars(SmallVec<[Symbol; 2]>),
}
```

It replaces L1–L5 as the answer to "where is this provision". Two questions stay apart from
it, under names that say what they answer: which parameters of an OPERATION fix its
instance (L6, per operation), and the spec's class (`sort_class`, 074 §2). Nothing reads
"the first" of anything.

**Stage 1: the derivations.** One helper, "the written provisions of `S` at an instance
that unifies with `t`", replaces `provisions_about` and `provision_carriers_of_spec` in:

- `eq_derive` (`spoken_for`, `equality_signatures`, `equality_reaching_no_eq`, `written_spec_of`)
- `load.rs` `EqProviders::of`
- `sort_domain_derive`'s `already`
- `type_value_derive`'s `already`. `HandWrittenTypeValue` reads the PROVIDER.

Every spec these read has one type-var, so this stage moves no verdict except b1 and b2. It
is small, and it holds every measured defect of §3 B.

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
- §5.2: a left-out parameter is `?` "the spec's carrier parameter excepted" (around 2143).
- §8.3: "a provision being about the sort it binds to its spec's carrier parameter, or to
  the sole one" (around 6266).
- §8.7: "One carrier declaring one spec twice" (around 7272); the member receiver "the
  first typed by a spec parameter the provision binds to the carrier" (around 7325).
- 058 §3.6 keeps its rule. A note says its "carrier" is the instance.

## 6. Decisions (taken with the user 2026-11-22, each as proposed)

1. **§8.7, one provider declaring one spec twice.** Today two provisions by the SAME
   provider that agree at the single parameter and differ in another type-var are refused,
   because "every reader of a carrier's provider view takes the first match". Under the
   model they are two instances, as a8's two providers already are. Decided: admit them.
   The refusal's reason is the single-parameter lookup this document removes.
2. **A written provision that overlaps the one a derivation would add without covering
   it** (`Eq[T = Box[T = Int64]]` against the derived `Eq[T = Box[T = T]]`). Today `Box`
   gets no derived equality at all. Decided: keep that (any overlap skips). §8.3's "Closed
   by the load" assumes it.
3. **A left-out type-var** (§5.2, `ProvisionNamesNoCarrier`). Today a left-out binding is
   `?`, except the carrier parameter, which a written provision must bind
   (`LiveLlm provides Llm[E = {External}]` is refused). Under the model every left-out
   type-var is `?`. Decided: keep the refusal, restated as "a provision binds each type-var
   an operation of the spec takes a value of". It is per operation, and it is the same
   refusal for every spec it refuses today.
4. **A spec that takes itself and also has a type-var an operation takes**
   (`spec_carrier_param`'s doc: "a spec declaring BOTH a carrier parameter and a
   self-receiving operation", measured to refuse a program that loads when its binding
   was discarded). Is its carrier `Self`, or `Self` and those type-vars? Decided: measure
   it in the tree before stage 2, and decide from the measurement.

## 7. Acceptance for JE2MT

- **Stage 1 rows:** b1 derives no second row; b2 names `W`; the equality rows of
  `wi_tv0pa_eq_gives_partial_eq_test` stay green. Each has its back-out.
- **Stage 2 rows:** b3 and b4 agree (`MyBag`'s own in both orders); `VectorSpace` declared
  `F` first still reads `Vec3`'s provision as its own; each of §6's decisions has its
  driven row.
- **The a-rows** pass before and after, by design.
- **Gates:** families green; full workspace via `rustland/scripts/test.sh`; scaland
  `testFull`.

## Reproduce

```bash
docs/design/spec-carrier-set/run.sh                     # rustland/target/debug/anthill
docs/design/spec-carrier-set/run.sh path/to/anthill
```

The two experiments of §3 were edits to the tree, measured and reverted:

- `witness_at_param(kb, spec_carrier_param(…)?, …)` → `spec_carrier_param_or_sole` in
  `witness_dispatch_carrier_value`: a–c unchanged except b2, which then named `C`.
- the same fallback inside `spec_carrier_param` itself: c1 still refused.
