# Type-parameter scoping, projection, and threading

**Status:** Decided (2026-06-04), in design dialogue. **Supersedes** the
sort-parameter-*sharing* framing of
[`expansion-during-unification.md`](expansion-during-unification.md) §5 (the
"R-1…R-6" rules / "within-signature sharing" — see *What this replaces* below).
**Realizes:** [`kernel-language.md`](../kernel-language.md) §8.1. **Drives:**
[042](../proposals/042-explicit-type-parameters-on-operations.md) (operation
type parameters — the *explicit* threading mechanism, already implemented),
WI-376 (value projection `s.T` / `s.Sort` — the *fluent* threading mechanism),
WI-374 (bare-reference expansion — a *convenience*, no longer load-bearing).

## The core principle

> **Type-checking depends on the *type* of a value, never on its provenance —
> and a type relationship a consumer relies on must be *written*, never inferred
> from an implicit shared sort parameter.**

Two values of the same type must type-check identically. So whatever a consumer
needs about a value must be readable *from the value's type*, stated explicitly
by the producer — not recovered from where the value came from, and not smuggled
in through a sort parameter that two unrelated references happen to share.

## 1. A value carries its type; project it (`s.Sort`, `s.T`)

A value `s` has a static type, and its type members are projected **off the
value**:

| form | meaning |
|---|---|
| `s.Sort` | the whole **parameterized** sort of `s` — e.g. `Stream[T = Int64, E = {}]` |
| `s.T`, `s.E` | a **named** member of that sort — `s.T = s.Sort.T` |

- **Capitalized** (`Sort`, `T`, `E`), matching anthill's type-vs-value case
  split: types and sort parameters are Capitalized (`List`, `Stream`, `T`, `E`),
  value fields are lowercase (`head`, `tail`). So the case at the dot says which
  world you are in: `s.head` is a value field; `s.T` / `s.Sort` are type members.
- `Sort` (not the lowercase keyword `sort`) is a free identifier, so `.Sort`
  needs no keyword gymnastics.
- A projection reads the **value's** static type — locally, concretely, per
  reference. No global variable, no provenance. (Rejected alternatives: `s.type`
  drags in Scala's *singleton* `s.type`; `s.Self` carries
  receiver/enclosing-type baggage and its member `Self.T` is `Stream.T` — the
  sort-parameter framing this document removes.)

`s.Sort` is the robust "same type as `s`" — it captures **every** parameter
whatever their number, so a sort growing a third parameter does not silently
drop from a `s.Sort`-typed return (where a spelled-out `Stream[T = s.T, E = s.E]`
would).

**Two projection forms — only one lives here.** `s.T` / `s.Sort` above are
**expression-carried** projections — `s` is a *value*, and the projection
elaborates to a fresh `Ti` plus the synthesis-time constraint `Ti =
typeof(s).T`, discharged when `s` is synthesized (no requirement; `Ti` is
*determined* by `s`). The **sort-carried** form `X.L` — `X` a *sort*, not a
value — is a different thing: it desugars to an **operation type parameter plus
a requirement** (`f(p: X.L) ≡ f[Ti](p: Ti) requires X[L = Ti]`), so its rules
live with operation type parameters in
[042 §"Type projections"](../proposals/042-explicit-type-parameters-on-operations.md),
not here. **Cross-dependency strictness** (a projection's receiver must resolve
first → topological / synthesis order; cycles, missing members, and an abstract
receiver with no such interface member are loud errors) applies to both — see
WI-376.

## 2. Threading is *written* — two mechanisms

A relationship from a parameter to the result is stated, never implicit. Pick
either:

**(a) Value projection (WI-376) — fluent.** Read the argument's type members:

```
iterator(l: List)  -> Stream[T = l.T, E = {}]
collect(s: Stream) -> List[T = s.T] effects s.E
splitFirst(s: Stream) -> Option[Pair[A = s.T, B = s.Sort]] effects s.E
```

**(b) Operation type parameters (042) — explicit, already implemented.** Declare
the operation's own `[…]` parameters, bound afresh per call:

```
collect[Elem, Eff](s: Stream[T = Elem, E = Eff]) -> List[T = Elem] effects Eff
splitFirst[Elem, Eff](s: Stream[T = Elem, E = Eff])
  -> Option[Pair[A = Elem, B = Stream[T = Elem, E = Eff]]] effects Eff
```

Both are explicit and **per-call**. Operation type parameters are *already*
per-call (042: "each invocation binds them afresh"), so **no separate
"per-call scheme substrate" is needed** — 042 is the substrate. Prefer (a) for
brevity and for wide sorts (`s.Sort` is one token for all parameters; `s.P7`
picks one); (b) when you want no new surface.

## 3. No implicit sort-parameter sharing

- A sort's `sort T = ?` declares its **genericity**, used **within the sort's
  own definition** — its constructors and own operations (`cons(head: T, tail:
  List)` ⇒ `tail` is a `List` of *this* sort's `T`). That is parametricity, and
  it is the *only* implicit tie, because the `sort T = ?` line *is* the
  declaration of it. **Within the sort's own definition, a bare self-sort
  reference participates in that tie**: `append(xs: List, ys: List)` declared
  *inside* `sort List` ties both parameters (and the return) to *this* sort's
  `T`. The tie is **enforced** (decided 2026-06-12, WI-374):
  `append(intList, strList)` is rejected — the conflicting binding of the
  shared `T` is a type error, not a silent first-binding-wins.
- It is **not** a cross-signature threading mechanism for **foreign**
  references — a sort referenced *outside its own definition*. Two foreign
  references to a sort do **not** silently share a variable across a
  signature: a top-level `f(a: List, b: List)` leaves `a` and `b`'s elements
  **independent**; to relate them you write a name — `f(a: List[T = ?t], b:
  List[T = ?t])` ties, `List[T = ?x]` / `List[T = ?y]` splits, `List[Int64]` /
  `List[String]` fixes.

**The tie is written down, not left implicit (WI-1082).** Every position named
above is a *rewrite*, applied once per declaration before any body check or call
site reads the signature: a self-sort reference that elides a slot is rewritten to
name this sort's own parameter. `cons(head: T, tail: List)` becomes `tail: List[T =
T]`; `append(xs: List, ys: List) -> List` gets `-> List[T = T]`; and a parameter
that *partially* writes the sort — `widen(s: MyStream[T = Int64])` — becomes `s:
MyStream[T = Int64, E = E]`. Leaving the slot *absent* was not equivalent to naming
it: an absent binding is width-**ignored** by unification, so nothing was claimed
about it and no consumer demand could be refuted — `docs/kernel-language.md` §8.1
carries the exploit that closed, and the parameter position is what closes it for a
member with no body to check.

Two exceptions, both measured. A **written** slot is never rewritten. A **bare**
self parameter is not either: `unify_parameterized_with_sort_ref` already binds the
sort's parameters when one side is a bare reference, and writing the tie in makes
that binding strict enough that the WI-424 sibling-call seeding refuses a member
called at a different instance (`List.mapElems` calls `reverse` at `Dst`). And an
operation with no parameter naming its own sort (`List.empty() -> List`) is left
alone, since nothing at a call could bind the parameter this would write.

The member/foreign split is decided by the **declaration context** of the type
expression — where it was *written*, not where a unification later runs. That
context is exported into the term *before* the unify boundary (the loader
knows a signature's enclosing sort; a typing site knows an annotation's
scope), so `unify_types` itself stays a pure, context-free term relation: by
the time two types meet, each bare reference already carries the right
variable identities. This is what removes the "accidental substitution"
fragility: nothing is the same variable unless the declaration context says
so.

## 4. Bare references still expand (WI-374) — but as a convenience

A bare or partial parametric sort still expands — `Stream` ≡ `Stream[T = ?, E
= ?]`, `Stream[T = Int64]` ≡ `Stream[T = Int64, E = ?]` — a **fresh variable
per ungrounded position**, **per occurrence**, so two independent bare uses
never alias. The expansion is **site-scoped** (it runs where the declaration
context is known, *before* the unify boundary — see §3's closing paragraph),
it keeps an *unannotated* reference usable, it is **not** how relationships
are threaded (that is §2), and it never *reconstructs* an erased relationship
(§5).

Delivered increments (2026-06-12):

- **Let-annotation rewrite.** A bare/partial parametric annotation is
  rewritten at the binding site to KEEP the value's inferred parameters
  instead of erasing them: `let s : Stream = List.iterator(xs)` binds `s` at
  `Stream[T = Int64, E = {}]`; `let s : Stream[T = Int64] = …` keeps its
  written `T` and takes `E` from the value. Written bindings stay
  authoritative (a contradicting one is still a mismatch); an alias annotation
  resolves to its shape first (WI-381).
- **Member-tie enforcement** (§3 bullet 1) — see above.
- **Remaining:** foreign bare refs in operation signatures still share the
  foreign sort's canonical vars internally (benign today — gated out of the
  enforcement, and nothing outside the sort can name `Sort.T`); normalizing
  them to per-occurrence variables at signature processing is the open
  WI-374 scope.

## 5. The boundary — type, not provenance

Expansion supplies **variables**, never **values**. A producer that erases a
relationship cannot have it reconstructed downstream:

```
iterator(l: List) -> Stream      -- bare return: the element/effect tie to `l` is GONE
```

No consumer-side mechanism can soundly recover `l`'s element or effect from such
a result — the type does not carry it. The fix is always to **write it in the
result type**: a projection (`Stream[T = l.T]`), a written effect row
(`Stream[E = {}]`, WI-375), or operation type parameters. Hence the stdlib's
bare returns (`iterator -> Stream`; `splitFirst`'s `B = Stream`) are exactly the
spots to make explicit.

**"Erased" is an existential, and naming it that way settles the return
(WI-1063).** What this section calls erasure — the tie is GONE, no consumer-side
mechanism can recover it — is exactly `∃`. `iterator(l: List) -> Stream` declares
`∃T,E. Stream[T, E]`: the body *packs* a witness, so the producer is not at
fault and needs no rewriting; a consumer *opens* and gets a fresh skolem, which
is why it "cannot be reconstructed downstream" and why
`wi374_expansion_test::bare_value_stays_unusable` is right to refuse. The advice
above — write it in the result type — is still the fix for an author who wants
the tie, and since WI-1063 it is load-bearing rather than cosmetic: a consumer
that needs the element or the row cannot get it any other way, not even by
annotating the result (`let l : List[T = Int64] = makeList()` is refused). What
does NOT need fixing is the producer: an author content to erase is writing a
correct existential, not a latent bug.

Read the quantifier off the arrow's polarity, and this section and
kernel-language.md §"Expansion during unification" stop competing: a parameter's
unwritten slot is negative-position and **universal** (§4's expansion, the caller
instantiates); a return's is positive-position and **existential** (this section).
One rule, two polarities.

Where the skolem is minted is the whole of it. At the **call**, fresh per opening
— `widen(s : Stream[T = Int64, E = {Error}]) -> Stream[T = Int64]` keeps loading
and its *consumer* is refused. Minting it in the **body check** instead demands
the body hold for every instantiation, which is a universal in a positive
position; that was built and measured and costs 40 tests across thirteen
delivered tickets, including the WI-401/402/457/480/488/491 escape gate.

The scope is the **foreign** slots. A reference to the callee's own sort in its
own return is §3's parametricity tie, not an existential — it names this
instance's parameter and the call's arguments pin it — so it is left to the
canonical channel, exactly as §4's parameter-side expansion leaves it.

The mechanism already existed for the *carrier* of an explicit existential
(`ensures Spec[C]`, WI-402 — §5 of `path-dependent-types.md`); the **members**
were not opened in either spelling, because the loader rewrites `-> C ensures
Spec[C]` to a bare `-> Spec` and they then rode the ordinary expansion path.
WI-1063 opens both by one rule; `wi1063_existential_return_test` drives it, and
the corpus reaches it zero times, so that file is its only coverage.

**Which slots are unwritten is a question about the SIGNATURE, not about the
spelling (WI-1078).** WI-1063 opened only the slots written `?` or omitted, which
exempted a *named* variable and left its own exploit alive under a two-character
edit (`-> Stream[T = Int64, E = ?E]`). The name buys binding *across the term*,
so read it there: a variable the declaration also uses in a **parameter**, in its
own **`[A]`** binder, or in a **`requires`** bound is an ordinary universal the
caller instantiates, while one used **only in the return** is the existential
above and opens at each use. A parameter of the **enclosing sort** needs no such
entry — written in a type it is a reference to its symbol, not a logical
variable, so `to_pair(h: Holder) -> Pair[A = T, B = T]` is not a candidate at
all. Sharing survives — a
named variable opens to one rigid per *use*, shared by every slot it appears in,
so `-> Pair[A = ?t, B = ?t]` still says its components agree.
`wi1078_unbound_return_var_test` drives it; the corpus reaches this one zero
times too.

## 6. Structured and higher-kinded parameters

The fresh-variable source is the `?` **leaves at any depth**, with structure
preserved — not "one variable per parameter":

- `sort T = ?` — one leaf. Opens to one fresh variable.
- `sort T = Pair[?X1, ?X2]` — `T` is constrained to a `Pair`; leaves `X1`, `X2`.
  Opens to `Pair[X1', X2']`; unification is first-order/structural.
- `sort F = { sort T2 = ? }` — `F` is **higher-kinded** (a sort-constructor
  variable). Opens to a fresh higher-kinded `F̂`, **grounded by provider
  dispatch** (`List[Int64]` receiver ⇒ `fact Functor[F = List]` ⇒ `F̂ := List`,
  first-order thereafter), with the residual unbound-`F̂` case bounded to the
  decidable pattern fragment — a loud error outside it, never a guess.

## 7. Alias resolution precedes expansion

Resolve aliases / defined types to their **shape** first
([011](../proposals/011-type-resolution.md)), then freshen the remaining leaves:

- `sort IntStream = Stream[T = Int64]` — a bare `IntStream` resolves to
  `Stream[T = Int64, E = ?]`, so **only `E`** is open and fresh; `T` stays `Int64`.
- `sort PairKey = Pair[?X1, ?X2]` — expands to `Pair[X1', X2']` with fresh leaves
  per use; chains (`A = B[?X]`, `B = C[?Y]`) follow to a finite shape.

Skipping resolution would wrongly send a partial alias all-fresh. (011 is still
*Brainstorming*; this resolution must be present, not assumed.)

## What this replaces

The earlier framing in `expansion-during-unification.md` §5 tried to motivate
*implicit within-signature sharing of a sort parameter* (`collect`'s `s` and its
return both "are" `Stream.T`). That framing is **withdrawn**:

- it conflated different sorts' parameters (`Stream.T` vs `List.T`) and leaned on
  a global-feeling `Stream.T` rather than the value's `s.T`;
- it did invisible work — `splitFirst`'s bare `B = Stream` *looked* fine only
  because the bare reference silently carried `Stream.T`;
- it made independence (two different-element lists) the thing you had to fight
  for, which is backwards.

The element/effect of a value `s` is **`s.T` / `s.E`** (a projection off the
value), or an operation type parameter — **never** a shared `Stream.T`.

## Relationship to the logical-rules engine — gaps, the framework, & invariants

"Types are terms" is the goal; today it is **aspirational**. Typing is a second
constraint engine (`unify_types`) alongside the resolver (`unify`). The honest
audit separates two kinds of gap, because they want different treatment.

**Implementation gaps — *one relation, several implementations that must agree*.**
Refactoring debt, not holes in the definition; sound as long as the
implementations agree, and WI-010 collapses them:
- **two `unify`s** (resolver-term vs typer-type) — §8.1 type-expansion is
  *asserted* equal to §8.3 partial-entity-patterns (a verify, not a proof);
- **provider admissibility read in hand-coded Rust** (`sort_provides_admissibly`)
  rather than a resolver goal — WI-356 existed because that reading had drifted;
- **the hand-coded typer passes** (WI-357 / 365 / 367 / 356 / 350 / 343 / 344) —
  logical relationships encoded imperatively;
- **directionality** — bidirectional synthesize / check (WI-379) is a *checking
  algorithm* for an undirected declarative relation, not a gap in the definition.

**Definitional content — and the largest is a *design*, not a gap.**

> **Unification is a framework with per-sort registered algorithms.** Syntactic
> unification is the *default*; a sort may register its own. Effect rows register
> the row algorithm (Rémy, WI-307); sets register AC; intervals register CLP(R).

Sketch and formal basis (the reprogrammable / monadic-unification approach):
[`docs/proposals/future/unification-framework.md`](../proposals/future/unification-framework.md).

This **condenses** several apparent gaps into one mechanism:
- **effects** stop being a "parallel algebra" — they are simply the sort whose
  registered unifier *is* the row algorithm;
- **value-in-type (`denoted`) equality** (`Modify[c1]` vs `Modify[c2]`) is just
  the *embedded value's sort's* unifier — no separate rule;
- the **two-`unify` implementation gap shrinks to a shared dispatcher** — the
  resolver and the typer dispatch the *same* per-sort algorithms in their two
  contexts.

The definitional work this turns into (cleaner than special-casing):
1. **the unifier interface** — what a sort registers (`unify_S(a, b, store) ->
   store?`), and the value-equality it induces;
2. **composition** — combining theories when a term mixes them (a structure
   containing an effect-row sub-term): the studied *combination of unification
   algorithms* / Nelson–Oppen, decidable under disjoint-signature conditions that
   order-sorted anthill largely meets;
3. **termination** — each registered unifier must terminate; a non-terminating
   combination is a loud rejection, not a loop.

The remaining definitional gaps are narrower: **projection cross-dependency
semantics** (resolution order, cycles, missing member, abstract interface —
WI-376) and **contracts vs. types** (whether `requires` / `ensures` are part of
well-typedness or a separate runtime obligation).

**Invariants to hold until WI-010 closes the implementation gaps.**
- **A typing rule is defined in terms of the facts it consults** (provider facts,
  `requires`), never by re-encoding the relationship (WI-356 is the cautionary
  case).
- **Bidirectional and projection carry a constraint-generation reading**
  (synthesize = emit a constraint; check = solve it).

**WI-010 (resolver-as-type-checker)** is the principled closure: typing-as-
constraints solved by per-domain solvers *is* CLP, and the per-sort unification
framework is exactly the engine it wants — effects are the proof-of-concept that
it must exist.

## Consequences for the work items

- **042 (operation type parameters)** — the explicit threading mechanism;
  already implemented (`op.type_params`, `seed_op_type_args`, the
  unconstrained-param inference). The per-call substrate. *Verify*: inference
  pins `[Elem, Eff]` from a **cross-sort** argument (a `List[Int64]` used as a
  `Stream`) via provider admissibility — the one piece to confirm.
- **WI-376 (value projection)** — grows the family `s.T` / `s.E` / **`s.Sort`**
  (the whole parameterized sort). The fluent threading mechanism; scales to wide
  sorts. Reads the value; no provenance.
- **WI-374 (bare-reference expansion)** — a convenience layer for unannotated
  references; **not** load-bearing for threading, and by §5 it cannot make
  `collect(iterator(xs))` thread on its own — the producer must write the tie.
- **No new sort-parameter-scheme substrate WI** — 042 already opens operation
  type parameters per call.
- **Stdlib** — bare returns that relied on the withdrawn implicit sharing
  (`iterator(l: List) -> Stream`; `splitFirst -> Option[Pair[A = T, B =
  Stream]]`) are rewritten explicit (projection or 042), with the observation
  effect written (`E = {}`, WI-375).
