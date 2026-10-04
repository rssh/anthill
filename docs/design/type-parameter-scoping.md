# Type-parameter scoping, projection, and threading

**Status:** Decided (2026-06-04), in design dialogue. **Supersedes** the
sort-parameter-*sharing* framing of
[`expansion-during-unification.md`](expansion-during-unification.md) §5 (the
"R-1…R-6" rules / "within-signature sharing" — see *What this replaces* below).
**Realizes:** [`kernel-language.md`](../kernel-language.md) §8.1. **Drives:**
[042](../proposals/042-explicit-type-parameters-on-operations.md) (operation
type parameters — the *explicit* threading mechanism, already implemented),
WI-376 (value projection `s.T` / `s.Self` — the *fluent* threading mechanism),
WI-374 (bare-reference expansion — a *convenience*, no longer load-bearing).

**Revised by [070](../proposals/070-self-and-fresh-bare-sorts.md)** (2026-10-03/04,
implemented through its stage (e)): the implicit self tie this document described in §3
— its first bullet, the WI-1082 paragraph and the "Two exceptions" — is gone, with §4's
member-tie enforcement and §5's "The scope is the foreign slots". A bare or partial sort
is fresh everywhere, inside its own definition too; `Self` writes this instance; and an
operation that uses its sort's parameter beside the sort at an open slot must have a
carrier (070 §1.4). §3–§5 below are rewritten to that. §1's projection is `s.Self` (it
was `s.Sort`), and `Self` is a type name inside a sort's definition.

## The core principle

> **Type-checking depends on the *type* of a value, never on its provenance —
> and a type relationship a consumer relies on must be *written*, never inferred
> from an implicit shared sort parameter.**

Two values of the same type must type-check identically. So whatever a consumer
needs about a value must be readable *from the value's type*, stated explicitly
by the producer — not recovered from where the value came from, and not smuggled
in through a sort parameter that two unrelated references happen to share.

## 1. A value carries its type; project it (`s.Self`, `s.T`)

A value `s` has a static type, and its type members are projected **off the
value**:

| form | meaning |
|---|---|
| `s.Self` | the whole **parameterized** sort of `s` — e.g. `Stream[T = Int64, E = {}]` |
| `s.T`, `s.E` | a **named** member of that sort — `s.T = s.Self.T` |

- **Capitalized** (`Self`, `T`, `E`), matching anthill's type-vs-value case
  split: types and sort parameters are Capitalized (`List`, `Stream`, `T`, `E`),
  value fields are lowercase (`head`, `tail`). So the case at the dot says which
  world you are in: `s.head` is a value field; `s.T` / `s.Self` are type members.
- `Self` is the one word for "a sort at its parameters" (proposal 070): of the
  enclosing definition when written as a type, of a value when projected.
- A projection reads the **value's** static type — locally, concretely, per
  reference. No global variable, no provenance. (Rejected alternative: `s.type`
  drags in Scala's *singleton* `s.type`. The projection was `s.Sort` until
  proposal 070: this document first rejected `s.Self` for its
  "receiver/enclosing-type baggage", when there was no `Self` for it to agree
  with.)

`s.Self` is the robust "same type as `s`" — it captures **every** parameter
whatever their number, so a sort growing a third parameter does not silently
drop from a `s.Self`-typed return (where a spelled-out `Stream[T = s.T, E = s.E]`
would).

**Two projection forms — only one lives here.** `s.T` / `s.Self` above are
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

## 2. Threading is *written* — three mechanisms

A relationship from a parameter to the result is stated, never implicit. Pick
either:

**(a) Value projection (WI-376) — fluent.** Read the argument's type members:

```
iterator(l: List)  -> Stream[T = l.T, E = {}]
collect(s: Stream) -> List[T = s.T] effects s.E
splitFirst(s: Stream) -> Option[Pair[A = s.T, B = s.Self]] effects s.E
```

**(b) Operation type parameters (042) — explicit, already implemented.** Declare
the operation's own `[…]` parameters, bound afresh per call:

```
collect[Elem, Eff](s: Stream[T = Elem, E = Eff]) -> List[T = Elem] effects Eff
splitFirst[Elem, Eff](s: Stream[T = Elem, E = Eff])
  -> Option[Pair[A = Elem, B = Stream[T = Elem, E = Eff]]] effects Eff
```

**(c) A shared logical variable (WI-1FKR2) — (b) without the bracket.** Write one
variable in both positions and the tie is the variable:

```
id(b: Box[?t]) -> Box[?t]
summarize(t: Text[L = ?l]) -> Text[L = ?l]
```

This is the same mechanism as (b), not a third kind of thing: §5.4's *"Which
variables the ∀ quantifies"* counts a variable named in a parameter type exactly
as it counts an `[A]` binder, so `?t` is per-call and caller-instantiated, and the
body is checked with it skolemized. It was listed nowhere for a while and did not
work: the body left such a variable *flexible*, which is what the unwritten-slot
filler reads as an omitted slot, so it overwrote the author's `?t` with (a)'s
projection `b.T` and the two ends of the signature stopped naming one thing. That
is why no generic operation could be implemented in terms of another one — the
form a *library* is written in is (c) delegating to (c).

All three are explicit and **per-call**. Operation type parameters are *already*
per-call (042: "each invocation binds them afresh"), so **no separate
"per-call scheme substrate" is needed** — 042 is the substrate. Prefer (a) for
brevity and for wide sorts (`s.Self` is one token for all parameters; `s.P7`
picks one); (b) when you want to name the parameter at the call site; (c) when the
relationship is between two positions and nothing needs to name it from outside.

## 3. No implicit sort-parameter sharing

- A sort's `sort T = ?` declares its **genericity**. Its parameters are type
  parameters of each of its constructors and operations (070 §1.1), named there by
  name: `cons(head: T, tail: Self)` holds a `T` and a list of *this* sort's `T`.
  **`Self` is the sort applied to its own parameters** — in `sort List` it is
  `List[T = T]` — so every `Self` in one signature is the same instance, the one
  the call fixes: `append(xs: Self, ys: Self) -> Self` takes one list type three
  times, and `append(intList, strList)` is rejected at the argument that does not
  fit. That is the whole of the tie, and it is **written**.
- A sort's **bare or partial name is not that tie** — anywhere. `append(xs: List,
  ys: List) -> List` declared *inside* `sort List` takes two lists of unrelated
  element types and returns a third the operation picks, exactly as a top-level
  `f(a: List, b: List)` leaves `a` and `b`'s elements **independent**. To relate
  them you write a name — `Self`, a parameter (`List[T = T]`), a variable
  (`f(a: List[T = ?t], b: List[T = ?t])` ties, `List[T = ?x]` / `List[T = ?y]`
  splits), or a concrete type (`List[Int64]` / `List[String]` fixes).

**It used to be implicit, inside the sort's own definition** (WI-374, WI-424,
WI-1082; removed by proposal 070). A bare self-sort reference there took *this*
instance — `append(xs: List, ys: List)` tied both parameters and the return to the
sort's `T` — first as an absence the unifier's canonical channel bound, then as a
rewrite of the declaration at load, enforced at each call. Nothing in such a
signature said that its three lists agreed, so the tie could not be checked by
reading, and it did not extend to `provides`. One text had two meanings, depending
on where it was written; it has one now.

**What the bare reading would let through is refused where it is wrong**: an
operation that *uses* its sort's parameter `V` beside the sort at an open `V` —
`get(c: Cell) -> V` — has no carrier for that `V`, and is refused at its
definition (070 §1.4; `kernel-language.md` §5.2). The author says which was meant:
`get(c: Self) -> V`, or `get(c: Cell) -> c.V`.

There is no member/foreign split left to decide. A type expression means what it
says wherever it is written, and `unify_types` is a pure, context-free term
relation: nothing is the same variable unless the declaration says so.

## 4. Bare references still expand (WI-374) — but as a convenience

A bare or partial parametric sort still expands — `Stream` ≡ `Stream[T = ?, E
= ?]`, `Stream[T = Int64]` ≡ `Stream[T = Int64, E = ?]` — a **fresh variable
per ungrounded position**, **per occurrence**, so two independent bare uses
never alias. The expansion is **site-scoped** (it runs at each use, *before*
the unify boundary, so `unify_types` stays a context-free relation),
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
- **Per-occurrence slots at a call.** A callee's parameter that leaves a slot
  out is expanded to a fresh variable per slot, per call — every sort alike,
  the callee's own included. (As first delivered the callee's own sort was
  skipped — its bare name rode the canonical channel as the member tie — and a
  call-time check enforced that tie; both went with it, 070 stage (e). A bare
  sort reference met in unification now binds nothing: it is compatible, by
  width, with every instance.)

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

The scope is **every** sort's slots, the callee's own included: `-> Box` declared
inside `sort Box` is a box the operation picks, as `-> List` is a list it picks.
A return that is this instance says so — `-> Self` — and its slots, being the
sort's parameters, are bound by the call's arguments like any other type
parameter. (Until 070 the callee's own sort was exempt: its bare name in a return
was §3's implicit tie.)

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
- **WI-376 (value projection)** — grows the family `s.T` / `s.E` / **`s.Self`**
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
