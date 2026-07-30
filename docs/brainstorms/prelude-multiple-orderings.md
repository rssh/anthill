# Two orderings of one carrier, in the SHIPPED library

## Status: CLOSED (2026-07-30) — see the Addendum and its closing note at the end. The title is a misnomer for what shipped: NO ordering went into the library. `Pair` gained componentwise equality; both orderings are the program's, and an `Ordered[Pair]` provision waits on WI-876. Design now in proposal 058 (rules: §3.2 rung 2a, §3.6 defaults, §3.8 bundles) + `docs/design/058-implementation.md` (§7 probe matrix, §8 build order; it also maps the older 058 section numbers cited below). The body below is the pre-drive record; two of its claims are corrected in the addendum (option 2's cost, and open question 5's "lawful" list).

Triggered by **WI-844** (proposal 058 phase 4). That ticket delivered
`stdlib/anthill/prelude/sortedset.anthill` — a set whose comparator is a NAMED
requirement slot, so the ordering is part of the type — but put its two demonstration
orderings (`ByLength`, `Alphabetical`) in the **test**, not the library. The instruction
is that the shipped library must carry two orderings of one carrier: a mechanism that
only the test suite can exercise has not really landed.

This document records what was measured when that was attempted, because the attempt hit
**two independent obstacles**, only one of which is a 058 question.

## Relates to

- **058** [§4.1 the coherence ladder](../proposals/058-modular-instances.md), §4.7
  (named slot = type parameter), §5.3 (the `SortedSet` driver), §10 (the spec amendment,
  which already says *"at most one **default** provider"*).
- **038** — per-language binding files; the layering obstacle below is entirely 038's
  rule meeting 058's.
- **004** (`docs/proposals/004-partial-vs-total-equality-and-ordering.md`) —
  `PartialOrd` / `Ordered`, and `Ordered requires Eq[T], PartialOrd[T]`, which is what
  makes obstacle B bite.
- **WI-857** — a dictionary built from a carrier-keyed provider bundles no
  sub-requirements. Interacts with option 1 below; see *Interaction with WI-857*.
- **WI-369** (`internal`), **WI-843** (tier 3 as delivered), **WI-841** (call-site
  selection).

---

## Obstacle A — the dispatch tie

`String` **already provides `Ordered[T = String]`**. Adding two witness sorts makes three
candidates, and 058 tier 3 as delivered (WI-843) refuses an unselected dispatch against
two or more. MEASURED (`anthill load`, 2026-07-30):

```
sort ByLength      fact Ordered[T = String]  operation compare(…) = … end
sort Alphabetical  fact Ordered[T = String]  operation compare(…) = … end
sort Use  operation cmp(a: String, b: String) -> Int64 = Ordered.compare(a, b) end
```
```
error: ambiguous dispatch of `anthill.prelude.Ordered.compare`: 3 instances provide
`anthill.prelude.Ordered` (anthill.prelude.String, ByLength, Alphabetical) and the call
selects none — they may coexist, so say which: write `[Ordered = anthill.prelude.String]`
(or another of them) in the call's bracket list
```

So **declaring an alternative ordering breaks every bracket-less `compare` on that
carrier** — for every downstream consumer, not just the declaring file. That is the
orphan-instance catastrophe 058 exists to avoid, arriving through 058's own front door.
In a *user program* that is arguably acceptable (the author chose to declare the rival).
In a **library** it is not: the consumer never opted in.

### What §4.1 says, and what it is missing

Tier 2 is *"the unique provider … today's rule, unchanged. Programs that load today load
identically."* Tier 3 is *"two or more providers and no explicit selection — a loud error
at that use site."* There is **no rung for a default**. But §10's spec amendment text
already speaks of *"at most one **default** provider for a given carrier"* — a notion the
ladder never cashed out.

There is a structural distinction available, and 058 already leans on it twice:

| candidate | provider vs carrier | 058's existing reading |
|---|---|---|
| `anthill.prelude.String` provides `Ordered[T = String]` | provider **IS** the carrier | §4.9/WI-855: *"a SELF-PROVIDER is a candidate of neither kind"* — this is why the three coexist at LOAD |
| `ByLength` provides `Ordered[T = String]` | provider ≠ carrier | a WITNESS (`witness_dispatch_carrier`, which returns `None` exactly when provider IS carrier) |

So "the carrier's own provision" is already a computed predicate with one owner. A rung
that reads it would be the ladder saying what §10 already promises.

**Candidate rung (2a): the carrier's own provision is the DEFAULT.** When a
`(spec, carrier)` goal has two or more candidates and exactly one of them is the
carrier's own provision, an unselected dispatch takes it; witnesses are opt-in by name.
Two-or-more **witnesses** with no self-provider stays loud — which is exactly §1's
`AddM`/`MulM` program, since `Int64` does not provide `Monoid` itself. So the headline
refusal the arc was built around is untouched.

Costs / objections to weigh:

- It is a **new coherence rule**, i.e. a language change, and §4.1 + §10 must both say
  it. This is not phase 4 plumbing.
- It makes a witness **silently not chosen** where the carrier self-provides. That is
  what "default" means, but someone will expect loudness. Note §4.1 boundary 3 already
  records a comparable implicit precedence (a specificity-ordered pair dispatches
  silently) as *"a widening, pinned rather than fixed"* — so the ladder is already not as
  loud as tier 3's wording suggests.
- It gives no way to say *"this carrier has no default, always pick"*, and no way for a
  library to add a default-eligible provision for a carrier it does not own.

**Candidate rung (2a′): an explicit `default` marker on a provision.** More expressive,
no implicit rule, and it lets an author say which of several is the default. Costs
grammar + loader + spec, and every existing self-provision in the tree would either need
marking or fall back to "unmarked self-provision is the default" — which collapses back
to 2a. Probably 2a first, this later if a case needs it.

---

## Obstacle B — the layering violation, and it is the harder one

**A prelude sort cannot provide `Ordered[T = String]` at all**, regardless of the tie.
`stdlib/anthill/prelude/string.anthill:2-3` states the rule:

> Spec satisfaction facts (`Eq[String]`, `Ordered[String]`) live in the per-language
> binding files (e.g. `rustland/anthill-stl/anthill/string.anthill`) — see proposal 038.

Measured: `Eq[T = String]`, `PartialEq[T = String]`, `PartialOrd[T = String]` and
`Ordered[T = String]` exist **only** in `rustland/anthill-stl/anthill/string.anthill:7-10`.
Nothing in `stdlib/` supplies them. `Int64` is the same (`anthill-stl/anthill/int64.anthill`).

`Ordered requires Eq[T]` and `requires PartialOrd[T]` (004), and
`check_provider_requires` (WI-343/356) demands that a provision's spec-level requirements
resolve. With the language binding loaded they resolve against the carrier. **Without it
they do not** — and binding-free loads are ordinary (many test fixtures, and any
non-Rust target). MEASURED with the binding-free load isolated —
`anthill load --no-stdlib stdlib/`, one prelude witness added:

```
error: 'anthill.prelude.ByLength' provides 'anthill.prelude.Ordered', which requires
'anthill.prelude.Eq', but 'anthill.prelude.ByLength' does not provide 'anthill.prelude.Eq'
error: … which requires 'anthill.prelude.PartialOrd', but … does not provide 'anthill.prelude.PartialOrd'
```

**Control:** the identical command with the witness removed loads clean
(`loaded: 2257 facts, 117 rules`), so the two errors are attributable to the witness and
not to loading `stdlib/` bindings-free. In the full suite the same cause failed tests in
bulk across several binaries; the isolated pair above is the honest measurement, since
that suite run was disturbed mid-flight by reverting the experiment.

Not a tie, not a coherence question — the prelude would be depending on facts only a
language binding supplies.

### It is the property being enforced, not a harness quirk

"`stdlib/` loads with no language binding" is **relied upon and deliberate.** There are
two test collectors, and `collect_stdlib_and_rust_bindings`'s own doc comment draws the
line: *"Use this in place of `collect_anthill_files(&stdlib_dir())` for tests that depend
on `fact Spec[Carrier]` records emitted by the rustland `provides Carrier language rust`
blocks."* `load_stdlib_kb()` — the binding-free one — is what many tests use. And the
property is right: under 038 the prelude is language-AGNOSTIC, so an `anthill` targeting
C++ or Scala must load its own prelude without the *Rust* binding present.

### The conditional spelling does not help — DRIVEN

The natural repair is to say the provision holds *given* that String is lawful:

```anthill
sort anthill.prelude.ByLength
  requires Eq[T = String]
  requires PartialOrd[T = String]
  fact Ordered[T = String]
  operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
end
```

**Still refused, identically.** `check_provider_requires` (`kb/typing.rs:17202`) never
consults the PROVIDER's own `requires` chain on the `concrete` branch: it computes
σ = `{T → String}`, forms the sub-goal `Eq[T = String]`, and asks
`spec_resolves_at_bindings` — a global resolution. In a binding-free load nothing
provides `Eq[String]`, so the answer is a true "no". **The check is right and the
statement it refuses is false**; this is not a limitation to relax casually.

### What this rules out and what it leaves

- **Ruled out:** `anthill.prelude.<Ordering>` witnesses over any PRIMITIVE carrier
  (`String`, `Int64`, `Float`, `BigInt`) — no primitive's lawfulness is prelude-level.
- **Not ruled out:** witnesses over a carrier the **prelude itself** makes lawful.
  `set.anthill` is the precedent — `Set` declares `provides PartialEq[T = Set]` and
  `provides Eq[T = Set]` in the prelude, with its own `eq`. A prelude-owned carrier can
  carry prelude-owned orderings.

### …and putting them in the LANGUAGE BINDING is a category error

An earlier draft of this document listed "declare them beside the
`fact Ordered[T = String]` they compete with" as the leading option. **That is wrong, and
what the binding actually contains is why.** Measured, `rustland/anthill-stl/anthill/string.anthill`
is three things:

| in the binding | what it is |
|---|---|
| `carrier { String: "String" }` | the CODEGEN type map |
| `fact PartialEq/Eq/PartialOrd/Ordered[T = String]` | LAWFULNESS assertions — *that* String is ordered |
| `artifact "rustland/anthill-stl/src/prelude/string.rs"` | **does not exist**, and no code reads that path |

There is **no Rust-side `compare` for String at all.** `Ordered.compare` is a *generic
interpreter builtin* — `ordered_compare` → `value_compare` (`eval/builtins.rs:673`) —
which switches on the `Value` VARIANT (`(Value::Str(x), Value::Str(y)) => x.cmp(y)`), not
on the carrier. So the binding's "ordering" is *the host's natural order, asserted in the
binding and implemented generically*.

An Anthill ordering is the opposite kind of thing: `ByLength.compare(a, b) =
sub(length(a), length(b))` is an ordinary Anthill body with **no host content whatsoever**
— nothing to write on the Rust side. Putting it in a per-language file would make it
invisible to every other target and force verbatim duplication of Anthill code into each
binding. **A language binding asserts host lawfulness and maps carriers; it is not a home
for Anthill implementations.**

---

## Options

| # | Where the two orderings live | Fixes A? | Fixes B? | Cost |
|---|---|---|---|---|
| **2** | A **prelude-owned** carrier instead of `String` — e.g. order `Pair` by `fst` vs by `snd` | — needs 2a *if* the carrier self-provides `Ordered`; **not needed if it does not** | ✅ | changes the driver away from §5.3's `String` example; the carrier needs its own `Eq`/`PartialOrd`. **The only option that can avoid a language change entirely** |
| **5** | Prelude, with a **conditional provision** the check honours — the provision holds *given* the carrier's lawfulness | — needs 2a | ✅ *if* `check_provider_requires` + the dictionary build learn to discharge a provider's own `requires` | a real language increment, and **the same mechanism as WI-857** (see below) |
| ~~1~~ | ~~the Rust language binding~~ | — | ✅ | **withdrawn** — category error; a binding holds host lawfulness + carrier maps, not Anthill bodies (above) |
| ~~3~~ | ~~prelude, accept the bracket~~ | ✗ (it *is* A) | ✗ | rejected by measurement |
| ~~4~~ | ~~the test suite only (WI-844 as delivered)~~ | n/a | n/a | rejected by the instruction |

**Option 2 deserves the most weight.** If the two orderings are witnesses for a carrier
that does **not** provide `Ordered` itself, there is no default to want and no tie to
break: two witnesses, no self-provider, and tier 3's *existing* rule is exactly right — an
unselected dispatch is loud, a selected one works. That is §1's `AddM`/`MulM` shape,
already delivered. It puts two orderings in the shipped library **with no language change
at all.** The cost is that the driver stops being §5.3's verbatim `String` example.

> **CORRECTED by driving (Addendum, 2026-07-30): "no language change at all" is false.**
> The parametric bundled witnesses LOAD today (measured) but die at eval on **WI-857** —
> which turns out to gate *every* option, not just rung 2a and option 5. And the `ByFirst`
> sketch below is a PREORDER (compares `fst` only), failing this document's own
> lawfulness section. See the addendum's probe matrix.

A concrete shape for option 2, for discussion:

```anthill
-- prelude-owned, prelude-lawful carrier; no `provides Ordered` on Pair itself
sort anthill.prelude.ByFirst   fact Ordered[T = Pair[A = …, B = …]]  operation compare … end
sort anthill.prelude.BySecond  fact Ordered[T = Pair[A = …, B = …]]  operation compare … end
```
— which raises its own question: can a witness's carrier binding be PARAMETRIC, and does
`requires Ordered[A]` on the witness then thread? Unmeasured. That is the first thing to
drive if option 2 is chosen.

**Option 5 is the principled one, and it is not new machinery.** "This provision holds
given that its carrier is lawful" is a CONDITIONAL provider, which the resolver already
models (`ResolvedRequiresNode::Conditional`; `candidate_provider_sub_goals` walks the
provider's own `requires` chain). What is missing is that the two *checkers* do not:
`check_provider_requires` resolves the sub-goal globally (measured above). And note where
else that split appears — **WI-857 is the same producer/consumer disagreement seen from
the other side**: there the dictionary PRODUCER walks the provider's chain while the
CONSUMER names the frame from the spec's. A conditional provision is precisely the case
where the provider HAS a chain, so option 5 and WI-857 want settling together rather than
separately.

---

## Interaction with WI-857 — twice over

WI-857: a requirement dictionary built from a **carrier-keyed** provider bundles no
sub-requirements, so it dies at eval (*"dispatching dict … has arity 0 but its requires
chain has 2 entries"*). Rung 2a routes an unselected dispatch **straight to the
carrier's own provision** — i.e. into WI-857 — for exactly the shapes that work today by
accident (a witness provider agrees because dispatch lands on the witness's own member,
whose parent chain is empty).

Measured today: `SortedSet.empty[T = Int64]()` (no `O`) already takes that route and
already dies. Under 2a, so would every bracket-less `Ordered.compare` on a carrier reached
through a `requires` slot. **So any option that adds rung 2a wants WI-857 delivered
first**, or at least measured against, rather than after.

And the second overlap, noted above: option 5 *is* WI-857's split seen from the checker
side. Both are "who owns the requires chain of a provision — the provider or the spec?"

---

## Recommendation, for the record

**Option 2** is the one to take first, and it is the cheapest by a wide margin: two
orderings in the shipped prelude, no language change, tier 3's existing rule already
correct because the carrier does not self-provide. Its one unknown — can a witness's
carrier binding be parametric — is a half-hour measurement, not a design.

**Option 5** is the principled answer to the general problem ("a library ordering of a
primitive"), but it should be settled together with WI-857, since they are one mechanism.

Independently of the choice: **rung 2a is worth filing on its own merits.** "Declaring a
witness breaks every unselected dispatch on that carrier, for everyone" is a defect in
the ladder that phase 4 merely surfaced — not specific to orderings, to `String`, or to
`SortedSet` — and §10's spec text already promises the notion of a *default* provider that
§4.1 never cashed out.

---

## Collect → rank → select: which dimensions, and how a tie settles

Anthill **already** does collect-then-rank. `collect_provides_candidates` gathers every
provision whose head matches the goal; `pick_most_specific` ranks them and returns
`None` on a tie, which is what becomes tier 3's refusal. So the mechanism is not missing —
it has **exactly one ranking dimension** (specificity), and the question is which
dimensions to add.

### What other languages do, and the one lesson they agree on

| language | collect | rank by | incomparable pair |
|---|---|---|---|
| Haskell | matching instance heads | specificity, **but only when the instance opts in** via `{-# OVERLAPPING #-}` / `{-# OVERLAPPABLE #-}` | compile error; global coherence + orphan rules |
| Rust | matching impls | overlap FORBIDDEN outright; `default impl` (specialization) adds one level | compile error |
| Scala 2 | implicit scope (lexical + companion) | specificity, plus a **trait-linearization hack** (`LowPriorityImplicits`) to encode "lower priority" | ambiguity error |
| Scala 3 | given scope | specificity; explicit lowering via a base trait, `NotGiven` for negation | ambiguity error |
| C++ | ADL overload set | partial ordering of templates + conversion ranks | ambiguity error |
| Idris / Agda | instance search | `%defaulthint`, search depth, backtracking | search failure |
| OCaml modular implicits | module scope | most specific | ambiguity error |

**The lesson: every one of these ranks by a PARTIAL order and errors on incomparable
pairs. None of them ships a numeric global priority.** The two that came closest — Scala
2's `LowPriorityImplicits` linearization — is widely regarded as a wart precisely because
it fakes a total order out of inheritance. That is the answer to *"need think, how to
settle"*: **do not build a scale.** A scale is a global namespace nobody owns; two
libraries both choosing `priority 10` collide with no principled resolution. Build a
*relative, pairwise* mark instead, and make the mark's own uniqueness checkable.

### The dimensions, in the order they would apply

**1. Explicit selection** — exists (§4.2/§4.5). Highest precedence. Not a ranking; it
filters the candidate set to one before ranking runs.

**2. Specificity** — exists (`pick_most_specific`). A ground head beats a parametric one.
Partial, and blind to our case: `String`'s `Ordered[T = String]` and `ByLength`'s are
*both* ground and equally specific, so this dimension cannot separate them. This is also
§4.1 boundary 3's recorded widening — where it *does* separate, it already picks silently.

**3. Provider kind — is the provider the carrier?** Free (`witness_dispatch_carrier`
already computes it, and §4.9 already treats a self-provider as "a candidate of neither
kind"). Zero syntax; matches §10's existing *"at most one **default** provider"* wording.
Weakness: **not author-controlled.** A library cannot add a default for a carrier it does
not own, and a carrier cannot say *"I have no default — always select"*.

**4. An explicit `default` mark on the provision** — the user's *(b)*, settled by making it
a bit rather than a scale:

```anthill
default fact Ordered[T = String]          -- the fallback
fact Ordered[T = String]                  -- (in ByLength) an alternative
```

- **At most ONE `default` per `(spec, carrier)`**, refused at load. *The default is itself
  coherent* — that is the whole settling rule, and it needs no ordering between marks.
- Non-defaults coexist freely (tier 3 as delivered) and are selected per call.
- An unselected dispatch takes the `default` when there is one; a tie among non-defaults
  stays loud.
- **Backward compatibility for free:** treat a SELF-provision as `default` unless it says
  otherwise. Then the prelude's existing `fact Ordered[T = String]` needs no edit, and
  dimension 3 becomes the *inference rule* for dimension 4 rather than a rival to it.

Note what "can be overridden" has to mean here, because the obvious reading is wrong: an
alternative overrides the default **when selected, or when strictly more specific** — not
by merely existing. A default that lost to any equally-specific rival would put us back to
needing a total order. So the default is a **fallback, not a competitor**, and that is
exactly what makes it settleable.

**5. Place of definition + reachability** — the user's *(c)*. Record the provision's
definition site on the fact and rank by scope distance. This is the one the design has
already ruled out, **three times and each for a different reason**, so it should not be
re-adopted quietly:

- §8 rejects it outright: *"implicit scope-directed selection (a nearer provider silently
  winning) is deliberately **not** the rule."*
- §3's ruling **measured** that per-`import` selection *"CANNOT EXPRESS EITHER DRIVER — the
  deciding argument needs both monoids in ONE body"*: `fold[Monoid = AddM](xs)` beside
  `fold[Monoid = MulM](ys)` is unwritable if a scope admits one provider.
- §4.2 rejects caller-scope-dependent keys for the bracket, with a sentence that applies
  verbatim here: *"a resolved key would make selection depend on the CALLER's imports,
  while the supply path takes no scope at all."*

There is a real distinction the rejections do not cover — reachability as a **filter**
(narrowing candidates) versus as a **selector** (picking among them). A filter would not
stop two providers coexisting in one body. But it still couples the supply path to the
caller's imports, which is the property §4.2 protects, and Anthill facts are **global**:
there is no instance scope today, so this dimension is also the most expensive to build
(a new fact field plus an import-graph reachability computation).

**6. A declared search sequence** — the weakest. It is the numeric scale in disguise: a
global total order that no single file owns, and it cannot be checked for consistency
across independently-authored libraries. Recorded as considered.

---

## Three regimes, and the regime belongs to the SPEC

The user's second ask — *"coherent type-classes and low-priority default type-classes
which can be overridden"* — is a **classification**, not a ranking, and Anthill turns out
to need exactly three:

| regime | rule | who needs it | enforced today? |
|---|---|---|---|
| **coherent** | at most one provider per carrier, **globally**, refused at LOAD | a spec whose dispatch has **no call site to bracket** — semantic `eq`/`neq` fire from UNIFICATION (§4.9, §6) | **YES, but hardcoded to one family**: `EqDispatchIndex` + `AmbiguousEqDispatch` (WI-837) |
| **default + overridable** | one `default` per carrier; alternatives coexist and win only when SELECTED or strictly more specific | `Ordered[String]` — a natural order that a library may add alternatives to without breaking consumers | no |
| **selectable** | alternatives coexist; every dispatch must say which; unselected is loud | §1's `Monoid` on `Int64` — no natural default exists | **YES** — 058 tier 3, delivered (WI-843) |

Two things fall out of writing it this way:

1. **The coherent regime already exists in the code and is hardcoded.** §4.9's table says
   why `Eq` needs it — *"no call site exists **anywhere** to bracket, because the dispatch
   fires from unification"* — and WI-837 built exactly that check for exactly that family.
   Declaring `coherent` **on the spec** would give that check an owner and let other
   law-bearing specs opt in, instead of the rule living in one family's index build.
2. **The regime is a property of the SPEC, not of the provision** — because it answers
   *"can a use site ever say which?"*, which is a fact about how the spec's ops are
   dispatched, not about who provides them. The `default` MARK, by contrast, is
   per-provision, because *which* provider is the fallback is a per-carrier decision.
   So the two mechanisms are not alternatives; they are a spec-level regime plus a
   provision-level mark, and 058's tier 3 is the `selectable` regime's rule.

---

## What ranking CANNOT fix: `ByLength` is an UNLAWFUL `Ordered[String]`

Driven while thinking this through, and it is a defect in **058 §5.3's own example**, not
in any of the options above.

`ordered.anthill:60` declares `Ordered`'s consistency law:

```anthill
compare_eq: eq(?a, ?b) <=> eq(compare(?a, ?b), 0)
```

`ByLength.compare("ab", "cd") == 0`, but `Eq[String]` says `"ab" ≠ "cd"`. So `ByLength` is
a **preorder**, not a total order consistent with `Eq` — it does not satisfy `Ordered`.
MEASURED, on the delivered prelude `SortedSet`:

```anthill
let s = SortedSet.empty[T = String, O = ByLength]()
SortedSet.toList(SortedSet.insert(SortedSet.insert(s, "ab"), "cd"))   -- ⇒ ab|   ONE element
```

**`"cd"` is silently lost.** The implementation is not at fault: `insertSorted` treats
`compare == 0` as "already present", which is precisely what the law licenses. The witness
breaks the law, so the set drops distinct elements.

Three consequences, all independent of where the orderings live:

- **The example must change.** A lawful alternative ordering of `String` must be a total
  order agreeing with `Eq` — `ByLengthThenAlphabetical` yes, `ByLength` no,
  `CaseInsensitive` no (it equates `"A"` and `"a"`), `ReverseAlphabetical` yes.
  **CORRECTED (Addendum, 2026-07-30): this list checked only `compare_eq`.** The
  derivation block `gt(?a,?b) <=> gt(compare(?a,?b),0)` (`ordered.anthill:44-48`) couples
  `compare` to the CARRIER's `PartialOrd`, inherited via `requires PartialOrd[T]` — so
  `ByLengthThenAlphabetical` and `ReverseAlphabetical` are unlawful too, as lone
  `Ordered` witnesses. The lawful form is a `PartialOrd`+`Ordered` BUNDLE per witness
  (058 §3.8).
- **This is the strongest argument for the regime split.** `Eq` is coherent — there is one
  `Eq[String]`, and a *selectable* `Ordered[String]` must be lawful **relative to it**. No
  amount of ranking, priority or reachability makes `ByLength` lawful; the regimes are
  about which provider is *chosen*, and this is about which provisions are *admissible*.
- **It suggests a fourth thing to want**, beyond the three regimes: `Ordered`'s laws are
  already written as `rule … <=>` in the prelude, and WI-558 shipped a proof-verify pass
  (`discharge_by_derivation`). Whether a provision's laws can be *checked* — even for
  ground carriers — is a separate question this document only flags.

## Open questions

1. **Is the `default` mark inferred, declared, or both?** Recommended: declared, with a
   SELF-provision inferred as `default` unless it says otherwise — that makes today's
   prelude behave correctly with no edits, and keeps the mark author-controllable.
2. **How does a carrier say "no default — always select"?** Needed for §1's `Monoid` shape
   to stay loud even if someone later adds a self-provision, and for the `Eq` family's
   argument (no call site can ever be written, §4.9). Probably falls out of the spec-level
   regime: `selectable` forbids a `default`.
3. **Should `coherent` be declarable on a spec**, generalizing the check WI-837 hardcoded
   for the `Eq` family? That is a strict improvement in ownership regardless of the
   ordering question.
4. Can a witness's carrier binding be **parametric** (`fact Ordered[T = Pair[A, B]]` with
   `requires Ordered[A]`)? Gates option 2. Unmeasured — the first thing to drive.
5. **Which two orderings should actually ship?** They must be LAWFUL (above), so not
   `ByLength` and not `CaseInsensitive`. `Alphabetical` is lawful but is the same relation
   as the carrier's own default, so it demonstrates nothing; `ReverseAlphabetical` and
   `ByLengthThenAlphabetical` are lawful and genuinely different.
6. Can a provision's LAWS be checked? `Ordered`'s laws are already `rule … <=>` in the
   prelude and WI-558 shipped `discharge_by_derivation`. Out of scope here, flagged because
   question 5 exists only because nothing checks them.

---

## Addendum (2026-07-30, same day): driven, corrected, and converged

The open questions above were DRIVEN the same day (scratchpad probes `q4a`–`q4g`,
`anthill load`/`run` at HEAD) and the design discussion converged through three drafts.
The full record: **proposal 058** (the rules — §3.2 rung 2a, §3.6 the relations, §3.8 the
bundle rule) and **`docs/design/058-implementation.md`** (§4 the step-0 `leaf` correction,
§7 the probe matrix, §8 the build order: WI-857 first — and a reference map for the OLDER
058 section numbers the citations below use). What
belongs HERE is what this document got wrong or left open:

### Two corrections to the body above

1. **The lawfulness section under-measured** (marked in place): the `gt/lt/gte/lte`
   derivation block couples a witness's `compare` to the carrier's inherited `PartialOrd`,
   so EVERY lone alternative `Ordered[String]` witness is unlawful — `ReverseAlphabetical`
   included, not just the preorders. The lawful alternative is a **bundle**: the witness
   provides its own `PartialOrd` + `Ordered`, consistent with each other, anchored to the
   one coherent `Eq` by `compare_eq`. Generalizes to any spec tower: alternatives are
   bundles of floors, never one floor over shared lower floors.
2. **Option 2 is not language-change-free** (marked in place): the bundled parametric
   witnesses over a prelude-lawful carrier LOAD today — measured, including the check
   discharging the `Eq` leg from the carrier's `provides` and the `PartialOrd` leg from
   the witness's own fact — and then **die at eval on WI-857**, from BOTH routes (σ-pinned
   slot and searched), with the frame named from the SPEC's chain (the count stays 2 when
   the witness's own chain is cut to 1). The ticket's "a witness sidesteps it" control is
   the ONLY shape that runs (ground + chain-free + slot-free body, measured `-1`).
   **So WI-857 gates every option in the table above**, and its settlement must include
   the LOCALITY rule (a provider's dictionary resolves a sub-goal the provider itself
   provides to its OWN provision) — otherwise the two-bundle library ties on
   `PartialOrd[Pair]` inside each witness's chain.

### The regime discussion resolved (supersedes "Three regimes" above)

The three-regime table collapsed under review, in two steps that are worth keeping:
a keyword surface fell to *"too many new keywords"*, and the spec-level mode fell to
**`Monoid[Int64]` vs `Monoid[List]`** — no canonical instance vs concatenation, one spec,
both behaviors, so selectable-vs-default is a per-**(spec, carrier)** state, not a spec
property, and not even a mode: it is the presence/absence of a row in a partial function.
Only **`Coherent`** stays per-spec, because it names the dispatch MECHANISM (§4.9: no
call site exists to bracket). Final shape, all in the reflect layer on the proposal-035
variance pattern (facts outside the sorts, absence = safe default, zero grammar):

- `entity DefaultProvider(spec, provider)` (named so — `Default` alone is too broad) +
  the inference rule `default_provider(?S,?C,?C) :- self_provides(?C,?S)` +
  `constraint one_default`. No-displacement is DERIVED: an explicit fact against a
  self-providing carrier violates `one_default` via the inferred row — no dedicated rule.
- rung 2a consumes it: a tied dispatch takes the unique default among the most-specific
  candidates; no row ⇒ tier 3's loud error, unchanged.
- deferred, same idiom, zero keywords: `Coherent` data rows (re-homing WI-837's family
  list, KEEPING target-counting), `within:`-scoped rows, per-carrier `NoDefault`.

### Open questions, closed out

1. **Inferred, declared, or both?** Both — inference for self-provisions (String's binding
   needs zero edits), `DefaultProvider` facts for the rest; `one_default` arbitrates.
2. **"No default — always select"?** Per-CARRIER absence (free), plus an optional
   per-carrier `NoDefault` guard later — `Monoid[List]` proves the spec-wide blanket
   would be wrong.
3. **Declarable `coherent`?** Deferred with a caveat: it must stay TARGET-counting
   (058 §6's measured `CoinEqB` admission), and it buys ownership only — WI-837's check
   already enforces the constraint.
4. **Parametric witness carrier?** MEASURED YES — loads, selects, and the conditional
   chain THREADS when the spec's own chain is empty (`q4a`: 3+6=9). The `Ordered` form
   loads and dies at eval — that is WI-857, not a missing 058 feature.
5. **Which orderings ship?** Bundled lex-by-`fst`-then-`snd` / lex-by-`snd`-then-`fst`
   over `Pair`, with `Pair` gaining componentwise `provides PartialEq/Eq` (the `Set`
   precedent, measured loading). Nothing on `String` until option 5 — and then bundles.
6. **Law checking?** Still out of scope; the reflect-layer home §4.10 creates is where a
   `discharge_by_derivation`-based check would later hang.

### The recommendation, updated

**WI-857 first** (extended acceptance: the ticket's reproducers + `q4e` + the locality
rule), **then the library** (058 §9 phase 7 — the WI-844 instruction finally met), **then
rung 2a** (phase 8 — obstacle A closed for `String` and every self-providing carrier).

> **CLOSED 2026-07-30, with option 2's CARRIER and NEITHER of its shapes.** WI-857
> delivered; WI-858 took `Pair` — as this document recommended — and then shipped **no
> ordering at all**. `Pair` gained componentwise `PartialEq`/`Eq`; both orderings are
> declared by the test program and selected by name. Two co-equal witnesses were built
> first and withdrawn (obstacle A, below); a single CANONICAL `Ordered[Pair]` was then
> built, driven working end to end, and withdrawn too — because it costs SEVEN
> operations in `pair.anthill` where one would do, six of them one-line restatements of
> "call `compare`, check the sign". Those six exist only because the eval builtins sit
> on the SPEC ops and compare host scalars only, which is **WI-876**; the library should
> not carry a workaround for a defect that has a ticket. The correction to this
> document's framing: **obstacle A bites `Pair` too.** The
> Options table assumed a `Pair` witness pair costs nothing because `Pair` self-provides
> nothing — true when written, but the moment `Pair` gains `Eq` (which obstacle B
> *requires* for any prelude ordering of it), shipping two rivals hands every downstream
> bracket-less pair compare the same tier-3 error that rules `String` out. And a pair is
> not `Monoid[Int64]`: it HAS a canonical order, the one every neighbouring language
> gives it, so "no default to want" was wrong on the facts.
>
> Obstacle B was discharged exactly as predicted (the `Eq` leg from `Pair`'s own
> provision, the `PartialOrd` leg from the bundle; the provision facts asserted directly
> in a binding-free load). Question 4's parametric witness carrier: confirmed again, now
> from the test side. Question 5 ("which orderings ship?") is answered differently than
> the addendum guessed — **the canonical one ships, the alternatives do not.**
>
> Five things the drive found that this document did not anticipate: the shared
> `requires` chain cannot condition `PartialEq[Pair]` and `Eq[Pair]` at their two
> strengths (**WI-869** — an `Eq` chain makes `Pair[A = Float, …]` a load error, so
> `Pair` takes the weaker `PartialEq` chain and `Eq[Pair]` over-claims); §3.3's
> composition leg is validated and then discarded (**WI-870**); a componentwise
> provider's second requirement slot is read from the first when the first's carrier is
> the provider itself (**WI-871**, pre-existing); a provision's carrier is matched by
> SHORT NAME at dispatch (**WI-872**, pre-existing); and `dispatch_origin` keeps one
> rewrite per spec op for the whole image (**WI-873**, pre-existing).
>
> Rung 2a is now load-bearing for `Pair` as well as `String`: while a rival is declared,
> the canonical order is unreachable through a `requires` slot, because a CONCRETE
> provider cannot be named (§3.5 check 3) and the bare goal is ambiguous. §3.6's
> inference rule closes it with no edit to the prelude — phase 8c, **WI-861**.
Option 5 remains the principled answer for library orderings of a PRIMITIVE and remains
paired with WI-857, exactly as §Options concluded — the pairing is now tighter, since
WI-857's settlement builds the machinery option 5's checker halves need.
