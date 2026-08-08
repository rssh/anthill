# Rules and effects

**Status: brainstorm.** Questions, with what is already measured or decided
attached to each. Nothing here is ratified. Opened from the WI-1049 / WI-1050
conversation, where writing one ordinary law on `PersistentCollection` turned
out to touch five separate settled decisions that do not jointly answer it.

## The case that opened it

```anthill
-- in sort anthill.prelude.PersistentCollection
rule isEmpty(insert(?c, ?x)) <=> false          -- loads clean, INERT
rule isEmpty(insert(?c, ?x)) <=> false [simp]   -- REFUSED, twice
```

Refused naming `PersistentCollection.insert` (row `{Effect}`) and
`Iterable.isEmpty` (row `{E}`). **Neither operation is effectful.** Both carry a
row *variable* (`effects Effect = ?`, `effects E = ?`), and `List`'s provision is
documented pure — "grounded to `{}` at the consumption boundary" (list.anthill,
WI-357/WI-365).

Measured, so the ground is firm:

| written | verdict |
|---|---|
| law on the effect-polymorphic spec, `[simp]` | refused (2 errors) |
| law on a carrier declaring its **own pure** ops, `[simp]` | loads clean, fires |
| law over a concretely-`External` op, `[simp]` | refused — 054's own case |
| same law untagged | loads clean, inert |
| binding `Effect = {}` at List's **provision** | changes nothing — the gate reads the *operation's* declared row |

Placed inside `List` instead of on the spec, the law is refused **once**, not
twice: `List` declares its **own** pure `insert` (`operation insert(c: List,
elem: T) -> List = cons(head: elem, tail: c)`, list.anthill:254 — a body, no
effects clause), so that leg passes. What `List` does not declare is `isEmpty`;
it imports `Stream.{isEmpty}`, whose row is `{s.E}` — the receiver's effect
parameter, projected. So in the stdlib as it stands there is still nowhere to put
this law where it would fire, but the obstacle is one operation, not two.

## The five decisions that meet here

Each is settled on its own and none is wrong; they simply were not written
against each other.

- **054, "Consumers that must decline it — loudly."** A `[simp]`-tagged rule
  mentioning an effectful op is refused at load: a directional rewrite
  duplicates, reorders or drops the matched call. Explicitly: *"The gate for
  that belongs at load-time tag validation, not the firing site."* **Scope: the
  argument is about a concretely-`External` row.** The row-*variable* case is
  not discussed there at all.
- **WI-881 / CLAUDE.md.** `[simp]` is the *enablement*, not the direction. An
  untagged equational rule is **inert** — it never rewrites.
- **WI-818.** A rule is a *law*, not backing. It does not discharge a spec
  operation's obligation.
- **WI-580.** An operation *with a body* is the single source of truth; its
  equational and relational views are **derived** from the body by abstract
  interpretation. An operation *without* a body is given meaning **by** rules.
- **Proposal 045 / WI-357 / WI-365.** A closed effect row is not a type
  argument; it is grounded to `{}` at the consumption boundary, per carrier.

## Q1 — may an INERT law mention an effectful operation?

An untagged equation never rewrites, so 054's duplicate/reorder/drop argument
does not reach it. Today it is allowed (measured: the untagged form loads
clean). Is that deliberate or incidental?

**Effects are not uniform for this question, and that is the whole of Q1.**
The first draft of this section argued from *allocation* — "`isEmpty(insert(c,x))
= false` over an `insert` that allocates is still a true claim about the returned
collection, so effect-freedom is the wrong precondition for stating a law". That
generalized from the easy case. It is false for `Error`.

`Error` is a **control** effect: `operation raise(error: T) -> Nothing`
(effects.anthill), and `sort Nothing` is uninhabited. On the raising path
`insert(c,x)` produces **no value at all**, so `isEmpty(…)` is never applied and
the equation has no witness. `isEmpty` after an error has no sense — the LHS is
not *false*, it is *undefined*.

So split by whether the effect can remove the value:

- **Control effects** — `Error` (→ `Nothing`), `Branch` (proposal 027:
  zero-or-many results), non-termination. The LHS may denote nothing. A value
  equation holds at best **on the defined path**, and it is not a claim about
  the whole operation.
- **Value-preserving effects** — allocation, logging, `Modify` on unrelated
  state. The LHS always denotes; the equation about that value can hold
  unconditionally.

**And this is the strongest form of 054's argument, not a weakening of it.**
Rewriting `isEmpty(insert(c,x)) → false` over an `Error`-carrying `insert`
does not merely lose a side effect — it turns a program that *raises* into one
that *answers `false`*. A **wrong answer**, not a lost effect. 054 argues
"duplicates, reorders, or drops"; for a control effect, *drops* is a soundness
bug in the value.

Two consequences worth carrying forward:

- **The sound law is spelled differently.** What actually holds for an effectful
  `insert` is the effect-preserving form — *run the insert, then answer `false`*
  — where both sides raise identically and nothing is dropped. That is a
  different equation from the one written. Whether anthill can spell it (a
  sequencing/monadic reading of `<=>`) is open, and it is the honest target for
  anyone who wants this law over an effectful carrier.
- **The conditional form is not a new mechanism.** Guarded effect atoms already
  exist: `effects { s.E, Error[EmptyStream] :- isEmpty(s) }` (`Stream.head`,
  `List.head`). A law conditioned on the non-raising path is the same shape
  pointed the other way.

## Q2 — does the answer differ per tag?

Three citations, three risk profiles, currently one gate:

- `[simp]` — rewrites during typing. Duplicates/drops. 054's argument applies.
- `[unfold]` — fired by the **resolver**, which never macro-expands (WI-757
  measured exactly this asymmetry, where keying on `is_macro` alone let an
  effectful macro under `[unfold]` rewrite an effectful call into the program).
- bare law cited by `using` in a proof — no rewrite at all.

## Q3 — is "effect-polymorphic" a third answer? **DECIDED: no.**

**Decision (2026-08-08): effect-polymorphic ⇒ potentially effectful. One
verdict, two explanations.**

Effect-polymorphism *translates to* effect. There may one day be
effect-**elimination** rules that discharge the polymorphic case — but they are
not known, and until they are, "may be an effect" and "is an effect" are one
category for every consumer that must decline. The union is named **potentially
effectful**, and that is what the gate refuses.

What stays split is the **explanation**, because the repair differs and because
the original defect was a *misdescription*: `Effectful` is a property of the
operation that no carrier can undo, `Polymorphic` is a property of the
declaration site only (repair: declare the equation where the row is already
concrete). Keeping them apart in the message is what stops it calling `insert`
effectful when `insert` is not; collapsing them in the verdict is what stops the
message promising an admissibility that does not exist.

**Deferred, explicitly: post-release.** A mode that applies `[simp]` *after*
typing, where effects are eliminated and the row is ground, is the only shape in
which the polymorphic arm could earn a different verdict. Not to be implemented
before release. WI-1050 carries it.

The rest of this section is the reasoning that led there, kept because the
alternatives should not be re-derived from scratch.

### why it was open

WI-1049 taught the predicate to tell them apart (`EquationBlock::Effectful` vs
`::Polymorphic`) and fixed the message, which used to call a row variable
effectful. The **verdict** was left unchanged deliberately. But the two are
different in kind: `Effectful` is a property of the operation that no carrier can
undo; `Polymorphic` is a property of the *declaration site* only.

Candidate shape, and it is not new here — 054 §3.4.1 already floats the analogue
for `requires` ("carrying the dictionary as an equation antecedent is a future
relaxation"): admit the law as a **conditional equation**, firing only where the
instantiated row is `{}`.

**Q1 makes the polymorphic refusal stronger, not weaker.** A row variable can be
instantiated to `Error`. So the current refusal is not merely conservative about
"an effect might run zero times" — it is protecting against the control-effect
case, where dropping the call changes the *answer*. Anyone relaxing this (WI-1050)
should note that "the instantiated row is `{}`" and "the instantiated row contains
no control effect" are different conditions, and only the first is obviously
sound for a rewrite that drops a call.

## Q4 — if conditional, where is the condition checked?

`docs/design/simp-rewrite-design.md` settles more of this than it looks:

- the engine is **type-directed, integrated with the typer** (§1), with "the
  typer over op-body occurrences" as a call site (§4.3);
- §6 already makes firing conditional on the receiver's sort — "a sort/spec rule
  applies iff `min_sort(receiver) <: S`".

So at the moment a rewrite is considered, **the carrier is known and
conformance is already being computed**. The row σ-instantiates off that same
carrier. An effect-row condition is one more test at a site that already
resolves the carrier for a different reason — not a new mechanism in a new
place.

Two constraints on any such move:

- **§4.4 — the semantic decisions belong to the shared core.** `apply_eq_rules`
  (resolve.rs) is the other call site running the same rewriter. A condition in
  one and not the other is the "two derivations must agree" defect (WI-860,
  WI-1016).
- **A decision not to fire is silent.** Moving a check from formation to firing
  turns one loud load-time refusal into a per-redex non-event. An author whose
  law never applies would get no rewrite and no diagnostic — the silent skip the
  repo forbids. Any relaxation needs a loud channel for "this redex declined,
  here is why".

## Q4a — a worked example: `head(insert(xs, e))` cannot raise

The best case for effect *elimination*, because the effect is already written as
a **guarded** atom and the guard is refutable by construction:

```anthill
operation head(xs: List) -> xs.T effects { Error[EmptyStream] :- isEmpty(xs) }
operation insert(c: List, elem: T) -> List = cons(head: elem, tail: c)
```

`insert` prepends a `cons`, so `isEmpty(insert(xs,e))` is **false**, so the
guard is refuted, so the `Error` is **not in the row**. The semantics is already
written down — `node_occurrence.rs`: a guarded effect atom is "present iff
`guard` is not refuted at the …" (proposal 048 / WI-478).

**Measured: it does not discharge today.**

```
operation probe(xs: List[T = Int64], e: Int64) -> Int64 = xs.insert(e).head()
  -> error: type mismatch in probe.effects (op-effects):
     expected declared: [], got undeclared effect: Error[T = EmptyStream]
```

And the reason is specific, not a missing mechanism. **WI-067 (delivered) is the
two-tier discharge**: refute `σ(G)` from **Γ** — the flow-sensitive logical env —
plus ground eval and the KB. Γ's producers are `if`-branch conditions, `match`
arm facts and guards. `xs.insert(e).head()` has **no `if` and no `match`**, so Γ
says nothing about the argument.

What would close it is exactly the user's word for it — *abstract
interpretation*: the argument is a **call**, and its body-derived equation
(`insert(c,e) <=> cons(head: e, tail: c)`, WI-580) is what says the result is a
`cons`. So the missing link is **Γ learning a fact from a callee's derived
equation**, not a new refutation engine. That is a well-scoped question: can
`refute_guard` reach WI-580's derived equation for the operation in argument
position?

**The open design question underneath this is PRE-OPENED as WI-1051**: does the
abstract interpreter maintain and propagate a **Γ** — an environment of facts
about the intermediate values it computes — or does Γ stay a purely syntactic
flow environment fed only by branch conditions? Effect discharge is one consumer;
the value-precondition check (WI-539/WI-602), in-body proofs (WI-538), WI-537's
two deferred Γ producers, and the `effect_present`/`effect_absent` reification below
are others. It is a shared substrate, so its shape wants deciding against several
consumers at once rather than being retrofitted for this one — which is why it is
pre-opened rather than open.

**And it is the effect-elimination rule Q3 said we do not have.** Q3 deferred the
polymorphic case because "effect-elimination rules … are not known". This is one,
for the *guarded* case: refute the guard, drop the atom. It does not help the
row-**variable** case (`effects E` has no guard to refute), so Q3's decision
stands — but it marks where the boundary actually is.

### a vocabulary question this raises

Should the rule dictionary gain `effect_present` / `effect_absent` as **predicates**?
The subject is the **effect row**, and the question is **binary**: the row is
*present* (non-empty) or *absent* (empty). Not "does it carry effect `E`" —
per-label questions are a different, later thing.

Guarded effects already condition an *effect* on a *predicate*
(`Error[EmptyStream] :- isEmpty(s)`); this is the dual — conditioning a *rule* on
the row — and it has no spelling today.

**There are TWO predicates here, not one, and they are not interchangeable.** A
first draft of this section wrote `effect_absent(head(insert(?x,?e)))` with no
effect argument, which is wrong for the case that motivated it: `head`'s row is
`{ Error[EmptyStream] :- isEmpty(xs), s.E }`, so even after the guard is refuted
`s.E` remains. The whole-row claim is false there, while the thing we actually
want — that `Error[EmptyStream]` is gone — is true.

```
-- (a) PER-LABEL. Is this effect in the term's row? What guard discharge needs.
effect_absent(head(insert(?x, ?e)), Error[EmptyStream])

-- (b) WHOLE-ROW. Is the row empty at all? What the [simp] gate asks.
row_empty(insert(?c, ?x))

rule isEmpty(insert(?c,?x)) <=> false :- row_empty(insert(?c,?x))
```

Which one each consumer wants, so the choice is not made by accident:

| consumer | needs |
|---|---|
| guarded-effect discharge (Q4a, WI-067) | **(a)** — drop one atom, leave the rest of the row alone |
| the `[simp]` formation gate | **(b)** — nothing may be dropped, so the row must be empty |
| Q1's law precondition | **(b)** — the law is about discarding the whole computation |
| Q7's "both sides carry the same row" | neither — that needs row **equality**, a third thing |

(b) is expressible as (a) universally quantified, or kept primitive; worth
deciding, since (b) is the one that already exists internally.

**And the argument is a TERM, analysed, not a value computed.** `effect_absent`
asks about a term's *typing*, so it is a reflective predicate — nearer
`anthill.reflect` than an ordinary goal. That is not alien here (occurrence-valued
operations and the `Term`/`KB` reflect surface exist), but it decides where the
predicate lives and what it may be applied to.

### naming

**`effect_present(X, E)` / `effect_absent(X, E)`**, chosen for a reason beyond
taste: *present* is already this system's own word for exactly this
property — a guarded atom is "**present** iff `guard` is not refuted"
(`node_occurrence.rs`, proposal 048). Reusing it keeps one vocabulary instead of
minting a second for the same idea.

One caveat any name must survive: the pair is **not** a simple
positive/negative. Under the never-NAF discipline below, `effect_absent` requires
a *positive refutation* of the guard, so it means "provably cannot occur", not
"not observed" — and there is a third state, undetermined, where neither holds. A
name suggesting plain negation (`not_effect_present`) would mislead about that. If
the modality should be visible in the name itself, `effect_possible` /
`effect_impossible` says it outright at the cost of length.

### the guarded declaration IS the definition

The per-label predicate needs no new analysis, because a guarded effect atom is
already a Horn clause written in effect-row syntax. From the stdlib
(`int64.anthill:65`):

```anthill
operation div(a: Int64, b: Int64) -> Int64 effects { Error[DivisionByZero] :- eq(b, 0) }
```

reads directly as

```
effect_present(div(?a, ?b), Error[DivisionByZero]) :- eq(?b, 0)      -- the declaration, verbatim
effect_absent (div(?a, ?b), Error[DivisionByZero]) :- neq(?b, 0)     -- its REFUTATION
```

**Mind the polarity: `effect_absent` carries the refutation of the guard, not the
guard.** `Err :- eq(b,0)` says the error is present *when* `b = 0`, so absence is
conditioned on `neq(b, 0)`. Getting this backwards would license dropping the
error exactly where it fires.

And it must be a **constructive** refutation. WI-067 already decided this in the
same words: *"drop the guarded element only on a positive proof of ¬G (never
NAF)"*, and framed the whole mechanism as *"SLD refutation over the
effect-row-as-Horn-theory"*. So this section is not proposing a new predicate so
much as **naming one that WI-067's discharge already computes** — which is the
strongest argument for the reification, and also the reason it is cheap.

**What the Horn reading does NOT cover is exactly the boundary Q3 drew.** A
guarded atom has a clause. An *unguarded* atom (`s.E`, `{External}`) has none, so
there is nothing to refute; a row *variable* has none either. Both stay
**undetermined**, and under the never-NAF discipline neither predicate succeeds
there. The Horn reading therefore buys the guarded case and leaves the
polymorphic case exactly where Q3 put it — which is a consistency check on both.

Two things make this cheaper and more coherent than it first looks:

- **It reifies a predicate that already exists internally.** "Is this row empty?"
  is exactly what `effect_row_blocking_equations` computes today to decide the
  gate. Exposing it is a reification, not a new analysis.
- **Its polarity reproduces the Q3 decision instead of fighting it.** A binary
  predicate has *three* outcomes in practice — present, absent, and
  **undetermined** — and the undetermined case is precisely the polymorphic row
  (`E` is neither provably empty nor provably non-empty until a carrier binds
  it). Under the established polarity — "act on a DECIDED obligation, never on an
  UNDETERMINED one" (WI-602, WI-067/WI-292) — *neither* `effect_present` nor
  `effect_absent` should succeed there. That is the same refusal Q3 decided,
  arrived at from the predicate's own discipline.

Open: whether it is a genuine predicate over terms (needing the typer's row as a
queryable value) or sugar for an obligation. Either way it gives the row a
**reified** form — the same thing Q7's "both sides carry the same row" needs, and
the same thing an abstract Γ (WI-1051) would want. Three consumers, one
representation question; design it once.

## Q5 — where may a law be WRITTEN?

*(Retitled: the first version said "should a law be declarable where its row is
already concrete", which was jargon. "Declarable" = where you are allowed to
write it. "Row" = the effect row. "Concrete" = ground/known — `{}` or `{External}`
— as opposed to a variable like `E` or a projection like `s.E`.)*

The plain question: **the gate refuses the law on the spec, so where does it go?**

This is what works today, and the WI-1049 message now points at it: declare the
equation on a carrier whose own operations are pure — i.e. where the row is
already `{}` rather than a variable.

Measured on `List`, and it is *nearly* there: `List` **does** declare its own
`insert` (`operation insert(c: List, elem: T) -> List = cons(head: elem, tail: c)`,
list.anthill:254 — pure, no effects clause), so that leg passes. What it does not
declare is `isEmpty`; it imports `Stream.{isEmpty}`, whose row is `{s.E}` — the
receiver's effect parameter, projected. So the law placed inside `List` is
refused **once**, on `isEmpty` alone.

**And the proof-time reading is the uncontroversial part.** When a rule is applied
in a *proof*, after typing, the types in the rule are substituted and `{}` is read
as no-effect — so at that point there is nothing polymorphic left and nothing to
refuse. That is the same observation as Q2's proof arm and Q4's "check after
substitution": the difficulty is never at *use*, it is that the gate fires at
*declaration*, where the substitution has not happened.

Adjacent, unsettled: proposal 044 records that a derived rule for an operation
inherited via `requires` may mint a *distinct sort-local symbol* shadowing the
inherited one. Measured in WI-1049: writing `rule isEmpty(insert(?c,?x))` inside
`PersistentCollection` does **not** mint `PersistentCollection.isEmpty` — the
head bound to the inherited `Iterable.isEmpty`. Whether that is guaranteed or
incidental is 044's question, and Q5 leans on the answer.

## Q6 — what is a law *for*, in this system?

Underneath the rest. If laws are primarily **executable** (rewrite rules), the
effect gate is central and 054 is right to be strict. If they are primarily
**specification** — proof obligations, `using` citations, the relational views
WI-580 derives — then effect-freedom gates the *execution* of a law and should
not gate its *statement*.

The current design says both at once: `[simp]` is the enablement (so an untagged
law is pure specification and inert), yet formation is gated on effects for
tagged and untagged alike at the same site. Q1 is the narrow form of this
question; Q6 is why it keeps coming back.

Q1 adds a middle term the dichotomy was missing. Even read purely as
specification, a law over a **control**-effecting operation is not
unconditionally true — it holds on the defined path. So the answer is not
"specification ⇒ no effect gate"; it is that a law over an effectful operation
needs a **reading** (total? partial? effect-preserving?) before it needs a gate.
Pick the reading first, and what to check follows.

## Q7 — the monadic reading, and the reformulation it suggests

Proposal **047, "Effects as monads, realized by Filinski monadic reflection"**,
already puts this on a footing: *an effect **is** a monad*, with two channels
(047 §, lines 100–101)

```
reflect : M a -> a            -- inject a monadic value into the direct-style computation
reify   : (() -> a) -> M a    -- capture a direct-style computation as a monadic value
```

and "effect operation = `reflect`" (`throw(x) = reflect(Err x)`), "handler =
`reify`/`reset`". So an effectful operation is a Kleisli arrow that the
direct-style surface `reflect`s.

Read that way, the three spellings of "our" law are three different statements:

| | statement | valid when |
|---|---|---|
| value equation | `isEmpty(insert(c,x)) = false` | `M` is the **identity** monad — i.e. the row is `{}` |
| partly preserving | `insert(c,x) >>= isEmpty  ==  insert(c,x) >> pure false` | any `M`, **but only if `isEmpty` itself is pure** — the RHS keeps `insert`'s effect and drops `isEmpty`'s |
| fully preserving | `insert(c,x) >>= isEmpty  ==  insert(c,x) >>= \c' -> (isEmpty c' >> pure false)` | **any** `M` — both effects performed, in order, exactly as the LHS does |
| direct-style (anthill's actual surface) | `isEmpty(insert(?c,?x)) <=> false` | ? — the bind is implicit, so which of the above is it? |

(The middle row is not enough for *our* law: `Iterable.isEmpty` carries `{E}` too
— it "costs one `splitFirst` step", iterable.anthill says so. A form that keeps
`insert`'s effect and drops `isEmpty`'s is still dropping one. Only the last row
is unconditionally sound, and it is unconditionally sound precisely because it
performs every bind the LHS performs.)

**So the current gate is not really about effects.** Demanding an empty row is
demanding that the Kleisli category *collapse to* the value category — which is
exactly when the first row of the table is sound. That is a coherent position; it
was just never stated in these terms, which is why "an effectful operation is not
equational" reads as a claim about operations rather than about which category
the equation lives in.

**And it suggests a sharper well-formedness rule than the current one.** Anthill's
surface is direct-style: `xs.insert(1).isEmpty()` has no visible bind, so a
written law is a Kleisli equation in disguise. The trouble with
`isEmpty(insert(?c,?x)) <=> false` is then not that `insert` is effectful — it is
that the **two sides do not carry the same effect row**: LHS `{Effect}`, RHS `{}`.
The law is asserting the effect can be discarded, and *that* is what makes the
rewrite drop the call.

Candidate rule, to be argued rather than assumed:

> `<=>` is well-formed only when both sides carry the **same effect row**.

Check it against everything measured so far:

- **pure carrier, own pure ops** — both rows `{}`. Accepted. ✓ (matches today)
- **concretely-`External` op** — LHS `{External}`, RHS `{}`. Refused. ✓
  (matches 054, and for the *right* reason: the RHS discards the row)
- **effect-polymorphic spec** — LHS `{Effect}`, RHS `{}`. Refused. ✓ (matches
  today, but the diagnostic becomes a **row mismatch**, which is explicable and
  actionable, rather than a claim that `insert` is effectful — the WI-1049 defect)
- **the sound spelling** — an RHS that carries the same row (the Kleisli form, or
  whatever direct-style notation anthill grows for it) is admitted with **no
  effect gate at all**, because nothing is dropped.

It also lands where Q4 says it should: rows are computed **during typing**, which
is where firing already happens.

**The cost, measured rather than guessed: side-rows do not exist today.** The
typer computes effect rows for operation *bodies* and for arrow types; nothing
computes a row for the LHS/RHS of an equational rule. The observed diagnostic is
`type mismatch in isEmpty.effects (op-effects)` — an **operation**-keyed check
that walks the functors a rule mentions (`check_simp_effectful_ops`), which is
why it can only ever name an operation and never a mismatch. So the candidate
rule is not a re-wording of the present check; it needs a quantity the typer does
not currently produce. That belongs in the comparison, on both sides of it: it is
the reason the rule is expensive, and also the reason it would be *worth* it —
side-rows are what make a "the two sides disagree" diagnostic possible at all.

## Q8 — the surface cannot spell the sound law, and that may settle it

Q7 ends with a "fully preserving" form that is unconditionally sound. Can it be
written? **In the present surface, no — and the reason is structural, not a
missing feature.**

In direct style, `isEmpty(insert(c,x))` is not an application of `isEmpty` to a
value. When `insert` is effectful it is

```
insert(c, x)  >>=  \c' -> isEmpty(c')
```

— the bind is **implicit in the nesting**. And an effect operation is exactly one
that may *omit* that bind: `raise` never invokes the continuation
(`Err v >>= f = Err v`), `Branch` may invoke it zero or many times. So the
argument position of an application is a place where a continuation is
implicitly created and may be implicitly discarded.

Now the matcher. `simp-rewrite-design.md` §"Matcher ≠ typer": **"a `[simp]` rule
LHS is a *functor-application* pattern."** Matching `isEmpty(insert(?c, ?x))`
binds `?c` and `?x`. It does **not** bind the continuation — there is no pattern
variable for "the rest of the computation", because in direct style the
continuation is not a subterm, it is the *nesting itself*.

Therefore the RHS can only be built from `?c`, `?x` and constants. The
fully-preserving form needs to name `\c' -> …`; the surface gives it no name. **The
only laws of this shape the syntax can express are exactly the ones that discard
the bind.**

That reframes 054's formation-time refusal. It is not merely the conservative
choice among several sound ones — with this surface, the effect-dropping form is
the *only* form expressible, so refusing it refuses the only thing that can be
said. "The gate belongs at load-time tag validation" follows from the syntax, not
just from caution.

Consequences, and they are the useful part:

- **WI-1050 stays sound but stays narrow.** Deciding on the substituted row can
  only ever admit the case where the row grounds to `{}` — precisely the case
  where there is no bind to preserve. That is consistent with everything above,
  and it is the whole of what a row check can buy.
- **The real request is a surface one.** "Let me state this law about an
  effectful operation" is a request for a *sequencing form* — a way to write the
  bind, or a matcher that binds the continuation — not for a weaker gate. That is
  a much larger question than the gate, and 047's `reflect`/`reify` are where it
  would start: they are the only place the monad is already spelled.
- **054's three verbs are one property.** DROPS = bind invoked zero times
  (`Error`, empty `Branch`); DUPLICATES = invoked more than once (`Branch`);
  REORDERS = order-sensitive (state). So "duplicates, reorders, or drops" is not
  a list of three hazards but one condition — *the bind is invoked exactly once,
  in place* — and it is the same condition 054's own decline list needs for
  memoization and CSE (§, "any future memoization or CSE joins the same decline
  list"). One property, several consumers; worth naming once rather than
  restating per consumer.

## References

WI-1049 (the classification and message) · WI-1050 (check after effect
substitution) · proposal 054 §"Consumers that must decline it — loudly"
(WI-698/WI-702) · `docs/design/simp-rewrite-design.md` §1/§4.2/§4.3/§4.4/§6 ·
proposal 043 (`[simp]`/`[unfold]`) · WI-881/WI-884/WI-885 · WI-818 · WI-580 +
`docs/design/abstract-interpreter-and-rules.md` §3.3 · proposal 045 +
WI-357/WI-365 · proposal 044 (inherited-op rule attachment) · WI-757 (the
`[unfold]`/`[simp]` asymmetry, measured)
