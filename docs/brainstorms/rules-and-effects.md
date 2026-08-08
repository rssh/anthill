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

`List` does not declare its own `insert`/`isEmpty`, so in the stdlib as it stands
there is nowhere to put this law where it would fire.

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

## Q3 — is "effect-polymorphic" a third answer, not a shade of "effectful"?

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

## Q5 — should a law be declarable where its row is already concrete?

This is what works today, and the WI-1049 message now points at it: declare the
equation on a carrier whose own operations are pure. The gap is that inheriting a
spec operation gives you no place to attach a carrier-specific law about it —
`List` inherits `insert`/`isEmpty` and declares neither.

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

## References

WI-1049 (the classification and message) · WI-1050 (check after effect
substitution) · proposal 054 §"Consumers that must decline it — loudly"
(WI-698/WI-702) · `docs/design/simp-rewrite-design.md` §1/§4.2/§4.3/§4.4/§6 ·
proposal 043 (`[simp]`/`[unfold]`) · WI-881/WI-884/WI-885 · WI-818 · WI-580 +
`docs/design/abstract-interpreter-and-rules.md` §3.3 · proposal 045 +
WI-357/WI-365 · proposal 044 (inherited-op rule attachment) · WI-757 (the
`[unfold]`/`[simp]` asymmetry, measured)
