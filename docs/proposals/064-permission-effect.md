# 064: `Permission[X]` — authority as an effect, at the point of acquisition

## Status: IMPLEMENTED (2026-08-26, WI-20260825-CBRSW). Spec: `docs/kernel-language.md` §5.5. Kind and variance: `stdlib/anthill/prelude/permission.anthill`; drive: `rustland/anthill-core/tests/include/wi_cbrsw_permission_effect_test.rs`. Design note: `examples/guardians/docs/design/effects.md`.

> **What the implementation cost, and it is the proposal's own claim confirmed.** The
> row half needed NOTHING: `Permission[X]` rides the existing algebra, both not-widen
> legs judge it unchanged, and `internal` already contains the constructor. The
> contravariance needed no kernel code either — it is a DECLARED fact
> (`fact Contravariant(sort: Permission, param: T)` in `permission.anthill`, proposal 035), and the typer's
> `check_binding_by_variance` reads it. Exactly one typer rule was missing, and it was
> the NEGATIVE form: the present-vs-absent verdict compared labels by EQUALITY, so
> `-Permission[Model]` beside an acquired `Permission[GptModel]` loaded clean —
> measured, not predicted. `typing::label_violates_absence` now decides it directionally
> (`A <: P`, and only that way round), which is a general rule about lacks constraints
> that this label is the first to need.

## Relates to: 054 (`External`, the orthogonal axis), 045 (effect rows — `Permission` is an ordinary member; the lacks-constraint verdict is the one thing it needed sharpened), 035 (declared variance — where the contravariance rule actually lives), 047 (handler discharge is what supplies a grant, and it came free), 048 (the sandbox case simplifies once the axes separate), `docs/kernel-language.md` §5.5 (the implemented rule) and §8.6 (`internal` — what makes containment structural), WI-20260823-VM3YB (the effect registration, prerequisite — delivered).

## What it is

`Permission[X]` is an effect denoting the **runtime consultation of an ambient
grant** for capability `X`. The consultation can refuse.

It is written on the operation that **mints** a capability object, and nowhere
else. Holding the object is the authority thereafter; the effect marks the
moment that authority was checked.

## Example

A filesystem capability. The constructor is `internal`, so `open` is the only
way to obtain an `FsRoot`:

```anthill
sort FsRoot
  internal entity fs_root

  operation open() -> FsRoot
    effects {Permission[FileSystem]}
end

operation write_file(root: FsRoot, path: String, content: String) -> Unit
  effects {External}
```

`write_file` carries no `Permission`: the check already happened, and the
`FsRoot` in its signature is the evidence.

The motivating consumer, from the guardians example. A generated agent's
checker must provably not consult a model — today that holds only because no
`Oracle` is passed to it, which the signature does not say:

```anthill
operation check(self: C, src: Source, spec: Spec) -> CheckResult
  effects {External, Error, -Permission[Model]}
```

Now it does say it. The checker cannot mint a model capability, and takes none
as a parameter, and both halves are readable off the declaration.

## Rules

**The label goes on the mint, never on the use.** An operation that consumes a
capability object it was handed carries whatever it carries and no
`Permission`. This is the whole design: it is what makes the label rare (a
program introduces far fewer capabilities than it uses), and it is what makes
the effect an event rather than a standing attribute of code.

**Containment is structural.** A capability object's constructor is `internal`,
which §8.6 makes the only hide gate — hiding a name from cross-scope resolution
and from field projection alike, with top-level code outside every declaring
scope (WI-977). So the constructor cannot be called from outside its sort, and
the `Permission`-carrying operation is the sole introduction. Without this the
effect is advisory: a program writes `fs_root()` and skips the check.

**`Permission` and `External` are orthogonal.** They answer different questions
about one call — *may I* versus *what licence does the runtime have here* — and
combine freely:

| | `External` | no `External` |
|---|---|---|
| `Permission[FileSystem]` | the real filesystem root | an in-memory root, still gated |
| — | reading through a handle you were passed | pure |

A test double occupies the top-right cell: the same authority path exercised,
nothing leaving the process.

**Licences taken.** The effect's observable is a possible refusal rather than a
value, which is what distinguishes it:

| | `Permission[X]` | why |
|---|---|---|
| constant-fold / equational use | ✗ | consults ambient state |
| reorder across the guarded operation | ✗ | moves the call across the gate |
| **drop when the result is unused** | ✗ | dropping the check drops the refusal |
| dedup within one grant's extent | ✓ | no revocation inside an extent |

**Subsumption is ordinary set inclusion.** `Permission[X]` is a row member like
any other, so the existing not-widen rule decides everything:

```
{}  <:  {Permission[X]}  <:  {Permission[X], Permission[Y]}
```

An operation acquiring nothing is usable where acquiring `X` is allowed; one
acquiring only `X` is usable where `X` and `Y` are. The converse is the
widening the override check already refuses — code declared `{Permission[X]}`
may not acquire `Y`. Two distinct capabilities coexist in a row by set union;
there is no join and no rank.

**A provider cannot grant itself a permission.** This is the property the
guardians harness depends on, and it needs nothing new: both legs of the
existing not-widen check apply to `Permission[X]` because it is an ordinary row
member. The spec's row bounds the provider's DECLARED row, and the declared row
bounds the row INFERRED FROM ITS BODY. So a generated implementation of

```anthill
operation run(self: C, box: Mailbox, llm: Llm) -> Report
  effects {External, Model, Error}
```

can neither declare `Permission[FileSystem]` — a widening, refused — nor mint
one in its body while declaring the spec's row, which the body leg reports as an
undeclared effect. The permission budget is fixed by the party that wrote the
spec, which is the whole point of putting authority in the row.

**`Permission` is contravariant in its capability.**

```
X <: Y   ⟹   Permission[Y] <: Permission[X]
```

A permission is a DEMAND, and demands weaken as their subject widens: requiring
`Y` is satisfied by anything that is a `Y`, so it asks less than requiring the
more specific `X`. The safety consequence is the test. With `AdminFs <: Fs`, a
spec granting `Permission[AdminFs]` accepts an implementation that acquires only
`Permission[Fs]` — it takes less — while a spec granting `Permission[Fs]`
REFUSES one acquiring `Permission[AdminFs]`. Covariance inverts exactly that and
admits privilege escalation.

The negative form follows: `-Permission[Y]` forbids `Permission[X]` for every
`X <: Y`, because an `X` capability IS a `Y` capability. A denial therefore
cannot be evaded by declaring a sub-capability, which is what makes
`-Permission[Model]` worth writing.

> **Correction from the implementation.** This paragraph said the negative form
> "needs no rule of its own". IT DID, and it was the only thing that did.
> Present-vs-absent was decided by label EQUALITY at every site, so
> `-Permission[Model]` beside an acquired `Permission[GptModel]` loaded clean —
> measured.
>
> AND THE RULE IS THIS LABEL'S, not a general one — the first cut made it general
> and review measured it backwards. Entailment ("performing `P` performs `A`") runs
> COVARIANTLY in the capability, while subsumption runs contravariantly; the two are
> opposite here and coincide for an ordinary nominal label, so no reading of the
> subsumption order serves both. Under the general version, `-Color` beside a present
> `Red` (with `Red provides Color`) still loaded clean, while `-Red` beside a present
> `Color` — admissible, and clean before — was newly refused. The verdict therefore
> compares the capability ARGUMENTS and runs only for `Permission`; what a lacks
> constraint means for an ordinary label is left open, being older and wider than this
> proposal.
>
> A SECOND HOLE, from the same review: writing the label PRESENT beside its own denial
> (`{Permission[Model], -Permission[Model]}`) silenced both legs at once and loaded
> completely clean. That is refused at load now, for every label — the row is
> uninhabitable — with a guarded occurrence still deferring to discharge.

Where no subtyping is declared among capabilities — the expected case, and the
whole of a first implementation — the rule degenerates to name equality.

## Surface

No syntax change, and the registration is today's — written ONCE, by the prelude
(`stdlib/anthill/prelude/permission.anthill`), since the KIND is kernel business
while the CAPABILITY is project vocabulary:

```anthill
  fact Effect[T = Permission[?]]
```

Rows are ordinary: `effects {Permission[FileSystem]}`,
`effects {External, Error}`, `effects {-Permission[Model]}`. A project declares
`sort FileSystem`, `sort Model` and any order among them (a constructor-less sort is a
spec; `provides` is the is-a) and writes nothing else.

## Not in scope

- **Release, revocation and lifetimes.** A capability is minted and never given
  back. Nothing here pairs an acquire with a release, and no locking is implied.
- **A general object-capability discipline.** One effect plus `internal` for
  containment; no ambient-authority elimination across the language.
- **The `External[mode]` split.** An unfiled idea in the design note, independent
  of this one; neither blocks the other.
- **Preventing a capability object from outliving the extent that granted it.**
  It can. See open question 4.

## Open questions — answered by the increment

1. **Does a lacks-constraint admit a variable argument?** — ANSWERED, and the
   question turned out to have the wrong subject. `-Permission[?]` parses and loads
   and CONSTRAINS NOTHING: an undecided argument leaves the pair undecided, so the
   verdict withholds exactly as it does for a row parameter. But the general denial
   does not need a variable at all — a **bare** `-Permission` is it. A bare label
   subsumes every application of it, so `-Permission` forbids `Permission[X]` for
   every `X`, assuming neither a capability order nor a root, which is precisely
   what the question asked for. Enumerating
   `-Permission[Model], -Permission[FileSystem], …` was never necessary.
   `a_bare_permission_denial_forbids_every_capability` drives it.

   The variable spelling stays a TRAP, and is pinned as one
   (`a_variable_argument_in_a_lacks_constraint_constrains_nothing`). Closing it
   means telling an ANONYMOUS wildcard apart from a rigid type parameter
   (`-Error[T]`, where an undecided argument must stay undecided) inside 045's row
   algebra — a question about every label rather than about this one, with no
   population measured: no `.anthill` in the tree writes a variable-carrying lacks
   atom.
2. **Does handler discharge come free?** — ANSWERED YES, and it is the cheapest
   part of the design as hoped. A grant is §5.5's ordinary handler shape with no
   kernel semantics of its own: a body performing `{Permission[Model], Error}` under
   `with_model_grant[Rho](body: () -> X @ {Permission[Model], Rho}) -> X @ {Rho}`
   has the residual row `{Error}`, and a call claiming to discharge the residual too
   is refused. `a_grant_is_an_ordinary_handler_and_discharges_the_label` drives both
   halves; the second is what makes the first non-vacuous.
3. **Does the capability handle have identity?** — ANSWERED NO for the shape this
   proposal's own example uses, and the CSE question is therefore VACUOUS rather
   than answered in the affirmative. `internal entity fs_root` is NULLARY, hence a
   constant of its sort, so two mints produce two structurally-equal values and
   there is nothing for a dedup to observe. A capability that wants identity must
   carry it in a FIELD, and nothing in this increment supplies freshness to put
   there. The effect still does not LICENSE dedup outside one grant's extent (the
   licence table above); nothing enforces that today because nothing optimises
   effect-carrying calls.
4. **A granted object outliving its handler.** STILL OPEN, and untouched: grants are
   handler-supplied and scoped, the object minted inside one is not, and nothing
   pairs an acquire with a release. Listed under *Not in scope* above, and the
   increment neither closes nor worsens it.

## Prerequisite — discharged

WI-20260823-VM3YB, DELIVERED 2026-08-25. `fact Effect[T = X]` was documented as the
effect registration and checked at no site — measured there: deleting a registration
left its suite green, and a `fact` whose functor does not resolve loads silently.
Adding an effect whose whole purpose is a negative claim, onto a registration nothing
validates, would have meant a misspelled `Permision[Model]` was a silent new effect
while `-Permission[Model]` still passed. `typing::check_effect_registration` now
refuses an unregistered label at load, and the prelude's
`fact Effect[T = Permission[?]]` is what makes `effects {Permission[FileSystem]}`
admissible at all.

## What was NOT taken up

**The guardians example still spells its model effect on the USE.** `Llm.complete`
carries a bare `Model` label and `Checker.check` denies it with `-Model`, which is the
pre-064 shape and the one this proposal argues against — the label belongs on the mint,
with the `Llm` carrier as the evidence thereafter. Migrating it means giving `Llm` an
`internal` constructor and a `Permission[Model]`-carrying mint, dropping `Model` from
five files' rows, and reworking the `bad_checker` fixture (whose body-leg refusal is
`complete`'s `Model`) — together with the design notes that argue the current shape.
That is a restructure of a running example's central safety argument, not an
application of this proposal, so it is left as separate work. Nothing in the kernel
capability waits on it.
