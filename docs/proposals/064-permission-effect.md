# 064: `Permission[X]` — authority as an effect, at the point of acquisition

## Status: Draft (2026-08-25). No implementation. Design note: `examples/guardians/docs/design/effects.md`.

## Relates to: 054 (`External`, the orthogonal axis), 045 (effect rows — `Permission` is an ordinary member; `-Permission[?]` is the one open question), 047 (handler discharge is what supplies a grant), 048 (the sandbox case simplifies once the axes separate), `docs/kernel-language.md` §8.6 (`internal` — what makes containment structural), WI-20260823-VM3YB (the effect registration is checked at no site — prerequisite).

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

The negative form follows and needs no rule of its own: `-Permission[Y]` forbids
`Permission[X]` for every `X <: Y`, because an `X` capability IS a `Y`
capability. A denial therefore cannot be evaded by declaring a sub-capability,
which is what makes `-Permission[Model]` worth writing.

Where no subtyping is declared among capabilities — the expected case, and the
whole of a first implementation — the rule degenerates to name equality.

## Surface

No syntax change, and the registration is today's:

```anthill
  fact Effect[T = Permission[?]]
```

Rows are ordinary: `effects {Permission[FileSystem]}`,
`effects {External, Error}`, `effects {-Permission[Model]}`.

## Not in scope

- **Release, revocation and lifetimes.** A capability is minted and never given
  back. Nothing here pairs an acquire with a release, and no locking is implied.
- **A general object-capability discipline.** One effect plus `internal` for
  containment; no ambient-authority elimination across the language.
- **The `External[mode]` split.** An unfiled idea in the design note, independent
  of this one; neither blocks the other.
- **Preventing a capability object from outliving the extent that granted it.**
  It can. See open question 4.

## Open questions

1. **Does a lacks-constraint admit a variable argument?** `-Permission[?]` —
   *acquires no authority at all* — is the general denial and the claim a checker
   most wants to make about generated code. It depends on neither a capability
   order nor a root: `?` ranges over every capability, so it holds whether or not
   anyone has defined one. A rooted `-Permission[Root]` is an alternative only
   where a root EXISTS and every capability descends from it — two conditions
   this proposal does not assume — so it is not a substitute. Whether 045's row
   algebra carries a variable in a lacks-constraint is UNMEASURED, and is the one
   thing that would force falling back to enumerating
   `-Permission[Model], -Permission[FileSystem], …`.
2. **Does handler discharge come free?** 045 §5.5 makes discharge purely
   type-level. If that holds here, a grant is an ordinary handler with no kernel
   semantics — the cheapest part of the design if true, a hidden cost if not.
3. **Does the capability handle have identity?** The check is idempotent within
   a grant's extent, so the *effect* dedups. Whether the *call* is CSE-able is
   separate: `open()` also mints an object, and two calls make two values.
4. **A granted object outliving its handler.** If grants are handler-supplied,
   the grant is scoped and the object minted inside it is not. Whether that is
   acceptable (it is, under an ocap reading) or wants an obligation is open.

## Prerequisite

WI-20260823-VM3YB. `fact Effect[T = X]` is documented as the effect registration
and checked at no site — measured there: deleting a registration leaves its suite
green, and a `fact` whose functor does not resolve loads silently. Adding an
effect whose whole purpose is a negative claim, onto a registration nothing
validates, means a misspelled `Permision[Model]` is a silent new effect and
`-Permission[Model]` still passes.
