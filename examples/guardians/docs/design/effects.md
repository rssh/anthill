# What the guardians example asks of the effect vocabulary

**Status:** Design argument (2026-08-22). Nothing measured — unlike
[`high-level-api.md`](high-level-api.md) §8.1, this note is reasoning, not
runs. Companion to [proposal 054](../../../../docs/proposals/054-external-effect.md).

## The test every candidate has to pass

054 fixes the admission rule, and it is strict:

> Effects carry semantics; carriers carry authority. The row answers the
> machine's question — *what may I still assume and transform?* — and every
> external capability revokes exactly the same licenses, so distinguishing
> them in the row adds nothing the machine can use. The question the
> distinctions *do* answer — *what may this code reach?* — is **authority**,
> and authority lives in **values**.

So a candidate effect earns its place only by revoking a **distinct machine
license**. "This code talks to a model" is authority. "This value came from an
attacker" is provenance. Neither is an effect.

An agent framework is the hostile case for that rule, because it is exactly the
domain where the temptation to mint capability labels is strongest. Running the
guardians example against it is therefore worth something as evidence about
054, independent of the example.

## Six candidates the rule rejects

**`LLM` / `Model`.** Semantics: `{External, Error}`, and nothing more. Two
calls may disagree with no tracked `Modify` between them, no replay is sound,
the result is not equational — that is the whole increment, and `External`
already names it. *Which* model, with *what* tool access, is authority, so it
rides in the carrier the operation takes. The `summarize` signature in
`high-level-api.md` §6.2 carries no model-specific label and loses nothing.

**`Tainted` / `Reads[label]`.** Provenance of a **value**, and a row describes
an **operation**. Measured to work as a type parameter instead
(`high-level-api.md` §8.1), so this one is not merely rejected in principle —
the alternative is running.

**`Approval`.** Splits cleanly into two things that already exist. Asking is
`{External, Suspend}`: it goes outside the process and it may block. Having
been approved is a **value** — the unforgeable `Approval` token of
`high-level-api.md` §6.2 — which is 054's "authority lives in values" applied
verbatim.

**`Budget` / `Cost`.** A resource whose state changes, which is `Modify[b]` on
a cell. The existing mechanism fits exactly, and a token budget threaded as
tracked state is *better* than a row label, because the row cannot carry a
quantity.

**`Trusted` / `Unverified` on a result.** Trust is metadata (§7.1), attached to
facts and already ordered. Nothing about it changes what the machine may
transform.

**`PcTaint`** — the implicit-flow label, for control steered by untrusted
content. This is the one worth dwelling on, because in a *conversational* agent
it would be unavoidable: the model reads an email and that email decides which
tool runs next. Plan-then-verify **removes the need for the label** rather than
typing it, because control flow is fixed before any content is read. The right
response to a hard effect was to make it unrepresentable, which is worth saying
out loud precisely because the effect system was the obvious place to reach.

Six candidates, six rejections, and the example is not weakened by any of them.
That is the note's main result: **the challenge motivates no new capability
labels**, and 054's "one effect, not one per capability" holds up under the
case designed to break it.

## The one thing that does not fit: `External` is one label doing three jobs

The gap is not a missing capability. It is that `External` bundles three
operations whose license sets genuinely differ, and the guardians architecture
is a staging discipline over exactly that difference.

| license | reading the world | writing it | writing it irreversibly |
|---|---|---|---|
| replay / re-run | ✗ | ✗ | ✗ |
| reorder | ✗ | ✗ | ✗ |
| dedup / CSE | ✗ | ✗ | ✗ |
| equational use | ✗ | ✗ | ✗ |
| perform under `Branch` | ✗ | ✗ | ✗ |
| **drop when the result is unused** | **✓** | ✗ | ✗ |
| **retry after a failure** | **✓** | **✓** | ✗ |
| **unwind when a later step fails** | n/a | **✓** | ✗ |

Three cells differ, and each is decision-relevant here.

**Dropping an unused read is sound.** A verified plan whose fetch step feeds
nothing can be pruned. Under one `External`, the pruning is illegal.

**Retry after failure is the sharpest one.** `External` revokes replay *for
optimization* — 054's table is about CSE, reordering, and dropping. It does not
speak to replay *for recovery*, and the two come apart: re-issuing
`recent_issues` after a timeout is sound, and re-issuing `send_email` after a
timeout may send the message twice. An agent executor has to make this call on
every step of every plan, and today the row does not tell it which kind of step
it is looking at.

**Compensation is real, and 054 slightly overstates its absence.** "There is no
`register_undo` for the world" is true of `send_email` and false of
`create_issue`, which has `close_issue`. A compensable external write can sit
inside a region that unwinds on later failure; an incompensable one cannot.
That is a transformation license, so by 054's own test it belongs in the row.

### Spelling: a mode parameter, not three labels

Effects already take bracket arguments (`Modify[target]`, `Error[type]`), so:

```
External[Read]      -- depends on outside state; changes nothing
External[Write]     -- changes it, and a compensating action exists
External[Commit]    -- changes it irreversibly
```

This keeps "one effect, not one per capability" **literally** true, because the
argument is a *mode*, not a capability. `fetch_mail` and `recent_issues` are
both `External[Read]` and differ only in the carrier they take, which is where
054 says the difference belongs.

The payoff for this example is one sentence: **the set of operations that must
be gated by a discharged obligation before they run is exactly the
`External[Commit]` set**, readable off the row. Meijer's architecture maintains
that set as a hand-written allowlist of "tools with potentially irreversible
side effects"; here it is derived. `high-level-api.md` D5 currently rests on
054's blanket `Branch × External` rule to force generate→verify→execute; with
the mode it rests on something sharper, since only the `Commit` tier needs to
wait for the proof.

Guarded effects (proposal 048) then give dry-run mode for free, and the
semantics line up without straining — 048 states that "the same effect label
may also occur unconditionally; refuting one guarded occurrence never removes
the unconditional occurrence":

```
operation send_email(to: Address, body: Text[Trust = Public]) -> Unit
  effects {External[Write], Error, (External[Commit] :- not(sandboxed()))}
```

In a sandbox the `Commit` tier is refuted and the operation is an ordinary
compensable write; in production it is not refutable and the obligation gate
applies. The same declaration serves the test harness and the deployment.

### The open question — which families answer

A row is a **set**, and `Modify[a]` and `Modify[b]` coexist in one because `a`
and `b` are distinct resources. `External[Read]` and `External[Write]` must
**not** coexist that way — an operation that does both is `External[Write]`,
full stop. So the mode is a **rank**, not a target, and row union has to take
the **join** rather than keep both members:

```
merge(External[Read], External[Write])  =  External[Write]
```

with `Read ⊑ Write ⊑ Commit`. Whether 045's row algebra can carry a label whose
arguments join, alongside labels whose arguments stay distinct, is the question
that decides whether this is a small change or a large one.

That question is the reason the next section exists. Asking one label to carry
a join while its neighbours carry set union is a special case; asking each
**family** to declare its algebra is a structure, and the mode split falls out
of it rather than being bolted on.

## Families: a row per family — and the label that came out of it

> **Reconciliation with proposal 064 (2026-08-25).** `Permission[X]` was found
> here, while asking what a `User` family would have to hold, and is now filed as
> [064](../../../../docs/proposals/064-permission-effect.md) — **without**
> families. It is an ordinary row member there: set-inclusion subsumption, both
> legs of the existing not-widen check, no family-indexed algebra. So this
> section is the note's exploration and the record of where the label came from;
> 064 is its specification, and the two must not be read as one proposal.
> Families remain unfiled, and nothing in 064 waits on them.

The six rejections above were all of the form "this is authority, not
semantics, so it does not belong in the row". That verdict is right about the
**kernel** row and wrong about what a project needs, and the gap shows up the
moment §3 of [`high-level-api.md`](high-level-api.md) makes the deliverable a
*generated program*.

### What forces it: a lacks-constraint is a claim a carrier cannot make

The strongest safety claim about a generated agent is a **negative** one:

```anthill
operation triage(box: Mailbox) -> Report
  effects {External[Read], Error, -Model, -External[Commit]}
```

`-Model` says the generated body provably never consults a model. Withholding
a carrier prevents the reach, but it says so *nowhere in the contract* — a
reader must audit a parameter list, and a reviewer of generated code must audit
it again on every regeneration. 045 already has `-label` for exactly this, and
nothing has used it yet, because there has been nowhere for a project-defined
label to live. §5.5 gestures at the hole — "users can define additional effect
kinds; the kernel stores and propagates them but only interprets the well-known
ones" — without saying where they go or how they combine.

This is the honest update to the six rejections: they stand **as kernel
effects**, and a user family gives the useful subset of them a home as project
vocabulary that the kernel threads without interpreting.

### What a family owns

A family is worth having only if it owns things that currently force every rule
to case-split on the label. Five qualify:

| | State | Control | World | Permission | User |
|---|---|---|---|---|---|
| members | `Modify[r]` | `Error[E]`, `Suspension`, `Branch` | `External[mode]` | `Permission[X]` | project labels |
| algebra | set union over distinct resources | set union over distinct payloads | **join** over a rank | set union over distinct capabilities | set union |
| scope obligation | yes — 046's region elimination | none | none | none | none |
| **droppable when unused** | yes, for a fresh non-escaping region | n/a | `Read` yes; `Write`/`Commit` no | **no** | per label |
| interpretation | `StateT` | `ExceptT` / `ContT` / `LogicT` | host binding | ambient grant, may refuse | none |

`Permission`'s column is here because it is what forced the droppability row.
064 claims no family; the row below is this note's finding about the TABLE, not
a dependency of the proposal.

**The droppability row is new, and `Permission` is why it has to be there.** The
opening table of this note — replay, reorder, dedup, drop-when-unused — is
written only for `External`'s three modes, and the family table records
algebra, scope and interpretation but not droppability. Those two tables never
meet, and they have to, because droppability is what decides whether a label
can share another family's rules. `Permission[X]` is the case that forces it: see
below.

The evidence that this cut is real is proposal 046. That document exists
because `effect_derive` has to be correct for both region-keyed and
non-region-keyed effects at once, and every one of its incorrect cases is a
`Modify` target escaping a callback binder. `Error` and `Suspension` cannot
have that bug, because they have no region to escape. **The well-scopedness
obligation belongs to a family, not to the row**, and stating it there turns
046's case analysis into a property of one family rather than a correctness
condition on one relation.

The same is true of the rank problem this note opened with. `External[Read] ⊑
External[Write] ⊑ External[Commit]` needs join, and `Modify[a]`/`Modify[b]`
need set union. Under a flat row that is a special case; under families it is
each family declaring its algebra, and the special case disappears. **The
`External` mode split of the previous section is not really a separate proposal
— it is the first thing families make expressible.**

Cross-family rules also get a place to be stated once. WI-701's `Branch ×
External` prohibition is a Control × World incompatibility, and 047 §8's
monad-transformer rank ordering is a total order on families. Both are
currently statements about label pairs.

### `Permission[X]`: the effect is the CHECK, at the point of acquisition

> Stated in final form — with subsumption, contravariance and the
> provider-cannot-self-grant rule — in **064**. What follows is why the label was
> reached; the rules are not restated here, and where the two differ 064 wins.

The six rejections above were each of the form *"this is authority, not
semantics"*. That is the right verdict about a **static** capability label —
`Model` as a standing attribute of an operation says nothing about what the
runtime may do with a call. It is the wrong verdict about the **act of
acquiring** one, and the difference is the whole of this family.

Write the check where a capability object is minted, and let holding the object
be the authority thereafter:

```anthill
sort FsRoot
  internal entity fs_root
  operation open() -> FsRoot
    effects {Permission[FileSystem]}
end
```

`write_file(root: FsRoot, …)` then carries `External[Write]` and no `Permission` at
all. `Permission[X]` gates **acquisition**, once; everything downstream is
ordinary. Two consequences make the family pay for itself.

**It passes 054's own test, which the six rejections failed.** A check consults
ambient state, so it is not constant-foldable; it can refuse, so its failure is
the result; reordering it across the operation it guards changes meaning; and
it is **not droppable when its value is unused**, because dropping it drops the
refusal. That is a distinct licence profile from `External[Read]`, which *is*
droppable, and from `Modify[r]` on a fresh region, which is memory and has
nothing to refuse.

**The minting site is few, so "one effect, not one per capability" survives.**
The previous section kept 054 literally true for `External` by making the
argument a *mode*. This keeps it true from the other end: the argument is a
capability, but the label appears only where capabilities are introduced, and a
program introduces far fewer than it uses.

The constructor escape is closed structurally rather than checked. §8.6 makes
`internal` the only hide gate, hiding a name from cross-scope resolution and
from field projection alike — *"a top-level operation reading `b.v`, where `v`
belongs to an `internal` constructor of another sort, is the same
forbidden-internal access as naming that constructor directly"* — and top-level
code is outside every declaring scope. So `fs_root()` from outside is a load
error, and the `Permission`-carrying operation is the only introduction.

That also shrinks the honesty problem stated below. A user label is only as
good as its leaf declarations, and under flat labels that audit is *every
leaf*. Here it is *every minting operation*, because a host-bound operation
still has to name `FsRoot` in its signature to touch one.

### `Permission` and `External` are orthogonal, and the test double proves it

The tempting cheap answer is to make authority a fourth `External` mode. A
fake carrier refutes it: it is `Permission[X]` with **no** `External` whatever —
same authority path exercised, nothing leaving the process — which is exactly
what a test wants. All four quadrants are populated:

| | `External` | no `External` |
|---|---|---|
| `Permission[FileSystem]` | the real filesystem root | an in-memory root, still gated |
| — | reading through a handle you were passed | pure |

They ask different questions about one call: `Permission` asks *may I*, `External`
asks *what licence does the runtime have here*. 054's "one effect, not one per
capability" is an argument about the externality axis and never spoke to
authority.

**The example already gets this wrong, which is the evidence.**
`guardians.FakeLlm.complete` declares `effects {External, Model, Error}` —
identical to `LiveLlm` — while touching nothing outside the process. Under the
split it narrows to `{Permission[Model], Error}`: a legal override narrowing, and
honest. A test can then assert the fake is not external, which today it cannot.

It also simplifies the sandbox story. The conditional-effect spelling above
makes the *mode* conditional; with the axes separated, a sandbox refutes
`External` and leaves `Permission` standing — you still need the grant, you just do
not reach the world.

### Spelling: no surface change

Effects are registered today as facts:

```anthill
  fact Effect[T = Modify[?]]
  fact Effect[T = Error[?]]
```

so the family belongs at the registration site, and `Effect` gains a required
parameter so that a registration without one fails to load rather than
defaulting silently:

```anthill
  sort Effect { sort T = ?  sort Family = ? }

  fact Effect[T = Modify[?],   Family = State]
  fact Effect[T = Error[?],    Family = Control]
  fact Effect[T = External[?], Family = World]

  fact Effect[T = Permission[?],   Family = Permission]   -- IF families land;
                                                          -- 064 registers it plain

  -- a project's own, in its own namespace
  fact Effect[T = Model,       Family = User]
```

**Written rows do not change.** `effects {Modify[c], Error, -Model}` still
parses and still reads the same; the typer partitions by consulting the
registration. That matters more than it sounds: a reorganization that churns
every effect annotation in the stdlib will not get done, and one that changes
no source might.

### What the kernel must not concede

**One user family, not user-declared families.** If projects can mint families,
"one effect, not one per capability" fails one level up, which is the exact
mistake 054 was written to prevent. Kernel families stay a closed set; projects
declare *labels* within `User`, and those labels combine by set union and carry
no interpretation. `Permission[X]` needs none of this: 064 gives it no family
at all, and its capability argument follows the same discipline `Modify[r]`
already does.

**A user label is only as honest as its leaf declarations.** `-Model` is
enforced through anthill-typed code; a host-bound operation that secretly calls
a model defeats it. That is precisely the trust boundary `Modify` and `External`
already live on, and it should be written down rather than discovered. Routing
a capability through an object narrows this from every leaf to every minting
operation, but it does not remove it: a host op declared to return an `FsRoot`
without the `Permission` effect defeats the scheme exactly as before.

**Discharge comes free, and that is worth checking rather than assuming.** 045
§5.5 makes handler discharge purely type-level — a shared row tail with the
label present on the body side and absent from the result. If that holds
per-family, a user family gets handlers with no kernel semantics at all. It is
the cheapest part of the design if true and a hidden cost if not, so it is the
second thing to verify.

### Cost, stated plainly

This is a typer refactor, not a syntax change: row union, subset conformance,
lacks-constraints, and discharge each become family-indexed. Nothing here has
been measured — unlike `high-level-api.md` §8.1, no probe was run — and the
claim that it *reduces* complexity rests on the argument that it localizes
case-splits that already exist, not on a diff. The way to find out cheaply is
to write the family table as facts, leave the typer alone, and see whether the
existing case-splits in `effect_derive` and the row algebra line up with the
four columns. If they do, the refactor is mechanical; if they do not, the cut
is wrong and the table cost nothing.

## Recommendation

Do not add capability effects to the **kernel** for the agent domain; the six
rejections stand as written, and are worth recording as evidence for 054
whether or not anything else happens. They are rejections of a **static**
capability label. Do add `Permission[X]` on **acquisition**, because the act of
checking a grant is an effect on 054's own test while the standing attribute is
not — and because `-Model` on a generated agent is a claim the design needs and
no carrier can make.

**The `Permission[X]` half is now proposal 064**, which carries the argument in
specification form together with the names and placements this note refuted
along the way. What remains open here is the FAMILY question, and it is
separable: whether 045's row algebra can carry a label whose arguments **join**
alongside labels whose arguments stay distinct, and whether the family table's
columns actually match the case-splits already present in the typer.

One prerequisite is not optional. WI-20260823-VM3YB measured that `fact
Effect[T = X]` is documented as the registration and checked at **no site**, so
a misspelled label is a silent new effect. The family plan above hangs a
required `Family` parameter off that same fact; adding a required parameter to
a registration nothing validates buys nothing. VM3YB comes first.

Treat the `External` mode split as the **first consumer of families**, not as
a standalone refinement of 054 — the rank algebra it needs is the thing
families supply, so proposing it alone would mean special-casing one label.
Neither belongs in the guardians example's first increment. The example can be built
today on the blanket rule, and it will produce the concrete cases — a
compensable `create_issue` next to an incompensable `send_email`, a fetch whose
result goes unused, a plan that fails at step three — that a proposal would
need as motivation. Filing it before those cases exist would be filing an
argument in search of evidence.

That caution applied to the mode split and to families, and it does NOT apply
to `Permission[X]`, which is why 064 was filed and these were not: its
motivating case already exists in shipped source. `-Model` on a generated
checker is a claim the design makes today and obtains only by withholding a
carrier, and `FakeLlm` declares an `External` it does not have. Evidence first,
then the proposal — the same test, passed rather than failed.
