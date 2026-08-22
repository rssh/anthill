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

## Families: a row per family, and one family for user labels

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
to case-split on the label. Four qualify:

| | State | Control | World | User |
|---|---|---|---|---|
| members | `Modify[r]` | `Error[E]`, `Suspension`, `Branch` | `External[mode]` | project labels |
| algebra | set union over distinct resources | set union over distinct payloads | **join** over a rank | set union |
| scope obligation | yes — 046's region elimination | none | none | none |
| interpretation | `StateT` | `ExceptT` / `ContT` / `LogicT` | host binding | none |

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
no interpretation.

**A user label is only as honest as its leaf declarations.** `-Model` is
enforced through anthill-typed code; a host-bound operation that secretly calls
a model defeats it. That is precisely the trust boundary `Modify` and `External`
already live on, and it should be written down rather than discovered.

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
rejections are the finding, and they are worth recording as evidence for 054
whether or not anything else happens. Do give the useful subset a home in a
`User` family, because `-Model` on a generated agent is a claim the design
needs and no carrier can make.

Verify two things before writing any of it as a proposal: whether 045's row
algebra can carry a label whose arguments **join** alongside labels whose
arguments stay distinct, and whether the family table's four columns actually
match the case-splits already present in the typer.

Treat the `External` mode split as the **first consumer of families**, not as
a standalone refinement of 054 — the rank algebra it needs is the thing
families supply, so proposing it alone would mean special-casing one label.
Neither belongs in the guardians example's first increment. The example can be built
today on the blanket rule, and it will produce the concrete cases — a
compensable `create_issue` next to an incompensable `send_email`, a fetch whose
result goes unused, a plan that fails at step three — that a proposal would
need as motivation. Filing it before those cases exist would be filing an
argument in search of evidence.
