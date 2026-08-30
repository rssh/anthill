# What the guardians example asks of the effect vocabulary

**Status:** Design argument (2026-08-22), with one half now MEASURED (2026-08-26).
`Permission[X]` — found in this note's §Families and filed as
[064](../../../../docs/proposals/064-permission-effect.md) — is implemented and this
example is its first consumer; see *What running it changed* below. The rest is still
reasoning rather than runs, unlike [`high-level-api.md`](high-level-api.md) §8.1.
Companion to [proposal 054](../../../../docs/proposals/054-external-effect.md).

**Spelling, 2026-08-29:** two renames since this was written, neither of which
touches an argument here. Where it writes `Permission[Model]` /
`Permission[FrontierModel]`, the shipped example writes `Permission[Llm]` /
`Permission[LiveLlm]` — the empty marker sorts were collapsed into the sorts one
actually acquires, and `LiveLlm provides Llm` now carries the sub-capability edge.
And where it writes the free operations `fetch_mail` / `send_email`, the example
writes `Email.fetch` / `Email.send`: the mail declarations moved into one
`lib/email.anthill` and one `sort guardians.Email`, so the article's source and
its sink sit adjacent. Same signatures, same rows, same guard.

## Result

**Acquire authority with `Permission[X]`** — one effect for the *act of acquiring*,
carried where a capability object is minted, not one label per capability. Holding
the object is the authority thereafter. Shipped as
[proposal 064](../../../../docs/proposals/064-permission-effect.md);
`LiveLlm.open` is the example's mint.

**Encode when authority is needed as a CONDITIONAL effect** — `send_email` carries
`(Permission[Outbox] :- external_addr(to))`
([proposal 048](../../../../docs/proposals/048-conditional-effects.md)), so the
guard says when the licence is required and no standing label has to.

That is the whole of what the agent domain added to the effect vocabulary. Six
further candidates suggested themselves and all six are rejected below, which is
this note's actual result: **the challenge motivates no new capability labels.**

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

**`LLM` / `Model`.** Semantics: `{E, Error}` where `E` is the CARRIER's row —
`LiveLlm` instantiates it at `{External}`, `FakeLlm` at `{}` — and nothing more. Two
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
verbatim. *(2026-08-29: the rejection stands, but the token was REMOVED from the
example. Nothing minted one, so `declassify` — its only consumer — could not be
written by any program; and `text(raw: u.raw)` re-labels a `Text` for free
regardless, so the guarded route was unreachable while an unguarded one was open.
"Authority lives in values" needs the value to be OBTAINABLE by someone; here it
was obtainable by no one, which is a different thing from unforgeable.)*

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

> **Where the `Model` rejection landed, in two steps (2026-08-26, then
> 2026-08-29).** The verdict above is about the KERNEL row and it never moved —
> `Permission[X]` is the one label 064 added, and its argument is a capability
> rather than a new label per capability. What moved is whether the EXAMPLE needed
> `Model` as a project label on top of it. For three days it did. It does not now,
> and the reason the first answer was wrong is worth more than the answer.
>
> **Step one: the rejection was overridden.** The example carried `Model`, on this
> argument — two claims, not one, and the checker needs both:
>
> | claim | spelled | catches |
> |---|---|---|
> | this code never CONSULTS a model | `-Model` | a checker handed an `Llm` it should not have |
> | this code never ACQUIRES one | `-Permission[Model]` | a checker that mints its own |
>
> Neither implies the other — minting is not consulting, and consulting a smuggled
> `Llm` acquires nothing — and both directions were measured:
> `rejected/bad_checker.anthill` and `rejected/minting_checker.anthill`, deleting
> either denial redding exactly one.
>
> **THE MEASUREMENT WAS OF THE MECHANISM, NOT OF THE REQUIREMENT, and that is the
> whole defect in it.** It established that `-Model` was the only thing catching
> `bad_checker`. It never asked whether `bad_checker` is an attack. That checker
> calls a model and *discards the reply* — it returns a hardcoded `Rejected`. It
> demonstrates CONTACT, not STEERING, and a verifier that consults an oracle and
> ignores the answer is not steerable by it. A fixture chosen to exercise a label
> was read as evidence that the label was needed.
>
> **Step two: the requirement dissolved.** Being steered requires READING the
> answer, so the claim to make is about the answer, not about the call.
> `Llm.complete` now returns `LlmOutput[Text[Untrusted]]` — an `internal`
> constructor, so generated code can neither project it nor match on it (measured:
> `'value' is internal`, `'llm_output' is internal`). A checker handed an `Llm`
> obtains a token it cannot read; the call teaches it nothing. Consultation became
> harmless, so it stopped being worth denying, and `bad_checker` is accepted today.
>
> The row keeps one denial, of ACQUISITION. `fact Effect[T = Model]` is gone,
> `Model` is a capability and nothing else, and
> `prelude/external.anthill`'s rule — "ONE effect, not one per capability (no Http
> / Db / Forge effects) … what distinguishes external capabilities is AUTHORITY,
> which lives in CARRIERS" — is restored. **Six candidates, six rejections, none
> overridden.**
>
> **What this costs the Recommendation below, and it is not nothing.**
> §"Recommendation" argues for `Permission[X]` partly on "`-Model` on a generated
> agent is a claim the design needs and no carrier can make". The carrier half of
> that stands — no carrier can say *never consults*. The needs half does not: the
> design wanted *cannot be steered*, which is weaker, sufficient, and exactly what
> a return type says. 064 is unaffected — it passes its own four-point test at the
> acquisition site independently — but it has one supporting argument fewer.

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

That question is what the FAMILIES proposal existed to answer — asking one label
to carry a join while its neighbours carry set union is a special case, whereas
asking each **family** to declare its algebra is a structure, and the mode split
falls out of it rather than being bolted on. That proposal was never filed and its
working is no longer here; see §"Families: worked out here, never filed" below.
The question above stands on its own regardless, and does not wait on it.

## `Permission[X]`: the effect is the CHECK, at the point of acquisition

*The one candidate that survived. It sat at depth three inside §"Families" until
2026-08-29, because that is where it was found — which made the note's only shipped
result the fourth subsection of a proposal that was never filed.*

> **Reconciliation with proposal 064 (2026-08-25), and what running it changed
> (2026-08-26).** `Permission[X]` was found here, while asking what a `User`
> family would have to hold, and was filed as
> [064](../../../../docs/proposals/064-permission-effect.md) — **without**
> families. It is an ordinary row member there: set-inclusion subsumption, both
> legs of the existing not-widen check, no family-indexed algebra. So this
> section is the note's exploration and the record of where the label came from;
> 064 is its specification, and the two must not be read as one proposal.
> Families remain unfiled, and nothing in 064 waits on them.
>
> IT IS NOW IMPLEMENTED (WI-20260825-CBRSW) and this example is its first
> consumer. Three things the note did not predict:
>
> * **The row half cost nothing and the NEGATIVE half cost everything.** 064
>   claimed the lacks-constraint would follow from the existing order with no rule
>   of its own. It did not: present-vs-absent was decided by label EQUALITY, so a
>   row denying `Permission[Model]` while acquiring `Permission[FrontierModel]`
>   loaded clean. `rejected/frontier_checker.anthill` is that program, and closing
>   it is the one typer rule the increment added.
> * **Containment is load-bearing, and was absent here.** These carriers' entity
>   constructors were public, so a generated checker could write
>   `fake_llm(fixture: "x")` and hold a model without acquiring one — the effect
>   would have been advisory. `internal` closes it;
>   `rejected/forged_llm.anthill` measures it.
> * **The `-label` this section says "nothing has used yet" now has TWO users on
>   one row**, and they are not redundant. See the table under *Six candidates*.

The six rejections above were all of the form "this is authority, not
semantics, so it does not belong in the row". That verdict is right about the
**kernel** row and wrong about what a project needs, and the gap shows up the
moment §3 of [`high-level-api.md`](high-level-api.md) makes the deliverable a
*generated program*.

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

**The example USED TO get this wrong, and that was the evidence — until an effect
ROW made half of it expressible without the split.** `guardians.FakeLlm.complete`
declared `effects {External, Error}`, identical to `LiveLlm`, while touching nothing
outside the process. It now declares `{Error}` and instantiates `Llm`'s row at `{}`
(`lib/llm.anthill`), and `a_carriers_effect_row_reaches_the_caller_that_was_handed_it`
asserts exactly that — so the sentence that stood here, "a test can then assert the
fake is not external, which today it cannot", is retired by measurement rather than
by argument.

WHAT THE ROW DID NOT BUY, which is what still argues for the split: the row makes
`External` a fact about the CARRIER, but it does not separate the two QUESTIONS. A
sandboxed live model still has to choose between declaring `External` it cannot
perform and dropping a row its authority requires. `Permission` asks *may I*;
`External` asks *what licence does the runtime have*. Parameterising one of them does
not give you the other.

It also simplifies the sandbox story. The conditional-effect spelling above
makes the *mode* conditional; with the axes separated, a sandbox refutes
`External` and leaves `Permission` standing — you still need the grant, you just do
not reach the world.


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

> **THE CRITERION SURVIVED THIS SECTION'S OWN EXAMPLE (2026-08-29).** "Say it in
> the contract, so nobody re-audits a parameter list on every regeneration" is the
> right test, and the paragraph above is right that withholding a carrier fails
> it. What is wrong is the next inference — that only a ROW can pass it.
>
> A RETURN TYPE PASSES IT TOO. `Llm.complete -> LlmOutput[Text[Untrusted]]`, with
> an `internal` constructor, states in the signature that what a model returns can
> be neither projected nor matched. Nothing is audited, nothing is re-checked on
> regeneration, and the claim is read where the operation is declared — and it is
> a claim about a VALUE, which is where 054 says authority belongs.
>
> The heading stays literally true: a carrier cannot say *lacks X*. The defeat is
> that the design never needed that sentence. It needed *cannot be steered*, and a
> sealed return type says it. `-Model` and the `Model` label are gone from the
> example (see the note under §"Six candidates"), so THIS SECTION HAS NO MOTIVATING
> CASE LEFT: the row above would today read
> `effects {External[Read], Error, -External[Commit]}`, in which every remaining
> `-` belongs to a KERNEL label.
>
> That does not refute the User family — it removes the one piece of evidence
> offered for it. `Filesystem` is the example's only surviving project label, and
> nothing has yet asked whether it earns its place by this same test.

## Families: worked out here, never filed

A `User` family — a home in the row algebra for project-defined labels — was
designed in this section and is no longer here. Three things retired it, in order:

* **It was never filed.** The Recommendation below said not to, and nothing since
  has: `Permission[X]` went to 064 as an ordinary row member, with set-inclusion
  subsumption and no family-indexed algebra.
* **Both documents that cited it said it was not needed.**
  [`two-flows.md`](two-flows.md) — "BUILT, and the family was not required";
  [`high-level-api.md`](high-level-api.md) — "remains unfiled".
* **Its motivating case is gone (2026-08-29).** The family existed to house
  `-Model`, the example's one project label. `Model` was retired when
  `Llm.complete` began returning a sealed `LlmOutput` — see §"Six candidates the
  rule rejects". `Filesystem` is the only project label left, and nothing has yet
  asked whether it earns its place by this note's own test.

What the exploration produced that outlived it is `Permission[X]`, promoted to its
own section above. The rest — the five-family table, the registration spelling,
the "one user family, not user-declared families" concession and the unmeasured
typer-refactor cost — was 151 lines arguing for a proposal that was not made, and
is recoverable from git history if the question reopens.

## Recommendation

Do not add capability effects to the **kernel** for the agent domain; the six
rejections stand as written, and are worth recording as evidence for 054
whether or not anything else happens. They are rejections of a **static**
capability label. Do add `Permission[X]` on **acquisition**, because the act of
checking a grant is an effect on 054's own test while the standing attribute is
not.

> **ONE SUPPORTING ARGUMENT WITHDRAWN (2026-08-29).** This sentence used to end
> "— and because `-Model` on a generated agent is a claim the design needs and no
> carrier can make". The carrier half stands; the *needs* half does not. What the
> design wanted was **cannot be steered**, which is weaker, sufficient, and stated
> by a sealed return type (`LlmOutput`). 064 is unaffected — it passes the
> four-point test at the acquisition site on its own — but it rests on one
> argument fewer, and the example that supplied the other one no longer does.

**The `Permission[X]` half is now proposal 064**, which carries the argument in
specification form together with the names and placements this note refuted
along the way. What remains open here is the FAMILY question, and it is
separable: whether 045's row algebra can carry a label whose arguments **join**
alongside labels whose arguments stay distinct. (The second half of this sentence
used to ask whether the family table's columns matched the case-splits already in
the typer. That table is no longer in this note — §"Families: worked out here,
never filed" — and the question is recoverable with it from git history.)

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
