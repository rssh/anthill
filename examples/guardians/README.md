# Guardians of the Agents — an anthill example

An answer to the challenge in Erik Meijer, *Guardians of the Agents: Formal
Verification of AI Workflows*, CACM 69(1), January 2026: build an email agent
that is resilient to prompt injection, and check it before it runs.

## The one-command demo

```
anthill load examples/guardians
```

refuses every candidate agent in `fixtures/agent/rejected/` and nothing else.
Each is refused by a **different** mechanism. Four of them:

```
rejected/leak.anthill: type mismatch in send.body (op-arg):
    expected Text[Trust = Public], got LlmOutput
```
The article's attack, as generated code: summarize the mailbox, mail the summary
to `it@othercorp.com`. Refused twice over, and the message names the outer half:
what a model returns is a sealed `LlmOutput`, which is not a `Text` at all, and
the `Text` inside it carries the label its input had — `summarize` preserves it,
so nothing that went through the mailbox comes back `Public`.
**Summarizing does not launder.**

```
'WideRowTriage' overrides 'Triage.run' but does not refine it: the override
    declares effect `Filesystem`, which is not covered by any effect the spec
    operation declares (effects must not widen)
```
Leaks nothing; claims a capability the spec never granted. One token apart from
`fixtures/agent/good.anthill`, so this measures the effect row and nothing else.

**Who guards the guard.** The checker must provably not be steerable, or it is as
manipulable as the thing it verifies. There are two routes to a model — being
handed one, and acquiring one — and only the second is still denied.

A checker CAN now be handed an `Llm` in its own carrier and call it. That used to
be `rejected/bad_checker.anthill`, refused by a `-Model` label on the row; it is
accepted today, because what `complete` returns is an `LlmOutput` — sealed, with
no projection and no pattern to match. The call hands the checker a token it
cannot read, so it learns nothing and cannot be steered. Being steered requires
reading the answer, and the type forbids that.

```
rejected/minting_checker.anthill: check.effects (op-effects):
    got denied effect: Permission[T = Llm] — the row DECLARES `-Permission[T = Llm]`
```
The mirror attack. This one is handed nothing and holds nothing — it **mints** its
own model. What confines it is that acquisition is an *effect* (proposal 064's
`Permission[Llm]`, on `LiveLlm.open`), which the checker's row does not grant.
**Before this, minting was unconstrained** — the constructors were public and
construction carried no effect, so a checker could obtain a model out of thin air.

The `-Permission[Llm]` in the row is the *contract*, not the mechanism: delete
it and this fixture is still refused, as `undeclared effect` rather than `denied
effect`. `docs/design/measured.md` D1 records exactly what each half buys.

```
rejected/outbox.anthill: run.effects (op-effects): expected declared:
    [External, llm.E, Error], got undeclared effect: Permission[T = Outbox]
```
The article's policy has two halves — *"forbid data flow from `fetch_email`'s
result to the `body` parameter of `send_email` **with an external email address as
the target**"* — and this is the second one, `Email.send` being the sink the
article names. The body it mails is a literal
`Public` string, so nothing flows and no label is violated; it is refused because
the recipient is outside the organisation. `Email.send` demands
`Permission[Outbox]` **guarded on its target**, so mailing a colleague needs no
authority at all (`fixtures/agent/internal_send.anthill`, one token away, loads)
and mailing outside needs an authority `Triage.run`'s spec never grants. **No
generated triage can mail outside the organisation** — a property of the spec, not
of any agent. The rule is precisely *an address written literally, inline, at the
call*: anything the guard cannot decide — a computed address, or even a let-bound
literal — is refused rather than deferred (`measured.md` D4).

Beside them, `rejected/forged_llm.anthill` — which skips the gate entirely by
naming the capability's `internal` constructor, and is refused before any effect
is considered. That one is what makes the rest mean anything: without it a
generated checker acquires nothing, calls nothing, and holds a model anyway.

And `rejected/frontier_checker.anthill`, which asks for `Permission[LiveLlm]`
rather than the denied `Permission[Llm]`. It is refused either way, but only the
downward closure names it as a **violated denial** rather than a missing
declaration — `LiveLlm provides Llm`, so acquiring a live model IS acquiring a
model. The capability is the SORT you acquire; there is no marker sort beside it.

## What is where

| file | what |
|---|---|
| `lib/vocabulary.anthill` | the trust lattice and nothing else that is not it: `TrustLevel`, `Text[Trust]`, and the one remaining project effect kind (`Filesystem`) |
| `lib/email.anthill` | the **email service** and every email-shaped declaration with it: `Message[Trust]`, `MessageId`, `Address`, `Mailbox`, the `Outbox` capability, `in_org`/`external_addr`, `releasable`, and `Email.fetch` / `Email.send` — the article's source and sink, adjacent |
| `lib/observe.anthill` | the **only** vocabulary the model may write at run time — a closed `Feature` enum with no constructor naming an address, a tool, or an action |
| `lib/llm.anthill` | the LLM as a **spec with interchangeable carriers** (`LiveLlm` / `FakeLlm`), on the `anthill.persistence.Store` pattern — and, since proposal 064, as a **capability object**: `internal` constructors, minted by a `Permission[Llm]`-carrying `open`, answering in a sealed `LlmOutput` |
| `lib/spec.anthill` | `Triage` — the task, as a spec the generated agent must provide — and what is SPECIFIC to it: `Category`, `Report`, `Verdict`, `categories_of`, `choose_recipient`, `mentions_all`, and the `verdict_is_not_silent` constraint |
| `lib/harness.anthill` | the generation loop as declarations: `check` carries `-Permission[Llm]` — it may not ACQUIRE a model; being handed one is harmless, since `LlmOutput` is unreadable |
| `lib/tasks.anthill` | `summarize` and `observe`, built on the one primitive rather than bound per task |
| `lib/classify.anthill` | what counts as suspicious — rules in the KB, not a prompt |
| `lib/gate.anthill` | the trust partition, as a policy: what the candidate DECLARED and what it ASSERTED, asked of a discardable layer |
| `lib/safety.anthill` | where the tiers compose: types produce facts, proofs consume them |
| `fixtures/*.anthill` | the article's inbox, including the injected email |
| `fixtures/agent/good.anthill`, `checker.anthill` | generated implementations that pass — the controls |
| `fixtures/agent/conceal.anthill` | a generated implementation that CONCEALS and is accepted anyway — the honest record of C13, since `ensures mentions_all(result)` is refined against the spec but never proved of a body (WI-20260830-2FP2K) |
| `fixtures/agent/rejected/` | fourteen that must not — thirteen one per mechanism, and `uncleared_external.anthill`, which breaks two at once and must report BOTH |

Design notes and the full measurement record are in `docs/design/`; the runnable
probes behind the measurements live in `docs/measurements/guardians/` at the
repository root, deliberately outside the example so this directory loads.

## Swapping the model

`Llm` is a spec; `LiveLlm` and `FakeLlm` are carriers. Choosing between them is
choosing a **value**, not re-registering a host function, and no agent source
changes. Both are obtained the same way — `LiveLlm.open` / `FakeLlm.open`, each
carrying `Permission[Llm]` — so the test double exercises the same authority
path as production and differs only in whether the call leaves the process
(`Permission` and `External` are orthogonal; proposal 064). Host functions are bound per carrier through
`operation_map` + `KnowledgeBase::register_host_fn`, which must be called
**before** load (WI-1122 — after load is refused, because the failure would be
silent in release).

## Why almost none of the tests need a model

Every **security** property here is a load-time refusal, decided with no oracle,
no fake and no network — see `rustland/anthill-core/tests/guardians_test.rs`.
Only the **usefulness** properties need an oracle, and there the fake answers
from a fixture. That ordering is itself the claim: if a model had to run to test
the security, the security would be statistical rather than checked.

## What stops a candidate simply asserting it is safe

Every refusal above is about what a generated agent may *do*. A separate question
is what it may *say*: a program loaded into the same knowledge base as the trusted
declarations can reopen `namespace guardians` and assert whatever it likes —
including `Checked`, the very fact a safety claim would cite **about it**. Those
facts are well-formed, so type checking has nothing to say about them.

`lib/gate.anthill` is the answer, and it is a policy rather than a scan. The
checker loads the candidate into a **discardable layer** over the trusted base
(`KB.loaded`), and then asks the layer three questions:

* **Provision.** Is there a carrier the candidate DECLARED that provides the spec
  it was asked for? A program that implements nothing is not an implementation,
  and the carrier this finds is what the verdict reports.
* **Containment.** Does every clause the candidate's SOURCE wrote head at a name
  the candidate introduced? One rule, and it refuses a forged `Checked`, a second
  clause for the `mentions_all` postcondition, and a hand-written reflect row —
  with no name list and no spelling enumerated.
* **Naming.** Is every name it declared — or REDECLARED — under
  `guardians.agent.`?

The two facts it reads are engine-side marks, not relations: a candidate can
hand-write any reflect fact, so a gate reading a relation about its own subject
would be reading a channel that subject controls. `docs/design/measured.md`
group E is the record, including the measurement that decided the shape.

## Honest state

The checking half is real and measured. The generating half is not yet wired: the
agents in `agent/` are hand-written stands-in for what a model would emit. The
`Checked` relation in `safety.anthill` is declared and asserted nowhere — the
typer already decides it on every load and currently discards the positive
verdict, which is the seam that would fill it. `docs/design/measured.md`
records what was measured, what is missing, and the two defects found while
building this — C7 and C8, both since fixed in `kb/typing.rs`.
