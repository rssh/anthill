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
rejected/leak.anthill: type mismatch in send_email.body (op-arg):
    expected Text[Trust = Public], got Text[Trust = Untrusted]
```
The article's attack, as generated code: summarize the mailbox, mail the summary
to `it@othercorp.com`. Refused because `summarize` preserves its argument's label
— whatever went in comes out — so the summary is `Untrusted` and the sink wants
`Public`. **Summarizing does not launder.**

```
'WideRowTriage' overrides 'Triage.run' but does not refine it: the override
    declares effect `Filesystem`, which is not covered by any effect the spec
    operation declares (effects must not widen)
```
Leaks nothing; claims a capability the spec never granted. One token apart from
`fixtures/agent/good.anthill`, so this measures the effect row and nothing else.

```
rejected/bad_checker.anthill: check.effects (op-effects):
    got denied effect: Model — the row DECLARES `-Model`
```
**Who guards the guard.** The checker must provably not be steerable, or it is as
manipulable as the thing it verifies. `Checker.check` is handed no `Llm`, so this
one smuggles one into its own carrier and reaches it through `self` — and is
caught anyway, because the row it DECLARES is the spec's and the row INFERRED
FROM ITS BODY carries `Model`.

```
rejected/minting_checker.anthill: check.effects (op-effects):
    got denied effect: Permission[T = Model] — the row DECLARES `-Permission[T = Model]`
```
The mirror attack. This one is handed nothing and holds nothing — it **mints** its
own model. Minting is not consulting, so `-Model` never fires: what confines it is
that acquisition is now an *effect* at all (proposal 064's `Permission[Model]`, on
`LiveLlm.open`), which the checker's row does not grant. **Before this, minting
was unconstrained** — the constructors were public and construction carried no
effect, so a checker could obtain a model out of thin air and `-Model` caught it
only if it went on to call one.

The `-Permission[Model]` in the row is the *contract*, not the mechanism: delete
it and this fixture is still refused, as `undeclared effect` rather than `denied
effect`. `docs/design/measured.md` D1 records exactly what each half buys.

Beside them, `rejected/forged_llm.anthill` — which skips the gate entirely by
naming the capability's `internal` constructor, and is refused before any effect
is considered. That one is what makes the rest mean anything: without it a
generated checker acquires nothing, calls nothing, and holds a model anyway.

And `rejected/frontier_checker.anthill`, which asks for `Permission[FrontierModel]`
rather than the denied `Permission[Model]`. It is refused either way, but only the
downward closure names it as a **violated denial** rather than a missing
declaration — acquiring a frontier model IS acquiring a model.

## What is where

| file | what |
|---|---|
| `lib/vocabulary.anthill` | `TrustLevel`, `Text[Trust]`, `Message[Trust]`, `Report`, the tools that consult no model, and the capability vocabulary (`Model`, `FrontierModel`, `Filesystem`) |
| `lib/observe.anthill` | the **only** vocabulary the model may write at run time — a closed `Feature` enum with no constructor naming an address, a tool, or an action |
| `lib/llm.anthill` | the LLM as a **spec with interchangeable carriers** (`LiveLlm` / `FakeLlm`), on the `anthill.persistence.Store` pattern — and, since proposal 064, as a **capability object**: `internal` constructors, minted by a `Permission[Model]`-carrying `open` |
| `lib/spec.anthill` | `Triage` — the task, as a spec the generated agent must provide |
| `lib/harness.anthill` | the generation loop as declarations: `generate` carries `Model`, `check` carries `-Model, -Permission[Model]` |
| `lib/tasks.anthill` | `summarize` and `observe`, built on the one primitive rather than bound per task |
| `lib/classify.anthill` | what counts as suspicious — rules in the KB, not a prompt |
| `lib/safety.anthill` | where the tiers compose: types produce facts, proofs consume them |
| `fixtures/*.anthill` | the article's inbox, including the injected email |
| `fixtures/agent/good.anthill`, `checker.anthill` | generated implementations that pass — the controls |
| `fixtures/agent/rejected/` | nine that must not, one per mechanism |

Design notes and the full measurement record are in `docs/design/`; the runnable
probes behind the measurements live in `docs/measurements/guardians/` at the
repository root, deliberately outside the example so this directory loads.

## Swapping the model

`Llm` is a spec; `LiveLlm` and `FakeLlm` are carriers. Choosing between them is
choosing a **value**, not re-registering a host function, and no agent source
changes. Both are obtained the same way — `LiveLlm.open` / `FakeLlm.open`, each
carrying `Permission[Model]` — so the test double exercises the same authority
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

## Honest state

The checking half is real and measured. The generating half is not yet wired: the
agents in `agent/` are hand-written stands-in for what a model would emit. The
`Checked` relation in `safety.anthill` is a fixture — the typer already decides
it on every load and currently discards the positive verdict. `docs/design/measured.md`
records what was measured, what is missing, and the two defects found while
building this — C7 and C8, both since fixed in `kb/typing.rs`.
