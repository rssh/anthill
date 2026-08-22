# Guardians of the Agents — an anthill example

An answer to the challenge in Erik Meijer, *Guardians of the Agents: Formal
Verification of AI Workflows*, CACM 69(1), January 2026: build an email agent
that is resilient to prompt injection, and check it before it runs.

## The one-command demo

```
anthill load examples/guardians
```

prints exactly three refusals and nothing else. Each is a candidate agent from
`agent/rejected/`, and each is refused by a **different, independent** mechanism:

```
agent/rejected/leak.anthill: type mismatch in send_email.body (op-arg):
    expected Text[Trust = Public], got Text[Trust = Untrusted]
```
The article's attack, as generated code: summarize the mailbox, mail the summary
to `it@othercorp.com`. Refused because `summarize` is typed
`Text[Trust = ?t] -> Text[Trust = ?t]` — whatever label went in comes out — so
the summary is `Untrusted` and the sink wants `Public`. **Summarizing does not
launder.**

```
'WideRowTriage' overrides 'Triage.run' but does not refine it: the override
    declares effect `Filesystem`, which is not covered by any effect the spec
    operation declares (effects must not widen)
```
Leaks nothing; claims a capability the spec never granted. One token apart from
`agent/good.anthill`, so this measures the effect row and nothing else.

```
'SteerableChecker' overrides 'Checker.check' but does not refine it: the
    override declares effect `Model`, ... (effects must not widen)
```
The design's sharpest claim, and one no carrier discipline can make: the checker
must **provably not consult a model**, or the guard is as steerable as the thing
it guards. `Checker.check` declares `-Model`; an implementation that calls the
Oracle is refused.

Three attacks, three independent mechanisms. Neither of the other two would
catch any one of them.

## What is where

| file | what |
|---|---|
| `vocabulary.anthill` | `TrustLevel`, `Text[Trust]`, `Message[Trust]`, `Report`, and the tools that consult no model |
| `observe.anthill` | the **only** vocabulary the model may write at run time — a closed `Feature` enum with no constructor naming an address, a tool, or an action |
| `oracle.anthill` | the LLM as a **spec with interchangeable carriers** (`LiveModel` / `FakeModel`), on the `anthill.persistence.Store` pattern |
| `spec.anthill` | `Triage` — the task, as a spec the generated agent must provide |
| `generation.anthill` | the generation loop as declarations: `generate` carries `Model`, `check` carries `-Model` |
| `classify.anthill` | what counts as suspicious — rules in the KB, not a prompt |
| `mailbox.anthill` | the article's inbox, including the injected email |
| `safety.anthill` | where the tiers compose: types produce facts, proofs consume them |
| `agent/good.anthill` | a generated implementation that passes |
| `agent/rejected/` | three that must not |

Design notes and the full measurement record are in `docs/design/`; the runnable
probes behind the measurements live in `docs/measurements/guardians/` at the
repository root, deliberately outside the example so this directory loads.

## Swapping the model

`Oracle` is a spec; `LiveModel` and `FakeModel` are carriers. Choosing between
them is choosing a **value**, not re-registering a host function, and no agent
source changes. Host functions are bound per carrier through
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
building this (C7, and C8 — which was fixed in `kb/typing.rs`).
