## Attributes

- id: WI-20260908-FJG8B-a-called-operation-with-no
- created: 2026-09-08T06:47:56Z

- status: Open
- status_agent: user
- status_at: 2026-09-08T06:47:56Z

- acceptance: cargo-test

## Description

A CALLED OPERATION WITH NO IMPLEMENTATION IS NOT REFUSED AT LOAD, so a program whose safety rests on a signature nothing backs is certified as if it were checked. MEASURED against examples/guardians 2026-09-08.

THE PROGRAM. A candidate declares its own producer and calls it:

  operation launder(s: String) -> Text[Trusted]      -- no body, no defining
                                                     -- equation, no host binding
  ...
  Email.send(to: Address(local: "boss", domain: "ourcorp.com"),
             body: launder(box.owner.local))

`anthill load` reports `loaded: 3176 facts, 220 rules` -- zero errors. The typer believes the declared return type, the call type-checks, and every downstream check that reads `Text[Trusted]` is satisfied by a value nothing can produce. Pinned as `examples/guardians/fixtures/agent/declared_mint.anthill`, an ACCEPTED fixture, with `a_candidate_may_declare_its_own_trusted_producer` asserting it still loads -- so the day this ticket lands, that row reds and the fixture is deleted rather than someone wondering why a refusal appeared.

WHY THE LOADER CANNOT DECIDE IT TODAY, and this is the whole difficulty: BODY-LESS-AND-CALLED IS THE NORMAL SHAPE. Twenty-one operations in `examples/guardians/lib/` are declared with no body and every accepted fixture calls some of them -- `Email.fetch`, `Email.send`, `categories_of`, `choose_recipient`, `render_task`, `Llm.complete`. A spec DECLARES and a deployment BINDS; the guardians test harness registers five host names and a real deployment would supply the rest. So "body-less" cannot be an error, and nothing consulted at load separates a declaration awaiting its binding from one asserting a type its author cannot produce.

WHY IT IS DECIDABLE ANYWAY. WI-1122 moved the embedder host-fn table ONTO the KB and sealed late registration, precisely because registering after load failed silently in release -- so by the end of `load_all` the KB already knows which host names exist. The three implementation channels are all KB-visible at that point: a body (`op_bodies`), a `[simp]` defining equation, and a host binding (the host-fn table plus the `provides ... language L ... operation_map` blocks). The check is: for every operation REACHED BY A CALL, at least one channel is present.

WHY "REACHED BY A CALL" AND NOT "DECLARED". A declaration with no caller is the ordinary spec surface and must stay legal -- `Triage.run` is declared by the spec and implemented only by a candidate that may not be loaded yet. It is the CALL that turns an unbacked declaration into a program that cannot run, and the call site is where the diagnostic belongs.

SCOPE QUESTIONS THE TICKET MUST SETTLE, none of them obvious:
  - a SPEC operation called through a spec-typed receiver (`chk.check(...)`, `h.render_task(...)`): the implementation is the carrier's, which may arrive with a later file. Per-carrier at the provision, or deferred?
  - a CANDIDATE loaded into a discardable layer (WI-SPGBP): the check must run against the layer's view, or a candidate calling a base operation reads as unbacked.
  - the guardians example itself must still load with its 21 declared operations and 5 registered host fns, which is the acceptance's real control.

ACCEPTANCE: a called operation with no body, no defining equation and no host binding is a LOAD ERROR naming the operation and the call site. CONTROLS, each of which must still hold: `examples/guardians` loads clean (its declarations are unbacked but UNCALLED, or bound by the harness); `cargo test -p anthill-core` green; and `fixtures/agent/declared_mint.anthill` becomes REFUSED, which is the positive measurement -- a test that only asserts the check exists is not evidence, drive the unbacked call and assert the refusal.

FOUND BY: /code-review during WI-20260829-MCKTE, which sealed four producers of `Text[Trusted]` and then measured that a candidate can declare a fifth. No seal in a vocabulary reaches a name the candidate invents; this is the check that does.

