## Attributes

- id: WI-20260829-MCKTE-a-trust-label-can-be-changed
- created: 2026-08-29T14:48:45Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T14:48:45Z

- acceptance: cargo-test

## Description

A TRUST LABEL CAN BE CHANGED BY RE-WRAPPING, so `examples/guardians`'s lattice pins a label AT A SINK but does not confine how a label MOVES between levels. `text(raw: u.raw)` re-labels any `Text[Untrusted]` as `Text[Public]` in one line and loads clean.

MEASURED. `enum guardians.Text` (lib/vocabulary.anthill) declares `sort Trust = ?` and `entity text(raw: String)`. The constructor is PUBLIC and `Trust` is PHANTOM -- it appears in no field -- so nothing relates the argument's label to the result's, and any label may be written at the wrap. Both routes work: the projection `u.raw` and a `match` on `text(raw: ?r)`.

WHAT THIS ALREADY COST, and it is why the ticket exists rather than a comment. `widen` (Public -> Untrusted, free) and `declassify` (the other way, guarded by an `Approval` token) were DELETED from the vocabulary, not because they were wrong but because they were unreachable theatre: neither was ever called -- not in lib/, not in a fixture, not in a test -- and `declassify` COULD not be, since nothing mints an `Approval`. Declaring a guarded door beside an open window suggested a discipline the example does not enforce. The finding is recorded under `enum guardians.Text`.

WHAT IS TRUE TODAY, stated exactly so the fix is not oversold. The lattice DOES pin a value's label at a sink: `Email.send(to: Address, body: Text[Public])` refuses `Text[Untrusted]`, measured by `fixtures/agent/rejected/leak.anthill`. And this is NOT an end-to-end exfiltration: `Email.send` demands `Permission[Outbox]` guarded on its target, which `Triage.run`'s spec row never grants, so a re-labelled body can reach a colleague and nobody else. The false claim is the one ONE LEVEL UP -- that the parameter models a lattice with controlled transitions. It models a tag that anyone may rewrite.

THE FIX IS TO SEAL `Text` THE WAY `LlmOutput` IS SEALED (lib/llm.anthill): `internal entity text(...)`, so §8.6 hides the constructor from cross-scope resolution AND from field projection, plus smart constructors at the boundary that fix the label. That is the shape already proven in this example -- it is what makes a model's answer unreadable and what `rejected/forged_llm.anthill` measures.

THE COST IS MEASURED AND IS THE REASON THIS IS NOT INLINE. `fixtures/mailbox.anthill` builds `Text[Untrusted]` inside FACTS -- 10 sites, counted -- and a fact cannot call a smart constructor. So sealing forces labelling to move to the boundary, which means either a fact-writable route that still fixes the label, or a deployment shape where the inbox is loaded rather than asserted. Deciding that is the work.

NOT WI-20260822-T70A2, and the distinction is the same one T70A2 draws about C7: T70A2 constrains the VOCABULARY (what may inhabit the `Trust` slot -- it would stop `Text[Publik]`), this constrains the TRANSITIONS (who may move a value between two admissible levels). Neither implies the other, and `text(raw: u.raw)` binds `Public`, an entity of `TrustLevel`, so T70A2's constraint is SATISFIED while the relabel goes through.

ACCEPTANCE: a program that re-labels -- `text(raw: u.raw)` where `u: Text[Untrusted]`, and the `match` spelling of the same -- is a LOAD ERROR naming the constructor and the scope it is internal to. CONTROLS, each of which must still hold: `fixtures/agent/rejected/leak.anthill` still REFUSED (the label must remain ENFORCED at the sink, not merely un-rewritable); `fixtures/agent/good.anthill` and `internal_send.anthill` still ACCEPTED; the deployment's 10 `text(raw: ...)` fact sites still load, by whatever route replaces them; and the guardians suite green (35 tests today). A test that only asserts the seal loads is not evidence -- drive the relabel and assert the refusal.

## Changes

### 2026-08-29T17:03:04Z — feedback — user

THE COST MEASUREMENT IN THIS TICKET UNDERCOUNTS, and the missing sites break the
ticket's own CONTROLS. Found by /code-review.

It says "10 sites, counted", all in `fixtures/mailbox.anthill`, all FACTS — and
concludes the work is finding a fact-writable route. There are 7 more `text(raw: ...)`
sites, all CALL sites in `fixtures/agent/`:

  internal_send.anthill:30        computed_recipient.anthill:45
  generate_from_content.anthill:26  letbound_recipient.anthill:38
  outbox.anthill:34               minting.anthill:24, :25

"A fact cannot call a smart constructor" does not cover a call site, so the stated
repair does not reach them — they need the smart constructor's NAME, whatever it is.

WHY THIS MATTERS MORE THAN A COUNT. Sealing `text` per the description breaks
`internal_send.anthill` at name resolution, and this ticket's ACCEPTANCE requires it
to stay ACCEPTED. Worse for the three refused fixtures: `outbox`, `computed_recipient`
and `letbound_recipient` would die in the BODY before the effect leg runs, so
`assert_refused(..., "undeclared effect: Permission[T = Outbox]")` goes red and those
fixtures stop measuring the outbox guard while still being "refused" — a silent
coverage loss of exactly the kind the ticket's controls exist to catch.

So the real scope is 17 sites in two shapes, and the acceptance must add: every
fixture in `fixtures/agent/` still loads or is still refused FOR ITS OWN REASON, with
the needle unchanged.

