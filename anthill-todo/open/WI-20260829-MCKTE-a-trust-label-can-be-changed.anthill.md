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

### 2026-09-06T08:12:46Z — feedback — claude

THE TICKET UNDERSTATES ITS OWN SEVERITY: THE RELABEL REACHES THE GENERATION PATH, WHERE NOTHING STANDS BEHIND IT. Measured 2026-09-05, three scratch fixtures driven through `guardians_test`'s own loader and then reverted.

THE TICKET SAYS the relabel is "NOT an end-to-end exfiltration", because `Email.send` demands `Permission[Outbox]` on an external target and `Triage.run`'s spec row never grants it. That is TRUE, and it is only true of the SINK. Measured, on the two send routes:

  relabel_leak_internal   -- mailbox content relabelled Public, mailed to boss@ourcorp.com
    REFUSED: "unsatisfied precondition ... releasable(text(raw: dot_apply(receiver: all, name: raw, args: nil)))"
  relabel_leak_external   -- the same, to it@othercorp.com
    REFUSED: the same precondition, PLUS "undeclared effect: Permission[T = Outbox]"

Note WHAT refuses them: `releasable`, and the outbox guard. NOT the trust label — the label was successfully stripped in both, and if the body had been a cleared string both would have gone through on the label's account.

THE THIRD FIXTURE IS THE FINDING. `relabel_generate` — `generate_from_content.anthill` with one line changed, `content: text(raw: all.raw)` in place of `content: join_texts(...)`:

  relabel_generate        LOADED CLEAN. No errors at all.

`fixtures/agent/rejected/generate_from_content.anthill` exists to refuse exactly this program, and its header states the stake in the example's own words: "this is the attack the whole staging argument rests on ... build the generation prompt out of the mailbox, and the agent that gets written is an agent an injected email had a hand in designing". The mechanism it names is `prompt_with(instruction: Public, content: ?t) -> Prompt[?t]`, which makes the prompt Untrusted the moment mailbox text enters it, so `Harness.generate(p: Prompt[Public])` will not take one. THE RELABEL WALKS AROUND THAT IN ONE LINE, and unlike the send routes there is no second mechanism behind it: no precondition, no guarded permission, no row. The refusal was the label, and the label is rewritable.

SO THE ANSWER TO "IS SEALING `Text` NEEDED" IS YES, AND THE REASON IS STRONGER THAN THIS TICKET RECORDS. As written the ticket argues from tidiness — a guarded door beside an open window, a claim one level up that is false. The generation path makes it a live hole in the example's headline argument rather than an overclaim in its prose.

CONSEQUENCE FOR THE ARTICLE (/Users/rssh/RD/toWrite/ICTERI-2026, article-anthill-icteri2026-1.tex), and this is why it matters beyond the repository. The section "Example: Generating and Checking the Agent" states: "Generating an agent cannot be influenced by mailbox content, as can be seen from the operation signatures (Listing~\ref{lst:harness})." The signatures do NOT establish that, and `relabel_generate` is the counter-example: it satisfies every signature in that listing and is built from mailbox content. Until the seal lands, that sentence is false as stated and should either be weakened or wait on this ticket.

WHAT THIS DOES NOT CHANGE. The cost measurement stands as the earlier feedback corrected it — 17 sites in two shapes, 10 fact sites in `fixtures/mailbox.anthill` and 7 call sites in `fixtures/agent/`. Adding `relabel_generate` as a permanent refused fixture is part of the acceptance, not a substitute for it: a fixture that measures the hole is not the seal.

### 2026-09-07T11:40:17Z — feedback — user

THE TICKET NAMES THE WRONG MECHANISM, AND ITS OWN FIX DOES NOT CLOSE THE HOLE.
Five fixtures measured 2026-09-07 through `guardians_test`'s own loader (scratch
files under fixtures/agent/, reverted). ALL FIVE LOADED CLEAN.

  relabel via Text projection    text(raw: m.body.raw)          0 errors
  relabel via Address            text(raw: m.from.local)        0 errors
  relabel via MessageId          text(raw: m.id.value)          0 errors
  the feedback channel           attempt(..., [all.raw])        0 errors
  the forged program             source(text: all.raw)          0 errors

Each is `rejected/generate_from_content.anthill` with one line changed, so each
reaches `Harness.generate` — the path the ticket correctly identifies as the one
with no second mechanism behind it.

WHY SEALING `Text` FAILS. The ticket's fix is `internal entity text(...)` plus
smart constructors at the boundary. But 13 sites need a `Text[Public]` —
lib/tasks.anthill:30's instruction, lib/email.anthill:73's `releasable` row,
every cleared `body:` in the agent fixtures — so the seal needs a public
`literal(s: String) -> Text[Public]`, and `literal(m.from.local)` is the same
laundering one call later. The door moves; it does not shut. Rows 2 and 3 above
are the proof that it survives sealing `Text.raw` entirely: neither touches it.

NOR CAN A PERMISSION SHUT IT. `Permission[Declassify]` on the Public door has to
be granted for `good.anthill` and `internal_send.anthill` to send a cleared body
at all, and once `Triage.run`'s row grants it the candidate holds it too. A
permission cannot tell the program's own literal from the attacker's bytes,
because at run time both are `String`. THE DISTINCTION IS SYNTACTIC BY NATURE.

THE RULE THAT COVERS ALL FIVE. No public operation or constructor may take a
`String` and return a value whose TYPE ASSERTS SOMETHING THE STRING CANNOT BACK.
Audited against lib/:

  text(raw: String)              -> Text[?t]         a trust level      VIOLATES
  render_task(... List[String])  -> Prompt[Public]   content-blindness  VIOLATES
  source(text: String)           -> Source           came from generate VIOLATES
  LiveLlm.open(endpoint, model)  -> LiveLlm          model authority    ok (064)
  Address(local:, domain:)       -> Address          NOTHING            ok
  MessageId(value: String)       -> MessageId        NOTHING            ok

SO `Address` AND `MessageId` NEED NO CHANGE, and the reason is worth recording
because the obvious inference is the wrong one: they carry attacker-authored
bytes, but a `String` there buys only matchable structure. Every dangerous use of
a computed `Address` is already refused by the `Permission[Outbox]` guard
(computed_recipient, letbound_recipient), and a fabricated `MessageId` covers no
real message in `mentions_all`. They become load-bearing ONLY if `Text.raw` is
sealed while a `String -> labelled` door stays open — which is an argument for
keeping `.raw` public and closing the doors instead. Keeping it public also keeps
`steering_checker` failing on `Permission[Reveal]` rather than on a name, so no
fixture loses its needle.

THE MINIMAL SHAPE, ranked by hole over fix.

(1) `internal entity source(text: String)` — DELIVERED INLINE with this feedback.
One word, ZERO construction sites in the whole example (`generate` is the only
introduction and is body-less), and it closes the largest hole: the model is not
in the loop at all. `rejected/forged_source.anthill` +
`a_forged_candidate_program_is_refused_by_containment` drive it; control measured,
backing out `internal` turns that one row red and no other.

(2) `entity text(raw: literal String)` — a field modifier admitting only a source
literal. ALL 23 EXISTING SITES ARE LITERALS AND STAY VERBATIM, so lib/, the
mailbox fixture and every agent fixture are untouched; rows 1-3 above die at the
construction site whatever the String's provenance; the `match` spelling dies on
the construction half while the pattern still binds. It needs one grammar token
and one term-shape test at argument binding (the choke point WI-1100 put arity
on). NOT YET IMPLEMENTED — it is the one language affordance this needs, and the
ticket should say so rather than describing a vocabulary fix that cannot work.

(3) `render_task` must JOIN its inputs' labels the way `prompt_with` does, rather
than asserting `Public` unconditionally:
  render_task(self: C, spec: Symbol, tools: List[T = Text[?t]],
              feedback: List[T = Text[?t]]) -> Prompt[?t]
Row 4 above then yields `Prompt[Untrusted]` and `generate` refuses it, by the
mechanism already in the example. THIS IS A DESIGNED FLOW, not an oversight:
`Rejected(diagnostics: List[String])` is documented as feeding `feedback`, and
steering_checker puts `text_of(...)` output straight into diagnostics, so model
output -> feedback -> `Prompt[Public]` is a path the design intends. The cost is
that lib/gate.anthill's diagnostics (`clause_diagnostic`, `symbol_diagnostic`,
`naming_violations`) build `String` from the trusted layer and need a route to
`Text[Public]`. OPEN DECISION: an `internal` `String -> Text[Public]` confined to
the gate's scope (stronger, reintroduces the shape at one site), or leave
`feedback: List[String]` and say plainly that the repair loop is NOT
content-blind and `generate`'s claim covers `tools` only (smaller, truthful).

CONSEQUENCE FOR THE ARTICLE, extending the 2026-09-06 note. The sentence
"Generating an agent cannot be influenced by mailbox content, as can be seen from
the operation signatures" is falsified by a parameter IN THAT LISTING —
`render_task`'s `feedback: List[T = String]` — not only by the relabel. Until (3)
lands the claim must be scoped to `tools`, or the listing must change.

WHAT THE EARLIER COST MEASUREMENT STILL UNDERCOUNTS: it is 23 `text(raw: ...)`
sites, not 17. Eleven facts (ten in fixtures/mailbox.anthill plus
lib/email.anthill:73's `releasable` row) and twelve calls (the seven listed plus
uncleared_body:38, uncleared_external:34, steering_checker:27 TWICE, and
lib/tasks.anthill:30). The two lib/ sites matter more than the number: they put
the seal inside the library, not only in the fixtures. Line numbers in the
earlier list have drifted (computed_recipient:46, letbound_recipient:40). Under
fix (2) the count is moot — every one of the 23 stays as written.

### 2026-09-07T12:42:06Z — feedback — user

CORRECTION TO THE PREVIOUS ENTRY, from /code-review on the inline (1).

"ZERO construction sites in the whole example" IS WRONG. There are three, all in
Rust: `guardians_test.rs` builds a `Source` through
`try_resolve_symbol("guardians.Source.source")` + `Value::Entity` at :390
(`guardians_generate`), :1484 and :2213. §8.6 gates NAME RESOLUTION, so a host
function bypasses it entirely — and must, one of those sites standing in for
`generate`. The claim that holds is "no anthill construction site", and the
property measured is "no CANDIDATE can mint one", not "nothing can". If an
embedder host-fn table (WI-1122) is ever exposed to candidates the seal is void
and no test here would notice. Recorded at the declaration and in measured.md D3a.

AND THE HIDE IS NOT FREE, which the previous entry also overstated. `internal`
leaves `Source` with NO anthill-reachable introduction at all — unlike
`LlmOutput` (paired with `text_of`) and `LiveLlm` (paired with `open`), whose
sibling mints live in the same sort. `generate` is the sole introduction and is
body-less with a host binding, so a pure-anthill `Harness` carrier is now
unwritable. That costs this example nothing (every carrier here declares and the
host implements) but it is a real narrowing and is now written down.

THE ACCEPTED CONTROL IS `fixtures/agent/checker.anthill`. measured.md's own
discipline is that a vocabulary appearing only in refused programs is
indistinguishable from one that refuses everything, and D3 pairs `forged_llm`
with `HonestChecker` for exactly that reason. `HonestChecker` RECEIVES a `Source`
and passes it to the gate, and is accepted — so what `internal` removed is
MINTING, not USE. It cannot be a minting control, per the paragraph above.

DELIVERED with (1): `internal entity source`, `rejected/forged_source.anthill`,
`a_forged_candidate_program_is_refused_by_containment`, measured.md D3a, and the
README containment paragraph. Guardians suite 51 green (was 50); BACK-OUT RUN
50 green / 1 red, that row alone. Full `anthill-core` 5702 green across 12 test
binaries, 0 failures. Diagnostic verified verbatim: `'source' is internal to
'guardians.Source' and cannot be referenced from scope
'guardians.agent.ForgingGenerator.build'`.

ITEMS (2) AND (3) REMAIN OPEN AND ARE THE TICKET'S WORK. (1) closes one of three
independent holes on the generation path; the ticket should not read as narrowed
by it. The `generate` declaration now carries a scoping note saying which half of
its claim is false today, rather than the example shipping prose its own record
contradicts.

