# Every measured run, as a flow

**Status:** Measurement record, 2026-08-22. Probes ran against
`anthill load` at commit `3b980e5c`; sources in [`docs/measurements/guardians/`](../../../../docs/measurements/guardians/). Everything
here was executed — unlike [`effects.md`](effects.md), which is argument.

**Two rows have been re-run since, and only two.** **C2**, after WI-9PGCM: it now
fires. **C1**, after WI-20260822-1MAGR (2026-08-23): `p3_spec_wrong_sig` and
`p7_sig_and_row` are both refused, and `p1_spec_good` — B2's control, and C1's by
reuse — still loads clean. Every other verdict below is the 2026-08-22 reading
against `3b980e5c` and was not re-run.

**Spellings that changed after the runs, and nothing else did.** The marker sorts
`Model` / `FrontierModel` were collapsed into the sorts one acquires, so a row
reading `Permission[Model]` is `Permission[Llm]` today and `Permission[FrontierModel]`
is `Permission[LiveLlm]`; the free operations `fetch_mail` / `send_email` became
`Email.fetch` / `Email.send` when the mail declarations moved into
`lib/email.anthill`; and `bodies_of` is gone, an agent writing
`msgs.map(lambda m -> m.body).collect()` for itself. Signatures, rows and guards
are unchanged, so every verdict below still reads as recorded. Where a CONTROL
stopped being available, the entry says so — see D2.

Each entry is written the same way: **the scenario** (what an attacker or a bad
generation is trying to do), **the flow**, **what fires**, **the control**, and
**what it would mean if it did not fire**. A run without its control measures
nothing, so the controls are not optional reading.

The runs fall into four groups. Group A is data confinement — the `Text[Trust]`
label. Group B is capability confinement — the `provides` chain. Group D
(2026-08-26, added with proposal 064) is authority at the point of ACQUISITION,
which is independent of B and measured to be. Group C is what did *not* work,
which is as load-bearing as the rest. Two of its
rows have since been closed — C1 by WI-20260822-1MAGR and C2 by WI-9PGCM — and both
are kept here with their original verdict beside the new one, because a measurement
record that quietly drops what it measured is not one.

---

# Group A — data confinement

## A1 · The label is enforced where data enters a sink

**Scenario.** The generated agent takes something that came out of the mailbox
and hands it to a sink that is only allowed public data. This is the base case
the whole design rests on; if it does not fire, nothing else matters.

**Flow.**
```
  fetch()  ──▶ Text[L = Untrusted] ──▶ sendPublic( body: Text[L = Public] )
                                                        ▲
                                                        └── mismatch here
```

```anthill
operation fetch()  -> Text[L = Untrusted]
operation sendPublic(body: Text[L = Public]) -> Unit
operation leak() -> Unit = sendPublic(fetch())
```

**Fires** — `docs/measurements/guardians/d2d_typecheck.anthill`:
```
error: type mismatch in sendPublic.body (op-arg):
       expected Text[L = Public], got Text[L = Untrusted]
```

**Control** — `docs/measurements/guardians/d2e_control.anthill`. A blatant sort mismatch,
`takesString(number())` with `number() -> Int64`, produces the same diagnostic
shape. Without it, A1 could be measuring a parse failure or a name that
resolves to nothing rather than a real type check.

**If it did not fire,** labels would be decoration and every other run in
group A would be vacuous.

## A2 · The label survives a transformation — the article's attack

**Scenario.** This is Meijer's exfiltration. The agent does not send raw mail;
it summarizes first, and sends the summary. A design that only checked direct
flows would pass this, and it is the single most important run in the record.

**Flow.**
```
  fetch()          Text[L = Untrusted]
      │
      ▼
  summarize()      Text[L = ?l] ─▶ Text[L = ?l]      ← ?l binds to Untrusted
      │                                                 by unification
      ▼
  sendPublic()     expects Text[L = Public]          ← refused HERE
```

```anthill
operation summarize(body: Text[L = ?l]) -> Text[L = ?l]
operation leak() -> Unit = sendPublic(summarize(fetch()))
```

**Fires** — `docs/measurements/guardians/d2g_leak.anthill`: the same diagnostic, at the `sendPublic`
call. The label propagated *through* the summarizer because `?l` in and `?l`
out is what "summarizing does not launder" means as a type.

**Control** — `docs/measurements/guardians/d2f_propagate.anthill` line 41:
`sendPublic(summarize(banner()))` with `banner() -> Text[L = Public]` loads
clean. The loader reports multiple errors per file and reported none at that
line, so the control genuinely passed. Without it, A2 would be consistent with
a rule that simply forbids calling `summarize` before a sink.

**If it did not fire,** an attacker would need only to insert one pure
transformation between source and sink, and every real agent has several.

## A3 · Widening is one-directional

**Scenario.** A generated agent tries to launder by routing public data through
a widening coercion and back. Widening `Public → Untrusted` is always safe;
the point is that it does not run backwards.

**Flow.** `banner()` → `widen()` → `sendPublic()`, where
`widen(Text[L = Public]) -> Text[L = Untrusted]`.

**Fires** — `docs/measurements/guardians/d2f_propagate.anthill` line 44, refused. Deliberate: the
coercion is one-way and the type checker keeps it that way.

**Control.** A2's control is this run's control too — the same file's line 41
passes, so the file is not simply rejecting everything.

**If it did not fire,** the lattice would be symmetric and therefore not a
lattice.

---

# Group B — capability confinement

These four run over the `provides` route, so they test what happens when the
generated artifact is a **sort implementation** claiming to satisfy a spec.

## B1 · A provision must actually back the member

**Scenario.** The generator emits a carrier and a `provides` clause but no
implementation — the cheapest possible way to claim success.

**Flow.**
```
  spec Agent { operation run(self: C, input: String) -> String @ {Error} }
  carrier EmptyAgent { provides Agent[C = EmptyAgent] }     ← nothing backs run
```

**Fires** — `docs/measurements/guardians/p6_missing_member.anthill`:
```
error: 'EmptyAgent' provides 'Agent' but backs no operation 'Agent.run'
       (no default on 'Agent', no own 'run' on 'EmptyAgent')
```

**If it did not fire,** "generate an implementation" would have a trivial
winning move.

## B2 · The provider's declared row may not widen the spec's

**Scenario.** The generated agent honestly declares that it reaches the outside
world, but the spec never granted that capability. This is the capability
question, separate from anything about data.

**Flow.**
```
  spec    run(...) @ {Error}
  carrier run(...) @ {Error, External}      ← declares MORE than the spec allows
          provides Agent[C = LeakyAgent]
```

**Fires** — `docs/measurements/guardians/p2_spec_wider_row.anthill`:
```
error: 'LeakyAgent' overrides 'Agent.run' but does not refine it: the override
       declares effect `External`, which is not covered by any effect the spec
       operation declares (effects must not widen)
```

**Control** — `docs/measurements/guardians/p1_spec_good.anthill`. A conforming provider with row
`{Error}` loads clean, so B2 measures the row and not a blanket refusal of
`provides`.

**If it did not fire,** the spec's effect row would be documentation, and
`-External[Commit]` — the design's strongest single claim — would mean nothing.

## B3 · The body may not exceed its own declaration

**Scenario.** The obvious evasion of B2: declare narrowly, act widely. The
generated `run` declares `{Error}` and then calls an operation that is
`External`. If this does not fire, B2 is trivially bypassed and the whole
capability story collapses.

**Flow.**
```
  carrier run(...) @ {Error}   ← declaration satisfies B2
              │
              └──▶ calls leak(...) @ {External, Error}   ← body exceeds it
```

**Fires** — `docs/measurements/guardians/p4_body_exceeds.anthill`:
```
error: type mismatch in run.effects (op-effects):
       expected declared: [Error], got undeclared effect: External
```

**Control** — `docs/measurements/guardians/p5_body_control.anthill`. The identical shape with a
callee typed `{Error}` loads clean, so B3 measures the inferred row and not the
presence of a call.

**If it did not fire,** every effect annotation in the language would be a
promise nobody checks, and B1/B2 would be theatre.

## B4 · A reshaped member does not smuggle a row past the check

**Scenario.** Backing is matched by short name (WI-935), so it is worth asking
whether a differently-shaped `run` escapes the widening rule by not lining up
with the spec's declaration.

**Flow.** A member named `run` with the wrong arity, the wrong return type, and
`External` in its row.

**Fires** — `docs/measurements/guardians/p7_sig_and_row.anthill`: refused by B2's rule, unchanged.
Name-only matching is enough for the effect check. (Since WI-20260822-1MAGR it is
refused twice — the wrong arity is now its own refusal, C1 — but B2's verdict here
never depended on that.)

**If it did not fire,** WI-935 would be a security gap rather than a
correctness one, and the chain B1→B2→B3 would have a hole at the bottom.

---

# Group D — authority at the point of acquisition (2026-08-26)

Added when proposal 064's `Permission[X]` landed (WI-20260825-CBRSW) and this
example became its first consumer. Group B confines what a generated agent may
DO; this group confines what it may ACQUIRE.

**What was actually missing, before anything else here makes sense.** Acquisition
was not typed at all. `LiveLlm`/`FakeLlm`'s entity constructors were public and
construction carries no effect, so a generated component could obtain a model out
of thin air, and `-Model` caught it only if it went on to CALL one. A checker that
acquired a model and stashed it, or passed it to something else, was unconstrained
by anything in the example. D3 closes the forging route and D1 types the remaining
one.

Run against `anthill load examples/guardians` and
`cargo test -p anthill-core --test guardians_test` at the commit that added them.

## D1 · Acquisition is confined by the same leg that confines use

**Scenario.** `Checker.check` must provably not be steerable by a model. There
are TWO ways to be steered, and they are caught at different moments:

| the checker… | fixture | what performs the effect |
|---|---|---|
| holds an `Llm` it was handed, and calls it | `rejected/bad_checker.anthill` | `complete` → `Model` |
| holds none, and MINTS one | `rejected/minting_checker.anthill` | `LiveLlm.open` → `Permission[Model]` |

**Flow.** `bad_checker` smuggles an `Llm` into its own carrier (`entity mk(llm:
Llm)`) and reaches it through `self`; it acquires nothing, so no `Permission` is
ever performed. `minting_checker`'s carrier is bare `mk` — an audit of "what was
this checker handed" comes back empty — and its body mints; it consults nothing,
so `Model` is never performed.

**Fires,** both on B3's body leg, each naming the label its own program performed:

```
check.effects (op-effects): expected declared:
    [External, Error, -Model, -Permission[T = Model]],
  got denied effect: Model — the row DECLARES `-Model` …
```
```
  got denied effect: Permission[T = Model] — the row DECLARES `-Permission[T = Model]` …
```

**Control**, and it corrects what an earlier draft of this entry claimed. Deleting
a denial from the spec, its carrier and the fixtures does **not** make the fixture
load — measured, both directions:

| edit | `bad_checker` | `minting_checker` |
|---|---|---|
| drop `-Permission[Model]` | refused (`denied effect: Model`) | **still refused**, as `undeclared effect: Permission[T = Model]` |
| drop `-Model` | **still refused**, as `undeclared effect: Model` | refused (`denied effect: Permission[T = Model]`) |

**So a `-X` on a CLOSED row is the contract, not the mechanism** — "not in the
row" already means "not incurred", and B3 refuses either way. What the denial buys
is that the claim is written where a reviewer reads it, and that the diagnostic
names a VIOLATED denial rather than a missing declaration: two failures whose
repairs differ, since an undeclared effect is fixed by adding the label and a
denied one cannot be. `guardians_test` asserts the `denied effect` needle, so both
rows do go red under the edits above — the fixture's verdict does not change, the
message does.

The positive control is separate and load-bearing: `guardians.open_round`
(`lib/harness.anthill`) mints legitimately and declares `{Permission[Model],
External, Error}`, while `guardians.attempt` — the same round with the
capability in hand — declares no `Permission`.
`the_legitimate_acquisition_path_is_accepted` reads both rows back out of the KB,
so moving the label downstream fails it.

**If it did not fire,** a generated checker could mint its own model. That is not
hypothetical: it is what this example permitted before 064, since construction
carried no effect at all.

> **SUPERSEDED IN ONE ROW, 2026-08-29 — and the measurements above are kept
> because they are what identified the defect.** The `bad_checker` row is gone:
> `Llm.complete` now returns `LlmOutput[Text[Untrusted]]`, sealed with an
> `internal` constructor, so a checker handed an `Llm` receives a token it can
> neither project nor match. `-Model` was deleted along with the `Model` effect
> kind, and `rejected/bad_checker.anthill` is ACCEPTED today.
>
> **What this entry got wrong, and it is a methodological point rather than a
> detail.** Every measurement above is sound, and the control table still reads
> correctly. What none of them asked is whether `bad_checker` is an ATTACK. It
> calls a model and DISCARDS the reply — it returns a hardcoded `Rejected` — so it
> demonstrates CONTACT, never STEERING, and a verifier that ignores an oracle's
> answer is not steered by it. The fixture was built to exercise `-Model` and was
> then read as evidence that `-Model` was needed. A control that varies the
> MECHANISM (delete the denial, watch it red) cannot see a requirement that was
> never in question; only varying the REQUIREMENT can, and nothing here did.
>
> The `minting_checker` row is untouched and still fires: acquisition remains the
> one thing worth denying, so the denial and this group's positive control both
> stand exactly as recorded. It is SPELLED differently now — the marker sort
> `Model` is gone, a capability being the sort you actually acquire — so the row
> reads `-Permission[Llm]` and the diagnostic `denied effect: Permission[T = Llm]`.
> What the measurement established is unchanged; only the argument's name is.

## D2 · A sub-capability is named as a violated denial, not as an omission

**Scenario.** The row denies `Permission[Model]`. A generated checker asks for
something whose NAME is different: `Permission[FrontierModel]`.

**Flow.** `rejected/frontier_checker.anthill` calls `LiveLlm.open_frontier`.
`FrontierModel <: Model` (vocabulary.anthill), declared with an ordinary
`provides` on a constructor-less sort.

**Fires** — `got denied effect: Permission[T = FrontierModel] — the row DECLARES
-Permission[T = Model]`.

**Control.** Deleting `provides Model` from `FrontierModel` — leaving the two
capabilities unrelated — reds this row alone. It does not make the fixture load:
the message degrades to `undeclared effect: Permission[T = FrontierModel]`,
because B3 refuses an unrelated capability just as readily. What the closure
decides is whether the checker is told it broke a denial it wrote, or merely
forgot a declaration it never intended to write.

**THE MECHANISM IS ENTAILMENT, NOT THE DECLARED CONTRAVARIANCE**, and the two run
opposite ways — an earlier draft of this entry got it backwards.
`fact Contravariant(sort: Permission, param: T)` is the SUBSUMPTION rule (a spec
granting `Permission[AdminFs]` accepts an implementation taking only
`Permission[Fs]`). The closure is the other direction: acquiring an `X` IS
acquiring a `Y` whenever `X <: Y`, which runs COVARIANTLY in the capability and
needed its own rule in the kernel (`typing::permission_entails`). See
`stdlib/anthill/prelude/permission.anthill`.

**If it did not fire,** the denial would still refuse the program, but would name
the wrong failure — and on an OPEN row, where a lacks-constraint is the only thing
standing between a program and a capability, it would not refuse it at all. That
case is measured in the kernel, not here:
`wi_cbrsw_permission_effect_test::permission_denial_is_not_evaded_by_a_sub_capability`.

> **SUPERSEDED IN ITS SPELLING AND IN ITS CONTROL, 2026-08-29.** The marker sorts
> `Model` and `FrontierModel` are gone — a capability is the SORT YOU ACQUIRE — so
> the row denies `Permission[Llm]` and `open_frontier` demands
> `Permission[LiveLlm]`. The sub-capability edge is no longer an empty marker's
> `provides` but the production one, `LiveLlm provides Llm` (lib/llm.anthill), and
> the fires-line reads `got denied effect: Permission[T = LiveLlm]`. The MECHANISM
> paragraph above is untouched: entailment still runs covariantly in the
> capability, opposite to the declared contravariance.
>
> **The control recorded above no longer exists, and that is the real cost of the
> collapse.** Deleting `provides Model` from a constructor-less marker reddened
> this row alone; deleting `provides Llm` from `LiveLlm` takes the whole example
> down, because `LiveLlm` is the production carrier every accepted fixture runs
> through. Nothing at fixture level isolates the closure any more — what does is
> the kernel test already cited under "If it did not fire".

## D3 · Containment is what stops the effect being advisory

**Scenario.** Skip the gate entirely: name the capability object's constructor
directly.

**Flow.** `rejected/forged_llm.anthill` writes `fake_llm(fixture: "advice")`.

**Fires** — `'fake_llm' is internal to 'guardians.FakeLlm' and cannot be
referenced from scope 'guardians.agent.ForgingChecker.check'`. A NAME RESOLUTION
failure, not an effect-row one, so it holds for a body carrying no effects at
all: `internal` is §8.6's only hide gate, and WI-977 puts a sibling namespace
outside the declaring scope.

**Control.** Removing `internal` from `fake_llm` reds this row alone — and that
is not a hypothetical edit: it is what this file said before 064. The constructors
were public, so every row in D1 and D2 could be satisfied by a checker that simply
never used a gate.

**If it did not fire,** D1 and D2 would both be true and both useless. THIS is the
row the other two rest on, which is the reverse of how the group reads at first
glance.

## D4 · A permission can be CONDITIONAL, and the article's policy is one

**Scenario.** The article states the policy as *"forbid data flow from
`fetch_email`'s result as the source to the `body` parameter of `send_email` with
an external email address as the target"*. That sentence has two halves, and they
are checked by two independent mechanisms — neither of which catches the other's
program.

| half | mechanism | fixture |
|---|---|---|
| the FLOW (`fetch_email`'s result reaching `body`) | the `Text[Trust]` label (group A) | `rejected/leak.anthill` |
| the TARGET (an external address) | a GUARDED `Permission[Outbox]` | `rejected/outbox.anthill` |

**Flow.** `send_email` carries
`effects {External, Error, (Permission[Outbox] :- external_addr(to))}` —
proposal 048's conditional effects on 064's label. At a call the argument is
substituted into the guard, and the label is dropped when the guard's negation is
constructively proved (§5.5). `rejected/outbox.anthill` mails a LITERAL `Public`
string to `it@othercorp.com`: nothing flows out of the mailbox, no label is
violated, and it is refused anyway.

**Fires** — `run.effects (op-effects): expected declared: [External, Model,
Error], got undeclared effect: Permission[T = Outbox]`.

THE PROPERTY IS THE SPEC'S, NOT THE AGENT'S, which is what makes it worth having:
`Triage.run` grants no `Permission[Outbox]`, so an implementation can neither
PERFORM one (what fires here) nor DECLARE one (a widening, group B). No generated
triage can mail outside the organisation, whatever it does.

**Control** — `fixtures/agent/internal_send.anthill`, ONE TOKEN away
(`boss@ourcorp.com` for `it@othercorp.com`), which LOADS on the unchanged
`{External, Error}` row. Two further edits, each reddening exactly one row
and measured:

| edit | red |
|---|---|
| drop the guard (make the permission unconditional) | `an_internal_send_needs_no_permission` — that row alone |
| drop `Permission[Outbox]` from `send_email` | `an_external_send_is_refused_by_the_conditional_permission` **and** `a_recipient_computed_at_run_time_is_refused` |

So the guard and the permission are separately load-bearing: the first decides
*when* authority is demanded, the second *that* it is. The second edit greens TWO
rows and not one — an earlier draft of this table claimed "each reddening exactly
one row", which was not run. In a record whose whole purpose is the control, an
unmeasured control is the defect it exists to prevent.

**If it did not fire,** the example would be enforcing "no generated agent may
send mail", which is both weaker and far less useful than the policy the article
states — and, being a refusal, would look identical in a suite with no control.

**THE GUARD IS DECIDED AT LOAD, so an address the checker cannot read demands the
authority too.** `rejected/computed_recipient.anthill` mails what
`choose_recipient` returns; the guard is neither proved nor refuted, and §5.5
keeps the effect on an undecided guard. Measured — same refusal, opposite route
(proved guard vs undecided guard), which is why it is its own fixture: a change
making an undecided guard DROP its effect would leave D4's first row green and
this one red.

**The rule is narrower than "provably internal", and stating it loosely was an
error in an earlier draft of this entry.** The guard is refuted only where the
checker can prove `in_org(to)` from the argument TERM AT THE CALL, so the address
must be written INLINE. Measured: `rejected/letbound_recipient.anthill` is
`internal_send.anthill` with the identical literal `let`-bound one line earlier,
and it is REFUSED — `refute_guard` proves the negation over Γ, a `let` deposits an
equation SLD does not use to ground the goal, the double negation flounders, and
§5.5 keeps the effect. Sound (it errs toward demanding authority) but stricter
than intended, since the bound value is statically known: a typer limit rather
than a policy decision, and worth a ticket.

So the operative rule is: **a generated agent may mail only an address written
literally, inline, at the call** — and matching a deployment's `in_org` rows.
Everything else needs an authority `Triage.run` never grants. A genuinely dynamic
recipient belongs to the trusted harness, which can hold `Permission[Outbox]`
where a generated agent cannot.

**WHOSE FACT `in_org` IS.** `lib/email.anthill` DECLARES it (proposal 061)
and asserts no row; `fixtures/mailbox.anthill` supplies it, like the inbox and the
address book — `safety.anthill`'s principle, that the relation is the library's
and the rows are a deployment's. The default is CLOSED: with no deployment
loaded the relation is empty, every address is external, and even
`internal_send.anthill` is refused. An unconfigured organisation grants nothing.
Pinned by `the_organisations_identity_is_a_deployment_fact_and_the_default_is_closed`.

**WHY THIS IS NOT AN `ensures`,** which is where this design started. A
postcondition would have been the obvious home for a safety statement, and it is
the wrong one: `ensures` is ASSUMED at a call site, checked only for
non-weakening at an override, and never proved from a body — and the evaluator
does not check it either (measured: no postcondition check exists in
`eval/`). A safety claim written there is a claim the implementation restates,
not one the checker establishes. Moving the target half into the ROW makes it a
refusal instead.

---

---

# Group E — the trust partition, as an analysis rather than a text scan (2026-08-28)

Added by WI-20260824-5XBBQ, the hand-off WI-20260823-SPGBP named: a scoped load
makes a candidate's contribution *distinguishable*, and a gate over what it
DECLARED and ASSERTED is what turns that into a refusal.

**What was there before, and why it had to be text.** The gate was
`namespace_violations` in `guardians_test.rs`: a walk over `src.lines()` matching
the prefixes `namespace `, `sort ` and `enum `. It read TEXT because that was the
only moment provenance existed — the candidate was loaded as
`try_load_kb_prepared_files(&[lib…, fixtures…, candidate])`, one flat list into
one KB, after which nothing distinguished its declarations from the library's.

Groups A–D are all about what a generated agent may DO. This group is about what
it may SAY: every measurement below is a program that passes every check in
A–D and then simply asserts what it wants to be true.

Run through `rustland/target/debug/anthill load` over `lib/` + `fixtures/` + one
candidate with `good.anthill` removed, and through
`cargo test -p anthill-core --test guardians_test`. Baseline (lib + fixtures +
good): `loaded: 2895 facts, 218 rules`.

## E1 · The safety fact, forged about itself

**Scenario.** `guardians.TypeChecked` is `lib/safety.anthill` — the
relation a safety claim cites, whose rows a real typer verdict would supply. A
candidate declares a carrier under `guardians.agent.` and then reopens the
trusted namespace to assert one about itself:

```anthill
    namespace guardians
      fact TypeChecked(carrier: "guardians.agent.ForgeTriage", spec: "guardians.Triage")
    end
```

**Measured, before.** Loads at `2896 facts, 218 rules`, and
`query --mode functor 'guardians.TypeChecked'` goes from `0 result(s)` to the forged
row. Type checking has nothing to say: the fact is well-formed.

**Measured, now.** Refused —
`the candidate asserts a fact at 'guardians.TypeChecked', a name it did not declare`.
The clause heads at a symbol the layer did not mint.

**It is the LEAST severe of the three.** At the time, `agent_is_safe` also needed
`ToolAlgebraSound` — since deleted, both of them: no rows, no uses, no definition
of what "sound" meant. So the forged claim was
underivable regardless. E2 is the one that was live.

## E2 · The concealment guarantee, inverted — and proposal 061 does not see it

**Scenario.** `guardians.mentions_all` is the `ensures` on `Triage.run`, and
`lib/spec.anthill`'s own comment calls it "exactly the CONCEALMENT half of the
injection". Its trusted clause is `:- not(omits_some(?r))`. The candidate adds a
second:

```anthill
    namespace guardians
      rule mentions_all(?r)
        :- omits_some(?r)
    end
```

The postcondition then succeeds exactly when the report OMITS a message.

**Measured — 061 protects a FLAT load and not a LAYERED one, and this decided the
fixture.** On one flat load, proposal 061 refuses the bare clause loudly, naming
both files — *and tells the attacker what to write*: supply
`rule mentions_all(?)` as a declaration in the same file and it loads, at
`2885 facts, 218 rules`, with two clauses under `mentions_all`. Under the layer
the checker actually uses, 061 does not fire AT ALL: the bare clause above loads
with no diagnostic and `mentions_all` goes from one clause to two. So 061 is a
HYGIENE rule and never was a trust boundary, and the fixture is the bare form,
because that is what reaches the KB under the design in use.

**Measured, now.** Refused —
`the candidate asserts a rule at 'guardians.mentions_all'`. The diagnostic names
the predicate, where the text scan named a line number.

## E3 · Hand-written reflect metadata, beside the loader's own

**Scenario.** A candidate writes a reflect row by hand:

```anthill
    namespace guardians.agent
      import anthill.reflect.{SortProvidesInfo}
      fact SortProvidesInfo(sort_ref: LiarTriage, spec: LiarTriage)
    end
```

**Measured, before.** Loads clean, and the functor then carries BOTH rows:

```
    SortProvidesInfo(sort_ref: LiarTriage, spec: SortView(Triage, C: LiarTriage))   -- loader
    SortProvidesInfo(sort_ref: LiarTriage, spec: LiarTriage)                        -- candidate
```

indistinguishable in the clause store except by well-formedness.

**THIS DECIDED THE SHAPE OF THE GATE.** A check phrased over reflect facts is
reading a channel its own subject can write. Two things follow, and both are in
the delivered design:

* The layer delta is exposed as OPERATIONS (`KB.layer_symbols`,
  `KB.layer_clauses`) rather than as emitted facts. They read engine-side marks
  outside the clause store.
* Clauses carry an ORIGIN (`ClauseOrigin::Source` / `Derived`), set by the loader
  at the moment it asserts. Without it the containment rule refuses
  `good.anthill`: its own `provides Triage[C = GoodTriage]` makes the loader bank
  a `SortProvidesInfo` row at a symbol the candidate did not declare. A
  name-based exemption ("head functor not under `anthill.reflect`") would be the
  wrong shape and would re-open exactly this measurement.

**Measured, now.** Refused —
`the candidate asserts a fact at 'anthill.reflect.SortProvidesInfo'` — while the
loader's row for `good.anthill` is admitted. The two assertions are each other's
control.

## E4 · The third channel: a redeclaration mints nothing

**Scenario.** A layer can rewrite a declaration the BASE owns. Nothing is
minted — the load re-enters the same symbol — and nothing is asserted, so neither
the mint high-water mark nor the containment rule sees it:

```anthill
    sort guardians.Triage
      sort C = ?
      operation run(self: C, box: Mailbox, llm: Llm) -> Report
        effects {External, Error, Filesystem}
    end
```

**Measured.** It loads. `guardians.Triage` keeps the same `Symbol`, and the load
banks a SECOND `OperationInfo` row for `run`: the reported effects go from
`[External, Error]` to
`[External, Error, External, Error, Filesystem]`.

**What it does NOT buy, and this is why the effect budget is not re-checked.** A
widening carrier is refused with the identical message
(`effects must not widen`) with and without the redeclaration present — the
override-refinement pass compares against the stored signature, not against the
fact. So re-deriving the budget from `OperationInfo.effects` would be strictly
WEAKER than what the load already does. The row appears in the verdict as
REPORTED, read from the BASE before the layer is applied, and never as
re-checked.

**Measured, now.** Refused by the naming rule —
`the candidate redeclares 'guardians.Triage'`. This is what `LayerSymbol.declared`
exists for; the mint mark alone is blind to it.

## E5 · What the accepted verdict says

**Scenario.** Before this group, `guardians_check` returned
`Accepted(carrier: "guardians.agent.Generated")` — a hardcoded string naming a
sort no candidate ever declares — and its `spec: String` parameter was ignored
entirely. The checker never learned what it had accepted, and a candidate that
loaded clean while implementing NOTHING was Accepted.

**Measured, now.** `spec` is a `Symbol` reference, and
`agent/good.anthill` yields `Accepted(carrier: guardians.agent.GoodTriage,
spec: guardians.Triage, budget: [External, Error])`. A candidate that
declares only under `guardians.agent.` and provides nothing is refused:
`the candidate declares no carrier that provides 'guardians.Triage'`.

## E7 · A denial over the trusted base — the clause with no head functor

**Scenario.** `rule ⊥ :- InMailbox(box: ?b, message: ?m)` is a DENIAL: it asserts that
its body must never hold. A candidate that installs one does not add a fact, it
FORBIDS one, over a relation the trusted library owns.

**Measured — it was a CRASH before it was a refusal, and review found it.** `Term::Bottom`
heads at no symbol, so the delta reader raised an `EvalError::Internal` the checker had
no way to turn into a verdict: three lines of candidate source denied the gate a verdict
at all, rather than being refused by it.

**Measured, now.** `LayerClause.functor` is an `Option` — a denial is REPORTED with
`none`, because a clause a policy cannot see is a clause it cannot refuse — and the
containment rule refuses it: `the candidate asserts a rule at a denial head (⊥)`.

## E6 · A candidate's own `mentions_all` does not discharge the spec's

**Scenario.** The narrower form of E2, asked once containment closes the wide
one: the candidate declares its OWN `guardians.agent.mentions_all`, trivially
true, and restates `ensures mentions_all(result)` so the override's postcondition
names that one.

**Measured.** REFUSED, by the typer rather than by the gate:
`'guardians.agent.ShadowTriage' overrides 'guardians.Triage.run' but does not
refine it: it weakens the postcondition`. Contract refinement
(WI-20260822-59CDQ) binds the override's `ensures` to the spec's predicate BY
SYMBOL, so a same-named local cannot discharge it. Recorded as a control rather
than a finding — it passes with or without the gate, and it is here because the
gate is what makes the narrow question the binding one.

---

---

# Group C — what does not work

## C1 · Signature conformance · **closed by WI-20260822-1MAGR**

**Scenario.** The generated implementation claims to provide a two-argument,
`Report`-returning spec with a one-argument, `Int64`-returning member.

**Loaded clean at `3b980e5c`** — `docs/measurements/guardians/p3_spec_wrong_sig.anthill`.
The spec said so outright: *"treat a provision as certifying that a member of
that name exists, not that it fits"* (WI-935).

**Fires now.** WI-20260822-1MAGR compares arity, parameter types and order, and
the return type wherever the spec operation has no implementation of its own that
would back the carrier — no default body and no resolver builtin — which is
exactly the shape of a spec an agent is asked to implement, since a spec
operation that already carries one is not something the generator has to supply.
(A host `operation_map` on the spec's own member is deliberately not counted: it
names no carrier, so it never backs one — WI-876.) `smoke.p3.Agent.run` is body-less, so `WrongSigAgent.run` is the only
thing that could back it, and the load is refused naming both shapes. The same
rule adds a second refusal to `p7_sig_and_row.anthill` (B4), which was already
refused by B2's row rule alone.

**Why it mattered here more than usual, and what changed.** For hand-written
code the gap was a latent mis-dispatch. For **generated** code it was backwards:
a bad generation was accepted at check time and failed at the first call, when
the entire premise of the workflow is that the checker tells the generator what
to fix. It was never a security hole — B4 showed the row chain was unaffected,
and a member nothing can call correctly reaches no sink — but it was on the
critical path, and it is off it. (It was recorded as *the* only such item; C2
turned out to be a second, and WI-9PGCM closed that one.)

**What is still not compared,** and stated because a generator will meet it: a
member whose spec operation *does* carry a default body (a same-named member of a
different signature is then a distinct operation, and the default is what backs
the provision), a parameter the spec types as itself (the dispatch receiver,
which an override narrows to the carrier by design), and a swap of two parameters
of the *same* type, which no comparison of types can see.

## C2 · An operation `requires` gates a call site — after WI-9PGCM

**Scenario.** Express the flow lattice as a contract —
`send(body: Text[L = ?l]) requires flows_to(?l, Public)` — and let the KB hold
the lattice as facts.

**Fires** — `docs/measurements/guardians/d2c_callsite.anthill:33`, at the `leak()`
body:

```
type mismatch in smoke.c.send.requires:
  expected precondition `flows_to(Untrusted, Public)` provable at the call site,
  got unsatisfied precondition
```

The argument's declared type binds `?l := Untrusted`, so the obligation is
grounded to the lattice edge that is deliberately absent, and the call is
refused.

**Control.** `ok()` in the same file — `Text[L = Public]` into the same sink —
still loads: `flows_to(Public, Public)` is a fact. And `flows_to(Untrusted,
Public)` correctly has **no solutions** when queried, so the lattice facts are
right in both directions.

**This row previously read `❌ by design (§8.5)`, and that was wrong twice
over.** It loaded clean, which was measured correctly; the *citation* was not.
§8.5 is about obligations on the **implementation**, discharged by agents against
an `Implementation` fact; §5.4 documents WI-539's later split, under which a
clause naming no spec is a **value precondition**, "proved, at the call site, from
what the caller knows". `flows_to(?l, Public)` names no spec and was in fact
routed to that check. It did not fail there by design — it *passed*, because `?l`
was left free and a free variable in a goal is witnessed **existentially**: the
clause proved itself off the unrelated `flows_to(Public, Public)` fact at every
call. Deleting that one fact made the *control* call fail too, which is the
measurement that shows the label was never being read at all.

**Consequence.** The lattice ordering CAN ride on the operation contract for a
call whose argument type decides the label. It still cannot for a
label-polymorphic wrapper: an undetermined label floats (WI-067 — never decide an
obligation by absence), and a wrapper that declares no contract of its own
swallows its callee's obligation rather than propagating it.

## C3 · A rule body cannot destructure a type argument

**Scenario.** Let policy rules read the label —
`releasable(?x) :- ?x: Text[L = ?l], flows_to(?l, Public)`.

**Syntax error** — `docs/measurements/guardians/d2h_ruleside.anthill`, at `?x:`. This is WI-742,
explicitly unimplemented in proposal 060.

**Consequence.** Labels live in the typer and are invisible to the rule layer,
so policy about labels must be expressed as operation signatures, not as rules.

## C4 · The label slot is invariant BY DEFAULT — and variance is declarable · **corrected**

**Scenario.** Get widening free from subtyping: pass `Text[Public]` where
`Text[Level]` is expected.

**Refused** — `docs/measurements/guardians/d2j_variance.anthill`:
`expected Text[L = Level], got Text[L = Public]`.

**The correction, and it matters because the original conclusion was wrong.**
That probe measured the **default**, and the default is invariant — which is
all it establishes. anthill *has* variance, declared as facts
(`Covariant(sort, param)` / `Contravariant`, `stdlib/anthill/reflect/typing.anthill`),
and `type_compatible` has a `provides` arm alongside identity, `is_entity_of`
and `refines`. So a lattice modelled as a **provides-chain** with a covariant
parameter gives the ordering directly:

```anthill
sort Untrusted end
sort Public  provides Untrusted end
fact Covariant(sort: Text, param: Trust)
```

| | |
|---|---|
| widening — `Text[Public]` into a `Text[Untrusted]` slot | **loads** |
| the dangerous direction — `Untrusted` into `Public` | **refused** |
| the same widening with the `Covariant` fact **deleted** | **refused** |

The third row is the one that matters: it shows covariance is doing the work
rather than the slot being unchecked.

**What this retracts.** The earlier entry concluded that widening needs explicit
coercions and that an *n*-point lattice costs O(*n*²) of them. Neither stands.
The `widen` operation in `lib/vocabulary.anthill` is unnecessary, and D2's
"scales to two or three levels and no further" was a conclusion drawn from a
probe that never declared the thing it was measuring the absence of.

**What survives.** The label position *is* invariant unless you say otherwise,
so a design that wants ordering must declare it — silence gives you the safe
default rather than the useful one. That is the right default and worth stating;
it just is not a limit.

**Related, and still open.** The label slot is also **untyped**: `sort Trust = ?`
accepts anything, so `Text[Int64]` loads clean, and a `requires IsLevel[T = Trust]`
does not constrain it either (both measured). Variance orders the labels; nothing
requires the argument to *be* one.

## C5 · A computed region is not admissible in `Modify[…]`

**Scenario.** State Meijer's frame condition directly —
`delete_files(fs, pattern) @ Modify[glob(pattern)]`.

**Syntax error** — `docs/measurements/guardians/d3_frame.anthill`:
```
error: syntax error near `glob`
error: a single parenthesized type is not a type
```
The region slot is a *type* position, so a parenthesized application is refused
by the type grammar.

**Settled, and the wording above was the misleading part** (WI-20260823-39AD2). The
slot is a type *position* in the grammar's sense, but what may stand in it is a
**place**, not a type: a parameter, `result`, or a field path off one. A type there
(`Modify[Cell]`, `Modify[T]`) is now a load error in its own right — see
kernel-language.md §5.6. So a computed region is refused for the same reason under
both readings, and this entry stays ❌: `glob(pattern)` denotes no slot in `Env`. A
frame condition over a computed set of files needs a *named* resource standing for
the filesystem (`Modify[fs]`, control (a) in the smoke) plus a `requires` narrowing
which part of it is touched — the smoke's (a) already works.

**Control.** `Modify[no_such_thing_at_all]` is an unresolved-name error, so the
slot is genuinely name-resolved and the forms that *do* pass — `Modify[fs]`,
`Modify[pattern]` — are not passing vacuously.

**Consequence.** The `delete_file` scenario is deferred out of increment 1.
§5.6's effect-env condition really is the frame axiom; what is missing is only
the surface for writing a computed region.

## C6 · A constructor cannot carry a type argument

**Scenario.** Introduce a label at a construction site —
`mk[L = Untrusted](raw: "secret")`.

**Refused** — `docs/measurements/guardians/d2b_callsite.anthill`, with a diagnostic naming every
position where the bracket *is* read.

**Consequence, and it is a feature.** Labels can enter only through operation
signatures, so the label on a piece of data always comes from the tool that
produced it and never from code that merely handles it. The design wanted that
discipline; the language enforces it.

## C7 · A sort mismatch against a variable-containing type passed silently · **FIXED**

**Scenario.** Not an attack that was designed — this one was found by writing
the vocabulary out as a real file and watching the exfiltration *succeed*.

The design's whole mechanism is `summarize(body: Text[Trust = ?t]) -> Text[Trust = ?t]`.
A2 measured it refusing the leak. But A2 passes a `Text` in. Pass a **different
sort** — a `Message`, which is what `fetch_mail` actually returns — and:

```anthill
operation fetch_one() -> Message[Trust = Untrusted]
operation sum_flat(m: Text[Trust = ?t]) -> Text[Trust = ?t]
operation sink(body: Text[Trust = Public]) -> Unit
operation leak() -> Unit = sink(sum_flat(fetch_one()))
```

**Loaded clean.** `docs/measurements/guardians/` reproduction in the `nest3`/`nest4`
shape. `Message` where `Text` was expected raised nothing, `?t` was never bound, and it
then bound to `Public` at the sink. The exfiltration went through.

**Controls, and they are what make this precise.** Ground against ground *is*
checked — `send_email(to: 42)` gives `expected Address, got Int64`, and A1/A2
fire. Nesting is *not* the cause — `List[T = Text[Trust = Untrusted]]` into
`List[T = Text[Trust = ?t]]` propagates correctly and the sink refuses it. The
variable is the cause: **an argument checked against a parameter type
containing a type variable is not rejected on a sort mismatch**, and the
silent pass leaves the variable free rather than erroring.

**Why it matters more than a typical typer gap.** A free variable is not a
neutral outcome here — it is the *maximally permissive* one, because the
consumer instantiates it to whatever it wants. So the failure mode is not "a
wrong program is accepted", it is "the label is laundered", which is exactly
the property the design exists to prevent.

**How it was found, and the lesson.** `examples/guardians/vocabulary.anthill`
was written to answer "where are these definitions?". The first agent written
against it — `send_email(body: summarize(fetch_mail(box)))`, the obvious
spelling — loaded clean. The smoke tests had never caught it because they used
one sort throughout. **A vocabulary of one sort cannot exercise a sort
mismatch**, and every run in group A was written that way.

**Fixed in `kb/typing.rs` (WI-RKMD4).** `validate_arg_against_param` gates on
groundness — a pair still carrying a variable is someone else's to settle, so it
returned `Ok` unchecked. That is right about the variable's *slot* and wrong
about the constructor the slot hangs off, and nothing downstream re-asked it:
the argument-unify loop's failure to bind `?t` is discarded, so `?t` reached the
sink still free. The gate now also asks whether the pair disagrees at a
**nominal head constructor**, descending through the parameters two instances of
one sort share, and refuses when it does:

```
type mismatch in sum_flat.m (op-arg): expected Text[Trust = ?t],
                                      got Message[Trust = Untrusted]
```

Both shapes above are refused — the flat one at `sum_flat.m` and the container
one at `sum_list.msgs`, one level beneath a `List` the two sides agree on. The
two controls still hold: ground-against-ground is refused as before, and the
matching-element container still **propagates** `Untrusted` and is refused at the
*sink*, not at the polymorphic call.

**The same hole was one coordinate over**, and was closed with it: a **callback
parameter** carrying the variable — `run(f: (m: Text[Trust = ?t]) -> Int64)` given a
`Message`-taking arrow, and the mirror with the variable on the slot's side — was skipped
by the identical per-component groundness gate, while the all-ground pair beside it was
refused. Both directions now refuse.

**The carve-out the fix needed re-opened the defect once, one level down.** `Option` and
reflect-`Term` must be withheld, because the ground path *accepts* them instead of
comparing — but both are properties of the ARGUMENT position, and honouring them at every
recursion depth left `take(xs: List[T = Option[T = Text[Trust = ?t]]])` accepting a
`List[T = Message[…]]`, laundering exactly as before. A second instance sat at the callback
site, where the pair is handed over slot-first. Found by `/code-review` after the workspace
was green, and closed by making the position an enum rather than a flag.

`wi_rkmd4_type_var_param_slot_test` carries seven refusals with nine controls, and
`guardians_test::a_wrong_sort_at_a_label_polymorphic_parameter_is_refused` carries one row
at **this** vocabulary — one token from `agent/good.anthill` — because a synthetic
reproduction cannot say the fix reaches the real declarations, and it was the real
declarations that surfaced the defect. Backing the predicate out fails exactly those eight
rows and nothing else in the workspace.

**The mitigation stands, and is no longer a mitigation.** `bodies_of(List[
Message[?t]]) -> List[Text[?t]]` was written to keep every label-polymorphic
operation reachable only through arguments of exactly its declared sort. It stays
in the vocabulary because a message's body genuinely *is* a projection and the
label genuinely does ride along it — but it is now ordinary API rather than the
thing standing between the design and a laundered label.

**And an agent can now write it out.** For a while the vocabulary's own comment
claimed otherwise — that both spellings a generated agent would reach for were
refused, so `bodies_of` was the *only* route from `List[Message[Untrusted]]` to
`List[Text[Untrusted]]`. One of those refusals was an artefact of the probe (a
qualified `Iterable.map` written into a file that does not import `Iterable`);
the other was WI-20260829-9TGP7, `map`'s free result parameter being used as a
BOUND on a `match` arm rather than as a hint, and it is fixed.
`msgs.map(lambda m -> m.body).collect()` and its match-destructure twin both load
through the whole checker, and the article's attack stays refused through both —
`guardians_test::an_agent_can_inline_the_body_projection`. That does not change
the decision above; it removes the last reason the decision could have been
mistaken for a necessity.

## C8 · A spec operation with `ensures` had no possible provider · **FIXED**

**Scenario.** Write the tier-2 obligation the design most wants —
`ensures mentions_all(result)` on `Triage.run` — and give it an implementation.

**Refused, and refused for every implementation:**

```
error: 'Impl' overrides 'Spec.run' but does not refine it: it weakens the
       postcondition — the override does not `ensure` a condition the spec
       operation promises
```

even when the override's `ensures` was **syntactically identical** to the
spec's. So a spec operation carrying a postcondition could not be implemented
at all.

**Isolated by one control.** An `ensures` over a **parameter** refines fine; an
`ensures` over **`result`** never does. That pinned it: `result` is defined per
operation as `<op>.result` with `SymbolKind::OpResult` (proposal 041), so the
spec's and the override's are distinct symbols, and the override-refinement
check's `align` map zipped **parameters only**. The comparison was
`Spec.run.result` against `Impl.run.result`, which are never structurally equal.

**Fixed** in `anthill-core/src/kb/typing.rs` by aligning the result binder the
same way parameters are aligned. Two controls hold: an `ensures` over a
parameter still refines (no regression), and a genuinely *different*
postcondition is still refused (the check still does its job). Scope: this
aligns the reserved name on both sides; an override that *renames* its result
binder is still not recognized, which needs the declared name the table does not
carry.

**Narrowed afterwards** by WI-20260822-59CDQ, filed from this fix's own review.
Aligning the two binders is a claim that they denote values of the same type, and
this pass compared no return types — so an identical `ensures P(result)` was
discharged between an operation returning `Report` and one returning `Int64`. The
alignment is now made only where the return types agree, and a mismatch is refused
naming both. The unconditional refusal C8 removed had been accidentally plugging
that hole: nothing could be discharged, so nothing could be discharged wrongly.

**Why it went unnoticed.** `ensures` on a spec operation is rare, and the
failure only appears once something *provides* that spec. The example's task
specification is exactly that shape, which is how it surfaced.

## C9 · A `Modify[p]` target is not compared by the refinement check · **FIXED**

**Scenario.** While building the row-widening fixture: an override declaring
`{External, Error, Modify[box]}` against a spec declaring
`{External, Error}`.

**Loaded clean.** A named effect (`Filesystem`) in the same position was refused
loudly, so the widening check worked — it just did not treat a `Modify` target
as a widening. `fixtures/agent/rejected/wide_row.anthill` is written with
`Filesystem` for exactly that reason.

**Why it mattered here.** `Modify[r]` is the frame condition (kernel-language.md
§5.6: for every resource not in the `Modify` set, `Env_after = Env_before`). A
spec granting no `Modify` is asserting the implementation changes nothing, and a
provider that could add one silently left that assertion unenforced on precisely
the axis §5.6 is about — while restating every named capability the spec did
grant, which is what kept it invisible to the label arm this record already
credited (B2).

**Diagnosed, and neither hypothesis was right (WI-20260822-1TKN0).** The ticket
guessed the `confident` gate or the parameter alignment. The cause was that the
gate asked a CARRIER question where an ABSTRACTNESS question was meant: it read
`matches!(e, Value::Term { .. })`, and a denoted `Modify[c]` rides a
`Value::Node` because it carries an occurrence, not because it is parametric.

**The measurement the ticket did not have: the fail-open was ROW-WIDE.** The
gate was an `all` over the whole effect row, so one `Modify[c]` disabled the
widening check for every effect beside it. An `Eff2` that is refused on its own
went unreported the moment a `Modify[box]` sat next to it in the same row — so a
provider could hide *any* capability widening behind one `Modify`. That is
strictly worse than the ticket's headline, and it is what the fix scopes to the
atom.

**Fixed in `kb/typing.rs`.** The gate now asks the two questions apart —
parametric, and denoted — and it runs per atom rather than per row. Two `Modify`
comparisons are now decided that were not: a target the spec never granted
(refused), and a target on a *different resource of the same type* than the one
the spec granted (refused — the frame condition is per resource, not per label).

**Fixture.** `fixtures/agent/rejected/wide_row_modify.anthill`, one token from
`good.anthill`. `wide_row.anthill` stays, unchanged and still refused: the two
travel different arms, and neither test catches the other's program.

**What was still not compared, and it was C5's neighbour — now closed.** A denoted
target facing a spec `Modify` over a resource TYPE — `Cell.set`'s `Modify[c]` against
`ModifyRuntime.set`'s `Modify[T = Cell]` — used to fail open, and the recorded gap
asked for a relation saying that the place `c` *is* a resource of that type.

**There is no such relation, because there was no such shape** (WI-20260823-39AD2).
The two docs disagreed about what `Modify[X]` denotes, and the question was settled
for the *place*: `Env` maps resource NAMES (kernel-language.md §5.6), so
`ModifyRuntime.set`'s `effects Modify[T]` was a **stdlib defect** — the only `Modify` over
a type in the *stdlib*, though not in the tree: five test fixtures wrote one too, and were
repaired with it — and not a lawful shape the pass could not judge. It now
reads `effects Modify[target]`, a type target is refused where it is written
(`check_modify_targets`), and the fail-open was deleted rather than filled in:
place-vs-place is related exactly by the equality the pass already had, once
`align_effect_label` rewrites the override's parameter name into the spec's. Measured:
`Cell.set` is accepted **by comparison**, and naming the wrong parameter
(`Modify[value]`) is refused — which under the fail-open loaded clean.

**Still open, and it is the other half of that ticket.** Nothing checks
`Modifiable[typeof(target)]`, at any site, which is why `Modify[pattern]` on a
`pattern: String` parameter loads clean.

## C10 · A label-preserving operation could not be written in terms of another · **FIXED**

**Scenario.** The design's load-bearing shape is an operation that PRESERVES a
label — `f(x: T[L = ?l]) -> T[L = ?l]`. A1–A3 measure it working at the EDGES,
where a call site supplies a concrete label, and that is what makes the article's
exfiltration a type error. It did not work in the MIDDLE: a library operation
that is itself label-preserving and delegates to another one could not be
written.

```anthill
operation upcase(t: Text[L = ?l]) -> Text[L = ?l]
operation summarize(t: Text[L = ?l]) -> Text[L = ?l] = upcase(t)
```

**Refused** — `summarize.return (op-return): expected Text[L = ?l], got
Text[L = t.L]`. The callee's variable came back as a PROJECTION of the argument
("the L of `t`") rather than as the variable the caller declared. The bare form
(`docs/measurements/op-type-var-does-not-thread.anthill`, twelve lines with no
labels, no specs and no dispatch — the identity delegating to the identity)
printed the two sides identically: `expected ?t, got ?t`.

**Control.** The identical delegation with a GROUND caller loads clean, which is
what pins the failure on the CALLER's polymorphism rather than on delegation,
arity or the sort.

**Consequence while it stood.** The property composed through the type checker
but not through user-written library code, which is what any real pipeline is
made of. `guardians.summarize` was narrowed to monomorphic for exactly this
reason.

**Fixed in `kb/typing.rs` (WI-1FKR2), and the two symptoms were one root.**
§5.4 "Which variables the ∀ quantifies" states that a variable written in a
parameter type is quantified — "an operation that writes no brackets at all
still generalizes". The body check skolemized only two of the three families
that reach it (the operation's declared `[A]` brackets and its enclosing sort's
parameters), so a variable the author wrote INLINE stayed *flexible* in the
body. A flexible variable is precisely what the unwritten-slot walk reads as an
omitted slot, so it overwrote the author's `?t` with the projection; and at the
top level the two flexible variables never met an arm of the subtype relation
that could relate them. Skolemizing the third family restores the premise the
first reader's own doc states — "by then … nothing else is left flexible".

**It is a soundness fix as well as an expressiveness one.** `operation
leaky(x: ?t) -> Int64 = sink(x)` with `sink(n: Int64)` loaded clean before: the
body PINNED the caller's universally-quantified variable, and the return type was
`Int64` on both sides so nothing downstream re-asked. It is now refused at
`sink.n (op-arg): expected Int64, got ?t`.

**What did NOT come back, and it is not this defect.** `summarize` still cannot
be `?t` in, `?t` out — measured on the fixed loader, refused at
`summarize.return: expected Text[Trust = ?t], got Text[Trust = Untrusted]`.
Its body ends in `llm.complete(p)`, and `complete` returns `Text[Untrusted]` for
every prompt *by design* (see C4's neighbour in `lib/llm.anthill`: the `?t` in /
`?t` out spelling let a model mint releasable text, kept as
`fixtures/agent/rejected/minting.anthill`). The INPUT side alone does now widen
— `List[T = Text[?t]] -> Text[Untrusted]` loads, `good` still loads and all five
rejected fixtures stay refused — and is left as written because in this pipeline
the summarizer only ever sees Untrusted mailbox text.

---

# Summary

| | run | verdict |
|---|---|---|
| A1 | label enforced at a sink | ✅ fires |
| A2 | label survives `summarize` — **the attack** | ✅ fires |
| A3 | widening is one-directional | ✅ fires |
| B1 | provision must back the member | ✅ fires |
| B2 | declared row may not widen the spec's | ✅ fires |
| B3 | body may not exceed its declaration | ✅ fires |
| B4 | reshaped member does not evade B2 | ✅ fires |
| E1 | forged safety fact about itself | ✅ fires |
| E2 | concealment guarantee inverted by a second clause | ✅ fires |
| E3 | hand-written reflect metadata, loader's own row admitted | ✅ fires |
| E4 | redeclaring a trusted name (the third channel) | ✅ fires |
| E5 | the verdict names the real carrier and the real row | ✅ fires |
| E6 | a candidate's own `mentions_all` does not discharge the spec's | ✅ control |
| E7 | a denial over the trusted base (no head functor) | ✅ fires |
| C1 | signature conformance | ❌ **gap** (WI-935) |
| C7 | sort mismatch vs a variable-containing type | ✅ **fixed** in `kb/typing.rs` |
| C8 | a spec op with `ensures` had no provider | ✅ **fixed** in `kb/typing.rs` |
| C9 | `Modify[p]` target vs the refinement check | ✅ **fixed** in `kb/typing.rs` |
| C10 | label-preserving operation in the MIDDLE of a pipeline | ✅ **fixed** in `kb/typing.rs` |
| C2 | `requires` gating a call site | ✅ **fixed** in `kb/typing.rs` (WI-9PGCM) — was mis-recorded as "by design" |
| C3 | rule body reading a type argument | ❌ WI-742 |
| C4 | variance in the label slot | ⚠️ **corrected** — declarable via `Covariant` + a provides-chain |
| C5 | computed region in `Modify[…]` | ❌ the slot takes a PLACE, and `glob(p)` names none (§5.6) |
| C6 | type argument on a constructor | ❌ and desirable |

**C7 changed the picture, and then was fixed.** A1–A3 and B1–B4 are real and
hold, but A1–A3 were all written over a single sort, and C7 was invisible to any
test built that way — **a vocabulary of one sort cannot exercise a sort
mismatch**. For as long as it stood, the design worked by *discipline in the
trusted declarations* rather than by the typer, which is a weaker claim than the
one this record made before the vocabulary was written out. The typer now makes
the claim itself, so C1 is again the one item on the critical path.

**C8 was found by writing the design's own obligation down and fixed in the
kernel** — the postcondition it blocked, `ensures mentions_all(result)`, is the
concealment half of the article's attack, so the defect sat exactly on the path
this example most needed. It is a small argument for building examples: the gap
was invisible to a suite where no spec operation carries `ensures`.

**A1–A3 and B1–B4 together are the design.** Data confinement and capability
confinement are checked by independent mechanisms, each with an unbroken chain,
and both hold on the current loader with nothing built. C1 is the one item on
the critical path; C3–C6 shaped the design rather than blocking it, and C2 —
recorded here as a design decision, on a stale §8.5 citation — turned out to be a
defect and was fixed.
