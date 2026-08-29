## Attributes

- id: WI-20260829-4S404-typer-a-guarded-effect-is-not
- created: 2026-08-29T14:49:42Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T14:49:42Z

- acceptance: cargo-test

## Description

TYPER: A GUARDED EFFECT IS NOT REFUTED WHEN ITS ARGUMENT IS LET-BOUND, so an address the compiler statically knows is refused exactly as if it were computed. The bound value IS known; `refute_guard` cannot use the binding to ground the goal.

MEASURED, and the two fixtures differ in ONE token -- whether the literal is written at the call or one line above it:

  fixtures/agent/internal_send.anthill      LOADS
    Email.send(to: Address(local: "boss", domain: "ourcorp.com"), body: ...)

  fixtures/agent/rejected/letbound_recipient.anthill   REFUSED
    let boss = Address(local: "boss", domain: "ourcorp.com")
    Email.send(to: boss, body: ...)
    -> run.effects (op-effects): expected declared: [External, Error],
       got undeclared effect: Permission[T = Outbox]

WHY. `Email.send` carries `(Permission[Outbox] :- external_addr(to))` (proposal 048's guarded effects on 064's label, lib/email.anthill). §5.5 drops the label when the guard's NEGATION is constructively proved, and `external_addr(?a) :- not(in_org(?a))`, so refutation is a DOUBLE negation over Γ. Written inline, the argument TERM is at the call and `in_org(to)` resolves against the deployment's rows. Let-bound, the `let` deposits an equation that SLD does not use to ground the goal, the double negation FLOUNDERS, and §5.5 conservatively keeps the effect.

SOUND BUT STRICTER THAN INTENDED, which is the whole complaint. Nothing unsafe is admitted -- the failure direction is to demand MORE authority. What it does is make the example's operative policy read "A GENERATED AGENT MAY MAIL ONLY AN ADDRESS WRITTEN LITERALLY, INLINE, AT THE CALL", which is a typer limit presented as a design decision. lib/email.anthill says so at the declaration and says this is worth a ticket; this is it.

WHAT MUST NOT BE LOST. Three cases are refused today and only ONE of them should stop being refused:

  external literal, inline      REFUSED   -- correct, must stay (rejected/outbox.anthill)
  computed address              REFUSED   -- correct, must stay (rejected/computed_recipient.anthill)
                                             the value is genuinely unknown at load
  INTERNAL literal, let-bound   REFUSED   -- this ticket; should LOAD

So the repair is not "look through lets" in general: it is that a `let` whose bound term is a GROUND CONSTRUCTION should be available to the guard's proof, exactly as the inline term is. A `let` bound to a call result must keep flding.

CONSEQUENCE FOR THE FIXTURE SET. `rejected/letbound_recipient.anthill` becomes an ACCEPTED fixture and moves out of `rejected/`, and `an_address_bound_one_line_earlier_is_refused` (or whatever asserts it) inverts. That is the deliverable's own acceptance evidence, so do not delete the fixture -- move it beside `internal_send.anthill`, where it becomes the second control for the guard.

ACCEPTANCE: the let-bound internal literal LOADS with the row `{External, Error}` and no `Permission[Outbox]`. CONTROLS, all of which must still hold: `rejected/outbox.anthill` still REFUSED (external literal, inline); `rejected/computed_recipient.anthill` still REFUSED (address returned by an operation -- the guard must not become optimistic); `internal_send.anthill` still ACCEPTED; guardians suite green. Say at the test site which rows fail when the change is backed out.

