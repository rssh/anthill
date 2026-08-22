## Attributes

- id: WI-20260822-9PGCM-an-operation-s-requires-over-a
- created: 2026-08-22T17:19:41Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T17:19:41Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN OPERATION'S `requires` OVER A TYPE-LEVEL VARIABLE IS AN OBLIGATION THAT IS NEVER DISCHARGED, so it loads clean and gates nothing.

MEASURED, and still true at origin/main (`59ac37b7`, after RKMD4 rewrote this area). `docs/measurements/guardians/d2c_callsite.anthill`:

  operation send(body: Text[L = ?l]) -> Unit
    requires flows_to(?l, Public)

  operation leak() -> Unit = send(fetch())     -- fetch() -> Text[L = Untrusted]

loads clean. `flows_to(Untrusted, Public)` is deliberately absent and, queried, has no solutions — so the lattice facts are right and it is the GATING that is missing, not the data. Recorded as C2 in `examples/guardians/docs/design/measured.md`, whose table still reads `❌ by design (§8.5)`.

THIS TICKET ARGUES THE DESIGN SHOULD CHANGE, not that someone forgot a check. The reason is an asymmetry in one keyword. Over VALUES, `requires` IS proved at load: WI-539's `operation needy(b: Int64) requires neq(b, 0)` admits `needy(5)` (substituting `b ↦ 5` and evaluating), admits `if neq(b, 0) then needy(b)` (the branch context supplies it), and REFUSES a call that establishes neither — `wi539_call_site_contracts_test.rs` drives all three. Over a type-level variable the same spelling is merely recorded: §6.5/§8.5, "`requires` generates proof obligations tied to an `Implementation` fact, not a static call-site check". The type variable never reaches the value-level obligation machinery.

WHY THAT IS WORTH FIXING RATHER THAN DOCUMENTING. An obligation that reads as a guarantee and is not one fails SILENTLY, and the author who wrote the clause has no way to see it did nothing. It is worse for GENERATED code, where the whole premise is that the checker tells the generator what to fix (examples/guardians/docs/design/two-flows.md): a generated call that violates the contract is accepted at check time and the contract is decorative.

NOT A SECURITY HOLE TODAY, and this must not be sold as closing one. The guardians flow is enforced by a sink demanding a LITERAL label (`send_email(body: Text[Public])`), not by this clause; the suite passes 15/15 including `exfiltrating_agent_is_refused_by_the_label`. What is unsound is the narrower claim that an operation's `requires` over a label constrains its callers.

RELATION TO PROPOSAL 062. Same defect class one level over. 062 decides that a `requires` goal over a sort's type parameters is PROVED at load — a substitution is well-formed only if every constraint it carries is satisfied. If both land, the keyword means one thing wherever it is written. 062 does not depend on this and this does not depend on 062; either may go first.

ACCEPTANCE: `leak()` in `docs/measurements/guardians/d2c_callsite.anthill` is a load error naming the operation, the goal, and the binding that refuted it.

CONTROLS: `ok()` in the same file (Public into the same sink) still loads. An UNDER-DETERMINED `?l` — one no caller has bound — must suspend rather than fail, never decided by absence (WI-067); a version of this that refuses an unbound label would break every label-polymorphic declaration in `examples/guardians/lib/`. WI-539's value preconditions keep their current behaviour, driven by `wi539_call_site_contracts_test.rs`. The guardians suite still passes 15/15. State at its site which of these fail when the change is backed out and which pass either way.

## Changes

### 2026-08-22T17:22:43Z — feedback — user

CORRECTION TO THIS TICKET'S OWN PREMISE. It was filed saying "this argues the DESIGN should change, not that someone forgot a check", on the strength of measured.md's `❌ by design (§8.5)`. That citation is STALE and the framing is wrong: this is a gap against the spec, not a design decision to revisit.

TWO SECTIONS OF docs/kernel-language.md DISAGREE, and the table cites the older one. §8.5 "Operation Contracts and Obligations" (line 3411) describes obligations on the IMPLEMENTATION — "prove that the implementation satisfies the contract", discharged by agents, elevating trust level — and never mentions a call-site check. §5.4 "Operation" (line 1918) documents WI-539's later split: an operation's `requires` list holds TWO kinds and different machinery checks them. A VALUE PRECONDITION is "proved, at the call site, from what the caller knows" — an unproved one is a load error in an operation body. Only a TYPE PRECONDITION (one naming a spec) is "never proved from the caller's Γ". §8.5 was not updated when that landed, so it now reads as the whole story and is half of it.

`flows_to(?l, Public)` names no spec. MEASURED — `is_value_precondition_clause` (typing.rs:43591) returns true for any clause whose functor is not a `SymbolKind::Sort`, so this clause IS classified a value precondition and IS routed to the call-site contract check. It does not fail there by design.

THE ACTUAL CAUSE. The call-site check proves conditions from Γ, which carries VALUE knowledge, while `?l` is bound in the argument's TYPE: `send(fetch())` with `fetch() -> Text[L = Untrusted]` unifies `?l := Untrusted` in the typer's σ at that call. The caller demonstrably knows the label — it is written in the argument's declared type — and the check does not look where it is written. Finding nothing, it reports the condition undetermined, and an undetermined obligation legitimately floats rather than raising (WI-557/WI-602, "act on a decided obligation, never on an undetermined one"). The silence is a correct rule applied to a lookup that missed.

WHAT THIS CHANGES. The fix is narrower and better defined than "revisit §8.5": the call-site contract check must be able to prove a condition from the argument's TYPE bindings, not from value-Γ alone. The floating rule stays exactly as it is — an `?l` no caller has bound is still undetermined and must still float; what changes is that a BOUND one is now found. That is the same distinction this ticket's controls already turn on, so acceptance and controls are unchanged.

ALSO IN SCOPE, being the same confusion: §8.5 should point at §5.4's split, and measured.md's C2 row should stop reading `by design (§8.5)`.

