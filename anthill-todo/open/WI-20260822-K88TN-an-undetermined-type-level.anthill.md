## Attributes

- id: WI-20260822-K88TN-an-undetermined-type-level
- created: 2026-08-22T20:23:23Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T20:23:23Z

- acceptance: cargo-test

## Description

AN UNDETERMINED TYPE-LEVEL OBLIGATION FLOATS OUT OF A POLYMORPHIC WRAPPER AND IS NEVER RE-ASKED, so a contract-less wrapper launders exactly the flow 9PGCM just started gating.

MEASURED, and pinned as a test that must FLIP when this lands: `wrapper_swallows_the_obligation_pending_propagation` in `rustland/anthill-core/tests/include/wi9pgcm_type_level_precondition_test.rs`. Given `send(body: Text[L = ?l]) requires flows_to(?l, Public)`, a direct `send(fetch())` is now REFUSED (9PGCM), while

  operation relay(t: Text[L = ?m]) -> Unit = send(t)
  operation leak() -> Unit = relay(fetch())

loads CLEAN. Two frames, two decisions, and neither is wrong on its own: inside `relay` the label is undetermined, and 9PGCM floats an undetermined obligation because deciding it by absence would refuse every label-polymorphic declaration (WI-067/WI-292 — act on a decided obligation, never on an undetermined one). At `relay(fetch())` the label IS decided, but the typer checks only `relay`'s OWN `requires`, and `relay` declares none. The obligation is dropped between the two.

THIS IS THE PROPAGATION HALF, and 9PGCM's site comment names it as the stopping point rather than leaving it implicit (`kb/typing.rs`, the `UNDETERMINED ⇒ FLOAT` block in `check_apply_iter`).

WHAT MUST BE DECIDED FIRST, because the implementation follows from it and not the other way round. An operation whose body floats an obligation over a variable its OWN signature binds is in one of two regimes and the ticket must pick:

 (a) DECLARE-OR-REFUSE. `relay` must write `requires flows_to(?m, Public)` or the body is a load error naming the callee, the goal, and the variable that carried it out. Sound and explicit; it is also a NEW REFUSAL over source that loads today, so its blast radius is the whole corpus and must be measured before it is chosen.
 (b) INFER ONTO THE SIGNATURE. The floated obligation is added to `relay`'s own effective `requires`, checked at `relay`'s call sites. Nothing new is refused at the declaration and the leak still closes; the cost is a contract no reader can see in the source, which is the objection §5.4 already makes to invisible slots.

EITHER WAY, ONE PREREQUISITE IS THE SAME and it is missing today: an operation's own `requires` is NOT in its body's Γ. `FlowEnv::empty()` is Γ₀, so even under (a) a DECLARED `requires flows_to(?m, Public)` cannot discharge the `send(t)` obligation — the check would refuse the very source it just demanded. Proposal 050's Hoare reading says a precondition is an ASSUMPTION inside the body; seeding Γ₀ with the operation's own value preconditions is that reading, and it is a prerequisite for both branches. NOTE THE ORDERING TRAP: 9PGCM's undetermined gate runs BEFORE Γ is consulted (deliberately — consulting the resolver with a free variable is what made the obligation vacuous, since a free variable is witnessed EXISTENTIALLY off any unrelated fact). So a Γ₀ seed alone changes nothing; the gate must learn to try Γ ALONE — structural match against the assumed clause, never a resolver query — before it floats.

ACCEPTANCE: `wrapper_swallows_the_obligation_pending_propagation` flips to `is_err` (rename it), OR — under (b) — a new test shows `relay(fetch())` refused while `relay(banner())` loads. State which regime was chosen and why, in the spec (§5.4's WI-9PGCM paragraph ends on exactly this open question and must be closed there too).

CONTROLS: every other test in `wi9pgcm_type_level_precondition_test.rs` keeps its verdict — in particular `undetermined_label_floats_rather_than_failing` must stay clean under (b) and must be RE-STATED under (a), since (a) refuses precisely that shape. `wi539_call_site_contracts_test.rs` and `wi557_rule_body_precondition_scope_test.rs` unchanged: a value precondition over value parameters is not this ticket. The guardians suite still passes 16/16. Under (a), report the corpus measurement — how many existing declarations the new refusal hits — before landing it; a double-digit count is itself an argument for (b). Say at each site which tests fail when the change is backed out and which pass either way by design.

ACCEPTANCE IS `cargo-test` ONLY. The filed default carried `scaland-sbt-test` too, which can never pass — this is a typer change and scaland has no typer. The parent 9PGCM carries the identical correction; `add` hardcodes both and the filer must strip the one that cannot apply.

RELATION TO 062. Same keyword, adjacent level: 062 proves a `requires` over a SORT's type parameters at load, and this proves an operation's over a variable its own signature binds, at the frame that binds it. Neither depends on the other; if both land the keyword means one thing wherever it is written.

