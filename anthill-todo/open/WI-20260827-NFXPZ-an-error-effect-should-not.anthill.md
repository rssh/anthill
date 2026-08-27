## Attributes

- id: WI-20260827-NFXPZ-an-error-effect-should-not
- created: 2026-08-27T05:19:03Z

- status: Open
- status_agent: claude
- status_at: 2026-08-27T05:19:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN `Error` EFFECT SHOULD NOT BLOCK A HOST OPERATION FROM REDUCING IN A RULE BODY -- decide what an erroring operand MEANS for SLD, then relax the gate.

USER DIRECTION 2026-08-27, on the WI-20260826-VPEWK delivery: "about effect - I think error effect we can allow (and handle error by erroring rule). Maybe handle it later in own ticket." This is that ticket.

WHERE THE GATE IS. `SearchStream::host_op_reducible_at_a_value` (rustland/anthill-core/src/kb/resolve.rs) admits a host-implemented operation into the rule-body VALUE position, and its second clause requires the declared effect row to be EMPTY. That clause is CONSERVATIVE, not principled, and its own doc says so. It was added because the effect row turned out to be the only thing standing between a rule body and a real host side effect: a BODIED op raises its effect while the eval bridge runs the body, so the bridge `Err(_) => None` arm catches it ("an unhandled effect (resolution must not perform effects)"), but a HOST function is opaque Rust that simply runs and raises nothing.

MEASURED, on the delivered tree. A fixture sort maps two operations to the SAME host function (`string_trim`), one declared pure and one `effects {Error}` -- so the effect row is the only difference:

  rule pure(1) :- MyS.trimIt("  a  ")  = "a"     1 solution
  rule err(1)  :- MyS.trimErr("  a  ") = "a"     1 solution, 1 CONDITIONAL (0 definite)

Before the effect clause both answered 1 definite; the clause is what makes the second residualize. Driven at `wi_vpewk_host_op_operand_test::an_effectful_host_op_does_not_run_at_an_operand`, whose doc already says this row is written to FAIL when this ticket lands.

WHY `Error` IS THE ONE THAT MATTERS, and why the state effects are NOT the question. A `Modify[p]` operation cannot be reached from a rule body with a literal argument at all: the typer refuses the CALL at load with "expected an argument naming a PLACE, because `<op>` declares `Modify[s]` over this parameter, got a literal, which produces a fresh value rather than naming a slot". So the state-effect hazard is guarded one rung up and there is no row to relax. `Error` is the effect a rule body can actually reach, which makes the empty-row test refuse exactly the case that should probably be allowed.

WHAT THIS TICKET MUST DECIDE, and it is a SEMANTICS question rather than a gate tweak -- which is why it was not done inline:
 1. WHAT AN ERRORING OPERAND MEANS. The user reading is "handle error by erroring rule". Three candidate readings and they are not equivalent: (a) the CLAUSE FAILS (the error is a silent no-match, which loses the error and is the thing `avoid fallbacks` argues against); (b) the error PROPAGATES out of resolution as a diagnostic, which needs a channel `kb.resolve` does not currently have; (c) the goal RESIDUALIZES, which is todays behaviour and is what the ticket is trying to move off. Say which, and say what a caller counting solutions sees.
 2. HOW IT INTERACTS WITH NEGATION. Under (a) an erroring operand inside `not(...)` SUCCEEDS, which turns a host error into a positive answer. That is the classic failure-vs-error conflation and it must be answered explicitly, not inherited.
 3. WHETHER THE GOAL SIDE MOVES TOO. `bare_bodied_bool_relation` refuses an effectful op the same way and for a reason that DOES hold there ("an effectful body is not a logical relation"). Decide whether `Error` is carved out of both gates or only the value one, and state why they may differ.
 4. THE ROW SET. `effects {Error}` alone is one case; `effects {Modify[s], Error}` (which `persist` / `flush` declare) must stay refused, so the predicate is "the row is a subset of {Error}", not "the row contains Error".

ACCEPTANCE: the `err` row above answers per the decision in item 1, in BOTH polarities (an operation whose host function would answer `"a"` and one that would not), with the `pure` control still at 1 and a `{Modify[s], Error}` row still refused; the negation interaction of item 2 driven; and the flipped assertion in `wi_vpewk_host_op_operand_test` carries the new reading. Full workspace green via rustland/scripts/test.sh.

