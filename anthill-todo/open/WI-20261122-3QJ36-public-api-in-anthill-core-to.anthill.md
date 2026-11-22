## Attributes

- id: WI-20261122-3QJ36-public-api-in-anthill-core-to
- created: 2026-11-22T12:07:02Z

- status: Open
- status_agent: user
- status_at: 2026-11-22T12:07:02Z

- acceptance: cargo-test, scaland-sbt-test

## Description

Public API in anthill-core to evaluate an operation's value contract (requires / ensures) on ground values
WHO NEEDS IT. anthill-traces (a tool outside this repository, not yet published; design: its docs/design/high-level-design.md §4.4) checks recorded traces against a specification: for a step (operation, input values, output value) it must decide whether the operation's requires held on the input and its ensures held on input and output. The operations are typically body-less members of a spec sort, e.g. shop.Shop.cancelOrder in the explicit-state shop example.

WHAT IS THERE TODAY (read from the code on 2026-11-22, not yet exercised by a caller):
- Nothing evaluates a value contract at run time: the interpreter and 'anthill run' do not check requires/ensures at a call.
- The static machinery that does the same work for call-site proofs is crate-private: clause_goal (kb/typing/effects.rs — substitutes parameter -> argument and carries the typed comparison members), assume_call_ensures (maps 'result'), substitute_ref_terms, clause_conjuncts, is_value_precondition_clause, OperationRecord.typed_contract (op_info.rs), const_slot_value / evaluated_const_value (const_value.rs).
- What a caller outside the crate can reach is OperationInfo.requires / .ensures as terms, and with them three traps: (1) parameters and 'result' are Expr.var_ref(<op>.<p>) nodes that the caller must replace by values with a walker of its own; (2) an '=' goal assembled by hand and never typed goes residual, so the answer is undecided rather than true or false; (3) a const named in a contract clause keeps its name there (kernel-language.md: contract clauses are not data slots), so 'now - ?u >= reservationTimeout' is undecided unless the caller substitutes the value, which it has no public way to read. Also a clause holding several goals is stored as a conjunction(...) term that nothing resolves, and requires carries loader-added type-requirement clauses the caller must tell apart from value preconditions.

WHAT IS ASKED. A public function (name open — e.g. contract::instantiate) that, for an operation, a binding of each parameter to a ground value and optionally a value for 'result', returns the operation's value clauses ready to resolve: per clause its index and source span, and its goals — conjunction flattened, parameters and result substituted, comparisons in their typed form, consts valued, loader-added type-requirement clauses left out. The clause-local ?variables must stay ONE scope over all the clauses of the operation (the parser resets variable scope once per operation, so ?cartId in two clauses is one variable), so that a caller can resolve a prefix of the clauses as one conjunction. Resolving stays the caller's business (resolve_goals_with_stats and SLDProof.of are public already); this item is only about building the goals the way the loader understands them.
Giving 'result' in a requires clause, a missing or unknown parameter, and a value whose type does not fit the parameter are errors, not silent skips.

WHAT IS NOT ASKED: checking contracts in the interpreter at a call; proving ensures of a body (WI-20260830-2FP2K).

STATUS OF THE NEED. anthill-traces has a spike planned (its WI-20261122-AJAVP) that first tries the public API alone on four shop operations, one per trap: cancelOrder ('='), addToCart (shared ?cartId), releaseCartReservations (const), checkout (tuple result, result.state / result.order.id). This item is filed ahead of that measurement at the user's request; the spike's result is to be recorded here as feedback and may narrow the item (for instance to const values only) or show it is not needed.

DONE WHEN: a test in anthill-core drives the function on those four shop-shaped operations with ground values and resolves the returned goals — a holding and a violated case each, both DEFINITE; the control at the test site says which of them come out undecided when the goals are instead assembled by hand from OperationInfo (the three traps above).

