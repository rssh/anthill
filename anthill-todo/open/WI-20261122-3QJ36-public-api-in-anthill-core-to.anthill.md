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

## Changes

### 2026-11-22T15:14:37Z — feedback — claude

Spike result (anthill-traces WI-20261122-AJAVP, measured 2026-11-22 on 53b1eb32c, release build; full numbers in anthill-traces docs/design/high-level-design.md §4.2 and §4.4). The public API already builds and decides the goals: a walker over OperationInfo.requires/ensures (var_ref and result -> value terms; a const with a literal body -> its literal, via kb.const_body_node; field_access over a ground receiver folded; conjunction flattened), each group of clauses as one LogicalQuery, execute_typed_logical_query. Holding and violated cases of cancelOrder ('='), addToCart (shared ?cartId), releaseCartReservations (const) and checkout (tuple result) are all definite. So this item narrows to: (1) options on execute — filed as WI-20261122-96QKW; (2) the value of a const with a COMPUTED body (const_slot_value / evaluated_const_value are crate-private; measured: 'const timeout: Int64 = 30 * 60 * 1000' leaves the clause undecided on the typed path, and only the text query path values it). The typed form the loader keeps (typed_contract_conjunct) is crate-private but not needed: typing the walker's goals recovers it.
Corrections to the description above, measured: a hand-built '=' resolved untyped is not residual but a resolver error ('compares two values with no eq member: no type reached the comparison'); a const left as stored is undecided even on the typed path ('PartialOrd.gte has no order for this operand pair (Int64 and reservationTimeout)'); the typer refuses field_access over a ground receiver ('type mismatch in products.name: expected resolved name, got unresolved') while the untyped resolver evaluates it; shared ?cartId is no trap (one variable per written ?name per operation, requires and ensures alike; the loader's field fillers are fresh per pattern); none of the four operations carries a loader-added type-requirement clause. Resolving prefixes of the clauses, as this item suggests, is what blows up (below); the caller resolves groups of clauses connected by shared ?variables instead.
Undecided whatever the goal building — for the resolver, not this item: a ground goal's alternative proofs are replayed when a later goal fails. forall is unrolled with no commit, and a disjunction inside it with several true branches gives each instance several proofs — e.g. a composite-key uniqueness written '(a.k1 != b.k1) | (a.k2 != b.k2) | (a = b)' is true twice for every pair differing in both fields, so such a rule has 1 / 4 / 64 proofs at 1 / 2 / 3 entities. A state-validity rule broken in a late conjunct, after such rules, is then out of fuel from 10 entities per kind (2 M steps; 10 M at execute's default, about 140 s). !!(goal) commits between goals; inside one rule body only a resolver option to commit to the first proof of a goal ground when selected would help. Also measured: about 0.1 MB kept per evaluation (91 -> 299 MB over 2 000 evaluations of one requires on a two-product state), on the typed and the text path alike.

