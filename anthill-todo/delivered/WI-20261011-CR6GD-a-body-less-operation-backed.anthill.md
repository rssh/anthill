## Attributes

- id: WI-20261011-CR6GD-a-body-less-operation-backed
- created: 2026-10-11T06:33:39Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-11T10:29:13Z

- acceptance: cargo-test

- tags: typing

## Description

A BODY-LESS OPERATION BACKED BY CLAUSES ANSWERS FROM A RULE BODY AND DIES `OperationBodyMissing` FROM AN OPERATION BODY, WITH A MESSAGE THAT SAYS IT HAS NO CLAUSE. Measured 2026-10-11 on fb862725, for a sort with a type parameter and for one without; found while delivering WI-20261011-RM247.

THE PROGRAM. `sort Box` with `entity mk(v: Int64)`, `operation full(b: Box) -> Bool`, `rule full(mk(v: ?v)) :- true`, `operation open(b: Box) -> Int64`, `rule open(mk(v: ?v), ?v) :- true`. From a rule body both answer: `rule held(?x) :- ?x <=> 1, Box.full(Box.mk(4))` gives 1 and `rule r(?x) :- Box.open(Box.mk(4), ?x)` gives 4. From an operation body neither runs: `operation go() -> Int64 = if Box.full(Box.mk(4)) then 1 else 0` and `operation go() -> Int64 = Box.open(Box.mk(4))` load with no diagnostic and fail 'operation has no body: …Box.full — nothing this runtime can run is registered for it: no operation body, no host operation_map entry for this language, no builtin, and no rule clause indexed under it'. The clause is indexed under the operation — the rule-body goal resolves through it.

MECHANISM, as far as read. Eval's dispatch (eval/eval.rs `dispatch_call_with_requirements_inner`) tries a builtin, the body, a value-directed implementation and a dictionary-resolved sibling, and then ONE bridge to the resolver: `eq_bridge_target`, a carrier's `eq` over two ground operands (WI-625). Every other clause-backed operation falls through to `unrunnable_target_error`. The message (eval/error.rs) lists four things looked for; eval does not look for the fourth. kernel-language.md §5.3 says a declared operation with no clause, no body, no host mapping and no builtin is unrunnable and says so — which reads as: one with a clause runs.

WHAT. Decide which holds, and make the load and the message say it. Either an operation's clauses run it from an operation body as they do from a rule body — the bridge taken for a Bool operation's predicate clauses, and for the clauses at arity + 1 of one that returns a value, ground operands only as the `eq` bridge is — or clauses are not what runs an operation outside a rule body, and then the message stops naming a missing clause, and a call from an operation body to an operation with clauses and nothing else is named before run time. WI-20260909-M8QWJ (an operation with nothing to run loads clean) and WI-885 (what counts as backing) are the neighbours; neither has this program.

CONTROL. Under the first rule the two operation-body programs run to 1 and 4, failing on the tree before, and the rule-body rows pass either way. Under the second, the message row and the load row fail on the tree before. The carrier-`eq` bridge's own rows unchanged.

## Changes

### 2026-10-11T10:29:12Z — feedback — claude

DELIVERED 2026-10-11 — THE SECOND RULE HOLDS: clauses answer a goal, not a call, and the load and the message say it.

WHY, AND IT WAS ALREADY DECIDED. I put the fork to the user as an open choice; the answer was that the relation/operation proposals cover it, and they do. Proposal 052, open question 7, names this shape ("an operation carrying the identical clauses is refused ... a self-inflicted limitation"). docs/brainstorms/rule-declaration-syntax.md measured it ("a goal face and no value-call face") and chose the body-less `rule` declaration over a standard body that consults the clauses. And 052 as delivered is the route from value syntax: the clauses written as a rule alone, cited as a relation. Measured on this ticket program with the two `operation` lines dropped and the heads written with variables: `Box.open(Box.mk(4)).takeN(5)` is one row `(v: 4)`, and `Box.full(Box.mk(4)).takeN(5)` is one row.

WHAT CHANGED. (1) LOAD: a call in an OPERATION BODY of an operation with clauses and nothing else — an operation of a namespace or of a sort with constructors, and not the `eq` of a carrier — is refused where it is written (`typing::clause_defined_own_operation`, asked in `check_apply_iter`; `TypeError::CallOfClauseDefinedOperation`). The refusal names the operation, the goal that answers, spelled off the clause heads (`open(..., ?result)`, `full(...)`), and two repairs: a body, or the clauses as a rule alone cited as a relation. (2) RUN TIME: `OperationBodyMissing` carries whether clauses are indexed under the target, and no longer says "no rule clause indexed under it" of an operation that has one. (3) SPEC: kernel-language.md §5.3 states the rule; the user confirmed the paragraph.

A RULE BODY IS NOT JUDGED, and the first cut got that wrong. I had also refused the application in the value positions of a rule body. /code-review, with a before/after binary, found two working programs stopped loading — a term matched against a head (`rule un(Box.open(?b), ?b)`) and a goal passed as data (`rule call1(?g) :- ?g`) — and a lambda written in a rule body. The refusal is gated on `in_rule_body`. A call a rule body needs the VALUE of still waits in silence (`?x <=> Box.open(Box.mk(4))` answers a residual); that is the rule-body half already noted on WI-20260909-M8QWJ.

CONTROLS, each measured by back-out; the header of `wi_cr6gd_clause_defined_call_test` has the lists. The refusal out: twelve rows load clean, and the two message rows fail. The rule-body gate out: four rows, and the clause-backed row of RM247. Each leg of the predicate out: one row each. The rows of the carrier-`eq` bridge are unchanged. Full workspace: 36 binaries, 9163 passed, 0 failed, and the same under ANTHILL_TEST_NODE_CARRIER=1.

FOUND ON THE WAY. (a) FIXED, in its own commit: a constructor written with POSITIONAL arguments in an operation body was read as a term in its written shape, so `rule open(mk(v: ?v)) <=> ?v @[simp]` did not fire on `Box.open(Box.mk(4))`, and `requires Pair.big(p)` was not provable at `need(Pair.pair(7, 2))`. The view and the term twin of the node now present the canonical entity form (`node_occurrence::canonical_positional_ctor_args`; docs/design/entity-term-mapping.md §2). It moved one row of `wi_9bkz4_sealed_bodies_test`, written for that day: a `@[simp]` rule headed by a constructor now rewrites a positional construction, and behind a seal the later load is refused. (b) FILED: WI-20261011-12VZB — the same for a constructor written all named, out of declaration order. (c) NOT FILED: a constructor of no field written bare (`Color.code(red)` under `rule code(red) <=> 1 @[simp]`) is not matched by the equation, though its precondition is proved; the node is a `var_ref`, kept so on purpose at the lowering boundary (WI-592, WI-756). (d) MEASURED, NOT BUILT: a later load that writes a clause under a sealed operation would change how a sealed call of it reads; no body in the standard library calls an own operation with nothing executable, so there is nothing there for such a clause to turn.

