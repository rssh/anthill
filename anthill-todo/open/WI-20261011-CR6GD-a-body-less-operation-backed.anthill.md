## Attributes

- id: WI-20261011-CR6GD-a-body-less-operation-backed
- created: 2026-10-11T06:33:39Z

- status: Open
- status_agent: claude
- status_at: 2026-10-11T06:33:39Z

- acceptance: cargo-test

- tags: typing

## Description

A BODY-LESS OPERATION BACKED BY CLAUSES ANSWERS FROM A RULE BODY AND DIES `OperationBodyMissing` FROM AN OPERATION BODY, WITH A MESSAGE THAT SAYS IT HAS NO CLAUSE. Measured 2026-10-11 on fb862725, for a sort with a type parameter and for one without; found while delivering WI-20261011-RM247.

THE PROGRAM. `sort Box` with `entity mk(v: Int64)`, `operation full(b: Box) -> Bool`, `rule full(mk(v: ?v)) :- true`, `operation open(b: Box) -> Int64`, `rule open(mk(v: ?v), ?v) :- true`. From a rule body both answer: `rule held(?x) :- ?x <=> 1, Box.full(Box.mk(4))` gives 1 and `rule r(?x) :- Box.open(Box.mk(4), ?x)` gives 4. From an operation body neither runs: `operation go() -> Int64 = if Box.full(Box.mk(4)) then 1 else 0` and `operation go() -> Int64 = Box.open(Box.mk(4))` load with no diagnostic and fail 'operation has no body: …Box.full — nothing this runtime can run is registered for it: no operation body, no host operation_map entry for this language, no builtin, and no rule clause indexed under it'. The clause is indexed under the operation — the rule-body goal resolves through it.

MECHANISM, as far as read. Eval's dispatch (eval/eval.rs `dispatch_call_with_requirements_inner`) tries a builtin, the body, a value-directed implementation and a dictionary-resolved sibling, and then ONE bridge to the resolver: `eq_bridge_target`, a carrier's `eq` over two ground operands (WI-625). Every other clause-backed operation falls through to `unrunnable_target_error`. The message (eval/error.rs) lists four things looked for; eval does not look for the fourth. kernel-language.md §5.3 says a declared operation with no clause, no body, no host mapping and no builtin is unrunnable and says so — which reads as: one with a clause runs.

WHAT. Decide which holds, and make the load and the message say it. Either an operation's clauses run it from an operation body as they do from a rule body — the bridge taken for a Bool operation's predicate clauses, and for the clauses at arity + 1 of one that returns a value, ground operands only as the `eq` bridge is — or clauses are not what runs an operation outside a rule body, and then the message stops naming a missing clause, and a call from an operation body to an operation with clauses and nothing else is named before run time. WI-20260909-M8QWJ (an operation with nothing to run loads clean) and WI-885 (what counts as backing) are the neighbours; neither has this program.

CONTROL. Under the first rule the two operation-body programs run to 1 and 4, failing on the tree before, and the rule-body rows pass either way. Under the second, the message row and the load row fail on the tree before. The carrier-`eq` bridge's own rows unchanged.

