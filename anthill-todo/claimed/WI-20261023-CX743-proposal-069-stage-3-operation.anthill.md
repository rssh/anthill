## Attributes

- id: WI-20261023-CX743-proposal-069-stage-3-operation
- created: 2026-10-23T05:45:56Z

- status: Claimed
- status_agent: claude
- status_at: 2026-10-24T17:43:14Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261023-GBH5F-proposal-069-stage-2-operation

- tags: proposal-069

## Description

PROPOSAL 069 STAGE 3 — OPERATION VALUE-PARAMETER DEFAULTS (§1.1, §3). `operation clamp(x: Int64, low: Int64 = 0, high: Int64 = 100) -> Int64`: a call leaving a parameter out takes its default, positional arguments fill the next unfilled slot, named ones fill by name, and a defaulted parameter need not form a suffix (`connect(host: String = "localhost", port: Int64)`, `connect(port: 5432)`). A default may name earlier parameters, the operation's and enclosing sort's type parameters, and visible constants, constructors and operations; a later parameter, `result` or a body-local is refused. The call is elaborated to full arity before evaluation — the evaluator, host ABI and generated code see the declared arity; each selected default is evaluated once, left to right, in the callee's frame, and its effects are the operation's and must fit its declared row. IN A RULE-BODY GOAL the result column is named `result:` (§1.1): positional arity + 1 keeps the functional view with every parameter written; a shorter goal is a call (a Bool operation succeeds on true; any other needs `result: ?r`); `result:` works at any arity; a short non-Bool goal without it is a load error naming `result:`. A spec operation owns its defaults; a provider's member does not redeclare them (refused), and a call through the spec elaborates from the spec. A function value obtained by eta-expansion is full-arity — no optionality in arrows. Reflect, persistence and both code generators keep the default. Also the `= none()` form of stage 2's `identity` row. ACCEPTANCE driven by value, each with a control that fails when default insertion is backed out: the clamp rows; a dependent default `range(first, last = first, step = 1)` evaluated once; an effectful default fitting / not fitting its operation's row; a missing required parameter declared after a defaulted one still refused naming it; `clamp(12, result: ?r)` binds 12, `clamp(12, 0, 100, ?r)` as today, `clamp(12, ?r)` refused naming `result:`; a Bool short goal; spec-owned defaults and refused redeclaration; a function value still needs full arity. Acceptance: rustland/scripts/test.sh, scaland sbt testFull, npx tree-sitter test.

## Changes

### 2026-10-24T17:56:55Z — feedback — claude

2026-10-24, implemented; the kernel-language sentences wait for the user's word. Proposal 069 stage 3: an operation's value parameter may declare a default (`operation clamp(x: Int64, low: Int64 = 0, high: Int64 = 100)`); a call that leaves it out takes it, and in a rule-body goal the result column may be named `result:`.

AT THE DECLARATION (`Loader::record_operation_param_defaults`): lowered in the operation's scope, filed on the operation's record (`OperationRecord::param_defaults`) and reflected as `anthill.reflect.OperationParamDefault(op, param, default: NodeOccurrence)`; refused where it names its own or a later parameter or `result`, or sits on a variadic capture. Typed by the body pass (`check_operation_bodies`, body-less operations with a default included) as an argument of its parameter, with the parameters before it in scope, its effects held to the operation's row at the operation's boundary; refused there for a parameter the signature reads (`Modify[c]`, `b.V`). A provider's member declaring one is refused (`check_override_refinement`).

AT A CALL (`typing/param_defaults.rs`): `bind_call_arguments` counts a defaulted parameter as filled; after the call's inference and its type defaults (`install_type_param_defaults`), `complete_defaulted_arguments` splices each default at the call (`substitute_occurrence` at the call's σ, an earlier parameter replaced by its argument, a call of a function-typed one by a call of the argument), types it there and writes the call out at full arity in parameter order; every reader past that point reads the completed call (a precondition's σ among them: `div2(4)` under `b = 1` proves `neq(1, 0)`). In an operation body a compound argument a default names is bound to a local first (`bind_arguments_a_default_names`, at the Apply visit), so it is evaluated once. A mixed call keeps its labels until the completion. A provider's member takes the spec's defaults (`call_defaults`; user). Refused at a call: a default that takes itself (`TAKING`), and in a rule body one that writes a call's bracket.

RULE BODIES: `result:` set aside (`split_result_column`) and written after the parameters; `call_dispatch_shape` and `operation_goal_reading` read a `result:` goal and a shorter goal on an operation with defaults as the call; a shorter non-Bool goal with no result column is refused naming `result:` (`short_goal_without_result`), and the declared-arity refusal (NonBoolOpInGoalPosition) now names it too. The arity message gives a range where parameters declare defaults.

EVAL (found here, fixed inline): a reference to a declaration (constant, operation, constructor, sort, relation) reads no local of its spelling (`names_a_declaration`). Eval read every reference by its short name first, so a spliced default was captured by a caller's local of that name (`let LIMIT = 3` beside `lim(1)` read 3 for `LIMIT`'s 50; a local `none`, a local `base` likewise) — the same class reaches a `@[simp]` right-hand side.

DECIDED WITH THE USER (2026-10-24): a call of a provider's member takes the spec's defaults; code generation — the Scala generator writes a literal default as the method's own and refuses another, the Rust generator emits none. Mine, for the user's word: the refusals of a default for a parameter the signature reads, of one that takes itself, and of a bracket-writing one in a rule body.

ROWS: rustland/anthill-core/tests/include/wi_cx743_operation_value_param_defaults_test.rs (12 tests; every part backed out alone, measured, recorded in its header); anthill-cpp-gen expr_body_test (the completed call lowered whole: `clamp(120, 0, 50)`, `clamp(120, 50)` without the completion); tree-sitter corpus (2 cases); scaland ParseTest (the parsed default) and BootstrapTest (literal defaults emitted and compiled, a non-literal refused).

RUNS: rustland/scripts/test.sh 10754 passed, 0 failed; scripts/families.sh holds, no verdict moved; node-carrier control over the new file passes; scaland sbt testFull 748 + 47 + 1 passed, 0 failed; npx tree-sitter test 240/240. /code-review (xhigh): 14 findings, 13 fixed, 1 no change needed (a body-less spec operation with a default and a projected return loads, measured).

### 2026-10-24T18:42:27Z — feedback — claude

2026-10-24, the rule-body bracket refusal (user): a call's bracket in a rule body should work and is not implemented yet. It waits on WI-20261013-RYDNV — the typer reads a rule-body call's bracket, the requirement weave reads the argument values — and lifting it, for a written bracket and for a default that writes one, is WI-20261024-TC54R (depends on RYDNV). Until then CX743 keeps the refusal, so the default is not dropped in silence.

### 2026-10-24T18:48:36Z — feedback — claude

DECIDED (user, 2026-10-24): a default for a parameter the signature reads — an effect over it (`Modify[c]`), a projection off it (`-> b.V`), a value in a type — stays refused at the declaration. Letting it work would make the call type the default before its own inference, the order 069 §2 reverses; the complexity is not worth it.

