## Attributes

- id: WI-20261126-7BJGQ-a-host-cannot-call-an
- created: 2026-11-26T07:17:01Z

- status: Open
- status_agent: claude
- status_at: 2026-11-26T07:17:01Z

- acceptance: cargo-test

## Description

A host cannot call an operation whose `requires` names its parameters: `Interpreter::call` types the call where no precondition can be established
WHO NEEDS IT. anthill-traces (private) runs a model of a spec sort, a carrier providing it with bodies, through `Interpreter::call` (its WI-20261122-4067S), on argument values it has already checked against the operation's `requires` with its own contract evaluator. Since WI-20261126-JR3AD such a provider loads. But a provider restates the spec's `requires` (it must, where an `ensures` restates a variable a `requires` binds), and a spec operation's own body, which a provider leaves to the spec, carries the spec's `requires` too. Every one of those operations is refused at the call.
WHAT HAPPENS. Read from code (2f7cbd4a2): `call_bracketed` (eval/mod.rs:1013-1155) builds the call `op(__host_argument_0, ...)`, each argument a name bound at its type, and types it as the body of an operation of the host's, `anthill.host.call`, which requires nothing; a refusal the typing parks refuses the call. A value precondition of the callee over a parameter is then to be proved at a call site with no enclosing guard, no prior `ensures` and no fact about the names (the three ways the refusal names), so it is refused whatever values are passed.
MEASURED 2026-11-26, anthill-traces' test binary on 2f7cbd4a2, `Interpreter::new` over the loaded program and `runner::register_runtime`:
  namespace probe3
    import anthill.prelude.{Int64}
    rule small(?n) :- ?n < 10
    sort S
      operation guarded(n: Int64) -> Int64
        requires small(n)
        = n + 1
      operation free(n: Int64) -> Int64
        = n + 1
    end
  end
`interp.call("probe3.S.free", &[Value::Int(3).into()])` is `Ok(Int(4))`. `interp.call("probe3.S.guarded", ...)` is refused: "host call of `probe3.S.guarded` refused: type mismatch in probe3.S.guarded.requires: expected precondition `small(__host_argument_0)` provable at the call site, got unsatisfied precondition". A provider's operation restating a `requires` over its parameter, and a spec operation's body with one, are refused the same way.
WHY IT MATTERS. A host (a test harness, a runner such as anthill-traces, a generated host binding) cannot run any operation with a value precondition over its parameters, although a body can call it by establishing the precondition. Running a spec's operations from outside on values is what a model is for.
WHAT IS ASKED. A host call that can run such an operation. Two shapes, to decide: (a) the host takes the precondition on itself, as a caller outside the language: an explicit entry (`Interpreter::call` with an option, or a second entry) types the call as if the callee's `requires` were established, and the default stays as it is; (b) the call evaluates the `requires` on the argument values when it is made, and one whose precondition does not hold is refused naming the clause (one not decided, refused as undecided, never run as holding). anthill-traces needs (a) at least: it decides `requires` itself before it calls.
DONE WHEN. (1) The probe's `guarded` is called through the new entry and returns 4. (2) The control: the default `Interpreter::call` still refuses it; or, if (b) is the default, a call whose precondition fails is refused naming the clause and one where it holds runs. (3) A provider's operation restating a `requires` over its parameter, and a spec operation's body carrying one, called through it. (4) The back-out measured, and said at the rows.

