## Attributes

- id: WI-20261126-7BJGQ-a-host-cannot-call-an
- created: 2026-11-26T07:17:01Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-26T07:53:05Z

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

## Changes

### 2026-11-26T07:53:03Z — feedback — user

Implemented 2026-11-26 (ffb0f2c3b), shape (a), the user's decision 2026-11-26: a host that has decided the callee's requires itself calls Interpreter::call_assuming_requires(name, args) or call_bracketed_assuming_requires(name, bracket, args); the call is typed as if its value preconditions were established. Interpreter::call and call_bracketed are unchanged and still refuse. Nothing checks a vouched goal at run time: guarded(12) runs to 13.
HOW: the four entries share call_entry(.., Preconditions); a vouched entry sets TypingEnv::vouch_for_preconditions_of(op) on the host's typing env, and check_apply_call skips the value-precondition block for a call the env vouches for. WHICH CALLS: the operation the host names (canonical symbol), and the calls of a default spliced into it (is_spliced_default provenance) -- a default is typed again at the splice with its own callees' preconditions, which follow from the operation's requires (it is typed in the body's gamma0 at its declaration). NOT a call a @[simp] equation rewrites the named operation into: proved as in a body. A requirement over a spec is no value goal and is still owed. The typed-call cache key (HostCallKey) carries the vouching, so a plain call at the types of a vouched one is still refused.
FOUND, fixed inline: (1) keying on the named operation alone refused the spliced default h(n) of withdef(n, m = h(n)) requires tiny(n) (MEASURED); (2) /code-review: vouching every call of the host's typing ran inner(7) for outer(n) requires small(n) rewritten by @[simp] outer(?n) <=> inner(?n), inner requiring tiny(n) (MEASURED, 107; the body twin is refused). Scoped to the named operation plus spliced-default provenance.
DONE: tests/include/wi_7bjgq_host_call_assuming_requires_test.rs (wi_tests), 11 rows. (1) the ticket's probe: guarded(3) through the entry is 4; free answers through both. (2) controls: the plain call refuses naming small(__host_argument_0); a plain call after a vouched one at the same types is refused. (3) a provider's member restating requires, named and through the spec (4/4); a spec operation's body carrying one (5); a spliced default (6); the bracketed entry; a clause mixing a value goal with Additive[T = X] (value half vouched, Additive supplied at Int64, owed at String). Controls: a requirement over a spec owed through either entry, same refusal; a simp-rewritten callee's precondition proved. (4) back-outs on a binary of the file alone, listed at its head: vouching not passed -> 8 RED, 3 GREEN by design; cache key without vouching -> 5; every call vouched -> 1 (the simp row); named operation only -> 1 (the default row).
SPEC: kernel-language.md, the host-call sentences of "Which dictionary a call uses": the vouching entry, what it covers (the callee's and a spliced default's value goals, not a simp rewrite's), that nothing checks a vouched goal at run time, and that a requirement over a spec is owed through either entry.
Gate: workspace 12823 passed, 0 failed; scripts/families.sh green, no verdicts moved. Scaland not run (no Scala touched; acceptance cargo-test).

