## Attributes

- id: WI-20260908-9WVT7-land-proposal-047-s-error
- created: 2026-09-08T13:03:02Z

- status: Open
- status_agent: user
- status_at: 2026-09-08T13:03:02Z

- acceptance: cargo-test

- tags: effects

## Description

LAND PROPOSAL 047's `Error` LAYER: the `reify` boundary and `Result`, so anthill code can CATCH a raise. Today nothing in the language can catch anything -- measured, no handler operation exists anywhere in stdlib, so every operation declaring `effects Error` is uncatchable from anthill.

THE SHAPE IS 047's, NOT A NEW CONSTRUCT. 047 §2 gives `Error` the monad `Result[_, T]` with `raise(x)` denoting `Err(x)`; §3 gives `reify : (() -> a) -> M a` and states "handler / `provide` = `reify` / `reset`" and "`Throw(v)` | `Result.Err v` | abort to the reify boundary". So the operation is `reify` at the `Error` layer:

  operation reify[Rho, X, P](body: () -> X @ {Error[P], Rho}) -> Result[P, X] @ {Rho}

WHY IT DOES NOT WAIT ON WI-078 (claimed). 047 SUPERSEDES 027's ambient-registry / scoping section, which is exactly WI-078's unlanded half; WI-078's own audit says what remains is `RuntimeAPI snapshot_eval_state/resume` -- CONTINUATION CAPTURE -- which 047 assigns to the RESUMABLE effects (`Suspension` WI-069, `Branch` WI-070). `Error` is short-circuit: run the thunk; `Err(EvalError::Raised { payload })` becomes `Err(payload)`, otherwise `Ok(v)`. No snapshot, no activation-stack clone. This ticket is 047's FIRST monad layer, chosen because it is the only one needing no continuations -- so it does not cut across WI-078 and WI-078 has nothing to reconcile with it later.

HALF IS ALREADY BUILT, AND IT IS THE RAISE HALF. `default_error_handler()` (rustland/anthill-core/src/eval/effects.rs:470), `HandlerAction::Throw(payload) => Err(EvalError::Raised { payload })` (effects.rs:593), and the `Raised { payload }` variant (eval/error.rs:80). 047 calls the `HandlerAction` carrier "the per-monad, defunctionalized form of `reflect`", so what is missing is only the reify boundary.

THE TYPING IS ALREADY DELIVERED AND NEEDS NOTHING. WI-329 shipped handler discharge -- a handler is an ORDINARY operation sharing a row tail, `(body: () -> X @ {K, rho}) -> X @ {rho}` -- with `infer_discharged_row_tails` and 20 tests. BUT NOTHING SHIPS A `reify`: WI-329's capstone `reify` is a test FIXTURE (`wi329.solver.reify`, tests/include/wi329_handler_discharge_test.rs:466), body-less and returning `Int64` rather than a monad, so the typing rule is proved while no monad layer exists. Do not read the capstone as an implementation.

SINGLE-CALLBACK IS FORCED, NOT CHOSEN. The two-callback form (body plus recovery, sharing `Rho`) is refused today: WI-20260820-RDNS4's witness (1) is literally `operation two[Rho](a: () -> Int64 @ {Error[Int64], Rho}, b: () -> Int64 @ {Rho})`, refused BEFORE and AFTER WI-329. So the sum-returning form is both what the typer admits and what 047 specifies; they agree, and that agreement is why this shape rather than a recovery callback.

`Result` DOES NOT EXIST. The prelude has `Option` and no `Result` / `Either` (measured: no such declaration under stdlib/anthill/prelude). `Option` will not do -- it drops the payload, and the payload IS the answer a caller wants (`LoadFailed(diagnostics)`).

THE TRAP, AND WHY THE DECLARATION MUST NOT LAND FIRST. Discharge is PURELY STATIC -- WI-329's words: "the typer's check is purely static -- it asserts the program is well-typed, not that the runtime handler exists". A `reify` declaration without its host binding would TYPECHECK AS IF IT CAUGHT, dropping `Error` from the enclosing row, while the raise propagates at run time: a program that declares it does not raise and does. Declaration and host binding land together or not at all.

NAMING, TO DECIDE HERE. 047 calls it `reify`; `anthill.reflect.KB.reify` already means Term -> TermRepr (reflect.anthill:495). Different sorts, so no collision, but the name would be doubly used.

THE DRIVER. `anthill.reflect.KB.loaded` declares `effects Error` and raises `LoadFailed(diagnostics)`; reflect.anthill's own comment at `sort LoadFailed` says the guardians example's `Rejected(diagnostics: List[T = String])` "takes exactly this shape ... so a handler can print one verbatim". guardians' `check` is host-bound (`guardians_check`, tests/guardians_test.rs:419) for this ONE reason -- its only irreducible Rust is the `Err(e) => load_failure_to_rejected(interp, e)` arm; `KB.loaded` and `guardians.gate` are already anthill. Landing this unblocks writing `check` in anthill, which in turn makes its `-Permission[Llm]` denial bind the actual checker instead of a declaration over an opaque host function.

ACCEPTANCE: DRIVEN, not loaded. Call an operation declaring `effects Error` inside the boundary and assert the RECOVERED PAYLOAD as a value. Three controls, each saying at its site which tests fail when the change is backed out and which pass either way by design: (a) the same call OUTSIDE the boundary still raises; (b) an enclosing operation declaring a row WITHOUT `Error` loads, and backing the boundary out makes it "undeclared effect: Error"; (c) a body that does not raise returns the `Ok` arm. Full cargo-test green. SCALAND: no work -- it has no typer and no evaluator (parse / load / kb / resolve / discrim / subst only), so there is no mirror.

