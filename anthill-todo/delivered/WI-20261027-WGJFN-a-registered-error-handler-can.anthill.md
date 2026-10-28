## Attributes

- id: WI-20261027-WGJFN-a-registered-error-handler-can
- created: 2026-10-27T20:07:13Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-27T23:18:24Z

- acceptance: cargo-test, scaland-sbt-test

- tags: effects

## Description

A REGISTERED `Error` HANDLER CAN VOID A DISCHARGE THE TYPER GRANTED: IT IS ASKED BEFORE ANY `Error.reify` BOUNDARY. A part of WI-20260908-9WVT7 (catching only what a boundary is typed at), filed from its leftovers with the user, 2026-10-27.

`Interpreter::raise_typed` (rustland/anthill-core/src/eval/effects.rs) runs a registered `Error` handler at the raise, before the raise travels to a boundary, so the handler is the innermost delimiter. The stock handler (`default_error_handler`, registered by `register_standard_effect_handlers` for `anthill run`, anthill-todo and a generated bundle) answers `Rethrow`, so nothing shows. A host handler that answers `Throw(v)` replaces the raise by one of unknown type (`RaisedType::Unknown`), which a typed boundary does not catch.

MEASURED 2026-10-27 on e9587427 (a temporary probe, removed), over

    sort Boom
      entity boom(why: String)
    end
    operation mayFail(n: Int64) -> Int64 effects {Error[Boom]} = Error.raise(boom(why: "x"))
    operation c(n: Int64) -> Int64 =
      match Error.reify[T1 = Boom](lambda () -> mayFail(n))
        case ok(_) -> 1
        case err(_) -> 2

`c(1)`: no handler, 2; the stock handler, 2; a handler throwing the payload it was handed, `Err(Raised { payload: boom(why: "x"), raised_type: Unknown })` — the raise leaves `c`, whose row the typer read with no `Error`; a handler throwing a string, the same with the string; a handler answering `Pure`, `Internal("Error handler resumed a raise (returned Int64) — Error is non-resumable")`. Only a host embedding registers one (eval_test, wi_8y5be, wi_5cdn5 do).

QUESTION FOR THE USER, before implementing: which delimiter wins. (a) The boundaries first: a raise reaches the innermost `reify` that catches it, and the handler sees only a raise no boundary catches, as the outermost delimiter (047 §3: handler / `provide` = `reify` / `reset`). (b) The handler first, as now, but it may only observe and `Rethrow`; a `Throw` under a boundary that catches the raise is refused loudly. (c) As now, and the spec says a host handler may void a boundary.

ACCEPTANCE: the decided order; rows driving `c` above under each handler answer (`Rethrow`, `Throw` of the payload, `Throw` of another value, `Pure`), and a raise no boundary catches still reaching the handler; back-out measured; full gate green.

## Changes

### 2026-10-27T21:57:26Z — feedback — claude

DECIDED WITH THE USER (2026-10-27). The `Error` handler stays: proposal 027's `Error[T]` entry gives it its purpose (a handler that logs and re-raises; try-catch), and it stays where it is, asked at every raise, a caught one too. It was written before a raise carried its type value, so the type value is added to both its input and its output: the handler is handed the raise's type value with the payload, and a re-raise carries it, so a boundary catches the re-raise by its type. A handler that throws a value of its own can pass it on: the thrown value is raised with a type value, and a boundary catches it by that type. The question in the description (which delimiter wins) is answered by this: the order is kept, the type is no longer lost. My earlier claim to the user that the `Error` slot was not needed was wrong — I had read only who registers one today, not 027.

### 2026-10-27T22:26:44Z — feedback — claude

DECIDED WITH THE USER (2026-10-27), the throw of a value of its own: refused for now where the raise's type does not admit the thrown one (a `Fatal` thrown for a raise at `Boom`), checked by the predicate the boundary and the typer's discharge already use (`type_pattern_admits`). The refusal is not a raise — no boundary catches it, and the old value is not thrown in its place — but a fault the host gets from `interp.call`, naming both values and both types. Every answer of a handler the runtime will not apply is one variant, `EvalError::HandlerError { effect, op, reason }`, reasons `ResumedARaise` (`Pure` to a raise, today two `Internal` messages), `ThrowNotAdmitted` (new), `NoRaiseToRethrow` (`Rethrow` from a handler of another effect) and `NotYetSupported` (`Fail`/`Choice`/`Suspend`); `UnsupportedHandlerAction` is folded into it.

### 2026-10-27T23:18:23Z — feedback — claude

DELIVERED (2026-10-27), as decided with the user the same day. The `Error` handler is handed `[payload, type_value]` — the `TypeValue` dictionary the raise carries, `[payload]` alone for a raise of the unknown type — and `HandlerAction::Throw` carries a type value (`Throw(payload, type_value)`; `Interpreter::type_value_of(&value)` reads one off a value). A handler's raise is applied only where the raise point admits its type, by the test a boundary runs (`type_pattern_admits` on the types `raised_type_value` reads): for the `Error` handler the raise it answers, for a handler of another effect the `Error` label of the operation it performs — the `Console` and `Clock` operations declare none, so their handlers' throws are refused. A raise that leaves a handler through its `Err` channel (one it makes with `raise_error`, or of anthill code it calls) is held to the same test. Found by /code-review and fixed in the same change: a host function raising for an operation whose row declares no `Error` is refused where it raises (`RaiseTypeUnread`), where it escaped as a raise of the unknown type.

Every answer of a handler the runtime will not apply is one variant, `EvalError::HandlerError { effect, op, reason }`: `ResumedARaise` (was two `Internal` messages), `ThrowNotAdmitted { raise_point, route, thrown, thrown_type }`, `NoRaiseToRethrow` and `NotYetSupported` (was `UnsupportedHandlerAction`). It is a fault: no boundary catches it and nothing is raised in its place.

Rows: tests/include/wi_wgjfn_error_handler_type_value_test.rs (9), whose header lists each back-out measured alone and the rows it moves; re-pointed: wi_5cdn5 (a replaced `String` refused; a host operation with a bare `Error` row raising at the unknown type, `atBox`, which carries the old 9WVT7 "not stolen" subject; a `Ticker` throw held to `tick`'s row; a raise from `silent`, whose row declares no `Error`, refused), wi_9wvt7_error_reify (a `Clock` handler's throw refused), eval_test (wi467, wi610, wi389), wi818 (a resume refused), 0QV5A, 8Y5BE, SPGBP. Proposals 027 (the carrier, the `Error[T]` entry) and 027.4 (the open question answered). The spec is unchanged: its note on the handler registry is the user's to word.


Gate 11047 passed / 0 failed / 17 ignored; families ok.

