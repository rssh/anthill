## Attributes

- id: WI-20261027-WGJFN-a-registered-error-handler-can
- created: 2026-10-27T20:07:13Z

- status: Open
- status_agent: claude
- status_at: 2026-10-27T20:07:13Z

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

