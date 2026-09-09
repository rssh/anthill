## Attributes

- id: WI-20260908-9WVT7-land-proposal-047-s-error
- created: 2026-09-08T13:03:02Z

- status: Open
- status_agent: user
- status_at: 2026-09-08T13:03:02Z

- acceptance: cargo-test

- tags: effects

## Description

LAND THE `Error` LAYER OF PROPOSAL 027.4 — `Error.reify` and `Result` — so anthill code can
CATCH a raise. Today nothing in the language can catch anything: measured, no operation
anywhere in stdlib REIFIES AN EFFECT, so every operation declaring `effects Error` (15 in
stdlib alone) is uncatchable from anthill. (`anthill.reflect.KB.reify` exists — the Term ↔
TermRepr bridge, reflect.anthill:495 — an unrelated use of the word. NAMING DECIDED:
`Error.reify`, a MEMBER of the effect sort, which keeps the two apart at every call site and
is 047 §2's own rule that an effect's monad lives in that effect's API.)

THE DESIGN IS SETTLED AND WRITTEN UP: `docs/proposals/027.4-error-effect-reify.md`. This
ticket is its build path. 047 is a DRAFT BRAINSTORM — 433 lines that survey monad
transformer stacks, effect ranks, `select_monad` and graded monads, none of it needed here
and none of it with an acceptance — so 027.4 extracts the one screen that is decidable for
`Error` and commits to it, in the 027.x sub-proposal series beside 027.2 (`Branch`).

THE SHAPE. 047 §3's Filinski pair at `M = Result`. `reflect` is ALREADY IMPLEMENTED — an
effect operation IS a reflect, so `raise(x) = reflect(err x)`; what is missing is `reify`:

  operation reify[Rho, X, T1](body: () -> X @ {Error[T1], Rho}) -> Result[E = T1, T = X]
    effects {Rho}

declared as a member of `sort anthill.prelude.Error`. `T1` is inferred from the body's row
and flows into `Result[E = T1]`; a caller writes nothing.

THE BOUNDARY IS A FRAME, and `reify` CANNOT be an ordinary builtin. `BuiltinFn` returns a
`Value` and has no way to enter a closure; re-entering `run()` is what 047 §4 rejects and is
unsafe here besides — `deliver` pops until the activation stack is EMPTY with no per-run
base, so a nested `run()` unwinds into its caller's frames (`guardians_check` survives its
`interp.call` only because every test enters it at top level). So: a new
`AwaitState::ReifyBoundary`, a dispatch arm that sets it and pushes the closure body instead
of the TCO frame replacement, `ok(v)` on normal delivery, and a `run()` catch that on
`EvalError::Raised` unwinds to the nearest boundary AT OR ABOVE this run's stack base and
delivers `err(payload)`. Keyed by SYMBOL, never by name (WI-897).

NO HANDLER-REGISTRY WORK, and this is the load-bearing scoping decision. `Error.raise` is
deliberately NOT one of the seven `effect_dispatcher!` sites (eval/builtins.rs) — an
unhandled Console/Modify effect is a missing-capability `Internal` fault, an unhandled
`Error` must default to Throw so the payload is never lost. `reify` must stay off that path
for a reason stronger than the registry being unscoped: A HANDLER CANNOT EXPRESS RECOVERY AT
ALL. `raise(error: T) -> Nothing` has no value to resume with, and `raise_error` already
refuses the attempt loudly ("Error handler resumed a raise — Error is non-resumable"). A
short-circuit needs somewhere to short-circuit TO, and that is not a handler — 047 §3 states
the identity: handler / `provide` = `reify` / `reset`.

NO CONTINUATION CAPTURE, which is why this does not wait on WI-078. 047 §5: first-order
monads are the degenerate fragment — abort/return, no `shift`, no prompt. WI-078's
remaining half is `snapshot_eval_state` / `resume_with` / the `Choice`/`Suspend`
interpretation, which 047 assigns to the RESUMABLE effects (WI-069 Suspension, WI-070
Branch, and 027.2, which needs a whole `StepOutcome::Suspend`). `Error` runs the thunk and
either returns or aborts.

DELIVERED ALREADY — the two typer fixes this needed, both green at 6650 passed / 0 failed:
 (a) `validate_callback_effect_row` DEEP-RESOLVES a callback row's labels. It compared them
     through `walk_value_to_resolved`, which chases a TOP-LEVEL var chain and never descends
     into an `Fn`'s arguments, so a declared `Error[T = ?P]` was compared UNRESOLVED against
     `Error[T = Boom]` — even though unification had already bound `?P := Boom` (measured by
     instrumenting the comparison). Not `Error`-specific: `Permission[C]` was the second
     witness.
 (b) The WI-325 abstract-param loop no longer demands a `requires` for a spec parameter the
     called operation NEITHER MENTIONS NOR RECEIVES. It walked every parameter of the spec
     sort without asking whether the operation uses it, and whether that became a diagnostic
     was then decided by `spec_warrants_abstract_check`'s NAMESPACE leg — so byte-identical
     source loaded under `anthill.*` and was refused outside it. USER DIRECTION: anthill and
     user namespaces should not differ. Measured, `MySpec.ping()` on a receiverless spec:
     before (b) refused in a user namespace and LOADING under `anthill.*`; after (b) both
     load. It removes an inconsistency rather than opening a hole — and the message it
     removes was the wrong one anyway, since `ping` is body-less with no provider and adding
     the suggested `requires` would not make it runnable. THAT missing check — an
     unimplemented operation reaching a call site — is a separate defect, undetected under
     `anthill.*` before this change and under both namespaces after it. Candidate ticket,
     not filed.
Tests: `wi_9wvt7_reify_typing_test` (5), each stating its back-out measurement at its site.

REMAINING — 027.4 build path steps 2-5:
 2. `Result` in the prelude: `sort E = ?` (payload) + `sort T = ?` (success value, the
    `Monad` carrier's member), `ok` / `err`, `map` / `flatMap`, and `reflect` (writable in
    anthill, no runtime work). `provides Monad[M = Result[E = E], …]` is DRIVEN, not
    assumed: measured `ok(3).map(+39) = 42`, `err(boom).map(+39) = nope`,
    `ok(3).flatMap(*2) = 6`.
 3. THE BOUNDARY (the risky increment — goes before the surface).
 4. `Error.reify` in effects.anthill, and `KB.loaded` retyped to `effects Error[LoadFailed]`
    — it raises `load_failed(diagnostics)` and nothing else, and those diagnostics are fed
    back to a model as repair feedback, so the payload should be CHECKED at the reify site
    rather than asserted. (A typed `reify` correctly REFUSES a bare-`Error` body: measured,
    an undecided payload does not satisfy a decided one, matching how a bare `Option`
    behaves in a value slot.)
 5. ACCEPTANCE, DRIVEN. Call an operation declaring `effects Error[…]` inside the boundary
    and assert the RECOVERED PAYLOAD AS A VALUE. Three controls, each saying at its site
    which tests fail when the change is backed out and which pass either way by design:
    (a) the same call OUTSIDE the boundary still raises; (b) an enclosing operation
    declaring a row WITHOUT `Error` loads, and backing the boundary out makes it "undeclared
    effect: Error"; (c) a body that does not raise returns the `ok` arm.

LANDMINE FOR STEP 5: `match` arms are NOT checked against the scrutinee's sort — measured,
`operation f(b: Boom) -> Int64 = match b case other(n) -> n`, where `other` belongs to an
unrelated sort, LOADS CLEAN. So an acceptance that destructures the recovered payload proves
nothing at load time; it must run and assert the value.

THE DRIVER. `anthill.reflect.KB.loaded` raises `load_failed(diagnostics)`; the guardians
example's `LoadChecker.check` is host-bound Rust for exactly one irreducible reason, its
`Err(e) => load_failure_to_rejected(interp, e)` arm. `KB.loaded` and `guardians.gate` are
already anthill; only the catch is not. Landing this lets `check` be written in anthill.

SCALAND: no work — it has no typer and no evaluator (parse / load / kb / resolve / discrim /
subst only), so there is no mirror.

ACCEPTANCE: step 5 above, plus full cargo-test green.

## Changes

### 2026-09-08T21:18:38Z — feedback — claude

REWRITTEN against `docs/proposals/027.4-error-effect-reify.md`. The original description was
written before three things were measured, and each changed the plan:

WHAT THE ORIGINAL GOT WRONG. (1) It proposed `reify[Rho, X, P](body: () -> X @ {Error[P],
Rho}) -> Result[P, X]` and asserted the typing "is already delivered and needs nothing".
That signature did NOT load — two independent typer defects stood in the way, both now
fixed and tested here. (2) It justified the single-callback shape by WI-20260820-RDNS4's
refusal of the two-callback form. That refusal is a BUG — RDNS4's own words: "`Rho =
{Clock}` is a valid solution in both; the typer rejects a well-typed program" — so it is not
support for anything. 027.4 argues single-callback on merit instead: the sum IS what makes
this a monad LAYER (the `Result` is a value you can `map` / `flatMap` / `reflect`), and 047
§7 already makes `try_catch(body, recover)` a library function over it. When RDNS4 lands
that sugar becomes writable with no change here. (3) It named "NAMING, TO DECIDE HERE" —
decided: `Error.reify`, a member of the effect sort, so the effect's API is where its monad
lives (047 §2) and `Branch.reify` / `Suspension.reify` follow the same shape later.

TWO PRE-EXISTING DEFECTS FOUND AND RECORDED IN 027.4, neither in scope, both needing an
owner: a GUARDED label (`Error[Boom] :- eq(b, 0)`, proposal 048) does not conform to an
unguarded `{Error[Boom], Rho}` callback row — which removes `Int64.div` and `Stream.head` as
demonstrators; and a `{Error[Boom], Rho}` parameter ADMITS an `{Error[?]}` body, where the
value-slot twin refuses, so an undecided payload satisfies a decided demand in row position
only.
