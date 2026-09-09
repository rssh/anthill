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

### 2026-09-09T15:21:28Z — feedback — claude

STEPS 2, 3 AND 5 DELIVERED; STEP 4 HALF. ANTHILL CAN NOW CATCH A RAISE. Measured with
`anthill run`: `Error.reify(lambda () -> mayFail(0 - 1))` returns `err(boom("negative"))`
and the payload destructures in anthill; the non-raising twin returns `ok(42)`.

WHAT SHIPPED.
 2. `stdlib/anthill/prelude/result.anthill` — `sort E` (payload) / `sort T` (success, the
    `Monad` carrier's member), `ok` / `err`, `resultPure` / `resultFlatMap` / `resultMap`,
    `reflect`, and `provides Monad[M = Result[E = E], …]`. Placed beside `option` and
    after the `monad` both provide into. The `Monad` provision is DRIVEN, not assumed:
    `ok(3).map(+39) = 42`, `err(boom).map = nope`, `ok(3).flatMap(*2) = 6`,
    `err(boom).flatMap = nope`, `reflect(ok(3)) = 3`, `reflect(err(boom))` raises.
 3. THE BOUNDARY. `AwaitState::ReifyBoundary` (`eval/frame.rs`) — the first LIVE state of
    its kind, since `OperationResult` is set nowhere (TCO replaces every operation entry
    in place). `enter_reify_boundary` suspends the dispatching frame on it and runs the
    thunk ABOVE; normal delivery wraps `ok(v)` and cascades; `run()` catches
    `EvalError::Raised`, unwinds to the innermost boundary AT OR ABOVE this run's floor,
    and delivers `err(payload)` FROM it — so both exits end in the same last step, pop the
    boundary and hand a `Result` to its parent. Keyed by SYMBOL: `ErrorLayerSymbols`
    resolves `reify` / `ok` / `err` once at construction, beside `ReflectSymbols`, so the
    per-dispatch test is one `Option<Symbol>` comparison.
 4a. `Error.reify` declared in `effects.anthill`, body-less on purpose.
 5. `wi_9wvt7_error_reify_test` (10 rows) + two `frame.rs` unit tests.

THREE THINGS THE PROPOSAL'S SKETCH DID NOT SAY, each settled by writing it.
 * The thunk is entered through a SHARED helper. `reify`'s argument is a callable VALUE
   with no name bound to it, where an ordinary HOF's callback is a LOCAL. So
   `dispatch_call_with_requirements_inner`'s two callable arms moved out to
   `apply_callable_value`, which both callers now use — the `OpRef` half (eta spread,
   captured dict, op-scoped slots) is not written twice. Its third arm is LOUD, and earns
   it: at the HOF site a non-callable is unreachable (the local is pre-filtered), at a
   `reify` argument it is not.
 * A PLACEHOLDER frame, because entering is REPLACING. `enter_closure` /
   `enter_operation` both TCO-rewrite the top frame, so the boundary pushes an
   `Expr::Bottom` frame for them to rewrite. `Bottom` deliberately: it must never reduce,
   and if some future arm ever entered by PUSHING, that surfaces as a loud `Internal`
   rather than a boundary answering its own placeholder.
 * THE FLOOR IS PINNED BY A UNIT TEST AND NOTHING ELSE. No anthill spelling reaches a
   nested `run()` with a boundary beneath it: the operation that re-enters `run()` on a
   live stack is reached from the RESOLVER, and a rule body's raise appears in no caller's
   row, so a typed `reify` cannot wrap it. `frame.rs::the_boundary_scan_stops_at_the_floor`
   drives `topmost_reify_boundary` directly — delete `floor` and nothing else goes red.
   (Bounding the RAISE scan is what 027.4 owed. The SUCCESS path still rides `deliver`'s
   pre-existing unbounded pop.)

BACK-OUT, MEASURED. Disabling the dispatch arm: 8 failed, 2 passed. Every row that CALLS
`reify` dies `OperationBodyMissing { name: "anthill.prelude.Error.reify" }`. The two that
pass either way are `a_row_without_error_is_still_refused` (the TYPER's half — the
discharge is in the SIGNATURE and needs no runtime) and `an_unreified_raise_still_escapes`
(the layer did not turn every raise into a value). `a_non_raised_error_is_not_caught` fails
under the back-out too, so it separates the boundary not from nothing but from a WIDER one:
it reds the moment recovery accepts anything but `EvalError::Raised`.

STEP 4's SECOND HALF — `KB.loaded` retype — NOT DONE, BLOCKED IN THE RUST BRIDGE, MEASURED.
The row is what `anthill-stl/build.rs` generates `KB::loaded`'s host signature from, so
`effects Error[LoadFailed]` makes it `Result<Box<dyn KB>, LoadFailed>` over a type the
generated module does not contain — `emit_only` is a CLOSURE THE AUTHOR STATES (its own
comment says exactly this, for `LayerSymbol` / `LayerClause`). Naming `LoadFailed` there
gets one step further and hits two codegen defects: a duplicate `use crate::prelude::{List,
String}` (E0252) and no `String` in the reflect prelude shim (E0432). Both live in the
rust-gen import emitter. Backed out, with a note at the declaration saying so.
CONSEQUENCE, and it is the typed `reify` being RIGHT rather than a gap: measured,
`Error.reify(lambda () -> KB.loaded(cons(src, nil())))` is refused — "the lambda argument
declares `Error`, which the closed row does not admit". A raiser that wants to be caught
must say what it raises. The guardians `LoadChecker.check` rewrite waits on that codegen
fix, not on this ticket.

FOUND WHILE DRIVING, NOT IN SCOPE, NOT FILED.
 * A HOST RAISE PUTS AN OFF-CHANNEL PAYLOAD IN A TYPED `err`. `raise_match_failed` raises
   `Error[MatchFailed]` through the channel an operation declared as `Error[Boom]`, and
   nothing puts that label in the row. A source `match` cannot reach it — a non-exhaustive
   one is a LOAD error — but a GUARD-exhaustible one can: measured,
   `match n case k | k > 0 -> k` inside a reify body returns
   `err(match_failed(occurrence, scrutinee))` in a `Result[E = Boom]`, and the caller's
   `case boom(w)` then fails at RUN time. The boundary is not what is wrong
   (`Error[MatchFailed]` IS an `Error`); the upstream rule that a host raise need not
   appear in the row it rides is. Pre-existing in kind; reify is the first thing that can
   observe it.
 * `interp.config_mut().depth_cap = Some(n)` AFTER construction changes the config and
   nothing else — `with_config` sizes the `ActivationStack` once and the stack keeps its
   own copy. Measured: a depth-cap control written that way ran to the 1,000,000-frame
   default and took 60+ seconds to assert the same thing. Noted at the test site.
\n
### 2026-09-09T17:33:36Z — feedback — claude

`/code-review` PASS: 15 findings, 8 FIXED HERE, 6 RECORDED IN 027.4's OPEN QUESTIONS, 1
refuted. The two that mattered:

 * A LOCAL NAMED `reify` CAPTURED A QUALIFIED `Error.reify(...)` CALL — a soundness hole,
   not a wrong answer. `dispatch_call_with_requirements_inner`'s local lookup matches by
   SHORT NAME, and the interception sat BELOW it, so a parameter called `reify` holding
   anything callable won. The DISCHARGE had already been granted on the resolved
   signature, so the raise then escaped an operation the typer certified effect-free.
   The WI-455 name-capture class at a second site; fixed by hoisting the test above the
   lookup, and DRIVEN — `a_local_named_reify_does_not_capture_the_boundary` reads
   `ok` instead of `err` when the hoist is backed out (measured).
 * `effects.anthill` NOW IMPORTS `Result`, AND SCALAND KEEPS ITS OWN PRELUDE LIST.
   Measured against the compiled scaland: working tree `LOAD-ERRORS: 1 —
   effects.anthill:130:38: unresolved name 'Result'`, control at HEAD `LOAD-ERRORS: 0`.
   One line in `EmbeddedStdlib.scala`. (The "scaland has no typer, ignore the mirror"
   rule is about TYPER work; a stdlib file list is not that.) It cost a second scaland
   line too, found by RUNNING the suite rather than by the review: `BootstrapTest`
   compiles `effects.anthill`'s emitted Scala against a HAND-LISTED closure, and
   `Error.reify` now names `Result` in its return type, so `Error.scala:5: type Result is
   not a member of anthill.prelude`. Two tests gained `preludeClosure("monad", "result")`
   — which is what that hand-listed set is FOR: a signature that reaches a new file is a
   line to add, not a silent shrink. `BootstrapTest` after: 111 total, 109 passed, 2
   failed, BOTH the pre-existing `field.anthill` refusal that is not in `expectedRefusals`
   (untouched by this change, committed by someone else earlier today, and the review
   measured it reproducing on a HEAD control). `ParserIntegrationTest` re-run for the
   13 no-load-error assertions the import would otherwise have broken.

ALSO FIXED: the `Error` layer is all-or-nothing (`Option<ErrorLayer>` rather than three
independent `Option<Symbol>`s — a half-resolved layer would have let the thunk RUN before
anything checked, and the check discarded the `Raised` payload on the way out);
`enter_reify_boundary` now decides EVERYTHING that can refuse the call before installing
anything, so its own comment is true (`Error.reify(42)` loads — a row-polymorphic arrow
slot does not refuse a non-callable — and used to reach the loud arm with the boundary
already marked); it uses the existing `suspend_and_push` / `bottom_node` instead of
hand-rolling them; `unwind_to_boundary` is `pub(crate)`, its precondition no longer being
a `debug_assert` on a public surface; the profiler counts a boundary entry; the dropped
`requirements` / `type_args` are documented as a DISCARD rather than left silent; and
`resultFlatMap` / `resultPure` are now DRIVEN (only `resultMap` was).

TWO DOC CLAIMS OF MINE WERE FALSE AND ARE CORRECTED. `result.anthill`'s header said the
partially-applied carrier `Result[E = E]` "is what makes map/flatMap short-circuit" —
measured, a `provides` carrier's written type arguments are INERT (a bare `Result`
dispatches identically, and even `MyRes[E = Boom]` admits a receiver at another payload);
the short-circuit is in the `match` bodies. And 027.4 said "a non-exhaustive match is a
LOAD error" — true for an `enum`, FALSE for a `sort`, which is a second door into the
off-channel-payload question below.

RECORDED, NOT FIXED — all in 027.4's open questions with their measurements:
 * THE BOUNDARY CATCHES ON THE CARRIER, NOT THE PAYLOAD'S SORT. The sharpest case is not
   the host-raise one already noted: a body declaring `{Error[Boom], Error[DivisionByZero]}`
   reified at `T1 = Boom` has the second label left in the CALLER's row BY THE TYPER, and
   the boundary swallows it anyway. Narrowing needs `T1` at run time and a rule for a
   payload that matches no boundary.
 * `Error.reify` WORKS ONLY FROM AN OPERATION BODY. `rule direct(?r) :- Error.reify(…, ?r)`
   answers NO SOLUTIONS. CONTROL MEASURED: an ordinary `operation nobody(n) -> Int64` with
   no implementation answers NO SOLUTIONS from a rule body too — so this is WI-20260909-M8QWJ's
   class, not a new hole. Not a two-line addition either: that entry pushes onto a LIVE
   stack and `deliver` has no per-run floor. Noted at the declaration in `effects.anthill`.
 * A USER-DECLARED effect layer's `reify` loads clean and traps at run time — the boundary
   is keyed to one hard-coded name. Same class; and the same question 027.2 will ask when
   `Branch.reify` wants a second field.
 * `Result` has no host `TypeMapping` in any realization profile, where `Option` has one in
   every profile. Codegen is out of scope by design, but WI-891's cpp degrade `static_assert`-fails.
 * WHICH DELIMITER WINS — a registered `Error` handler is consulted BEFORE the default, so
   it is dynamically outermost and a custom one can void a declared discharge. Invisible
   with the stock handler (it Throws), and `interp_for` registers none.
\n
### 2026-09-09T20:33:12Z — feedback — claude

STEP 4's SECOND HALF DELIVERED — `KB.loaded` IS RETYPED AND THE DRIVER RUNS. The
"blocked in the rust bridge" note in the previous entry was written from two error codes;
reading the emitter turned three symptoms into ONE defect plus two one-line settings, and
CLAUDE.md's rule then applies — a change smaller than its ticket description is inline
work, so nothing was filed.

WHAT IT ACTUALLY WAS.
 1. `LoadFailed` named in `anthill-stl/build.rs`'s `emit_only` — a CLOSURE THE AUTHOR
    STATES, as its own comment already says for `LayerSymbol` / `LayerClause`. One line.
 2. `String` re-exported from the reflect prelude shim. NOT a defect: that file exists
    for exactly this and documents it — `Type`, `TypeExtractor` and `FieldOf` are each
    there because a generated `use crate::prelude::{…}` names them. One line.
 3. THE ONE REAL DEFECT — ANTHILL IMPORTS ARE PER-DECLARATION, RUST `use` IS PER-MODULE.
    A generated file is one Rust scope, so two declarations that both
    `import anthill.prelude.{List}` emitted two `use crate::prelude::{List};` — E0252.
    Latent until now because no two emitted declarations of one file had shared an
    import; `LoadFailed` joining the reflect subset was the first. `RustCodegen` carries
    an `imported: HashSet<(path, name)>` and `emit_import` filters against it, dropping
    REPEATS rather than whole imports — a second import's new names still arrive, which
    is the assertion that stops the fix passing by emitting nothing.

DRIVEN. `codegen_test::one_name_is_imported_once_per_file` and
`a_repeated_plain_import_is_emitted_once`; measured under a back-out both read "got 2"
while the other 37 codegen rows pass either way. The corpus witness is louder: with the
filter off, `anthill-stl` does not compile at all.

AND THE DRIVER ITSELF, which is what the whole ticket was for:
`Error.reify(lambda () -> KB.loaded(cons(src, nil)))` on a candidate that does not parse
returns `err(load_failed(diagnostics))` with the diagnostics intact — the arm that kept
the guardians `LoadChecker.check` in host Rust (`Err(e) => load_failure_to_rejected`),
now writable in anthill. `a_scoped_loads_diagnostics_are_caught_in_anthill` asserts both
arms: a candidate that loads reaches `ok`, one that does not yields exactly one
diagnostic. It fails under a back-out of the RETYPE at LOAD time, not at run time — a
bare-`Error` body is refused by a typed `reify`, which is the point of retyping.

The bridge's own `loaded` now returns `LoadFailed::LoadFailed { diagnostics }` rather
than the generic `Error`. That is the retype's consequence, not a defect: the ROW is what
generates the host signature, so a raiser that says what it raises types its bridge too.
