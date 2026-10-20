## Attributes

- id: WI-20260908-9WVT7-land-proposal-047-s-error
- created: 2026-09-08T13:03:02Z

- status: Open
- status_agent: user
- status_at: 2026-09-08T13:03:02Z

- acceptance: cargo-test

- depends_on: WI-20260911-3MV2C-a-reify-boundary-decides-on

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
   drives `reify_boundaries` directly — delete `floor` and nothing else goes red.
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
`Error.reify(lambda () -> KB.loaded(cons(src, nil)))` returns `err(load_failed(ds))` with
the LOADER'S OWN PROSE intact — the arm that kept the guardians `LoadChecker.check` in
host Rust (`Err(e) => load_failure_to_rejected`), now writable in anthill.

THE ACCEPTANCE ASSERTS THE PROSE, NOT A COUNT, and the first cut of it got this wrong —
it answered `length(ds)`, which proves a list of the right length arrived and nothing
about its content, and a model reading "1" learns nothing about what to fix. What the
diagnostics actually carry, measured:
  * `namespace broken.` -> `source 0: 1:1: syntax error near `namespace broken.``
    — located, and it says WHICH candidate, which is what a checker handed several
    sources needs to attribute the failure.
  * `operation f(n: Int64) -> String = n` -> `type mismatch in f.return (op-return):
    expected String, got Int64` — this names the CHECK THAT RAN and both sides of what
    it wanted. That is a repair instruction, not a verdict, and it is the whole reason
    the payload is worth catching.
`a_scoped_loads_diagnostics_are_caught_in_anthill` pins both shapes plus the `ok` arm. It
fails under a back-out of the RETYPE at LOAD time, not at run time — a bare-`Error` body
is refused by a typed `reify`, which is the point of retyping.

The bridge's own `loaded` now returns `LoadFailed::LoadFailed { diagnostics }` rather
than the generic `Error`. That is the retype's consequence, not a defect: the ROW is what
generates the host signature, so a raiser that says what it raises types its bridge too.
\n
### 2026-09-10T09:16:23Z — feedback — claude

THE ONE SOUNDNESS GAP IS CLOSED: a boundary now catches ONLY the payload it is typed at.
USER DIRECTION, and it is the standard rule — handle ours, return not-ours as an error;
Scala additionally lets a handler name several types.

THE TYPE SYSTEM ALREADY SAID THIS. `reify` shares its row tail, so a body raising
`{Error[Boom], Error[Other]}` reified at `Boom` leaves `Error[Other]` in the CALLER's
row. Measured three ways: the caller declaring it LOADS; the caller omitting it is
REFUSED ("undeclared effect: Error[T = Other]"); and a `reify` at `Boom` around a body
raising only `Other` is REFUSED too ("expected Result[E = Boom], got Result[E = Other]")
— `T1` is INFERRED from the body's row, so a boundary cannot even be typed at a label its
body does not raise. Only the runtime disagreed.

WHAT IT DID INSTEAD. `AwaitState::ReifyBoundary` was a unit variant, so recovery could
only ask "is this an `EvalError::Raised`". It swallowed the `Other` into a
`Result[E = Boom]` and the caller's `case boom(w)` died one step later on a value that
could never legally be there: MEASURED, `caughtBoom(7)` answered
`match_failed(scrutinee: other(n: 7))`. Now it answers `error: other(n: 7)` — the raise
escapes carrying its own payload.

THE MECHANISM. `ReifyBoundary { payload: Option<Symbol> }` carries the payload SORT, read
off the type-argument channel the dispatch arm already received and previously dropped —
probed, the channel really does carry `key=T1 term=Ref(Boom)`. `T1` is narrowed to the
sort it names at INSTALL, not at the catch, so the catch path is total. The unwind goes
from
"the innermost boundary" to "the innermost boundary that ACCEPTS this payload":
`ActivationStack::reify_boundaries` returns candidates innermost-first and
`payload_matches` judges each against `runtime_carrier_sort` of the raised value. Nothing
accepts it -> it propagates out of the run, exactly as a raise outside every boundary
does.

A WIDER BOUNDARY ADMITS A NARROWER RAISE, and that is not a choice made at the boundary.
`Error`'s payload is declared `Covariant` (035's variance facts), so a body raising
`Error[Narrow]` conforms to a `reify` typed at `Error[Wide]` where `sort Narrow requires
Wide`, and the typer DISCHARGES the label. Equality would therefore be UNSOUND, not
merely strict — the raise would escape an operation already typed effect-free.
`payload_matches` answers through `sort_sym_compatible`, the typer's own sort-vs-sort
predicate. NOT full parity — the typer's arm is `bare_sort_compatible` and discharge runs
through `labels_match_aligned`, and the covariant DIRECTION is hardcoded here while the row
reads `fact Covariant(sort: Error, param: T)`. The extra legs were driven and both programs
are refused at load today, so nothing escapes; that is containment, not agreement. Driven by
`a_boundary_catches_a_payload_whose_sort_refines_its_own`
— and the DRIVING SHAPE NEEDS A WRITTEN `Error.reify[T1 = Boom]`: left to inference `T1`
comes from the body's row, so the boundary lands ON the raiser's sort and equality answers.
The first fixture written for this passed with the leg backed out for exactly that reason.
Measured with the written bracket: 1 failed of 24, and the inferred-`T1` control in the
same test still passes.

TWO CONSEQUENCES, NEITHER A TRADE.
 * THE OFF-CHANNEL HOST RAISE IS FIXED BY THE SAME RULE. `raise_match_failed` /
   `raise_division_by_zero` ride a row they never appear in; they are not `Boom`, so a
   boundary at `Boom` declines them. Measured: a guard-exhaustible match inside one now
   surfaces as `match_failed(scrutinee: -5)` where it used to surface as a `match_failed`
   NESTED INSIDE A SECOND ONE. That was recorded here as a separate open question; it is
   the same question.
 * A MULTI-LABEL CATCH NEEDS NO NEW FORM. The effect ROW is the list of labels, and one
   `reify` per label composes as nested `Result`s — driven: inner at `Boom`, outer at
   `Other`, and each raise reaches the boundary typed at it. 047 §7's `try_catch` can
   flatten the nesting later as ordinary sugar.

DRIVEN, with the control. Three new rows —
`a_boundary_declines_a_payload_it_is_not_typed_at`,
`each_raise_reaches_the_boundary_typed_at_it`,
`a_host_raise_is_not_mistaken_for_the_declared_payload`. Measured with `payload_matches`
forced to `true` (the old carrier-only rule): 3 failed, 12 passed — exactly those three,
because every other row is about a boundary catching its OWN payload, which both rules
agree on. The two-way row pins the CHOICE rather than passing by luck: under
"innermost wins" both raises answer through the inner boundary.

`payload_matches` answers `false` for a value whose sort cannot be read, deliberately: an
undetermined payload has not been shown to be this boundary's, so it travels on carrying
its real value rather than being placed in a `Result[E = T1]` a caller is about to
destructure.

`None` IS "CANNOT NARROW", AND IT CATCHES WIDE — the shape a first attempt at this got
wrong twice, both caught by `/code-review` with driven repros, and both REGRESSIONS
against a working program rather than theory:

 * A GENERIC `reify` REACHED THROUGH A RULE BODY OR A HOST `interp.call`. Those push a
   frame with an EMPTY type-argument channel (`eval/mod.rs:1091`, `:1540`), so nothing can
   ground `P`. Refusing was measured as `rule viaGenericRule(?r) :- catchIt(lambda () ->
   mayFail(0 - 1), ?r)` answering `no solutions`, SILENTLY, beside `viaPlainRule` — the same
   call at a concrete payload — answering `err(boom(why: "negative"))`. In a debug build
   the sibling `debug_assert` in `bridge_op_to_eval` ABORTS instead. Pinned by
   `a_generic_boundary_answers_through_a_rule_body`, with the concrete row as its control.
 * A TUPLE PAYLOAD. A tuple type's head is `TypeExtractor.NamedTuple`, an ENTITY, so
   head-reading alone installed a boundary at a symbol no value's `runtime_carrier_sort`
   can equal and every raise was declined. Measured as `error: Tuple` escaping `main` from
   an operation the typer typed effect-free, beside a `Boom` row in the same program that
   caught. Pinned by `a_payload_the_runtime_cannot_narrow_is_still_caught`.

And a type PARAMETER is registered as `SymbolKind::Sort` (so `x: P` routes through the
type-param branch), so `has_kind` alone answers YES for `catchIt.P` — the first of the two
above. The guard is symbol identity against the declaring scope's parameter list.

ALSO FIXED HERE, BECAUSE THE NARROWING MADE IT REACHABLE: A DECLINED RAISE POISONED THE
INTERPRETER. `run()` drains to empty on success but an `Err` return abandoned live frames,
and until now nothing could error with a SUSPENDED frame installed — any boundary beneath
a raise absorbed it. A declined raise is an ordinary outcome now, so the leftovers became
reachable: `deliver` answers `Done` only on an empty stack, so the NEXT call on the same
interpreter popped past its own base into the stale frame and died
`Internal("deliver: parent frame had no awaiting state")`. Measured on one interpreter, a
call that answered `ok(42)` fresh. `invoke_op_with_requirements` now truncates to its entry
depth on error; pinned by `a_declined_raise_leaves_the_interpreter_usable` with the
fresh-interpreter row as its control. Every other test builds its own interpreter, which is
why none of them would have noticed; `anthill-todo`'s remint loop is the real caller that
would.

`payload_matches` answers through `sort_sym_compatible`, the typer's OWN sort-against-sort
predicate (canonical identity, the entity→parent climb, `requires`-refinement), rather than
a two-leg reimplementation. A NARROWED boundary DECLINES a payload whose sort it cannot
read, and an un-narrowable one catches it: catching at a narrowed boundary was measured
letting an inner `reify[T1 = Boom]` swallow a tuple label its own row had left to the
caller (`a_narrowed_boundary_does_not_steal_an_unreadable_payload`).

ALSO OPEN, EACH RECORDED AT ITS SITE:
 * AN INLINE SIGNATURE VARIABLE IS NOT REWRITTEN. `op_own_param_ref_rewrite` keys off
   `OperationInfo.type_params`, but the rigid list it joins against is that PLUS the
   WI-1FKR2 inline family (`via(b: Box[?t]) -> Box[?t]`, which §5.4 quantifies exactly as
   a bracket). An inline variable therefore still rides out ungroundable, reproducing the
   WI-708 dangling-var shape. Not a regression — that is the behaviour before the rewrite
   — and not covered by a test.
 * A RENAMED `T1` IS SILENT. `enter_reify_boundary` finds the payload parameter by the
   NAME `"T1"`; a missing key reads as "cannot narrow", which is legitimate for two other
   reasons, so a rename in `effects.anthill` would quietly revert every boundary in the
   program to catching wide. The repair is to resolve the SYMBOL once at
   `ErrorLayer::resolve`, where a rename fails at layer construction.
 * A RAISE THAT ESCAPES A BRIDGED OPERATION IS REPORTED AS "NO SOLUTIONS".
   `bridge_op_to_eval` turns every `EvalError` into `None`, so the goal residualizes with
   nothing said. MEASURED, with two controls, on an operation whose row is EMPTY:
   `rule answer(?r) :- guardExhaustible(0, ?r)` — a guard-exhaustible match, so the HOST
   `Error[MatchFailed]` channel is the door — answered `no solutions`, while
   `guardExhaustible(5, ?r)` answers `?r = 5`.

   THE ARGUMENT MUST BE A LITERAL, and the first two fixtures written for this were wrong
   because it was not. Spelled `guardExhaustible(0 - 5, ?r)` the operand reaches the bridge
   UN-REDUCED, so the guard compares a `Node` against an `Int64` and the bridge answers
   `TypeMismatch { expected: "Ord scalars of matching type", got: "Node and Int64" }` — a
   DIFFERENT defect that presents as the same silent `no solutions`. Only a probe inside the
   bridge's `Err` arm told them apart.

   AN EARLIER DRAFT OF THIS ITEM SAID "a DECLINED reify raise", AND THAT IS REFUTED.
   `rule viaDeclinedClean(?r) :- declinedClean(?r)`, where an inner boundary declines an
   `Other` and an outer effect-free one catches it, answers `?r = err(error: other(n: 7))`.
   What the first probe actually hit was a rule body calling an operation whose ROW IS
   NON-EMPTY, which residualizes for its own pre-existing reason — its control
   (`viaCaught`, no declined raise at all) failed identically, which is what exposed it.
   So this is PRE-EXISTING and not a consequence of the narrowing: it predates 027.4 and
   is reached through the host channel, not through `reify`.

   FILED as WI-20260911-0V0F7 after an attempt was built and REVERTED. `BuiltinResult::Error`
   is the right home, but the producer is the easy half: four consumers (`read_facts_resolved`,
   `prove_from_gamma_verdict`, reflect's `split_first`, and the load-blocking guard path) were
   each written when faults were rare, and a bridged raise changes what every one of them does.
   The channel's own doc draws exactly this line — "`Failure` claims the answer is no, `Unknown` that there is no
   answer, `Delay` that the answer is not available yet. This claims nothing about the goal
   at all — it says the resolver could not ask it."

OPEN, AND NOT CLOSED BY THIS: THE TYPE-ARGUMENT AXIS. A value's runtime sort is its HEAD,
so a boundary at `Box[V = Int64]` accepts a `Box[V = String]`. Driven by the review:
nested boundaries at `Box[V=Int64]` / `Box[V=String]` both answer through the INNER one
whichever way round they are, the control with two distinct payload SORTS answers
`outer-caught`, and a caller that then uses the field at its declared `Int64` type answers
`no solutions` — the confusion degrading into a silent failure. The typer DOES distinguish
them (`expected declared: [], got undeclared effect: Error[T = Box[V = Int64]]`). This is
PRE-EXISTING — before the narrowing no boundary judged at all — so the narrowing neither
opens nor widens it, but it is the same defect class one type-argument deeper. Closing it
needs the raised value's type ARGUMENTS, which the runtime does not reconstruct.

THE GENERIC BOUNDARY WAS NOT A `reify` PROBLEM. `operation catchIt[P](body) -> Result[E =
P, T = Int64] = Error.reify(body)` has `T1 = Var(Rigid P)` at its call site — correct, and
useless on its own, since what `P` stands for is decided by the CALLER. That was the one
case the narrowing regressed, and chasing it found a GENERAL, pre-existing defect: a
callee's type-argument channel was installed UNCLOSED, so any type parameter routed
through a generic caller arrived as a dangling skolem. MEASURED on main, with no `reify`
in sight: `operation tyOf[T](x: T) -> Type = Cell[V = T]` called from `operation tyOf2[U](y:
U) -> Type = tyOf(y)` gave `Cell[V = Var(Rigid(VarId { id: 1624, … }))]` while the direct
`tyOf(5)` gave `Cell[V = Int64]` — the WI-708 dangling-`Ref(T)` regression one level
deeper, produced by the other half of the same join.

`collect_closed_type_args` closes a callee's channel over the CALLING frame's before
installing it, which is the invariant WI-708 half-established: a frame's type-argument
channel is GROUND with respect to the generic context it came from, so no reader has to
chase. The typer cannot do the grounding — at a call site inside `caller[U]` the callee's
`T` genuinely IS `U`, a skolem, and what `U` stands for is a run-time fact.

BUT THE TYPER OWNS THE SPELLING, and that is what makes the join identity-keyed.
`op_own_param_ref_rewrite` writes each skolem standing for one of the ENCLOSING
operation's own parameters as `Ref(<op-scoped symbol>)` — the spelling a BODY reference
already carries — so eval grounds it with the same `find_type_arg` identity match
`reduce_var` uses (WI-708) and never compares a name.

THE REWRITE APPLIES TO A WHOLE ENTRY, NEVER INSIDE ONE, and that restriction is measured.
A skolem nested in a canonical `effects_rows(...)` spine is a ROW TAIL (WI-516: a rigid
set-valued var is a row VARIABLE, not a label), and `row_tail_var_of` / `row_tail_termid`
both match only `Term::Var` — rewriting one to a `Ref` leaves the decompose side reading
NO tail and silently closes a row that must stay open. `/code-review` raised it against the
first shape of this fix; instrumented, a DEEP rewrite fired on exactly those, `EffP` and
`E2` entries shaped `effects_rows(...)`, across the stdlib and a row-threading probe. The
cost of the restriction: a skolem nested in a NON-row type argument (`List[T = U]`) still
rides out ungrounded — the behaviour before this change, unchanged.

A FIRST ATTEMPT JOINED BY SHORT NAME AND WAS WRONG. `/code-review` drove it with a
one-letter control: an ANONYMOUS skolem — the `?` an unwritten `Box[V = ?]` slot becomes,
named after the SORT's parameter — was captured by a caller declaring `[V]`, giving
`Cell[V = Box[V = String]]` where the same program with the caller's parameter spelled
`[W]` left the slot a visibly dangling `Box[V = ?V]`. Pre-change it was visibly wrong;
short-name-joined it was CONFIDENTLY wrong, which is worse. Only skolems minted for the
enclosing operation's declared parameters are rewritten, so nothing else can match.

Driven by `a_reify_at_an_operations_own_type_parameter_catches` (with `viaGenericOk` as
the control that passes either way) and, for the general defect,
`a_type_argument_passed_through_a_generic_caller_is_ground` in the WI-708 file.
### 2026-09-11T13:16:42Z — feedback — claude

WHERE THIS TICKET STANDS AT THE END OF THE SESSION. Its five-step build path is DELIVERED and
the layer runs end to end; what kept it open was follow-on work appended here. Three of the
four items recorded above are now resolved, and the way each resolved is worth stating because
two of them were recorded WRONG and only measurement found that out.

DONE INLINE: `T1` is resolved once at `ErrorLayer::resolve`, so renaming the payload parameter
in `effects.anthill` makes the layer `None` and `Error.reify` fails loudly as the body-less
declaration it is, instead of silently reverting every boundary in the program to catching
wide. The existing 21 rows are the drive — a `None` there fails all of them with
`OperationBodyMissing`.

FILED, NOT INLINE, after tracing showed the inline plan was wrong: WI-20260911-VNQTR. An
inline `?t` does not ride the type-argument channel in EITHER direction —
`set_resolved_type_args` is gated on the callee's declared brackets, and `op_own_params =
rec.type_params ++ inline_type_params` is a LOCAL in `check_operation_bodies` that never
reaches `OperationInfo`. So extending `op_own_param_ref_rewrite` to it would mint a
`Ref(?t)` nothing binds — a term that reads as a nominal sort where the skolem was visibly
wrong, which is the same "confidently wrong beats visibly wrong" hazard /code-review drove
against the first shape of the channel join. That is a feature, not a patch.

FILED: WI-20260911-3MV2C, the payload's type ARGUMENTS. Pre-existing and untouched by the
narrowing.

FILED AFTER BEING BUILT AND REVERTED: WI-20260911-0V0F7, the bridged raise. The producer took
an afternoon; the revert is the finding. Four consumers — `read_facts_resolved`,
`prove_from_gamma_verdict`, reflect's `split_first`, and the truncation path into the
load-blocking guards — were each written when faults were rare and specific, and a bridged
raise changes what every one of them does. Two of those changes can stop a working program.
NONE of it was visible to a green suite at 6851 passed / 0 failed.

THE METHODOLOGICAL FINDING, since it cost the most and will recur. The repro for that item was
wrong THREE times, and each wrong version presented identically as `no solutions`:
 1. "a DECLINED reify raise in a rule body" — refuted. `rule viaDeclinedClean(?r) :-
    declinedClean(?r)` answers `err(error: other(n: 7))` correctly. The first probe had hit a
    rule body calling an operation whose ROW IS NON-EMPTY, which residualizes for its own
    unrelated reason — and its CONTROL failed identically, which is the only reason it was
    caught.
 2. `guardExhaustible(0 - 5, ?r)` — the operand reaches the bridge UN-REDUCED, so the guard
    compares a `Node` against an `Int64` and the bridge answers `TypeMismatch { expected: "Ord
    scalars of matching type", got: "Node and Int64" }`. A different defect entirely.
 3. `guardExhaustible(0, ?r)` — a literal argument, which actually raises.
Only a probe inside `bridge_op_to_eval`'s `Err` arm separated them. Had it not been written,
version 2 would have shipped as the recorded measurement with a test passing green over a
defect that was never fixed.

TWO /code-review PASSES ON THE CHANNEL-CLOSURE COMMIT, and both found regressions the suite
could not: a hard refusal that made a generic `reify` in a rule body answer `no solutions`
silently; a short-name skolem join that captured an unrelated anonymous `?` slot; and catching
an unreadable payload at a NARROWED boundary, which let a nested inner boundary steal a label
the row had assigned to the outer. All three are fixed and pinned. Two header tallies that had
drifted were replaced by the named sets a back-out actually produces, re-measured.

WHAT REMAINS ON THIS TICKET: nothing of its own. The three open questions live on 3MV2C,
VNQTR and 0V0F7, each with its measured repro and the reason it is not inline work.

### 2026-10-15T14:49:07Z — feedback — claude

RE-MEASURED 2026-10-15 on ee3696eb, and wired to 3MV2C (user, 2026-10-15).

The build path holds: the 28 rows of wi_9wvt7_error_reify_test and wi_9wvt7_reify_typing_test pass. Since the note above, WI-20260921-28TAT replaced the frame type-argument channel with `requires ErrorTag[T = T1]` on `Error.reify`, so the paragraphs above about `None` catching wide, `collect_closed_type_args` and `op_own_param_ref_rewrite` describe code that is gone.

Each leftover, run today:
 * 3MV2C, the type-argument axis. A `Box[V = String]` raise under an inner `Error.reify[T1 = Box[V = Int64]]`, inside an outer `Error.reify[T1 = Box[V = String]]`, answers "inner-caught". Catching only what a boundary is typed at is this ticket's goal, so this ticket now depends on 3MV2C. That one waits on the continuum decision (point 2 or point 3) in 027.4.
 * A guarded raise in a callback. `Error.reify(lambda () -> a / b)` and `Error.reify(lambda () -> head(xs))` are refused at load: "the lambda argument declares `Error[T = DivisionByZero]`, which the closed row does not admit". So is any higher-order operation with `@ {Error[DivisionByZero], Rho}`, with `T1` written or not, and an eta'd operation whose row is `Error[DivisionByZero] :- eq(b, 0)`. The direct call under `effects {Error[DivisionByZero]}` loads, and so does a lambda over an unguarded wrapper. Kernel-language §5.5 keeps the label of a guard that is not refuted, so this is a conformance defect. To be fixed here.
 * VNQTR. Its channel is gone, and its program now shows a different gap: the refusal of forwarding a rigid into an operation that reads it misses an inline and a nested one. `midInline(y: ?t) = tyOf(y)` and `midNested[U](y: List[T = U]) = tyOf(y)` load and panic at run time (`DeferToRequirement: requirement param __req_typevalue not bound in caller frame`); `mid[U](y: U)` is refused. Not a part of this ticket.
 * M8QWJ's class, not parts of this ticket: `rule direct(?r) :- Error.reify(..., ?r)` answers no solutions; a user-declared layer's `reify` loads and dies "operation has no body".
 * Unchanged, no ticket: `Result` has no host type mapping; which delimiter wins between a registered `Error` handler and `reify`.
 * The guardians `LoadChecker.check` is still host Rust. Writing it in anthill needs two decisions about the example: it must read `Source`'s internal `text`, which only `guardians.Source`'s scope can, and the budget strings come from `type_display_name_value` in Rust.

### 2026-10-15T17:18:53Z — feedback — claude

GUARDED RAISES ARE CAUGHT (2026-10-15), after a /code-review at max effort that refuted the first shape of the fix.

`Error.reify(lambda () -> a / b)` returns `err(division_by_zero(op: "Int64.div"))` at `b = 0` and `ok(3)` at `7 / 2`; `Error.reify(lambda () -> head(xs))` returns `err(empty_stream)` on `nil`. Both were refused at load before (the entry above).

THREE REPAIRS, none specific to reify:
 (1) A function value's row is what applying it incurs. `make_arrow_value` (typing/result.rs; the row of a lambda and of an eta'd operation) wrapped every element in `present`, so a kept guarded atom became a label named `guarded(…)`, an absence a label named `-X`, and two atoms of one label (a dispatched `a / b` carries the spec operation's and the implementation's) stayed two. It now reads each element through `explode_incurred_effect_row`, as the operation boundary does, and builds a set. The same repair admits an eta'd or lambda-wrapped operation declaring `{ -Error }` into a closed slot, and `Apply.call(lambda (x) -> 10 / x)` against a provision at `@ {Error[DivisionByZero]}`; both were refused.
 (2) Paired rows are sets (`match_present_labels`, typing/effects.rs): a label that pairs with nothing but equals, under the bindings made so far, a paired label of its own row is that element. `Error.reify[T1 = DivisionByZero](zq)` over `zq[Q] effects {Error[Q], Error[DivisionByZero]}` now catches.
 (3) A guarded atom of a callback slot admits no callback label (`validate_callback_effect_row`, typing/args.rs; proposal 048's lattice, an undecided entailment refuses). Before, `runG(f: (x: Int64) -> Int64 @ {Error[DivisionByZero] :- eq(x, 0)}, b) effects {Error[DivisionByZero] :- eq(b, 0)}` took `lambda (x) -> 7 / k`, and any unguarded raiser, and `runG(…, 5)` was typed pure, so the raise escaped `main` (measured; the unguarded case on HEAD too). A callback that does meet the guard is refused as well.

THE FIRST SHAPE, REFUTED: placing the guarded atom bare in the value's row. Its guard names the callee's parameters, the multi-tail absorb copied the lambda's row into a row variable, and a later call to the same operation refuted the guard with its own arguments: `h(lambda () -> g() + k() + h(lambda () -> 1, 0), 5)` loaded and raised out of an operation declaring no Error. Four reviewers reproduced it, one with Γ holding `neq(x, 0)` for a guard that meant `x - 1`. The same shape made a stream's `-s.E` and `{s.E :- g}` refuse to distribute over such a row.

DRIVEN: `wi_9wvt7_guarded_callback_row_test` (13 rows, four fixtures). Back-outs measured from one build: (1) off fails 10 rows; the bare-atom shape fails 2 (the collision program, the provision); (2) off fails 1; (3) off fails 1; `a_raise_admitted_into_a_slot_is_not_lost` passes either way. Full workspace 9901 passed / 0 failed / 17 ignored; families green, also under ANTHILL_TEST_NODE_CARRIER=1; the 41 `wi_9wvt7` rows green under the node carrier.

VERDICTS THAT MOVED BESIDES THE TARGET: `run2[Rho](f: () -> Int64 @ {Rho}) -> Int64 effects {Rho, -Error[DivisionByZero]}` given a lambda dividing by a variable is refused with one tail or several, as its unguarded twin always was (with several it loaded before: the atom was opaque); a guarded slot's correct callback (`lambda (x) -> 35 / x` at `eq(x, 0)`) is refused.

FOUND AND NOT FIXED, each pre-existing (same verdict on HEAD):
 * The greedy pairing binds `T1` to whichever `Error` label of a two-label body comes first, so swapping `if` branches flips a reify verdict; `[T1 = …]` is the workaround. A design question: which label an unwritten `T1` is.
 * An operation declaring a guarded row variable (`{Rho :- eq(b, 0)}`) is refused when called directly ("undeclared effect: ?R"); resolving the kept atom through the call's σ did not fix it (tried and reverted).
 * `run5[Rho = {Error[DivisionByZero]}]` into `@ {Rho, -Error}` loads: the self-contradiction check compares a bare `-Error` with `Error[DivisionByZero]` by equality, the tail-binding check by unification. What a bare lacks constraint means for an ordinary label is left open in permission_entails' doc.
 * The entry above put a rule body's `Error.reify(…, ?r)` (no solutions) in M8QWJ's class. It is not: reify is implemented. It is a rule-body evaluation gap with no ticket.

### 2026-10-15T17:32:45Z — feedback — claude

FILED (user, 2026-10-15) for the three pre-existing items the entry above lists as found and not fixed: WI-20261015-D2KZ5 (which `Error` label an unwritten `T1` is when the body raises two), WI-20261015-HCQVS (a guarded row variable refused at a direct call), WI-20261015-CZWFF (a bare `-Error` against an explicitly written `Rho`). None is a dependency of this ticket.

### 2026-10-15T18:05:02Z — feedback — claude

A RULE BODY'S `Error.reify` CATCHES (2026-10-15, user: implement now, file the general face as a 068 ticket). `rule direct(?r) :- Error.reify(lambda () -> mayFail(0 - 1), ?r)` answers `?r = err(error: boom(why: "negative"))` where it answered no solutions; the `ok` arm, and a thunk whose captured variable the caller binds, answer too. This closes 027.4's open question "Error.reify works only from an OPERATION BODY", for a lambda thunk.

FOUR CHANGES, each measured with a temporary switch:
 (a) THE RESOLVER (kb/resolve.rs). WI-938's functional-relation view reads `f(a₁…aₙ, ?r)` as `unify(?r, f(a₁…aₙ))` only for an operation the bridge can run, and a parametric effect row only for a bodied one; `bridge_runs_anthill_code` now answers yes for `Error.reify`, whose thunk is what the bridge runs. The value-slot reduction needed nothing: its body-less arm already bridges a clause-less `Error.reify` (an arm added for it was dead, and with a clause written under `Error.reify` it gave one call two opposite answers; removed after review).
 (b) THE BRIDGE'S HOST ENTRY (eval). `Interpreter::invoke_reify_boundary` installs the boundary as the two in-body faces do: the one frame the run owns is the boundary, and entering the thunk is the run's first step (`run_from`), so a raise there meets it as any later raise does. The `ErrorTag` evidence is the one the typer stamped on the call. Top-level bookkeeping is shared with `invoke_op_with_requirements` (`begin_host_entry` / `end_host_entry`).
 (c) THE FAULT NAMES THE BOUNDARY: a declined payload reads "The boundary catches the payload it is typed at, which this is not" instead of advising a `reify`.
 (d) A PAYLOAD TYPE THE CALL LEAVES OPEN IS REFUSED AT LOAD (user, 2026-10-15). With no `ErrorTag` evidence the boundary caught every payload: over `raiseEither[P](p: P, n: Int64) effects {Error[P], Error[Other]}`, `either(boom("b"), 7, ?r)` answered `err(other(n: 7))` definitely. A rule declares no `requires`, so until 060's S7 threads the evidence (the test it owes is a note on WI-20260911-5G28A) the typer refuses the call (`build_op_scoped_dicts`'s rule-body reify gate). The one-label shape and a thunk bound by another goal are refused with it. Spec: kernel-language.md, the arity+1 view and the marker exemption.

DRIVEN: `wi_9wvt7_reify_rule_body_test` (8 rows). Back-outs from one build: (a) fails 4, (b) 4, (b)'s first step 1, (c) 1, (d) 1; the repairs row and the operation-body twin pass either way. Full workspace 9909 passed / 0 failed / 17 ignored; families green, the callback family under the node carrier too. The bridge's stack canary (`eval_undecidable_instance_fact_eq_is_loud_not_false`) re-measured under RUST_MIN_STACK: opt-level 0 overflows at 1 MiB and passes at 1.5 MiB, opt-level 2 overflows at 384 KiB and passes at 512 KiB — the brackets `BRIDGE_REENTRY_CAP` records, unchanged.

REVIEWED (/code-review max, 2026-10-15): fixed in this change — the dead reduce arm, one predicate and one `Raised` arm, the reify symbol cached on the KB, the shared host-entry bookkeeping, the entering step, the test controls, the comments, the spec. Pre-existing, found by the review and not fixed here, each with the same verdict before through an ordinary higher-order call: a host-implemented `Clock` read runs during rule evaluation; a `KB.loaded` layer outlives a bridged run; a tuple or set literal captured by a rule-body lambda panics a debug build; a function value reaching a clause through its head (a rule parameter, a `|` / `&` branch) drops the match silently; a lambda in a constraint guard keeps the parser's pattern marker; the bridge runs uncapped; a typed rule head does not choose `T1` (D2KZ5); `?f <=> lambda () -> body` parses as a function type.

THE GENERAL VERSION is filed: WI-20261015-ZPETZ (proposal-068), one dispatch for the host entry and the in-body faces.

### 2026-10-15T20:59:11Z — feedback — claude

FIXED INLINE (2026-10-15, the plan the user approved): a tuple or set literal a rule-body lambda captures through a rule variable. `rule h(?e, ?r) :- callIt(lambda () -> okIt(?e), ?r)` evaluated as `h((1, 2), ?r)` panicked a debug build ("unhandled Expr variant in eval: Discriminant(13)", the `debug_assert` in `bridge_op_to_eval`) and faulted a release one: the binding is spliced into the lambda when the call is evaluated, and reached the evaluator as `Expr::TupleLit`, which only the typer reads as a constructor. The evaluator now reads a spliced `TupleLit` / `SetLit` / `ListLit` as that constructor and builds it by the arm the typed one takes (`start_literal_constructor`), so `h((1, 2), ?r)` answers `(1, 2)`, a fact-held tuple and a tuple inside an entity answer too, and a spliced set is the `SetLiteral` value an operation body builds from the same literal. Rows: `wi_9wvt7_spliced_literal_test` (4); the literal arm backed out fails 3, the controls pass either way. Full workspace 9913 passed / 0 failed / 17 ignored; the stack canary unchanged at opt-level 0 and 2.

### 2026-10-15T21:10:19Z — feedback — claude

FIXED INLINE (2026-10-15, the plan the user approved): a scoped KB (`KB.loaded`) made by a rule-body call stayed applied to the resolver's KB after the call. A bridged call runs against the resolver's own KB, lent to a scratch interpreter, and a scoped load is applied to it in place until its last holder goes; a call that answered a value still holding one handed the KB back with the layer applied, so `loads(?r), Seen(n: ?n)` answered the loaded `42` beside the base's `1`, the goals swapped answered only `1`, and a failed clause's or a failed negation's layer survived the backtrack (the operation-wrapper spelling did the same before 9WVT7). `Interpreter::release_layers_for_handback`, called by `run_in_bridge_interp` before the KB goes back, discards every layer the run made and refuses an answer that still holds one (`EvalError::ScopedKbOutlivesCall`, a fault naming the repair: read what the scoped KB answers inside the call and return that — driven, `countInside` answers 2 and the later goal the base's 1). Rows: `wi_9wvt7_bridged_scoped_kb_test` (3); the handback backed out fails 2, the repair row passes either way. Full workspace 9916 passed / 0 failed / 17 ignored; the stack canary unchanged at opt-level 0 and 2.

### 2026-10-15T21:17:18Z — feedback — claude

FIXED INLINE (2026-10-15, the plan the user approved): a `Clock` read in a rule body was performed. `Time.now` read the wall clock itself, asking no handler, so the SLD→eval bridge's empty effect registry did not stop it: `applyThunk(lambda () -> now(), ?r)`, `List.mapElems` with a clock callback, a bodied `{Clock}` operation in a value slot and a rule-body `Error.reify` of a clock-reading thunk each answered a definite timestamp, a different one at each query. `Time.now` now reads `Clock` through the handler the runtime registers (`effects::system_clock_handler`, in `register_standard_effect_handlers`, which `anthill run`, anthill-todo and a generated bundle call), as the `Console` operations read theirs; a rule body cannot read it and the goal is undecided, and an interpreter with no `Clock` handler refuses the read loudly (`UnhandledEffect`). Rows: `wi_9wvt7_clock_handler_test` (3); the direct read put back fails 2 (four definite timestamps; the frozen handler not asked), the direct-goal control passes either way; `time_now_test` registers the handler. Full workspace 9919 passed / 0 failed / 17 ignored.

### 2026-10-16T00:47:26Z — feedback — claude

SECOND REVIEW FIXED (/code-review max over 47765477..894a8855, 2026-10-16, 15 findings; the user asked for the review). In the change:
 * A SPLICED LITERAL IS DELIVERED AS THE VALUE THE RULE HOLDS (068 §1.2), not built again. The first repair (the 20:59 note) built a tuple with no functor, a set with its duplicates dropped and a cons spine for a by-name `ListLiteral`, none unifying with the rule's literal, so `holder(p: ?p), not(roundTrips(?p))` proved a falsehood definitely. `wi_9wvt7_spliced_literal_test` (4 rows): building put back fails 2, `Internal` put back 3.
 * THE `ErrorTag` REFUSAL IS KEYED ON THE SLOT, not on the payload type's groundness or on the callee. `eitherNil(7, ?r)` (`nil()` for `?p`, an open element) and a tuple payload beside `Error[Other]` answered `err(other(n: 7))` definitely; they, a pure thunk and an operation named bare are refused at load, with a text naming each repair. A generic operation reifying at its own `P` cited from a rule (`catchAll`) has its slot filled from argument values when it runs, and an unpinned one is now an absence the boundary's read refuses (`UnpinnedRequirement`) where it answered `err(other(n: 7))`. A host's `Interpreter::call` of `Error.reify` with an operation reference is refused the same way, since an `OpRef` views as the sort `OpRef`, not as its arrow, so no public route reaches a raise as the thunk is entered; the first step's other error path, the run truncated to its floor, is driven.
 * A raise out of `Error.reify` is a fault whatever its payload, a declined `load_failed` too.
 * THE HANDBACK lets the scratch interpreter's const cache go first, so a const holding a scoped KB, read by a call answering an Int64, answers (2, and 201 for the goal after it, where it was refused); a raise whose payload holds a layer is refused naming the raise; the message states the limit (each application in a run of its own, arguments first) and both repairs, which are driven.
 * THE TRAMPOLINE: the loop state is the last step's answer, `run()` seeds `Continue`, and `invoke_reify_boundary` borrows its requirements. The review's loopEq probe (the CLI under ulimit) needs 1572 KiB before rule-body reify, 1588 on the reviewed tree and 1580 now. The canary brackets are unchanged: opt-level 0 (1.0, 1.5] MiB, minimum (1488, 1496] KiB; opt-level 2 (384, 512] KiB, minimum (496, 504] KiB.
 * LEDGERS MEASURED, nine switches in one build: (a) fails 5 rows of the reify file plus the clock and scoped-KB rows that go through a rule-body reify; (b) 5 plus 1; (b)'s first step 1; (c) 1; (d)'s load refusal 1 (alone, the bridge absence then faults the call when it runs); (d)'s bridge absence 2; the handback 4; the const cache 1; the raise arm 1. The 18:05 note's "the repairs row and the operation-body twin pass either way" was wrong: the repairs row fails under (a) and (b). The twin row is removed (its twin is `viaPlainRule` in `wi_9wvt7_error_reify_test`), and so is the clock file's direct-goal row, which passed for any cause that empties the relation.
 * DOCS: the spec (the arity+1 sentence, the `ErrorTag` exception, the structural-former exemption), the stdlib reify comment, the anthill-stl header, 027.4 (the rule-body paragraph, the thunk's other effects, the handler and site counts), comments. Five notes relabelled `claude`.
Rows: reify_rule_body 8, bridged_scoped_kb 5, clock_handler 2, spliced_literal 4. Full workspace 9920 passed / 0 failed / 17 ignored; families green, family c under the node carrier too.
OPEN, put to the user: `time_now` as a `const_map` value source fails at load with an internal error; `Cell.set`, `Store`'s writers and `Forge` perform their effects in a rule body; a clause under `Error.reify` or a host-mapped operation takes the goal over; a clock read in a rule body is undecided with nothing said; and (pre-existing) an operation-body boundary at a tuple payload catches a label its row leaves to the caller.

### 2026-10-16T05:13:13Z — feedback — claude

DECISIONS 1 AND 2 DELIVERED (user, 2026-10-16: "Ok, let do a'", "Agree with b on 2").
 (1, a') A REIFY AT A TUPLE PAYLOAD IS REFUSED AT THE CALL, as a requirement at any structural former is (065's open question 3): `former_carrier`'s body-less exemption is gone. It let `Error.reify` catch WIDE where it had no evidence, on the reading that the row guarantees what it may catch; measured false: an operation-body boundary at a tuple beside `Error[Other]` caught `other(n: 7)` as the tuple's `err`, past a boundary at `Other` around it, the same on the binary before 9WVT7. Why it could not be narrowed: `ErrorTag[T = (…)]`'s one provision is `Error provides ErrorTag[T = T] :- TypeValue[T = T]`, and `TypeValue` is derived for sorts only (065 §7 step 2's formers, deferred 2026-09-20 on WI-20260919-HXGXF); and the boundary narrows by sort, which a tuple has none of.
 RUNNING THE REFUSAL'S ADVISED REPAIR — a sort's `provides ErrorTag[T = (…)]` — loaded and caught wide again, the row carrying no `TypeValue`. So the boundary refuses evidence that names no payload sort (`EvalError::ReifyPayloadUnread`: no `ErrorTag` slot, as from `call_with_requirements`, or a dictionary with no `TypeValue` sub), `ReifyBoundary.payload` is a `Symbol`, and no boundary catches wide. The former refusal names the row as its repair only where a row works: for `TypeValue` (none may be written, measured `HandWrittenTypeValue`) and `ErrorTag` it names a value of a sort.
 Rows: `wi_n31xx_type_value_read_rule_test::a_body_less_callee_is_held_to_the_former_refusal` (the exemption's control, inverted), `a_requirement_at_a_former_is_refused_rather_than_aborting` (both repairs), `wi_9wvt7_error_reify_test::evidence_that_names_no_payload_sort_is_refused` (the written row, the host entry), `a_narrowed_boundary_does_not_steal_an_unreadable_payload` (the tuple leaves the call as its raise); `a_payload_the_runtime_cannot_narrow_is_still_caught` is removed with the shared fixture's tuple boundaries. Back-outs in one build: the guard put back fails 1; the wide catch put back fails 1 (both halves answer, `err(other(n: 7))` and `ok`); the generic repair text fails 2.
 (2, b) A `time_now` CONST IN A DATA SLOT IS REFUSED NAMING `Clock`. `const_slot_value` asks the operation mappings which operation a host value source backs and refuses one with an effect other than `Error`: "is `anthill.prelude.Time.now`'s host function, which performs `Clock`, and a load performs no effect", where the scratch run said "internal evaluator error: anthill.prelude.Time.now not in scope". An operation body still reads the const through the handler. Rows: `wi_9wvt7_clock_handler_test::a_clock_const_in_a_data_slot_is_refused_naming_clock` (fails with `host_source_effect` taken out), `a_clock_const_in_an_operation_body_reads_the_handler` (passes either way).
 Docs: kernel-language.md (the structural-former exemption withdrawn, the repair per spec, the `ErrorTag` paragraph, the data-slot table), the stdlib reify comment, 027.4 (the wide catch superseded), 065 (the exemption withdrawn).
 Full workspace 9922 passed / 0 failed / 17 ignored; families green, no verdict moved; family c under the node carrier too.
 Still open, put to the user: 3 (`Cell.set`, `Store`'s writers and `Forge` perform their effects in a rule body), 4 (a clause under `Error.reify` takes the goal over), 5 (a clock read in a rule body is undecided with nothing said).

### 2026-10-16T07:12:34Z — feedback — claude

DECISION 3 (user, 2026-10-16): `Cell.set`, a store's writer and anthill-todo's `Forge` perform their effects in a rule body — declined AT THE BOUNDARY, by the application's typed row, strict (`Modify[result]` counts); added as a row on WI-20260926-7D48J, whose clause typing computes that row ("1 - add to 7D48J"). Tried first at the host function — a bridged run registered each host function whose operation declares an effect other than `Error` as the refusal of an unhandled effect — and backed out: it also refused `localCell(3, ?r)`, an operation whose cell never leaves it (WI-314 masks the `Modify`), which answers `9`; the full gate was green on it. Kept from the try: `HostOperationMapping::performs` and `typing::declared_effect_other_than_error`, now read by decision 2's const refusal instead of a walk of its own. 027.4 and 068 §5 say where the decline lives. Still open, put to the user: 4 (a clause under `Error.reify` takes the goal over), 5 (a clock read in a rule body is undecided with nothing said).

### 2026-10-16T09:06:26Z — feedback — claude

DECISION 4 DELIVERED (user, 2026-10-16, "ok, lets (a)"): A CLAUSE AT THE ARITY + 1 OF A HOST-IMPLEMENTED OPERATION, OR OF `Error.reify`, IS REFUSED AT LOAD, as one at a bodied operation's was (WI-939 item 4's one-definition check, `check_operation_body_and_clauses`). The functional-relation view reads a goal at that arity as the call for every operation the bridge runs — a body, a host function of this runtime, the reify boundary — and the check walked bodies only, so a clause beside the other two loaded clean and answered the rule-body goal alone: MEASURED, `rule String.length(?s, 99) :- true` made `String.length("abc", ?n)` answer `99` beside `?n <=> String.length("abc")` and an operation body answering `3`; `rule Error.reify(?f, ok(0)) :- true` made `Error.reify(lambda () -> mayFail(0 - 1), ?r)` answer no solutions and its value-slot form undecided, the operation body still catching `err(boom(…))`. The population now adds every interpreter-mapped operation without a body that is not a resolver builtin (whose clauses are alternatives, WI-899) and `Error.reify`, at arity + 1 only; `LoadError::OperationBodyAndClauses` carries which definition the clauses meet (`OperationDefinition::{Body, HostFunction, Boundary}`) and an optional declaration site (a library operation's is in its own load's ledger), and the refusal says the repair: delete the clauses, give a relation of your own a name of its own. Rows (wi939_one_definition_test): `a_clause_beside_a_host_operation_is_refused`, `a_clause_beside_error_reify_is_refused` — the population restricted to bodies again fails exactly those 2 — and `a_clause_at_a_host_operations_own_arity_is_another_relation`, either way by design (an own-arity clause loads, and an arity + 1 goal beside it is refused for its arity, loudly). Spec: kernel-language.md's one-definition paragraph, and the body-less bullet narrowed to an operation with no host function and no boundary. Corpus cost zero: full workspace 9925 passed / 0 failed / 17 ignored; families green. Still open, put to the user: 5 (a clock read in a rule body is undecided with nothing said).

### 2026-10-16T09:28:25Z — feedback — claude

DECISION 5 DELIVERED (user, 2026-10-16, "ok, led so (a)"): A DECLINED EFFECT IS REPORTED. An effect a rule-body call reaches — a `Clock` read, a print — stops the operation asking its handler (the scratch interpreter's registry is empty), and the bridge SCHEDULED that, so the goal was a bare residual with nothing said and a relation drained from an operation body died `relation_floundered(goals: …)`, which reads as an unbound variable. `EvalError::UnhandledEffect` is a fault now: the goal still delays, and the search records "`test.d5.applyThunk` could not be evaluated by the resolver: it performs `anthill.prelude.Time.Clock`, and a rule body performs no effect" and is marked incomplete; the drain fails with `evaluation_failure(…, reason: …)` naming it. The disposition's old note ("calling that a fault would make a program that loads today stop loading") was MEASURED stale: the full workspace is green with it (9925 / 0 / 17). Rows: `wi_9wvt7_clock_handler_test::a_declined_clock_read_is_reported` (four routes), `a_drained_relation_names_the_declined_effect`, and `wi_9wvt7_reify_rule_body_test::an_effectful_thunk_leaves_the_goal_undecided` (names `ConsoleOutput`); with the effect scheduled again those 3 fail. Spec: §5.3's fault paragraph; 068 §5. The end state is a load error for a typed call, added to the WI-20260926-7D48J row (user, 2026-10-16: "finally it should be a compile-time error?"); run time keeps this report for what no typer sees. All five of the second review's decisions are now taken.

### 2026-10-16T12:45:16Z — feedback — claude

THIRD REVIEW (`/code-review max` on 7ef96a6d, 15 findings) — THE FIX PASS, before the user's answers on F1, F2 and F10.
F3 + F9 + F15, THE CONST REFUSAL DEPENDED ON LOAD ORDER: it read the operation's declared effect off the host mappings, which `build_host_op_mappings` builds after a load's clauses convert, so a one-call load (and a program handed in before the stdlib) still read "internal evaluator error: anthill.prelude.Time.now not in scope". The cause was the dispatcher: `time_now` asked for its operation's symbol before its handler, and the scratch interpreter a load runs a `const_map` source on has an empty KB. It takes the handler first now (`Interpreter::dispatch_effect_operation`), so the run itself names the effect (`EvalError::UnhandledEffect` -> `ConstUnavailableWhy::HostPerformsEffect { key, effect }`), whatever order the files load in, and the arity check runs before it as it did (F9). `HostOperationMapping::performs`, `typing::declared_effect_other_than_error` and its walk at every load (F15) are gone; `UnhandledEffect` carries the name alone. A const whose source is a pure host function now loads even when an operation mapping that function declares an effect (`fakePi() effects Spooky` -> `float_pi`): the const reads the host function, not the operation. Row: `a_clock_const_in_a_data_slot_is_refused_naming_clock_ahead_of_the_stdlib` (pinned in `wi_rah0z_one_recipe_test`).
F4: a clause at a host `Bool` operation's OWN arity is refused as a bodied one's is — MEASURED, `rule String.contains("abc", "z") :- true` made that goal hold where the call answers `false`, and `String.contains("abc", "b")` stop holding (row `a_clause_at_a_host_bool_operations_own_arity_is_refused`; `LoadError::OperationBodyAndClauses.bool_view`). F8: the refusal's reason is the one-definition rule, which holds whether or not a view reads the goal (an effectful host operation has none), and it names the slot. F11: the wi939 rows assert tokens that hold with or without a declaration site.
F5: a `TypeValue` or `ErrorTag` requirement at a sort holding a former (`Option[T = (a: Int64, b: String)]`) is refused as one at the former, naming a value of a sort; it advised a written `TypeValue` row (refused at load) and an `ErrorTag` row (never read). The deep "no impl provides TypeValue" hint names no written row either. Rows: `a_library_spec_at_a_former_inside_a_sort_is_refused_naming_a_value`, `the_advised_value_of_a_sort_is_caught`, `control_a_users_spec_at_a_former_inside_a_sort_keeps_the_row_advice`.
F7: a drained relation's `evaluation_failure` reaching a rule carries its fault's own sentence and no `Error.reify` advice (row `a_drain_reached_from_a_rule_names_the_effect_and_no_reify`).
F12-F14: the three headers re-measured with every back-out switched off alone in one build (wi939: the whole check 5 fail, the population restricted to bodies 3, the `Bool` slot for bodies only 1; the clock file: the old direct clock read fails every reading row, so the op-body const row passes under all but that one; reify-rule-body: (b) also fails the effectful-thunk row, and with (d)'s halves off the call is undecided, not `err(other(n: 7))`); the stale catch-wide texts (the rule-body refusal, two eval comments, the `UnhandledEffect` doc, spec §6553's first sentence); spec text (no bold in new text, the measured 2975 rephrased as the rule, "the call is not run", the carrier-shaped sentence, the const row); the stdlib reify comment; 068 §5 and 027.4 for 7D48J's amended rule.
INCIDENTAL, fixed: `register_standard_effect_handlers` registered `Modify` by its short name, which resolves to nothing, so `ModifyRuntime.set` on a cell died "no handler registered for effect `anthill.prelude.Modify`" under `anthill run` since the first evaluator commit (row `wi205_cell_test::the_standard_handlers_answer_modify_runtime_on_a_cell`). `reflect.anthill`'s "NOT YET ENFORCED" sentence about written `TypeValue` rows was stale.
Full workspace 9934 passed / 0 failed / 17 ignored; the touched files green under FRESH_LOAD, TWO_STEP and the node carrier; families green.

### 2026-10-16T15:02:04Z — feedback — claude

THIRD REVIEW, THE OPEN FINDINGS DECIDED (user, 2026-10-16).
F2 — KEPT (a): a declined effect is a fault, and a fault marks the WHOLE search incomplete from the moment the goal is first tried, a branch a later goal refutes included, as a raise already does. CORRECTION to the 09:28 note: "calling that a fault would make a program that loads today stop loading" was NOT stale — MEASURED, `constraint c_effect_first: no ?n: rec(n: ?n) -: effectFirst(?n)` over `effectFirst(?n) :- rec(n: ?n), applyThunk(lambda () -> now(), ?s), ?n > 100` does not load ("undecidable within the resolver depth budget"), where its `testFirst` twin (`?n > 100` first) does. Pinned in `wi_9wvt7_clock_handler_test`: `a_branch_refuted_after_a_declined_effect_is_incomplete`, `a_negation_over_a_declined_effect_is_conditional`, `a_drain_over_a_refuted_branch_fails_naming_the_effect`, `a_constraint_over_a_declined_effect_does_not_load`, each with its `testFirst` control; the decline scheduled again fails all four. Spec §5.3's fault paragraph says so; the disposition's comment too.
F10 — FOR NOW, A CORRECT DIAGNOSTIC: `localMod` (a cell it keeps to itself, written through `ModifyRuntime`) has a pure row, but its write asks the `Modify` handler and a rule body's run has none. It stays declined; the report says "its row declares no `anthill.prelude.Modify`, yet running it asks the `anthill.prelude.Modify` handler" where it said "it performs" (`typing::declared_row_may_hold`). Row: `wi205_cell_test::a_rule_body_declines_modify_runtime_on_a_callees_own_cell_naming_its_row`; the row check backed out fails exactly it. The user's direction for later: every `Modify` goes through `ModifyRuntime` (`Cell.set` included), so an implementation such as time travel can intercept it, and the typer's masking of a local cell gets a run-time counterpart — not filed yet.
F1 — MOVES TO PROPOSAL 071 (`docs/proposals/071-type-patterns.md`): `ErrorTag` is retired at stage (c), WI-20261016-YM8HD, and the written row with it. Stages filed: Y1EZJ (a), SQZPQ (b), YM8HD (c), 5CDN5 (d, delivers WI-20260911-3MV2C), BDVYW (e), tagged `proposal-071`.

### 2026-10-16T17:56:11Z — feedback — claude

CORRECTION to the third review's note (INCIDENTAL, fixed): the short-name `Modify` entry did not fail since the first evaluator commit. It resolved when it was written (69392726, 2026-04-20) and stopped resolving at efdd989a (2026-05-10), when `effects.anthill` moved into `namespace anthill.prelude`; `ModifyRuntime` itself came at be5bb1d8 (2026-06-04), so `ModifyRuntime.set` under `anthill run` died from then on. Found by the fourth review.

### 2026-10-17T08:04:06Z — feedback — claude

NEXT SESSION (user, 2026-10-17, from the fifth review's contract-only finding): `TypeValue.type_value` ALWAYS takes its type-argument. A `requires` states what an operation needs and has no say in what a call returns, so `TypeValue.type_value[X]()` answers `X`, and `TypeValue.type_value()` with none is refused at load: no clause in scope stands in for the type-argument, not the operation's, not the sort's, not a contract inherited from a provided spec. A `requires` only supplies the evidence: `type_value[B]()` under `requires TypeValue[T = B]` takes that slot; `type_value[Option[T = E]]()` under `requires TypeValue[T = E]` builds `Option`'s derived instance over it; a ground type-argument needs none; one nothing can supply is refused at load as a call is. Proposal 065 §8 already spells it `type_value[T = B]()`; the value read of a rigid (`B` in value position, lowered to the slot dispatch) is sugar for the written call and stays. MEASURED on the tree after the fifth review's fixes: (1) the named bracket loads and is IGNORED — inside `sort W { sort E = ?  requires TypeValue[T = E]  provides Desc[T = Option[T = E]]  operation d() -> Type = TypeValue.type_value[T = Option[T = E]]() }`, `dOf(some(1))` answered `W(E: Int64)`, the running dispatch's provider, silently (`type_value_of_self` reads `builtin_dispatch_dict` and nothing else); in a free operation the same call panics 'no dispatching dictionary' through a rule body; (2) the positional `type_value[Option[T = E]]()` is refused, 'expected at most 0 positional type argument(s), got 1 — the callee is over-applied'; (3) `type_value()` with only `Desc requires TypeValue[T = T]` in reach loads and panics (the contract is checked at the provision and is not in the member's frame). POPULATION: about 12 `TypeValue.type_value()` calls in tests (wi_hxgxf, wi_n31xx, wi_xsvcs, wi_9wvt7_review5) and the stdlib's reflect doc text; `elaborate.rs` (`type_value_slot`'s doc) still says the bracket 'is refused today'. OPEN QUESTION for the user: does the same principle retire the spec's 'a receiver-less member of a spec, called where the enclosing scope has exactly one `requires` clause over that spec and the call pins none of the spec's parameters, runs at that clause's bindings' for EVERY spec (`Stamp.stamp()` under `requires Stamp[T = A]` → `Stamp.stamp[T = A]()`), or only for `TypeValue.type_value`?

### 2026-10-17T11:48:28Z — feedback — claude

SIXTH REVIEW (2026-10-17): the /code-review of b437fdbb (max effort) reported 15; all are fixed, four by the user's decisions that day. Rows: tests/include/wi_9wvt7_review6_test.rs.
* The contract walk through a program's own specs (the fifth review's F14) kept a list of the goals it had asked, so a contract asking for a spec again at a larger type (`Desc2 requires Desc2[T = List[T = T]]`, or two specs asking for each other at growing types) never ended: the load overflowed its thread's stack, or ran past 2 GB. It reads the spec's transitive chain now, a spec on a path once, as the scope cover reads a requirement.
* Which provision a call gets: one order on the heads replaces the fifth review's count of what a head reached through the subtype relation. A head is more specific than another where the other's provision answers at it and its own does not answer at the other's. Incomparable heads tie (provisions at `Tri[A = Dog, B = Animal, C = Animal]` and `Tri[A = Animal, B = Dog, C = Dog]` were a silent pick at a `Tri` of dogs, and so were two `Duo`s), a chain is ranked (`Being` and `Animal` at a `Dog` were a tie), a variant ranks above its sort in both spellings. A default arbitrates only among the tied most specific; it was handed every candidate and answered over two more specific providers. Locality is read by the half of the dictionary a sub-goal fills: in the spec half a provider's own row wins wherever it answers (`AscW`'s bundled `POrd` used at a `Dog` was `Dog`'s: a silent 20 for 10), in the provider half only where no candidate is more specific. Spec §8.7.
* The bottom type meets a provision at every head, an application, a tuple and an arrow as a bare sort: a rival written `Stamp[T = Box[V = V]]`, at a tuple or at an arrow was never met, and `Leaf` answered in silence. A provision whose conditions ask about a head parameter `Nothing` leaves open is no candidate there. An arrow's parameter is met as itself and its result through the subtype relation: callbacks at `(Dog) -> Int64` and `(Nothing) -> Int64` met a provision at `(Animal) -> Int64`, loaded and died. Spec §5.2 and §8.7.
* The runtime's accounts (user: the constructor is the mark): `relation_floundered`, `load_failed` and `evaluation_failure` are the runtime's wherever they are raised; a program matches one and raises a caught one again, and a construction of one is refused at load, by the typer in operation-body text and by the loader in a clause's own term. The per-interpreter table of the runtime's raises is gone: it was lost between two goals of one rule, never cleared, and scanned twice per raise. Spec §5.3.
* `ModifyRuntime.get` and `set` (user: refuse the place itself): the place must be of a modifiable type, a `Cell`, a sort that provides `Modifiable` or provides one that does, a variant of one, or a type parameter. An empty `List[T = Cell]` (every `nil` was one slot: 42 written through one empty list, read back through another), a tuple with a `Cell` part, a function value returning one and an entity with a `Cell` field are refused. The advice names a `Cell` first, and `Modifiable` only for a sort whose constructors take no fields; the region sorts are remembered by the provider index instead of computed per call. Spec §5.6.
* The induction axiom's name (user: refuse operations and rules): an operation or a rule under `<Sort>.induction`, in the sort's own load or a later one, is refused naming where it is written; an entity, a const or a nested sort of that name loads. Spec §5.2.
* The forward's account: a parametric variant is read at its sort for the library's two specs only (for another spec the advised clause was one the scope cover never matches); the caller's evidence is read as a call reads it, through the contracts of its requirements; a part's missing instance is told by the goal it failed at. A structural former is the cause only where no provision answered at it and the scope cannot supply it, at a construction and at a call alike: a same-spec condition is told its condition, an untyped lambda's parameter is no parameter of the scope, and a former holding the scope's parameter is told the requirement slot only where some row could answer it. A cycle is told to drop a condition, not to pin the element or to declare a slot.
* Tests and code: the row-atom row drives its unregistered twin; the pasted clauses run; the fifth review's either-way list; `CallerRigidCarrier` is an enum of its two outcomes; one resolution of a spec at a type for `NonEq` and `TypeValue`; one phrase for an operation's clause slots; the comments that still said a callee that never reads the slot loads.
MEASURED: every fix switched off alone in one build, over the file and over the whole wi_tests binary, each moving only its own rows (the groundness reading also moves `typer_capability_matrix_test`'s call-site cell); the readings deleted rather than switched, against the tree before this review, where every row of the file fails. Full workspace 10029 passed / 0 failed / 17 ignored; families green on both carriers; anthill-core green under the fresh-load, two-step and node-carrier recipes and under the provision oracle on the shared base and two-step (9006 / 0 each).
NOT DONE HERE: the NEXT SESSION item, `TypeValue.type_value` always taking its type-argument, for every spec (user, 2026-10-17). OPEN: whether a dispatch through the subtype relation should read each position by its variance (a result position, a requirement covering another in one direction) — the user's call whether to file it. OBSERVED, not changed: `spec[C](s: Coll[T = C]) requires TypeValue[T = C] = tyOf(s)` is refused where some sort provides `Coll` and loads where none does, since `TypeValue` is derived for a sort that no sort provides.

### 2026-10-17T14:08:38Z — feedback — claude

`TypeValue.type_value` ALWAYS TAKES ITS TYPE-ARGUMENT, FOR EVERY SPEC (user, 2026-10-17: "Every spec"; "positional parameter is form of named"; "If we can infer parameters, we can not to write it. But if we can't infer - we should report error"). Rows: tests/include/wi_9wvt7_type_value_bracket_test.rs.
* A call of a member of a sort that may be provided, whose signature names nothing of that sort, names the instance it is at in its bracket. Where nothing at the call fixes a parameter of the sort (its bracket, its arguments, the type expected of its result) and no single provision answers it, the call is refused at load (`TypeError::CallNamesNoInstance`), the advice the bracket written as the caller writes it (the sole clause's bindings, else `P = …`). A `requires` in scope supplies the evidence for the instance a call names and no longer says which instance that is: the spec's "a receiver-less member … runs at that clause's bindings" is retired (§5.4), and `bind_sort_params_from_sole_enclosing_requirement` with it.
* `TypeValue.type_value[X]()` answers `X`: named or positional, at a ground type (no `requires` needed), at a parameter a `requires` covers, at a type built over such parameters. `type_value()` is refused, and so is a type-argument nothing supplies. The builtin builds its answer as the type written in value position is built, each parameter keyed by its name, so `type_value[T = Option[T = Int64]]()` equals `Option[T = Int64]`.
* A positional bracket entry takes the next parameter of the one list, the operation's own and then its sort's, that no key took. This supersedes B6QYA (2026-10-10) and WI-841's limit to the operation's own parameters: `probe[Int64]` answers, `conv[String, Bool]` gets its named twin's refusal (`call_bracket_scopes_split` and `positional_limit` are gone).
* No inference from a lone provider for such a call: with `Red` the only `Desc` provider, `pick(x: Box) requires Desc[T = x.E] = Desc.tag()` would have answered `Red` at a blue box. A sort nothing provides runs its own operation (`Map.empty`, `Error.reify`), and a sub-interface's forwarding row (`Mid provides Base[T = T]`) is no provider. A member whose argument, result or effect names the sort is inferred from the call as before.
* A defaulted member runs at the instance its bracket names (`carrier_the_call_binds`, a carrier source only where some sort provides the spec), with the operation's own `requires` in the instance's resolution. M8QWJ's repair names the bracket.
* Fixtures that relied on the one-clause reading now write the bracket: wi_r541x (the two-clauses row is the refusal, its `[T = Q]` twin answers), wi_nr6fj, wi_h20yy, wi_s8cbv, wi_gfs6a, wi_n31xx, wi_hxgxf, wi_xsvcs, wi_9wvt7_review5, wi_2kv4y, wi_0rp29 (two), wi_m8qwj, wi_4dyr6, nar1x, 5g28a, p7vp4, wi1093, wi_nx4fd, wi_jmmhq, wi841's positional rows. The stdlib's reflect docs say the rule.
MEASURED: nine back-outs, each switched off alone in one build over the new file and the whole wi_tests binary, each moving only the rows its header names. Full workspace 10070 passed / 0 failed / 17 ignored; families green on both carriers; anthill-core 9046 / 0 under the fresh-load, two-step and node-carrier recipes and under the provision oracle on the shared base and two-step.
OBSERVED, not changed here: an alias in value position is not its expansion (`PartialEq.eq(Option[T = Int64], IntOpt)` is false over `sort IntOpt = Option[T = Int64]`); the user agreed it denotes its expansion, next. `MissingRequiresForSpecOp` advises a `requires` "on the enclosing sort" for a free operation too.

### 2026-10-17T15:13:44Z — feedback — claude

AFTER STEP 3 (2026-10-17): the step's one hole, the alias read as a value, the one-term clause canon, and the missing-requires advice. Rows: tests/include/wi_9wvt7_value_position_alias_test.rs; wi_9wvt7_type_value_bracket_test::a_tuple_or_an_arrow_has_no_instance.
* `type_value` at a tuple or an arrow is refused at load, advising a sort in the bracket. The builtin's `@[host_implemented]` claim exempted the call from the refusal of an operation nobody implements at a carrier, so it loaded with no dictionary to hand it: MEASURED on 6e3ab20b, in `Box.d` entered through `Desc` it answered `Box` (the dictionary `d`'s frame was entered with, through the sibling channel), and in a free operation it faulted "no dispatching dictionary". A builtin whose answer is its instance's dictionary (`BuiltinTag::answers_from_its_dictionary`) is no implementation the host owes every carrier (`typing::host_implements`). The rule-body message and the `TypeValueOf` doc still said `type_value()`.
* A type alias written as a value is the type it stands for (user agreed, 2026-10-17): in an operation body — bare, through a chain, a `let`, a nested bracket, a dotted path, a `@[simp]` right-hand side, applied further with both bindings (`IntPair[B = String]`, `IntPair[String]`), a `?` slot left unwritten, the sort's own parameter read through its `TypeValue` clause, a tuple as a bracket's entry writes it — and in a clause's data slot and a query, so a fact holding `IntOpt` is found by a goal or a query writing `Option[T = Int64]`. Binding again what the alias fixes is refused, once (an operation's equation term and its occurrence both read it). A tuple's alias stays its name in a data slot, where a tuple written is a tuple of values; an alias naming the sort's parameter stays its name outside the sort, as in a type position. Before, the value was the alias's own name (`PartialEq.eq(IntOpt, Option[T = Int64])` false) and an applied alias was refused. Rewritten: `let t = BS` inside `sort Outer[S]` over `sort BS = Box[V = S]` reads `S` as a value, as `let t = Box[V = S]` always did, and takes `requires TypeValue[T = S]` (wi_hzvqa); `alias_written_name_test::a_rule_reads_the_type_and_no_alias` (a goal asking with `Money` asks for `Int64`).
* One term per type in a clause (user, 2026-10-17: positional and named are two inputs normalized to one term, their order included): a type application in a fact, a rule head, a rule body and a query binds a positional to its parameter and puts the arguments in canonical order, so `Pair[Int64, String]`, `Pair[A = Int64, B = String]` and `Pair[B = String, A = Int64]` are one term, as they are one value in an operation body. Spec §5.4's "two terms" sentence rewritten, §5.1's list has the value position. `wi_tcsgt…::a_positional_entry_in_a_clauses_term_is_stored_as_written` turned (now `…_is_the_named_one`). A part of WI-20260823-53W12, noted there.
* `MissingRequiresForSpecOp` says where the clause goes — on the calling operation, on it or its sort for a member, `requires(…)` in a rule's body — and is reported at `path:line:col`; it said "on enclosing sort" for a free operation too, at a byte range (`req_insertion::run`'s errors joined the load with no file).
MEASURED: the former refusal's back-out over the whole wi_tests binary moves only its row; the three alias/canon back-outs, each alone in one build over the new file and the whole wi_tests binary, move only the rows the file's header names. scaland: its loader records no aliases and no type-application canon, nothing to follow.

### 2026-10-17T18:35:36Z — feedback — claude

THE SEVENTH REVIEW (of be220580, 2026-10-17): 15 findings, 14 fixed, rows in tests/include/wi_9wvt7_review7_test.rs (each back-out measured alone over it and the whole wi_tests binary). (1) The runtime's accounts are constructed by no route: reflection's make_fn and replace_named_arg fault ('a functor a program may construct'), a query pattern and a data file (anthill.json/TOML) are refused, and a payload is an account only as an APPLICATION of its constructor — a bare constructor name raised is the program's (0V0F7's partition row now raises each account with its field). (2) A variant of a modifiable sort is a place of that sort for Modify too (region.rs is_modifiable_sort). (3) A direct call of a defaulted spec member at a pinned carrier that reaches a provision only through the subtype relation dispatches to it (TOrd.cmp(dog, dog) answers AscW's own cmp); only for another sort's provision and a carrier the goal pins (goal_pinned_carrier) — the first cut also fired on a sort answering for itself and on an abstract-spec value, and 26 cover/dispatch rows failed. (4) A requires in scope covers an arrow only where the two are one binding, parameters and result the same (§5.2); a provision still answers a result below its own. (5) get at an argument that names no place is refused at load, as set's is. (6) The bottom type meets a bare parametric head as the written one (open parameters noted). (7) A spec whose contract asks for itself at a larger type is refused at its declaration; the resolver answers it NoMatch and the provision check skips it, so the load ends. (8) Ranking reads each provider parameter as one rigid minted once (KB.ranking_rigids), decodes each head once per ranking, and computes the tie once: the run-time dispatch interns nothing per firing; an 800-provision tie at Nothing costs a third. (9) An arrow nested in a parameter is matched back once, with its enclosing parameter (MatchAt::InParameter): depth 22 was 60 s, now flat. (11) A failure forwarded from beneath a provision names the condition ('a provision answers it, but X beneath it does not hold'), at a call and a construction alike; a construction is told no requirement slot where no caller can say the requirement, and a ground goal no 'requires' in scope (wi1102's row updated). (12) A cycle is told only to drop a condition. (13) An entity with fields named induction is refused (user), and an equation under the axiom's name, tagged or not, again (spec §5.2 sentence added). (14) review6's rows drive what they claim (arrow row with Nothing imported and the deep List case; advised repairs run). (15) §8.7: a provider's own row is local where no candidate is more specific, in both halves (user) — review6's bundled-witness row moved to review7 at 20. SKIPPED (10): a rule-body tie at Nothing panics a debug build — a row on WI-20260923-KCNA0, with the operation-body no-provider twin found beside it. Gate 10098/0; fresh and two-step 9074/0; provision oracle on both 9074/0; node carrier 10098/0; families both carriers ok.

### 2026-10-17T19:44:57Z — feedback — claude

A CONSTRUCTOR'S QUALIFIED NAME IS THE REFERENCE ITS ONE-SEGMENT NAME IS (user, 2026-10-17: 'holds(red) should work the same as plain(red), it should be no difference between reference to red as qualified name or as name, which should be reference to symbol'). Found while writing the seventh review's rows: `Colour.red` and `Colour.method.sketch` written without `()` parse as a field_access chain (§6.7), which was kept as written — in a fact a term of its own that `holds(red)` did not find (`holds(?x)` answered the chain `Colour.red`, whose last segment is an unresolved identifier), in a rule body's `=` a load error naming 'a defect in the walk that built this occurrence', and in an operation body a refusal ('field_access.field: expected String, got Colour', or past a nested sort 'sketch.name: expected resolved name'). Now each walk reads a dotted chain that names an entity constructor as the one-segment name: the operation-body walk (try_qualified_ctor_ref, after the sort's rung), the clause term walk and the rule-body walk in a data slot (data_slot_dotted_ctor, beside the const fold), the query walk (ctor_named), and scaland's reallocTerm. §6.7: the value-position paragraph says so, and the data-slot exception names a constructor beside a const. Rows: tests/include/wi_9wvt7_qualified_constructor_test.rs (each walk backed out alone over the whole wi_tests binary moves only the rows its header names); wi_4nekz's agreement row now PAIRS the constructor and the free-standing entity (both positions refuse alike); wi_vnwaw's data-slot row notes the fact now holds the reference; scaland QualifiedConstructorTest (fails with the reading removed). NOT ASKED YET: the same for other kinds — a dotted nullary operation in an operation body is still refused by an earlier rule (dotted_nullary_op_call_test::an_operation_body_is_not_widened), and a dotted operation or rule name in a data slot keeps the chain. Gate 10103/0; fresh and two-step 9079/0; node carrier 10103/0; families both carriers ok; scaland 740/0.

