## Attributes

- id: WI-20260929-6NMGQ-a-spec-operation-call-on-an
- created: 2026-09-29T20:17:10Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T20:17:10Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260904-34J8Z-a-binder-list-lambda-s-arrow

- tags: typing

## Description

A SPEC-OPERATION CALL ON AN UNANNOTATED LAMBDA PARAMETER DEFERS TO THE ENCLOSING `requires` BEFORE THE PARAMETER IS SOLVED, AND RUNS THAT REQUIREMENT'S PROVIDER ON A VALUE OF ANOTHER SORT. `sort User { requires Store[State = Other]; operation go() -> Int64 = let f = lambda x -> Store.peek(x)  f(buf(v: 7)) }`, providers `Carrier` at `Buf[T = Int64]` (answers `s.v + 30`) and `OtherImpl` at `Other` (answers 99), called `User.go()`: runs `OtherImpl.peek` on the `Buf` (99). The annotated lambda `lambda (x: Buf[T = Int64]) -> Store.peek(x)` runs Carrier (37). MEASURED before and after WI-20260929-WBHTM, and not about value-in-type (the `Buf` here holds no value). MECHANISM: when `Store.peek(x)` is typed, `x`'s type is still an unbound variable, so `State` is open and the OPEN-T defer trigger (`find_requires_slot` / `entry_matches_subst`, an unbound spec param is "no constraint") classifies the call `DeferToRequirement` onto `requires Store[State = Other]`; the application `f(buf(v: 7))` pins `x` later, after the classification is fixed. FIX: re-check a deferral whose element was open once the lambda's parameter is solved (the WI-20260904-50B2K binder discharge is the nearest owner of "a binder's uses solve it later"), or refuse the call when the enclosing requirement's element is concrete and the call's is still open. FOUND by WI-20260929-WBHTM's /code-review. ACCEPTANCE: the unannotated lambda runs Carrier (37) as the annotated one does, or is refused at load — never runs `OtherImpl`; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-02T17:44:24Z — feedback — claude

PART 1 DELIVERED, ticket stays Open (user 2026-11-02, option 1): it now depends on WI-20260904-34J8Z for the shape below. DECIDED WITH THE USER: dictionaries are passed to the lambda — a let-bound lambda's quantified context is an implicit requires, each application hands it the dictionary at the type it gives the parameter, as a call supplies an operation's requires (the enclosing declaration's own where its requires covers that type, a provider's otherwise, a load error where none or two answer); a reference handed on unapplied is wrapped, lambda y -> f(y) (option (a)). WHAT CHANGED: a spec-op call whose element is a walk-minted variable (a lambda's unannotated parameter, either direction of the link in the call's sigma) is held instead of deferred to the requirement the unsolved element matched vacuously (classify_or_hold_deferral, beside the 50B2K binder deferral, one DeferredSpecRequirement); at the walk's end (WalkSolutions::discharge) the call reads the dictionary at the parameter's one type, or, for a generalized lambda, the slot __ctx_<spec>_<carrier>_<serial> each application hands (NodeOccurrence closure_dicts stamp, ho_apply_within's meaning; a re-quantified instance forwards the slot); the dictionary is build_dep_projection's (lambda_requirement_dict). New CallClass::DeferToDictionary; eval adds handed dictionaries to the closure's captured ones. MEASURED HEAD -> now: ticket 99 -> 37; f(7) with an Int64 provider 99 -> 107; f(buf)+f(other) 198 -> 136; requires Store[State = S] with S = Other, f(buf) 99 -> 37; f(s)+f(other) run-time panic -> 136; providers at Buf[T = Int64] and Buf[T = Bool], no requires: run-time ambiguous -> 37; two providers at the use's type: 99 / run-time failure -> load error at the use; uses the requirement covers still read it, a caller's selection honoured (77). Rows: wi_6nmgq_lambda_requirement_passing_test (17), back-outs per part in its header. Spec: kernel-language 4.4 (discharge at the elimination); design operation-call-model 'Closure invocation'. REMAINS: a binder-list lambda, 'let f = lambda (a, b) -> Store.peek(a) + b  apply2(f, buf(v: 7))' under requires Store[State = Other], still runs OtherImpl on the Buf (100, as on HEAD): the component's type is a ??pat variable the call's sigma never links to Store.State, so neither the hold nor a narrow refusal can see it (measured); the link is WI-20260904-34J8Z's. UNVERIFIED (/code-review): contested_slot_read inspects DeferToRequirement only, so a passed forward of a contested FromParam slot may escape that refusal; no fixture reaches it yet.

