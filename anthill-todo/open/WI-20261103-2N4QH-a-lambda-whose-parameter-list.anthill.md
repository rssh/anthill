## Attributes

- id: WI-20261103-2N4QH-a-lambda-whose-parameter-list
- created: 2026-11-03T09:09:40Z

- status: Open
- status_agent: user
- status_at: 2026-11-03T09:09:40Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261104-6HVXM-every-arrow-is-a-function-in

- tags: typing

## Description

A LAMBDA WHOSE PARAMETER LIST NAMES SEVERAL ANNOTATED BINDERS TAKES ANY ARGUMENT WHERE NO EXPECTED ARROW IS IN SCOPE: `let h = lambda (s: Int64, b: Int64) -> s + b` / `h("a", 1)` loads, and `anthill run` dies "type mismatch: expected Int64, got String and Int64" in eval; `lambda (s: List[T = Int64], b: Int64) -> true` applied to `(["a"], 1)` loads (measured 2026-11-03 on HEAD 9c60680a and with WI-20261103-SG16K, found while measuring it). One binder is pinned (`lambda (s: Int64) -> true` applied to `"a"` is refused at the argument), and against an expected arrow each binder is compared with its component (WI-794: `let h: ((Int64, Int64)) -> Bool = lambda (s: String, b: Int64) -> true` is refused). With neither, the lambda arm mints the parameter a fresh variable (rung 3) and `bind_and_label_pattern` binds each binder at its own annotation without tying that variable to them, so the arrow is `?param -> …` and the body is typed at types the call never meets. kernel-language.md (the lambda binder paragraph) says the conflict "surfaces through the body's use of the binder" — `s + b` above uses both and does not. WHAT: where no context type reaches the parameter, the parameter type is the tuple of what the binders write — an annotated binder its annotation, an unannotated one a fresh variable — so the call is checked against it; measure first whether the expected-arrow path needs anything. The spec sentence is to be corrected with the user. ACCEPTANCE: both programs above are refused at the argument, `h(1, 2)` loads and runs to 3, the partly annotated `lambda (s: Int64, b) -> s` applied to `("a", 1)` is refused; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-03T20:41:19Z — feedback — claude

Waits on proposal 002's correction (2026-11-03, decided with the user: every arrow is a Function; an application keeps its form f(x1, ..., xn) and is checked against A, converted at load to the tupled form). The fix this ticket names is WI-20260904-34J8Z's (built and backed out 2026-10-23); under the correction h("a", 1) and h(("a", 1)) are refused at load and h(1, 2) runs; h((1, 2)) depends on 002's open question 1 (the labels of a callable's A).

### 2026-11-13T21:46:18Z — feedback — claude

THE EXPECTED-ARROW PATH NEEDS SOMETHING TOO (measured 2026-11-13 on 53a0d453, found while restating proposal 074 §4). A lambda with two annotated binders, written as a call's argument, does not fix a type parameter its slot's arrow names: operation ab[X](f: (x: X, y: X) -> X) -> Int64 = 1 with go() = ab(lambda (x: Int64, y: Int64) -> x) is refused at the call, "type mismatch in ab.type_arg: expected a type for X, got unconstrained — use ab[X = …](…)"; the same with a result not over X ((x: X, y: X) -> Int64 given lambda (x: Int64, y: Int64) -> 1), with unnamed components ((X, X) -> X), and with requires Additive[T = X] on ab. The same slot is fixed by one binder (ab[X](f: (x: X) -> X) given lambda (x: Int64) -> x answers 1), by the lambda bound with let first (let g = lambda (x: Int64, y: Int64) -> x, then ab(g), answers 1), and by an operation name (ab(add) over add(x: Int64, y: Int64) -> Int64 answers 1). The member spelling shows it too: applyBoth(f: (x: Additive.T, y: Additive.T) -> Additive.T) -> Int64 = 1 given lambda (x: Int64, y: Int64) -> x + y is refused "expected a type for Additive.T, got unconstrained", and loads when an argument z: Additive.T is added (answers 4 for f(z, z) at z = 2). So the binders' annotations reach neither the open parameter type (this ticket's case) nor an expected tuple whose components are open variables; the fix owes both, with these rows.

