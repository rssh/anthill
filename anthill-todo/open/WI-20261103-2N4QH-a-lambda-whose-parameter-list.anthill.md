## Attributes

- id: WI-20261103-2N4QH-a-lambda-whose-parameter-list
- created: 2026-11-03T09:09:40Z

- status: Open
- status_agent: user
- status_at: 2026-11-03T09:09:40Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A LAMBDA WHOSE PARAMETER LIST NAMES SEVERAL ANNOTATED BINDERS TAKES ANY ARGUMENT WHERE NO EXPECTED ARROW IS IN SCOPE: `let h = lambda (s: Int64, b: Int64) -> s + b` / `h("a", 1)` loads, and `anthill run` dies "type mismatch: expected Int64, got String and Int64" in eval; `lambda (s: List[T = Int64], b: Int64) -> true` applied to `(["a"], 1)` loads (measured 2026-11-03 on HEAD 9c60680a and with WI-20261103-SG16K, found while measuring it). One binder is pinned (`lambda (s: Int64) -> true` applied to `"a"` is refused at the argument), and against an expected arrow each binder is compared with its component (WI-794: `let h: ((Int64, Int64)) -> Bool = lambda (s: String, b: Int64) -> true` is refused). With neither, the lambda arm mints the parameter a fresh variable (rung 3) and `bind_and_label_pattern` binds each binder at its own annotation without tying that variable to them, so the arrow is `?param -> …` and the body is typed at types the call never meets. kernel-language.md (the lambda binder paragraph) says the conflict "surfaces through the body's use of the binder" — `s + b` above uses both and does not. WHAT: where no context type reaches the parameter, the parameter type is the tuple of what the binders write — an annotated binder its annotation, an unannotated one a fresh variable — so the call is checked against it; measure first whether the expected-arrow path needs anything. The spec sentence is to be corrected with the user. ACCEPTANCE: both programs above are refused at the argument, `h(1, 2)` loads and runs to 3, the partly annotated `lambda (s: Int64, b) -> s` applied to `("a", 1)` is refused; full workspace green via rustland/scripts/test.sh.

