## Attributes

- id: WI-20261003-H7KFV-a-callback-in-a-function-a-b
- created: 2026-10-03T09:18:51Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-03T12:58:01Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CALLBACK IN A `Function[A, B]` SLOT (E UNWRITTEN) IS ADMITTED AT ANY ROW AND CHARGED NOWHERE IT IS APPLIED, SO ITS EFFECTS LEAVE OPERATIONS TYPED PURE. `operation boom(x: Int64) -> Int64 effects {Error[String]} = Error.raise("boom")`; `operation via(g: Function[A = Int64, B = Int64]) -> Int64 = g(1)`; a `main` that declares no effect calls `via(boom)`: it loads, and dies `error: boom` at run time (MEASURED on the trees before and after WI-20260929-0RP29's ninth and tenth passes alike). The arrow spelling `g: (x: Int64) -> Int64` and the pure spelling `g: Function[Int64, Int64, {}]` are refused at the call ('… (a closed row), got operation `boom` declares `Error[T = String]`'). MECHANISM: ADMISSION reads an unwritten `E` as any row — typing/subtype.rs's `Function` arm '(None, _) | (_, None) => true' (WI-332: 'omitting the binding means polymorphic (accept any), NOT empty'), which is now the stated semantics (user decision 2026-10-03; kernel-language.md §4.4 corrected to follow §8.1: `Function[A, B]` is effect-polymorphic, `Function[A, B, {}]` is pure). APPLICATION charges nothing for it — `callable_effect_present_values` (typing/callable.rs) charges no unwritten `E` (a value projection `f.E`, a flexible variable, a rigid that is no declared parameter's), kept so by the tenth pass because charging it refused every operation that applies such a value (the suite's `wi_2tmb5` / `wi_5nszy` programs: 'undeclared effect: f.E' / '?E') while no operation can declare `effects {f.E}` for a callable parameter (MEASURED on every build). The two readers disagree, and the effect falls between them. FIX — decide which, then measure the suite and the stdlib: (a) give the operation a way to declare the row it applies — `effects {g.E}` for a callable parameter `g`, re-keyed to the argument's row at the call — then charge an unwritten `E` at the application and refuse an operation that applies it undeclared, as the arrow `@ {E}` spelling is refused; or (b) refuse applying a callable whose `E` is unwritten, naming the repair `via[E](g: Function[A, B, E = E]) -> … effects {E}`, which is charged correctly since the tenth pass. ACCEPTANCE: `via(boom)` from a pure `main` refused at load (at `via`'s declaration under (b), at the caller under (a)); `via(inc)` still runs; the declared spelling charges the caller the argument's row — a caller declaring `Error[String]` runs `via(boom)` to its handler, one declaring nothing is refused; `wi_2tmb5` / `wi_5nszy` rewritten to the chosen spelling; scaland mirrors it; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-10-03T09:22:30Z — feedback — user

USER DECISION (2026-10-03): `via` must not compile — an operation that applies a callable whose effect row is unwritten (`g: Function[A = Int64, B = Int64]`, any row) is refused at the application inside it, not at its callers; the message names the two spellings that state the row: a declared row parameter (`via[E](g: Function[A = Int64, B = Int64, E = E]) -> Int64 effects {E}`) or the pure row (`Function[Int64, Int64, {}]`). Fix (b) of the description, with the refusal at `g(1)`. Prototype measured in the tenth pass: `applies_unwritten_row` (typing/callable.rs) at the callable-application site of check_apply_iter; a row still being inferred (a flexible variable) is not refused.

### 2026-10-03T09:38:57Z — feedback — user

MEASURED (tenth pass, 2026-10-03): the prototype refusal at the application — an `E` binding left out, a parameter's own unwritten slot as the body reads it (`g.E`), or a rigid no declared parameter owns; NOT a flexible variable still being inferred — fails 131 existing rows: 117 in wi_tests across 25 files (wi_qqpq2_tuple_carrier 11, wi_50b2k_binder_inference 9, wi_fc2x4_lambda_in_a_rule 8, wi_emvcb 8, wi817_polyrec 8, wi786 8, wi_5nszy 7, wi803 6, wi788 6, wi_02err 5, wi801 5, wi787 4, wi785 4, wi784 3, wi1095 3, wi1093 3, wi1087 3, wi275 2, wi1088 2, wi_9r5hn 1, wi_2tmb5 1, wi792 1, wi_0rp29_review9's an_unwritten_function_slot_charges_nothing_control 1), 10 in eval_tests (e.g. `spin(f: Function[Int64, Int64], x)`, `cyc.a`, `reduce_set3.f`), 4 in parse_tests (typing_test). Sampled failures are the intended case (an operation declaring nothing applies an unwritten-row parameter); the stdlib loads clean. So the work is the refusal (small) plus rewriting those programs to a written row — `Function[…, {}]` where pure, `[E] … E = E … effects {E}` where a row is meant — and the scaland port.

### 2026-10-03T12:57:55Z — feedback — user

SUPERSEDED BY WI-20261003-QV5W5 (implement proposal 069), user decision 2026-10-03. Proposal 069 makes `Function[A, B]` pure: `Function` declares its `E` with `default {}`, so an omitted `E` is the closed empty row, and `Function[A, B, ?]` is the explicit effect-polymorphic spelling. Under it this ticket's program changes verdict at the CALL, not at the application: `via(boom)` is refused because `boom`'s `{Error[String]}` does not fit the slot's `{}` — as the arrow and `Function[Int64, Int64, {}]` spellings already are — and applying `g` inside `via` charges the empty row, which is right. So no operation applying a `Function[A, B]` must declare anything, and the refusal asked for here (and the 131 rows a prototype of it broke) is moot. WHAT CARRIES OVER to QV5W5's acceptance: this ticket's program (`boom` through `via` escaping a `main` that declares no effect) refused once 069 lands; the exception `callable_effect_present_values` (typing/callable.rs) keeps — an unwritten `E` charges nothing where it is applied, whose doc names this ticket — removed with the `default {}`, since nothing is unwritten after defaulting; and applying a `Function[A, B, ?]` (the explicitly open spelling) still charges its row at the application. Until then the interim stands: an unwritten `E` is any row (WI-332, kernel-language.md §4.4 as corrected 2026-10-03), uncharged where applied.

