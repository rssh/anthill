## Attributes

- id: WI-20260911-073GH-defect-a-constructor-whose
- created: 2026-09-11T07:49:06Z

- status: Open
- status_agent: claude
- status_at: 2026-09-11T07:49:06Z

- acceptance: cargo-test, scaland-sbt-test

## Description

DEFECT: a constructor whose short name equals a parameter that is APPLIED as a function anywhere in loaded code captures that application. `entity f` in any sort makes every call in every operation body (and rule body) fail to load with "constructor 'f' given N positional argument(s) but has 0 unfilled field(s) (declares: none)", because the prelude's `Function.apply(f: Function[A, B, E], x: A)` applies its parameter `f`.

MEASURED 2026-09-11 (CLI `anthill load`, current tree). (a) `sort Bit { entity t; entity f }` beside `operation count(args: List[T = String]) -> Int64 = length(args)` in a fresh namespace: three "constructor 'f' given 1 positional argument(s)" errors; rename the entity to `ff` and it loads clean. (b) With `entity f` present EVERY application with one or more positional arguments reports it -- `length(args)` (1), `a + b` (the `add` desugar, 2), a RULE-body `length([1, 2])` (1); a nullary `t()` does not. (c) It is NOT the letter: entities named `x`, `s`, `args`, `l` load clean beside the same bodies. (d) It IS the applied-parameter name: `sort Shape { entity g; entity h }` beside `operation twice(g: (v: Int64) -> Int64, n: Int64) -> Int64 = g(g(n))` reports "constructor 'g' given 1 positional argument(s)", while `operation keep(h: Int64) -> Int64 = h` (parameter used as a value, never applied) is clean. Found while writing examples/classic-mini/tiny-sat, whose bits are `yes`/`no` instead of `t`/`f` for this reason (its README says so).

CAUSE (read at the sites, not driven by a fix -- verify first). The error is EvalError's WI-20260827-T2470 variant (eval/error.rs:38 doc), raised from `finish_constructor`'s positional-to-named desugar in the eval twin -- whose own doc says it is "unreached by any source program". It is reached because `KnowledgeBase::is_constructor_symbol` (kb/mod.rs:10109) is a SYMBOL-set lookup, `mark_constructor_symbol` (kb/mod.rs:10196) is called in scan pass 1 for every sort-nested entity, and `nullary_canon`'s note in kb/mod.rs ("`Color` was measured registering under BOTH spellings in one run") records that a constructor is marked under its BARE interned short name as well as its qualified symbol. A parameter reference is a bare name, so an APPLIED parameter `g(...)` becomes an application whose functor is `intern("g")`; the twin asks `is_constructor_symbol` on it and a nullary constructor answers yes. The load-time refusal the T2470 doc relies on never fires because the loader's own arity check runs against a RESOLVED constructor, which this path never resolved to.

FIX DIRECTION (verify before building; two routes, measure both). (1) A parameter in scope must SHADOW a same-named constructor at an applied position -- the rule `rule_param_vars` already states for rule heads ("FIRST, so the parameter SHADOWS a same-named symbol in scope", load.rs): ask the frame's parameter map before the constructor table at whichever of the converter / body specializer / eval twin turns `g(args)` into a constructor application. (2) Per "make illegal state unrepresentable": stop marking a constructor under its scope-less short symbol and key `constructor_symbols` on the QUALIFIED symbol only -- but the `nullary_canon` note records that sending an unresolved functor to `Ident` was TRIED AND BACKED OUT (`is_entity_of` probes `Ref(c)` and the unit fixtures reach both through `kb.intern`), so census every reader of the bare spelling before choosing this route. Whichever route: it must cover rule bodies too (measured (b)).

ACCEPTANCE (cargo-test via scripts/test.sh). (1) The (d) program loads and `twice((v) -> v + 1, 1)` evaluates to 3, asserted by VALUE. (2) `entity f` beside `length(args)` in an operation body loads and evaluates. (3) A rule body applying a parameter that shares a constructor's name answers by value. CONTROLS, each stated at its site: a hand-written over-arity constructor application `f(1)` stays a LOUD load error -- this is the row that separates "stop treating a parameter as a constructor" from "stop checking constructor arity", and the T2470 backstop must survive; `entity h` beside a value-only parameter `h` passes either way BY DESIGN. Say which rows fail with the fix backed out. Then rename tiny-sat's bits back to `t`/`f` and drop its README paragraph about this.

