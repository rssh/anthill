## Attributes

- id: WI-20261003-4DYR6-a-spec-with-no-type-parameters
- created: 2026-10-03T08:57:43Z

- status: Open
- status_agent: user
- status_at: 2026-10-03T08:57:43Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SPEC WITH NO TYPE PARAMETERS CANNOT BE CALLED THROUGH THE SPEC: THE CALL LOADS CLEAN AND DIES AT RUN TIME. `sort Sp { operation size(s: Sp) -> Int64 }`, `sort Car { entity car(n: Int64); provides Sp; operation size(c: Car) -> Int64 = 42 }`, `operation go() -> Int64 = Sp.size(car(n: 1))` loads with no diagnostic and `anthill run` dies 'operation has no body: …Sp.size — nothing this runtime can run is registered for it'; so does a call through an abstract receiver, `operation measure(s: Sp) -> Int64 = Sp.size(s)` called as `measure(car(n: 1))`. Adding one unused parameter (`sort T = ?` in Sp, `provides Sp[T = Int64]`) makes both run to 42, and the carrier's own member called directly (`car(n: 1).size()`) runs. MECHANISM: an operation counts as a dispatched spec operation only in a PARAMETRIC sort — `spec_op_parent_sort` (typing/call_class.rs:33; WI-210: 'at least one `sort <Param> = ?`'), which gates the typer's self-receiver classification (`self_receiver_spec_sort`, typing/carrier.rs:908, and `lookup_spec_op_dispatch` built on it) and eval's value-directed dispatch (eval/eval.rs:5236) — while the loader accepts `provides Sp` and the member, so nothing names the gap before run time. MEASURED identically on the trees before and after WI-20260929-0RP29's ninth and tenth passes; FOUND by the tenth pass's gate (verify/S1b/s2/min_noparam: a spec op returning a function, behind a parameterless spec). Nothing in stdlib/ or examples/ provides a parameterless spec. FIX: decide which rule holds and apply it everywhere — either a sort something PROVIDES is a spec whether or not it declares a parameter (the dispatch gates ask for a body-less operation of a provided sort, typer and eval alike), or a parameterless sort cannot be provided and `provides Sp` is refused at load naming the rule; the spec says neither today. ACCEPTANCE: under the first rule the two programs above run to 42 through the spec call, the one-parameter twin unchanged; under the second, both refused at the `provides` clause; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-10-11T05:28:14Z — feedback — claude

RELATED, filed 2026-10-11: WI-20261011-RM247 is the other side of the same identification. There an operation of a PARAMETRIC sort that nothing provides (`sort Box[V]` with constructors) is read as a spec operation, so the `@[simp]` equation that defines its body-less `open` is held to `Box` providing `Box` and never fires. Deciding here what a spec is — a sort something provides, or a sort with a parameter — decides that one too only if the rule narrows as well as widens.

### 2026-10-11T06:16:46Z — feedback — claude

MEASURED 2026-10-11 while delivering WI-20261011-RM247, which narrowed the body-less half only: `lookup_spec_op_dispatch` no longer answers for an operation of a sort with constructors. THE SAME TEST MOVED TO THE SHARED LEG (`sort_is_parametric`, read by `spec_op_parent_sort`, `defaulted_spec_op_parent` and `spec_op_call_parent`) IS NOT A ONE-LINE CHANGE: over the full workspace it fails three rows of wi_hzvqa_alias_receiver_test (a_rule_body_call_through_an_alias_is_at_its_parameters, a_rule_body_goal_through_an_alias_is_checked_and_answers, a_paren_less_goal_through_an_alias_is_the_applied_goal), each loading clean where a refusal is due. The rule-body walk is triggered by that leg, so a rule-body call of a data sort's operation stops being typed at all — as the call of a plain sort's operation is not typed today. Whatever is decided here has to separate 'the walk types this call' from 'this operation is dispatched' first. Still reading a sort with a parameter and constructors as a spec after RM247: the defaulted half, `spec_op_parent_sort` and eval's value-directed dispatch on it, the loader's `enclosing_is_spec`, and the reading in `requires`.

