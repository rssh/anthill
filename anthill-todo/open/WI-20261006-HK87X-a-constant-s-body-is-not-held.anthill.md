## Attributes

- id: WI-20261006-HK87X-a-constant-s-body-is-not-held
- created: 2026-10-06T07:36:58Z

- status: Open
- status_agent: claude
- status_at: 2026-10-06T07:36:58Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CONSTANT'S BODY IS NOT HELD TO THE CONSTRUCTION RULE — a value an operation body may not build is built by a `const`. `sort Shown { sort T = ?; operation show(x: T) -> Int64 }`, `sort Other { entity other }` (it provides nothing), `sort Hold { sort E = ?; requires Shown[T = E]; entity hold(inner: E); operation read(h: Self) -> Int64 = match h case hold(i) -> Shown.show(i) }`. `operation build() -> Hold[E = Other] = hold(other())` is refused where it is written — "requirement `Shown[T = Other]` of `Hold` cannot be supplied for the construction `Hold.hold`" (kernel-language §5.2, the rule WI-20261005-KSSA4 added) — and `const bad: Hold[E = Other] = hold(other())` LOADS. MEASURED on the tree that delivers KSSA4; the rule is new with it, so the constant was never reached by it. WHY: a constant is folded to a value and typed as one (`constructor_value_type`, typing/value_type.rs), a reader with no refusal to give; the occurrence typer, which makes the check (`construction_meets_sort_requires`, typing/constructor.rs), is not run over a constant's body. WHAT IT COSTS, MEASURED — nothing dies: `operation go() -> Int64 = Hold.read(bad)` is refused at the call ("cannot be supplied for call to `Hold.read`"); with `Hold provides Shown[T = Hold[E = E]]` and `operation show(h: Hold[E = E]) -> Int64 = match h case hold(i) -> Shown.show(i)`, `Shown.show(bad)` is refused at its dispatch ("no impl matches — unresolved: Shown[T = Other]"); `operation takes(h: Hold[E = Other]) -> Int64 = 1` given `bad` loads, owing nothing. So the defect is one rule with two verdicts by where the value is written. NOT LOOKED FOR: what else the occurrence typer checks in an operation body and a constant's body skips the same way. ACCEPTANCE: the `const` above is refused as the operation body is, naming the requirement and the construction; `wi_kssa4_spec_typed_value_test …a_constants_body_is_not_reached`, which records the gap, becomes that refusal; a constant built over a provider (`sort Leaf { entity leaf; provides Shown[T = Leaf]; operation show(x: Leaf) -> Int64 = 7 }`, `const good: Hold[E = Leaf] = hold(leaf())`) loads and `Hold.read(good)` answers 7; full workspace green via rustland/scripts/test.sh. REFERENCE: kernel-language §5.2; WI-20261005-KSSA4.

