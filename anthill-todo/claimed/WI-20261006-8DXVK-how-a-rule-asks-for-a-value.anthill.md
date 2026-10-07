## Attributes

- id: WI-20261006-8DXVK-how-a-rule-asks-for-a-value
- created: 2026-10-06T06:39:39Z

- status: Claimed
- status_agent: codex
- status_at: 2026-10-07T18:35:15Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

HOW A RULE ASKS FOR A VALUE WHOSE SORT PROVIDES A SPEC IS DECIDED FOR NOW AND NOT YET DESIGNED — think it through and write the proposal, the next in the sequence after 060. WI-20261005-KSSA4 made the rule language read a type as a signature does: a spec over a parameter is no type of its providers' values. With `sort Summable { sort T = ?; operation plus(a: T, b: T) -> T }`, `Int64 provides Summable[T = Int64]`, `fact src(1, 10)`, `fact src(true, 20)`: (1) `rule keep(?x: Summable, ?y) :- src(?x, ?y)` is a load error, and so are `?x: List[T = Summable]` and `sort Sum1 = Summable` / `?x: Sum1`; (2) `rule keep(?x: Summable.T, ?y) :- src(?x, ?y)` and the introducer `rule keep[A](?x: A, ?y) :- src(?x, ?y), Summable[A]` hold of the `Int64` row alone; (3) `rule d(?b) :- src(?a, ?b), domain(?a, Summable)` is a load error, in a rule body and in a constraint body. The user confirmed this reading on 2026-10-06 as the present rule and asked for it to be thought through. WHAT IS NOT SETTLED, each MEASURED on the tree that delivers KSSA4: (a) A QUERY IS NOT LOADED, so its `domain` goal cannot be refused, and it answers by provision — `domain(1, Summable)` holds and `domain(true, Summable)` does not — the reading the same goal is a load error for inside a rule. One goal, two readings, by where it is written. (b) THE INTRODUCER TAKES ONE SPELLING OF ITS GUARD, `Spec[A]`. Over `sort Tagger { sort C = ?; sort Out = ?; operation tag(x: C) -> Out }` with `Int64` providing it at `Out = Int64` and `String` at `Out = String`: `:- Tagger[A]` holds of both, `:- Tagger[C = A, Out = Int64]` and `:- Tagger[A, Int64]` are refused ("rule type-variable `A` has no bounding guard"), and the instance can be said only through an alias — `sort IntTagger = Tagger[Out = Int64]`, `:- IntTagger[A]` holds of the `Int64` alone. The member spelling cannot say it at all: `?x: Tagger.C` holds at every `Out`, `?x: IntTagger.C` is refused. (c) WHICH MEMBER STANDS FOR THE PROVIDER is read off the spec's operations (`?x: Tagger.Out` is refused naming `Tagger.C`; `?x: Stream.T` is refused the other way, `Stream` being its own carrier), and A SPEC THAT DECLARES NO OPERATION is classified by its provisions: with `sort Summable { sort T = ? }` and no provision, `rule keep(?x: Summable, ?y) :- src(?x, ?y)` loads and holds of nothing; add `Int64 provides Summable[T = Int64]` — in any file — and the same rule is a load error. A verdict on one declaration that another declaration decides. (d) THE REQUIREMENT A RULE VARIABLE CARRIES IS STORED AS THE BARE SPEC and told from a type by a mode its readers set (`spec_as_its_providers`: the bound's verdict, the pin of a bound with an open slot, a citation's argument, `Without`, a `Permission` denial). A reader that compares a bound outside the mode refutes every provider in silence — KSSA4's /code-review found two (a bound with an open slot answered nothing; `keep(1)` cited from an operation body was refused). A term of its own for the requirement, or the type variable with the instance as a goal, would need no mode. ACCEPTANCE: a proposal under docs/proposals/ saying how a rule's head and body ask for a provider, what a `domain` goal at a spec means in a rule, a constraint and a query, how an instance of a spec with several parameters is said, and how a spec with no operations says which parameter its providers are; kernel-language §5.3 agrees with it; the decisions are the user's. REFERENCE: kernel-language §5.3, §8.2; WI-20261005-KSSA4; `wi582_typed_rule_pattern_test`.

## Changes

### 2026-10-07T18:37:57Z — feedback — user

Drafted docs/proposals/071-rule-provider-constraints.md for user decision. Recommends normalized explicit instance guards, uniform type-membership domain semantics including query validation, declaration-owned carrier classification, and explicit provider-constraint IR. Canonical specification unchanged pending discussion required by repository instructions. Item remains claimed until decisions and specification agreement.

### 2026-10-07T18:39:36Z — feedback — user

User corrected scope: understand existing proposal 060 before proposing new semantics. New-design recommendations withdrawn; investigation notes added. Source shows WI-582 introducer recognizes one positional guard, stores only a spec symbol and folds guard away, distinct from 060 instance-bearing requirement channel. Query domain shares provider-bound reader while load checks reject same source goal. Next: executable comparison through existing require[...] typed-head anchor.

### 2026-10-07T18:40:55Z — feedback — user

Replaced premature proposal with docs/design/8dxvk-060-gap-analysis.md. Existing 060 typed-head anchor suite: 24 passed, including executed multi-parameter dictionary consumption yielding provider-specific 7. Design 060-implementation §8.7 already records free-T example cannot load without bounding guard; acceptance relies on WI-582 introducer. Gap is admission/representation of polymorphic typed heads through nominal spec bounds, not general multi-parameter dictionary fetch. No spec or implementation changed.

### 2026-10-07T20:05:51Z — feedback — user

Scope corrected by user: remove the replacement proposal and repair existing 060 implementation gaps. Introducer bounds now retain the full normalized instance, named/multi-positional guards load, alias members preserve fixed sibling bindings in both head spellings, and applying an introduced bound preserves its existing bindings. Query domain diagnoses parameter-carried specs before delay or negation, while compiler-generated annotation guards keep their requirement interpretation. Existing 060 dictionary consumption is executed through a nullary provider-specific operation. Compatibility classification retained by user agreement: a single member-free parameter cannot be assumed to be the carrier (DataProvider[K] is the counterexample). Existing nominal-bound readers/spec_as_its_providers remain; this does not claim their architectural replacement or independent unbounded rule variables. Manual review added alias-rebinding/unknown-label/excess-arity/wrong-carrier refusal controls. Focused binary: 199 passed, 2 ignored; production back-out: 193 passed, 6 failed, 2 ignored. Temporary binary removed and new tests registered once. Scala testFull: 600 passed. Final Rust workspace gate running. No /code-review skill is installed; manual review performed. Queue: 163 open unblocked items. Item remains claimed because the original description also requests replacing the nominal-bound representation.

### 2026-10-07T20:07:53Z — feedback — user

Final verification completed: rustland/scripts/test.sh exit 0, 8757 passed, 0 failed, 14 ignored across 36 test targets (test-run-20261007-200410.log). Scala sbt testFull: 600 passed, 0 failed. All 726 include files are registered exactly once across integration binaries; git diff --check passes. Changes are uncommitted. The functional guard/instance/query fixes are verified; item remains claimed for the separately documented nominal-bound representation gap.

