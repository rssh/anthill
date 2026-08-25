## Attributes

- id: WI-20260825-EBMG8-the-declare-an-operation-once
- created: 2026-08-25T18:48:07Z

- status: Open
- status_agent: claude
- status_at: 2026-08-25T18:48:07Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE "DECLARE AN OPERATION ONCE" RULE IS DOCUMENTED IN TWO PLACES AND ENFORCED IN NEITHER, so a carrier reaching one operation by two provision paths picks its implementation BY SOURCE ORDER, silently. Found by constructing the diamond while designing WI-20260825-1WBZT; the shapes below are driven, and none of them involves any stdlib sort.

THE RULE, as written. `stdlib/anthill/prelude/ordered.anthill` explains why `gt`/`lt` are declared on `PartialOrd` and NOT re-declared on `WeakOrd` where their laws live: "Declaring them a second time above would give a carrier that provides BOTH specs two `sort_ops` entries for one short name, and which one wins is HashMap-iteration order (`build_sort_ops_table` pass 2) — a coin flip, not a rule." Proposal 058 §3.8 restates it for the derived-provision case: "the derivation adds a provision ROW, never a second op declaration". Both are prose. Nothing checks either.

THREE SHAPES, DRIVEN, all built from user sorts only:

  1. THE DISCIPLINED DIAMOND — `Base` declares `f` once; `L` and `R` each `provides Base[T = T]` and declare only their own members; `C` asserts `fact L[T = C]` and `fact R[T = C]`.
     LOADS CLEAN, and is BENIGN: implementation is CARRIER-directed, not path-directed — both routes resolve `f` to `C`'s own member by the short-name join, so there is no "which parent's method" question to answer. This is the shape a well-formed tower has.

  2. THE REDECLARATION ALONE — `L provides Base[T = T]` AND declares its own `f`; one carrier, no diamond.
     LOADS CLEAN. So the rule's PREMISE is unrefused on its own: a spec may shadow the operation of a spec it provides, and nothing says so.

  3. THE DIAMOND PLUS THE REDECLARATION — `L` and `R` both provide `Base` and both declare `f`, with different bodies (22 and 33); `C` provides both.
     LOADS CLEAN, and answers BY SOURCE ORDER. MEASURED: with `sort L` declared first it answers 22 on five consecutive runs; with `sort R` moved above it (and the two `fact` rows swapped) it answers 33, likewise stable.

SOURCE ORDER IS WORSE THAN A COIN FLIP, and that is the reason to file this rather than leave it as prose. A random pick announces itself — a suite goes flaky and someone looks. A pick keyed on declaration order is STABLE: it is stable in tests, stable across runs, stable across machines, and it flips when a maintainer reorders two declarations, moves one to another file, or renames a file in a way that changes load order. Nothing at that moment says a semantics changed. (The `ordered.anthill` note calls it HashMap-iteration order; the measurement says source order. Whichever the mechanism, neither is a rule, and the note's own verdict stands.)

WHY NOW. WI-20260825-1WBZT gives each operator a SYNTAX CATEGORY — a spec owning exactly the operation that operator mints — with bundles reaching them by `provides`. That makes the diamond REACHABLE IN THE STDLIB for the first time: `Numeric` and `Ring` would both provide `Additive`, and `rustland/anthill-stl/anthill/float.anthill` already writes both `provides Numeric[T = Float]` and `provides Ring[Float]`. Shape 1 is what that produces — benign — and the design's safety rests ENTIRELY on the discipline this ticket is about. A tower whose invariant is unchecked is one refactor away from shape 3.

AND A GOOD-NEWS HALF, so this is not read as an objection to that ticket: 1WBZT REMOVES a live duplication rather than adding one. Today `Numeric.add` and `Ring.add` are two DIFFERENT operations with one spelling, and a bare `add` in a scope seeing both is ambiguous — driven under WI-20260824-VT8CF's census, "`add` is a member of sorts Numeric, Ring, not in scope as a bare name here", resolved today only because the implicit tier deterministically answers `Numeric.add`. Collapsing them onto one `Additive.add` declaration is the fix for that, and it lands in shape 1.

WHAT TO REFUSE. Two readings, and the ticket should pick deliberately:
  (a) AT THE DECLARATION — refuse a spec that declares an operation whose short name is already declared by a spec it provides (or requires). Best error location, names the repair ("move the members into the base, or rename"), and is the direct reading of `ordered.anthill`'s sentence.
  (b) AT THE EFFECT — refuse a carrier whose `sort_ops` table ends with two entries for one short name from two provision paths. Catches more (including routes assembled through `requires` chains) and is the condition that actually decides the pick.
(b) is the EFFECT and (a) is a proxy for it, so (b) is what must hold; (a) is where the message belongs. Likely both: check at (b), report at (a) when the cause is a single declaration.

WHAT MUST NOT BE REFUSED, and needs a control row each: shape 1 above (a well-formed tower — `Eq`/`PartialEq`, `Ord`/`WeakOrd`/`PartialOrd`, `Field`/`EuclideanDomain`/`Divisible` are all this shape and must stay loading); a carrier's OWN override of a spec op (that is `carrier_own_op`, the whole dispatch mechanism); and a spec DEFAULT body on the base (`PartialOrd`'s `gt` derivation from `compare`), which is one declaration with a body, not two declarations.

NOT DRIVEN: everything under "WHAT TO REFUSE". The three shapes ARE driven, on the built tree, with the source-order swap as the separating measurement.

CONTROL, when it is fixed: shape 3 becomes a load error naming both declarations; shape 2 becomes a load error naming the redeclaration; shape 1 still loads and still answers from the carrier's own member. Back the check out and shape 3 must return to answering 22-or-33 by declaration order — that inversion, not the mere presence of an error, is what says the check reaches the real condition.

ACCEPTANCE: the three shapes above behave as the control says; every existing prelude tower still loads (`Eq`/`PartialEq`, the three ordering floors, the division tower); full workspace green via rustland/scripts/test.sh and scaland sbt test.

