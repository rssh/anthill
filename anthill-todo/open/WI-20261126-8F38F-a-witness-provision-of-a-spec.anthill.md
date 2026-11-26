## Attributes

- id: WI-20261126-8F38F-a-witness-provision-of-a-spec
- created: 2026-11-26T19:20:18Z

- status: Open
- status_agent: user
- status_at: 2026-11-26T19:20:18Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A WITNESS PROVISION OF A SPEC WHOSE OPERATIONS TAKE THE TYPE PARAMETER ONLY INSIDE ANOTHER TYPE IS READ AS ABOUT ITS PROVIDER: `W provides Sp[T = Other]` over `Sp { sort T = ?  operation count(xs: List[T = T]) -> Int64 = 0 }` answers `Sp` at `W` itself, and `W`'s member written for `Other` is handed `W`'s values. Found after WI-20261126-DHB0C (user, 2026-11-26: file it).

THE PROGRAM, MEASURED (one load, on eea88ed51):

    namespace test.narrow
      import anthill.prelude.{Int64, Bool, List}
      sort Sp
        sort T = ?
        operation count(xs: List[T = T]) -> Int64 = 0
      end
      sort Other
        entity o(n: Int64)
      end
      sort W
        entity w(n: Int64)
        provides Sp[T = Other]
        operation count(xs: List[T = Other]) -> Int64 = 7
      end
      operation atOther() -> Int64 = Sp.count([Other.o(n: 1)])
      operation atW() -> Int64 = Sp.count([W.w(n: 1)])
    end

Loads; `atOther()` is 7 (right) and `atW()` is 7 — `W.count` handed a list of `W`s, where nothing provides `Sp` at `W` and the call should be refused. With `provides Sp[T = W]` written beside it, `atW()` is still 7, where `W.count` does not fit `Sp.count` at `T = W` and the default's 0 should run (NNQ1S's *A member that does not fit is no supplier*). With `provides Sp[T = W]` alone the load is refused at `atOther`, "unresolved: Sp[T = Other]" (right).

WHAT IS GOING ON, READ AND NOT YET MEASURED. Which sort a provision is about is `witness_dispatch_carrier`'s answer, at the single carrier parameter `spec_carrier_param` reads: a type parameter some operation of the spec takes a value of — a parameter typed at it, or at an application it HEADS (`m: M[A]`, WI-20261122-CXR5B step 4). `xs: List[T = T]` is headed by `List`, so `Sp` has no carrier parameter, no provision of it is a witness's, and every one is keyed at its provider: dispatch takes `W`'s row for a call at `W`, and the member-fit verdict judges `W.count` at `W`'s rows, where it fits at `T = Other`. `typing::provision_is_own` (DHB0C, decision 6 of docs/design/spec-carrier-set.md) reads `Sp[T = Other]` as a witness's, so the derivation and the dispatch disagree about this row. CXR5B kept the dispatch key apart from decision 6 on purpose: moved to decision 6 it broke wi_rydnv's four rows (`Meters provides Conv[A = Meters, B = String]` is found by `Conv.tag("km")` at `B = String`).

DIRECTION, not decided: the dispatch key counts a type parameter wherever an operation's parameter type mentions it (inside `List[T = T]`), as decision 1 of the design reads a call's operation carrier — the type-vars its signature mentions. About 120 sites read the single carrier parameter (docs/design/spec-carrier-set/readers.md); the corpus is to be measured first. Whether a provision of a spec with no such parameter at all should then be refused at load is the second question.

ACCEPTANCE: the program above is refused at `atW` (nothing provides `Sp` at `W`); with `provides Sp[T = W]` beside it `atW()` answers the default's 0 and `atOther()` 7; wi_rydnv's rows unchanged; backing the fix out fails the new rows; full workspace green via rustland/scripts/test.sh, families green.

REFERENCE: kb/typing/provision.rs `spec_carrier_param`, `declared_type_param_head_vid`; kb/typing/coherence.rs `witness_dispatch_carrier`; kb/typing/sort_carrier.rs `provision_is_own`; kb/typing/signature.rs `member_fits_spec_op`; WI-20261122-CXR5B (step 4, step 13), WI-20261126-DHB0C, WI-20261020-NNQ1S.

