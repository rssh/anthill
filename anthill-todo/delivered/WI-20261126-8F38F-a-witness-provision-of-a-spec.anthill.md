## Attributes

- id: WI-20261126-8F38F-a-witness-provision-of-a-spec
- created: 2026-11-26T19:20:18Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-26T20:33:25Z

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

## Changes

### 2026-11-26T20:33:10Z — feedback — user

DONE (f8afae506; kernel-language §5.1 wording approved by the user 2026-11-26): `spec_carrier_param` — the one type-var dispatch, the witness criterion (`witness_dispatch_carrier`), the coherence grouping and the supplier walks read — has a second rung: a spec with a dictionary of ONE type-var that no operation takes has it where a parameter's type MENTIONS it, inside an application, an arrow, an option (`count(xs: List[T = T])`). So `W provides Sp[T = Other]` is a witness at `Other`, as decision 6 (`provision_is_own`) already read it. MEASURED (the ticket's three programs): refused at `atW`, "no impl matches — unresolved: Sp[T = W]"; beside `provides Sp[T = W]` `atW()` 0 and `atOther()` 7; `provides Sp[T = W]` alone refused at `atOther` (unchanged). The same through a `requires` dictionary (`G.g([w(n: 1)])` 7 → 0), and the arrow and `Option` shapes at `W` (7 → refused). wi_rydnv unchanged.

THE CORPUS, MEASURED (a census of the sorts whose answer moved): with the rung for every spec, 6 stdlib sorts moved — `Stream`, `FiniteStream`, `LogicalStream`, `Option` (self-representing) and `MappedStreamFinite`, `FilteredStreamFinite` (provider sorts of 5 type-vars). Gated to one type-var and a spec that is not self-representing: no stdlib sort moves, 30 fixture sorts do, anthill-core green. Why each gate: over several type-vars the first mentioned is not where decision 6 reads ownership (`Bag provides Pc2[C = Bag, Element = Int64]` beside `both2(xs: List[T = Element])` filed as a witness at `Int64`; wi_me8wr's refusal moves); for a self-representing spec the element is filed as the carrier (WI-1076), 13 rows of eight files fail. Decision 3's "takes" (`spec_taken_type_vars`) is unchanged. THE SECOND QUESTION (refuse a provision of a spec with no such parameter): its defaulted shape (`Tag { sort T; name() -> Int64 = 0 }` with a witness overriding `name`) is already refused at load (CBRD2); not taken further.

ROWS: `tests/include/wi_8f38f_witness_at_a_mentioned_type_var_test.rs`, 7. BACK-OUT, MEASURED: the rung off fails four, the three controls pass either way.

/code-review (high): one doc overclaim fixed (the two readers agree only for a binding headed by a sort). LEFT, not ticketed: (1) a spec of TWO type-vars keeps the defect in the defaulted route, before and after — `Sp { sort A; sort B; count(xs: List[T = A], b: B) -> Int64 = 0 }` with `W provides Sp[A = Other, B = Int64]` answers `Sp.count([w(n: 1)], 1)` 7 (its dispatch key is `B`, and nothing checks `A`), and a defaulted `cnt(xs: List[T = A]) = 0` beside a body-less op answers 0 at `A = W`, where nothing provides `Sp`; (2) the one-type-var gate is pinned by wi_me8wr's refusal text alone — no wrong answer was found with it dropped. Gate 12897 / 0; families green; scaland testFull 811 + 51 (2 skipped) + 1.

### 2026-11-26T20:33:27Z — feedback — user

Delivered in f8afae506 — the change, rows and measurements are the feedback above. Gate 12897 / 0; families green; scaland testFull 811 + 51 (2 skipped) + 1. Left, not ticketed: a spec of two type-vars keeps the defect in the defaulted route (`count(xs: List[T = A], b: B) = 0` answers 7 at `A = W`); the one-type-var gate is pinned by a refusal text alone.

