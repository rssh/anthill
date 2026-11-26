## Attributes

- id: WI-20261126-QG6ZR-a-witness-provision-of-a-spec
- created: 2026-11-26T20:36:18Z

- status: Open
- status_agent: user
- status_at: 2026-11-26T20:36:18Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A WITNESS PROVISION OF A SPEC OF TWO TYPE-VARS, ONE OF WHICH ITS OPERATIONS TAKE ONLY INSIDE ANOTHER TYPE, IS JUDGED AT THE DISPATCH KEY ALONE: over `Sp { sort A = ?  sort B = ?  operation count(xs: List[T = A], b: B) -> Int64 = 0 }`, `W provides Sp[A = Other, B = Int64]` answers `Sp` at `A = W` with `W`'s member written for `Other`, and beside `W`'s own `provides Sp[A = W, B = Int64]` the call at `Other` loses `W`'s member and runs the default. Found by the /code-review of WI-20261126-8F38F, which fixed the one-type-var shape (user, 2026-11-26: file it).

THE PROGRAM, MEASURED on 246f3c962 (`anthill run`, a `main` printing each call):

    sort Sp
      sort A = ?
      sort B = ?
      operation count(xs: List[T = A], b: B) -> Int64 = 0
    end
    sort Other
      entity o(n: Int64)
    end
    sort W
      entity w(n: Int64)
      provides Sp[A = Other, B = Int64]
      operation count(xs: List[T = Other], b: Int64) -> Int64 = 7
    end
    -- Sp.count([Other.o(n: 1)], 1)   and   Sp.count([W.w(n: 1)], 1)

- t1, the program: `7`, `7`. The call at `W` runs `W.count` on a list of `W`s, where nothing provides `Sp` at `A = W`; it should be refused (the same verdict on 88a94552d).
- t2, `provides Sp[A = W, B = Int64]` written beside it: `0`, `0`. The call at `W` is right (`W.count` does not fit at `A = W`, the default runs), and the call at `Other` is WRONG: `W.count` fits at `A = Other` and should answer 7.
- t4, t2 through a generic `G { sort X = ?  requires Sp[A = X, B = Int64]  operation g(xs: List[T = X]) -> Int64 = Sp.count(xs, 1) }`: `G.g([o(n: 1)])` 0 (wrong, 7), `G.g([w(n: 1)])` 0.
- t5, a body-less `count(xs: List[T = A]) -> B` beside a defaulted `cnt(xs: List[T = A]) -> Int64 = 0`, `W` writing both at `Other`: `Sp.cnt([o(n: 1)])` 7 (right), `Sp.cnt([w(n: 1)])` 0, the default at an application no provision is at, where it should be refused (the same verdict on 88a94552d).
- CONTROLS, right: t3, `provides Sp[A = W, B = Int64]` alone, refuses the call at `Other`, "no impl matches — unresolved: Sp[A = Other, B = Int64]"; t6, the body-less `count` of the program, refuses the call at `W`, "`W` provides `Sp` at `Int64`, but no such row answers at the …".

WHAT IS GOING ON, READ AND NOT YET MEASURED. `count` takes `B` bare, so `B` is `Sp`'s dispatch parameter (`typing::spec_carrier_param`, the first rung), and every provision of `Sp` is filed by its binding of `B`: both of `W`'s rows are witness rows at `Int64` (`witness_dispatch_carrier`), although decision 6 of docs/design/spec-carrier-set.md (`provision_is_own`) reads `Sp[A = W, B = Int64]` as `W`'s own. A call fixes `A` only inside the list (`List[T = A]` against `List[T = W]`), and the supplier filter beside the dispatch key reads a call's carriers by argument SORT (`call_arg_carriers` → `known_call_carrier`, `supplier_answers_at`, WI-20260926-Y6ZCD), so `List` and not `W`: nothing checks `A` (t1, t5). Beside two rows at one key the witness member's verdict (WI-20261126-Q1WE9, per carrier witnessed) is reached at one of them, and at `A = W` `W.count` does not fit (t2, t4) — a guess from the verdicts. 8F38F's second rung is for a spec of ONE type-var only: over several, the first type-var mentioned is not where decision 6 reads ownership (`Bag provides Pc2[C = Bag, Element = Int64]` beside `both2(xs: List[T = Element])` was filed as a witness at `Int64`), so it does not reach this shape.

DIRECTION, not decided: the dispatch key cannot say it. A call's supplier is chosen at what the call fixes (decision 1), so the supplier filter and the witness member's verdict read every type-var the call fixes, inside a parameter type too, per application (`SpecApplication`) rather than per dispatch carrier. Moving the witness criterion itself to decision 6 was measured in WI-20261122-CXR5B step 13 to break wi_rydnv's four rows (`Conv.tag("km")` finds `Meters provides Conv[A = Meters, B = String]` at `B = String`).

ACCEPTANCE: t1's call at `W` refused (nothing provides `Sp` at `A = W`); t2 and t4 answer 7 at `Other` and 0 at `W`; t5's `cnt` at `W` refused; t3, t6, wi_rydnv, wi_me8wr and wi_8f38f unchanged; backing the fix out fails the new rows; full workspace green via rustland/scripts/test.sh, families green.

REFERENCE: kb/typing/apply.rs the defaulted arm (`carrier_override_suppliers`, `call_arg_carriers`, `supplier_answers_at`); kb/typing/provision.rs `spec_carrier_param`, `provision_supplier`; kb/typing/call_class.rs `witness_own_op`; kb/typing/coherence.rs `witness_dispatch_carrier`; kb/typing/sort_carrier.rs `provision_is_own`, `SpecApplication`; WI-20261126-8F38F, WI-20261126-Q1WE9, WI-20260926-Y6ZCD, WI-20261122-CXR5B.

