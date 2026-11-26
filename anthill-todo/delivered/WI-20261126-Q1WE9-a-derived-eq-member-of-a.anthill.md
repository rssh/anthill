## Attributes

- id: WI-20261126-Q1WE9-a-derived-eq-member-of-a
- created: 2026-11-26T15:33:09Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-26T17:04:04Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DERIVED `eq` MEMBER OF A WITNESS SORT IS COUNTED AS A SUPPLIER OF THE SORT IT WITNESSES: a call at the witnessed sort is refused as an ambiguous dispatch, though the witness binds that sort's `eq` and its derived member does not take the sort's values. Found by WI-20261102-YX17K's review (user, 2026-11-26: file it).

THE PROGRAM, MEASURED (one `load_all`, OneShot, over the three sources; refused on 2c1ef430f, the tree before YX17K, and on 62806cafa, after it):

    namespace test.le.total
      import anthill.prelude.{Int64}
      sort Point
        entity point(x: Int64, y: Int64)
      end
    end

    namespace test.le.total.Point
      import anthill.prelude.{Eq, PartialEq, Bool, Int64}
      sort Other
        entity o(n: Int64)
        operation oeq(a: Other, b: Other) -> Bool = true
      end
      provides PartialEq[T = Other, eq = Other.oeq]
      provides Eq[T = Other]
    end

    namespace test.le.onecheck
      import anthill.prelude.{Bool}
      sort Check
        import anthill.prelude.PartialEq.{eq}
        operation check() -> Bool = eq(test.le.total.Point.Other.o(n: 1), test.le.total.Point.Other.o(n: 2))
      end
    end

The load is refused at the call in `check`: `AmbiguousSpecOpDispatch { op: anthill.prelude.PartialEq.eq, carrier: test.le.total.Point.Other, candidates: ["witness sort 'test.le.total.Point' (supplying 'test.le.total.Point.eq')", "witness sort 'test.le.total.Point' (supplying 'test.le.total.Point.Other.oeq')"] }`.

WHAT IS GOING ON, READ AND NOT YET MEASURED. `Point` writes nothing about its own equality, so it derives `PartialEq`+`Eq` and the derived member `Point.eq(a: Point, b: Point)` (`eq_derive::derived_eq_member_source`). Its two provisions name `Other`, which makes `Point` a WITNESS sort for `Other`, and the witness route of the eq-dispatch index (WI-837: a witness sort's own `eq`) then reads `Point.eq` as a supplier of `Other`'s `eq`, beside the `eq = Other.oeq` the provision binds. `Point.eq` takes `Point`s, so it can answer no call at `Other`. A written member is held to fitting the carrier it supplies (WI-NNQ1S, `wi_nnq1s_member_supplies_only_where_it_fits_test`); whether the derived member escapes that check, or the binding should simply decide, is the first thing to find out.

DIRECTION, not decided: a derived member of a witness supplies only the witness's own carrier, the one its operands are typed by, so the binding answers `Other`; or the witness route reads the derived member not at all. The written-member twin, `Point` with a written `eq(a: Point, b: Point)` and the same provisions, has not been tried and says which of the two is the rule.

WHY IT SURFACED: YX17K's row `wi_szkv7_later_equality_test::an_earlier_sort_witnessing_a_later_ones_equality_is_accepted` makes `Point` this witness in a later load, and could not drive `eq` at `Other` for this reason; its doc says so. Once this is fixed, that row should call `eq(o(n: 1), o(n: 2))` and expect `true` (the bound `oeq`).

ACCEPTANCE: the program above loads, and `check()` answers `true`; the written-member twin's verdict is measured and stated; the YX17K row drives `eq` at `Other`; backing the fix out fails the new row; full workspace green via rustland/scripts/test.sh, families green.

REFERENCE: kb/load.rs `EqDispatchIndex` / `build_eq_dispatch_index` (the witness route), kb/eq_derive.rs `derived_eq_member_source`, `is_eq_boundary`; WI-837, WI-NNQ1S, WI-20261102-YX17K.

## Changes

### 2026-11-26T16:54:54Z — feedback — user

WIDER THAN FILED, MEASURED 2026-11-26 (one load each of `Point`, `Point` witnessing `Other`'s `PartialEq`+`Eq`, and a probe calling `eq` at `Other`): not specific to a DERIVED member. (a) derived `Point.eq` + `eq = Other.oeq` bound: ambiguous at the call (as filed); (b) written `Point.eq(a: Point, b: Point)` + the binding: ambiguous, at load too ("ambiguous semantic equality"); (c) derived, nothing bound: loaded, answers matching structural equality; (d)/(e) written, nothing bound: LOADED, and with `Point.eq = true`, `eq(o(n: 1), o(n: 2))` answered `true` — `Point.eq` handed `Other`'s values, silently, and TV0PA's no-`eq` refusal did not fire because the member read as answering. CAUSE: the witness route (`provision_supplier`'s witness leg, `spec_op_suppliers_of_provider`'s seed) took the provider's own member through `carrier_own_op`, whose NNQ1S fit verdict is the PROVIDER's, reached "at one of" its provisions — and `Point.eq` fits at `Point`.

DECIDED WITH THE USER (option 1): a witness's own member supplies a carrier it witnesses only where it fits there, at the witness's provision for that carrier — kernel-language §8.4, *A member that does not fit is no supplier*, one sentence added. DONE: `typing::record_members_that_supply_nothing` also judges each witness provision (`member_fits_at`, factored out of `member_fits_spec_op`), filing `(witness, spec op, carrier)` misfits on the sort-ops table (`witness_supplies_nothing`); `typing::witness_own_op` reads it, and both witness readers go through it. A derived member needs no rule of its own: it is typed by its composite and the comparison refuses it at another carrier's provision. `LoadError::EqualityReachesNoEq` gains `passed_over`, the witness member it passed over, named in the refusal ("none is written that takes `Other`'s values (`Point.eq` is the witness's own equality and does not)"). AFTER: (a), (b) load, `Other`'s `eq` the bound `oeq`, `Point`'s its own; (c), (d), (e) refused, `EqualityReachesNoEq`.

ROWS: `tests/include/wi_q1we9_witness_member_fit_test.rs`, 5 — both bindings answer (derived, written member beside), both no-binding programs refused naming the member, and the control (a witness whose `eq` takes the witnessed values still answers; passes either way by design). `wi_szkv7_later_equality_test::an_earlier_sort_witnessing_a_later_ones_equality_is_accepted` now drives `eq` at `Other`. BACK-OUTS, MEASURED: the witness verdict left empty fails the four rows and the szkv7 one; `passed_over` left empty fails the two refusal rows. The new rows pass under ANTHILL_TEST_FRESH_LOAD=1 too. Cost, release build: a stdlib load's pass ~10 ms either way; a later load's two passes ~220 -> ~270 µs each.

LEFT (read, not measured): the reverse direction — `member_fits_spec_op` still counts a provider's witness provisions toward its OWN carrier's verdict, so a witness `W` with values whose `eq(a: C, b: C)` fits at `W provides PartialEq[T = C]` may be taken as `W`'s own equality.

### 2026-11-26T17:04:02Z — feedback — user

Delivered in a21d3e229 — the change, rows and measurements are the feedback above. Gate 12875 / 0; families green; scaland testFull 811+51+1 / 0; the new rows also pass under ANTHILL_TEST_FRESH_LOAD=1. Left, not ticketed: the reverse direction (a witness's member fitting its witness provision still counts toward the provider's OWN equality; read, not measured).

