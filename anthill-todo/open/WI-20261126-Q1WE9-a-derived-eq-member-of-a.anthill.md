## Attributes

- id: WI-20261126-Q1WE9-a-derived-eq-member-of-a
- created: 2026-11-26T15:33:09Z

- status: Open
- status_agent: user
- status_at: 2026-11-26T15:33:09Z

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

