## Attributes

- id: WI-20261126-DHB0C-a-witness-s-eq-written-for-the
- created: 2026-11-26T17:11:07Z

- status: Open
- status_agent: user
- status_at: 2026-11-26T17:11:07Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A WITNESS'S `eq` WRITTEN FOR THE SORT IT WITNESSES COUNTS AS ITS OWN EQUALITY: a sort with values that witnesses another's equality through `operation eq(a: Other, b: Other)` is read as supplying its OWN `eq`, so its equality is not derived and a comparison of two of its values is refused at load. The reverse of WI-20261126-Q1WE9 (user, 2026-11-26: file it).

THE PROGRAM, MEASURED (one `load_all`; the same verdict on 2c1ef430f, before WI-20261102-YX17K, and on a21d3e229, after Q1WE9):

    namespace test.rev
      import anthill.prelude.{Eq, PartialEq, Int64, Bool}
      sort Other
        entity o(n: Int64)
      end
      sort W
        entity w(n: Int64)
        provides PartialEq[T = Other]
        provides Eq[T = Other]
        operation eq(a: Other, b: Other) -> Bool = true
      end
      sort Check
        import anthill.prelude.PartialEq.{eq}
        operation ws() -> Bool = eq(W.w(n: 1), W.w(n: 2))
      end
    end

Refused at the call in `ws`: `type mismatch in anthill.prelude.PartialEq.eq.dispatch: … no impl matches — unresolved: anthill.prelude.PartialEq[T = test.rev.W]`. `W` provides no `PartialEq` of its own.

THE CONTROL, MEASURED: the same `W` with its member named `oeq` and bound by the provision (`provides PartialEq[T = Other, eq = W.oeq]`) loads, and `W`'s equality is derived — `eq(w(n: 1), w(n: 2))` is `false`, `eq(w(n: 1), w(n: 1))` is `true` — while `Other`'s is `oeq` (`eq(o(n: 1), o(n: 2))` is `true`). So it is the member's NAME that takes `W`'s equality away, not the witness.

WHAT IS GOING ON, READ AND NOT YET MEASURED. `typing::member_fits_spec_op` judges `W.eq` "at one of" the provisions that dispatch to `W` — its witness provisions among them — and it fits at `PartialEq[T = Other]`. So the NNQ1S verdict says `W`'s own member supplies `PartialEq.eq`, `carrier_own_op(W, eq)` returns it, the eq-dispatch index keys `W` to it, and `eq_derive::is_eq_boundary` makes `W` a boundary: its `eq` is "the author's", and nothing is derived for it. Q1WE9 made the witness route judge the member at the witness's provision for the witnessed sort; this is the same verdict for the provider's OWN carrier, still reached at any provision.

DIRECTION, not decided: the provider's own route judges its member at the provisions about the provider itself (and at the carrier where there are none), not at its witness provisions — those are the per-carrier witness verdict's since Q1WE9. Then `W.eq(a: Other, b: Other)` supplies `W` nothing, `W` is no boundary, its equality is derived as the control's is, and `Other`'s `eq` is `W.eq`. Whether a sort whose only `eq` is for another sort should instead be refused at load (as NNQ1S refuses an `eq` that does not fit beside the carrier's own provision) is the decision to make first: kernel-language §8.4, *A member that does not fit is no supplier*, states the "at one of" reading for a carrier's member and would change.

ACCEPTANCE: the program above loads and `ws()` answers `false` (or is refused by a stated rule, if that is the decision); `Other`'s `eq` is `W.eq`; the control's verdicts unchanged; backing the fix out fails the new rows; §8.4 says which provisions a carrier's own member is judged at; full workspace green via rustland/scripts/test.sh, families green.

REFERENCE: kb/typing/signature.rs `record_members_that_supply_nothing`, `member_fits_spec_op`, `member_fits_at`; kb/typing/call_class.rs `carrier_own_op`, `witness_own_op`; kb/eq_derive.rs `is_eq_boundary`; WI-20261126-Q1WE9, WI-NNQ1S, WI-837.

