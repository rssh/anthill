## Attributes

- id: WI-20260905-175SD-a-witness-that-reaches-the-per
- created: 2026-09-05T05:42:03Z

- status: Open
- status_agent: user
- status_at: 2026-09-05T05:42:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a witness that reaches the per-binding descent with a non-covariant parameter

WHAT IS MISSING IS A WITNESS, NOT A GATE — which is why this is a TEST ticket. The gate
is three lines and was WRITTEN, MEASURED AND REVERTED under WI-20260904-50B2K; the
measurement is recorded at `nominal_head_mismatch`'s descent loop and at
`HeadPosition::Nested`. Nothing here needs re-deriving, only driving.

THE EXPOSURE. `nominal_head_mismatch`'s per-binding descent pairs `actual`'s binding with
`declared`'s AT THE SAME LABEL and recurses — a COVARIANT reading, and the only one it
has. It does not call [`declared_variance`], which has existed since WI-293. A verdict
claimed there is wrong for a parameter declared CONTRAVARIANT.

WHY THE GATE WAS REVERTED RATHER THAN SHIPPED, and both halves are measured:

  INVARIANT IS THE DEFAULT AND MUST NOT ASK BOTH DIRECTIONS. Invariance does require both,
  but the predicates under this descent are ONE-DIRECTIONAL BY CONSTRUCTION —
  WI-20260904-50B2K's fourth edit made `callable_against_callable_free` so, after measuring
  that the reverse pairing has legitimate coercions (an eta-lift, a zero-arg thunk). So the
  swapped call DECIDES where the design says WITHHOLD. Driven:

      take[X](l: Holder[T = Function[A = X, B = Int64]], w: X)  given  holder(v: 1)
        -> "expected Holder[T = Function[A = ?X, B = Int64]], got Holder[T = Int64]"
      the SAME program over `List` (covariant) LOADS — WI-836's own row

  Every sort with no variance fact is `Invariant`, so that turned a loading program into a
  refusal the moment its container was a user sort. Invariant must ask the un-swapped
  direction, i.e. behave exactly as covariant does here.

  CONTRAVARIANT IS THEN THE ONLY ARM THAT COULD CHANGE AN ANSWER, and I could not reach it.
  `Contravariant(sort: Function, param: A)` is the stdlib's ONLY contravariant fact
  (`stdlib/anthill/reflect/typing.anthill`), so the descent must run with `d_base =
  Function` — a `Function[…]` on BOTH sides, agreeing at the head, reaching the non-ground
  branch. Probed over the whole `wi_tests` binary:

      Invariant       145,858 reaches        Contravariant   0
      Covariant        50,480 reaches        Bivariant       0

  BIVARIANT IS UNREACHABLE BY CONSTRUCTION: it needs `Covariant` AND `Contravariant` on one
  parameter, and nothing asserts both.

TWO ATTEMPTS THAT DID NOT REACH IT, recorded so they are not re-invented. Both LOADED under
every reading, so neither distinguishes anything:

    operation take[X](l: List[T = Function[A = red,   B = X]], w: X) -> Int64
      given a  List[T = Function[A = Color, B = Int64]]
    the same with `Color` and `red` exchanged

THE FIRST QUESTION IS WHETHER SUCH A PROGRAM EXISTS AT ALL, and the answer decides what
this ticket delivers:

  * IF IT DOES — that program is the witness. Ship the three-line gate WITH it: covariant
    asks the pair as written, contravariant SWAPPED, invariant the un-swapped direction
    (see above), bivariant withholds. The row must FAIL under the covariant-only reading,
    which is the control the reverted change never had.
  * IF IT DOES NOT — say why, structurally. The likely reason is that a `Function` /
    `arrow` pair is DECIDED EARLIER, by `arrow_compatible` / `arrow_function_compatible`
    (which hardcode the same variance) or by the head verdict, so it never reaches the
    NOMINAL descent. That is a closure by construction rather than a gate, and it belongs
    at `HeadPosition::Nested`, replacing the prose that currently states the exposure as
    open.

COVARIANCE IS ALSO NOT DIRECTLY ASSERTED HERE, and it is worth one row of the same test.
The descent reaches Covariant parameters 50,480 times, but nothing says the reading is
covariant BECAUSE the parameter is declared so — a test that passes under
"covariant-everywhere" measures nothing. The probe found the axis is live: of the decided
reaches, TWO answer `cov=false, con=true` — the two directions genuinely disagree at this
site, and the covariant one is what ships. A row that pins that pairing is assertable today
and is this ticket's cheap half.

CONTROLS THIS OWES, both green today and both must stay green:
  * `wi836…::a_callback_slot_nested_in_a_sort_application_still_withholds` — the row the
    reverted `Invariant` arm broke. Any gate must keep it loading, over `List` AND over a
    user sort.
  * `wi_cbrsw_permission_effect_test::a_denial_of_a_sub_capability_does_not_forbid_the_
    super_capability` — the row that made `callable_against_callable_free` one-directional
    in the first place ("expected () -> Unit, got Unit" on a program that must load clean).

NOT A REGRESSION AND NOT URGENT: the descent's reading has always been covariant-only, and
the corpus contains no program that notices. This ticket exists because a hazard whose only
record is a comment rots — /code-review asked for an owner twice.