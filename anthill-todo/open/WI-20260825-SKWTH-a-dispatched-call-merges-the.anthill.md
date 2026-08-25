## Attributes

- id: WI-20260825-SKWTH-a-dispatched-call-merges-the
- created: 2026-08-25T16:14:19Z

- status: Open
- status_agent: claude
- status_at: 2026-08-25T16:14:19Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DISPATCHED CALL MERGES THE IMPL'S EFFECT ROW INTO THE SPEC OP'S INSTEAD OF REPLACING IT, so a carrier that NARROWS a guarded effect to nothing still pays for it at every call the guard cannot discharge. Split out of WI-20260824-VT8CF, which made the shape reachable and pinned it rather than changing it: the question — does a resolved call take the impl's row or the union — is typer semantics affecting every dispatched spec op, and it needs a census rather than an inline repair.

THE GAP, DRIVEN. Measured on the built tree through the loader's verdict, three spellings of ONE division over `Float` operands, differing only in how the name is written:

  operation f(a: Float, b: Float) -> Float = a / b               carries Error[DivisionByZero]
  operation f(a: Float, b: Float) -> Float = Float.div(a, b)     pure
  import anthill.prelude.Float.{div}
  operation f(a: Float, b: Float) -> Float = div(a, b)           pure

IEEE `Float.div` CANNOT RAISE — `1.0 / 0.0` is `+Infinity`, which `wi_vt8cf_division_tower_test::float_division_by_zero_is_still_infinity_not_an_effect` drives — and `Float.div` declares no effect at all. The row the bare `/` carries comes from `anthill.prelude.Divisible.div`, the SPEC operation, whose guarded `Error[DivisionByZero] :- eq(b, 0)` a SYMBOLIC divisor cannot refute. So the author must declare an effect the arithmetic cannot produce, or write a carrier-naming spelling.

WHY THE SPEC OP CARRIES A ROW AT ALL, so a fix does not start by deleting it. An override may NARROW a spec operation's effect row and may not WIDEN it. With no row on `Divisible.div`, the four carriers that declare a guarded `Error[DivisionByZero]` are LOAD ERRORS ("... does not refine it: the override declares effect ... which is not covered by any effect the spec operation declares (effects must not widen)") — measured on `Int64.mod`, `Int64.rem`, `BigInt.mod`, `BigInt.rem` while VT8CF was being built. The spec's row is the PERMISSIVE direction and is correct; what does not happen is the narrowing reaching the CALL.

WHERE IT IS. `typing::dispatched_impl_effects` builds the impl's row and each of its four call sites does `merge_effects_into(kb, &mut effects, &derived)` — a MERGE, onto an `effects` that already holds the spec op's own row from `check_apply_iter`'s op's-own-effect loop. Nothing subtracts. The union is SOUND (an over-approximation never claims an effect is absent), which is why this is a precision ticket and not a correctness one.

NOT SPECIFIC TO DIVISION, and that is the reason it is filed rather than patched. Every dispatched spec op with a guarded effect behaves this way; division is merely the first place a bare operator made it easy to hit, because WI-20260824-VT8CF repointed `/` at a spec operation. A change here reaches `Iterable.map`, `Stream.splitFirst` and every other dispatched member — the population to census before touching it.

WHAT A FIX HAS TO DECIDE, none costed:
  (a) where the dispatch resolves UNIQUELY to a concrete impl, take the impl's row INSTEAD of the spec op's. Most precise, and the largest blast radius: a spec op whose own row carries something the impl's does not mention would lose it, so the census is "which dispatched calls today rely on the spec op's row surviving".
  (b) subtract at the merge — drop from the spec op's contribution any label the resolved impl's row does not carry. Narrower than (a) and needs the carrier-aware label comparison `drop_refuted_guarded_labels` already uses (`resolved_labels_equal`).
  (c) leave it, and make the DIAGNOSTIC say so: an "undeclared effect" naming a guarded row that the resolved carrier narrows away is currently indistinguishable from a real one, and a message that named the carrier would make the wart self-explaining at no semantic risk.
  (d) accept and document at the spec's effects section.

CONTROL, when it is fixed: `wi_vt8cf_division_tower_test::a_bare_float_division_over_approximates_its_effect_row` RECORDS the gap — it asserts that the bare `/` form fails to load and the `Float.div(a, b)` form loads clean, i.e. the SEPARATION rather than a value. That row inverts when this closes, and its inversion is the measurement. Do NOT restate it as "the bare form loads": that passes under (a), (b) AND a change that simply deleted the spec op's guarded row, which is the one repair that must not be made — it re-breaks the four carriers named above.

ACCEPTANCE: a bare `a / b` over `Float` operands loads with an EMPTY effect row, `Int64.mod`/`Int64.rem`/`BigInt.mod`/`BigInt.rem` still load (the widening check still passes), `n / 0` still carries the effect, and full workspace green via rustland/scripts/test.sh.

