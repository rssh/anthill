## Attributes

- id: WI-20261124-H31PJ-a-binding-at-a-higher-kinded
- created: 2026-11-24T04:08:26Z

- status: Open
- status_agent: user
- status_at: 2026-11-24T04:08:26Z

- acceptance: cargo-test

- tags: typing

## Description

A BINDING AT A HIGHER-KINDED SLOT IS OF THE SLOT'S KIND, WHEREVER IT IS WRITTEN — a provision binding one to a sort of another kind loads today. Found during WI-20261024-XGRKZ (user: file, 2026-11-24).
MEASURED on b1ae8f25e:

  sort Lift[C, F[T]]
    operation lift(c: C, x: F[T = Int64]) -> Int64
  end
  sort Num
    entity num(n: Int64)
    provides Lift[C = Self, F = Int64]
    operation lift(c: Self, x: Int64) -> Int64 = 1
  end

loads clean, though `F` declares a parameter `T` and `Int64` declares none: no `F[T = …]` is a type at `Num`, so no call of `Lift.lift` at `Num` can be typed. `operation go() -> Int64 = Lift.lift(num(n: 1), some(1))` is refused at the CALL, "Lift.lift.dispatch: expected matching impl for per-call bindings, got no impl matches", which names no provision. XGRKZ's `constructor_fits_slot` (kb/typing/carrier.rs) declines to apply such a binding, so no argument is checked against the malformed `Int64[T = Int64]` (it was, before the guard: "expected Int64[T = Int64], got Option[T = Int64]"), and the call keeps the dispatch's refusal every such call had before XGRKZ. A provision no call reaches is refused nowhere. Pinned as it stands: `wi_xgrkz_higher_kinded_dispatch_test::a_binding_of_another_kind_is_not_applied`.
WHAT THE SPEC SAYS: kernel-language §5.2 states the kind for a higher-kinded parameter's DEFAULT only — "for a higher-kinded parameter a sort declaring as many parameters, written bare" — and nothing for a binding of a `provides` or `requires` clause, a type written with the slot, an alias, or a call's bracket at such a slot. §8.1 says a bare sort written into a higher-kinded slot (`F = List`) is the unapplied constructor.
ASKED — A LANGUAGE RULE, the §5.2 wording to be agreed with the user before code: a binding at a higher-kinded slot is of the slot's kind, and one that is not is a load error AT THE BINDING, naming the slot, the parameters it declares and the sort written. To decide in that discussion: (a) "as many" by count or by the slot's parameter names — XGRKZ's head fill and WI-453's grounding apply `F[T = A]` by the slot's labels, so `F = Box` over `sort Box[V]` would be read as `Box[T = A]`, a label `Box` does not declare; (b) which positions the rule covers (a `provides` / `requires` binding, a signature's type, an alias, a call's bracket, a default already); (c) what else may stand there — `Self`, a carrier's own type parameter, an alias of a constructor.
ACCEPTANCE (cargo-test via rustland/scripts/test.sh): the §5.2 rule agreed and written; `Num`'s provision refused at load, at the binding, naming the slot; a binding of the slot's kind loading as before (`Car provides Lift[C = Self, F = Option]`, XGRKZ's rows unmoved); each position the rule names driven; `a_binding_of_another_kind_is_not_applied` moved to the provision's refusal; each back-out measured; the full gate; families green.

