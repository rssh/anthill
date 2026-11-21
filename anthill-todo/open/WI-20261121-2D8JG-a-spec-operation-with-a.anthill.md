## Attributes

- id: WI-20261121-2D8JG-a-spec-operation-with-a
- created: 2026-11-21T18:04:41Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T18:04:41Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SPEC OPERATION WITH A RESOLVER BUILTIN IS READ AS BACKED FOR EVERY PROVIDER, so a provision that writes no member for it loads clean and dies at the call (filed with the user 2026-11-21, beside WI-20261121-TV0PA, whose witness with no `eq` was the equality instance of it). MEASURED on cae41c9cc:

  sort C
    entity c(v: Int64)
    provides Additive[T = C]
    operation neg(a: C) -> C = a
    operation zero() -> C = c(v: 0)
  end
  operation main() -> Int64 = match Additive.add(c(v: 1), c(v: 2))
    case c(v) -> v

loads clean, and `main` fails at run time, `OperationBodyMissing { name: "anthill.prelude.Additive.add" }`. The same with the provision and the two members on a witness (`sort W { provides Additive[T = C]; neg; zero }`). Written with neither `neg` nor `zero`, the load is refused for those two ("backs no operation 'anthill.prelude.Additive.neg'", "… zero") and not for `add`. `stdlib/anthill/prelude/arithmetic.anthill` records it — "omit `add` -> loads clean … the row still owed to WI-879" — and WI-879 is delivered, so the row is owed to no ticket.

CAUSE: provider coverage, `op_backed` (kb/typing/provision.rs), accepts the spec operation itself as backing when `kb.is_builtin(spec_op) || op_has_runnable_body(kb, spec_op)`. `Additive.add` carries `BuiltinTag::Add` (the SLD registry's, which answers for host carriers) and `PartialEq.eq` its builtin, so the check demands nothing of any provider, a composite's own or a witness. For `eq` alone TV0PA added `LoadError::EqualityReachesNoEq` (`eq_derive::equality_reaching_no_eq`).

TO DO: a builtin on a spec operation backs a provider only where it implements that provider's carrier (a host carrier, an `operation_map`); any other provider supplies a member, or the spec's default body backs it. List which spec operations carry a builtin today. Decide whether `EqualityReachesNoEq` becomes an instance of the general rule — it differs: a composite's own provision with no `eq` is given a derived member, and the literal desugaring targets are compared without one (`eq_derive::compared_without_a_member`).

ACCEPTANCE: both programs above refused at load naming `add`; `Int64` / `Float` / `BigInt` arithmetic unchanged; `wi_tv0pa_eq_gives_partial_eq_test` unchanged; a back-out measured; families green; full workspace green via rustland/scripts/test.sh; scaland testFull.

