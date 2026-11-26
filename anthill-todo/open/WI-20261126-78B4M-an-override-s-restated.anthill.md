## Attributes

- id: WI-20261126-78B4M-an-override-s-restated
- created: 2026-11-26T07:17:05Z

- status: Open
- status_agent: claude
- status_at: 2026-11-26T07:17:05Z

- acceptance: cargo-test

## Description

An override's restated `requires` that names the spec sort's const never matches the spec's
WHO NEEDS IT. A provider restating a spec operation's `requires`: anthill-traces' model of a spec (its WI-20261122-4067S) restates them, as WI-20261126-JR3AD's rule makes it where an `ensures` restates a variable a `requires` binds, and as a faithful provider does elsewhere. Three of that spec's `requires` clauses name a const of the spec sort.
MEASURED 2026-11-26, the loader through anthill-traces' binary on 2f7cbd4a2:
  namespace probe2
    import anthill.prelude.{Int64}
    sort Spec
      const lim: Int64 = 5
      operation qualified(n: Int64) -> Int64
        requires n < lim
      operation unqualified(n: Int64) -> Int64
        requires n < lim
      operation sub(n: Int64) -> Int64
        requires n - 1 >= 0
    end
    sort Impl
      entity mk
      operation qualified(n: Int64) -> Int64
        requires n < Spec.lim
        = n
      operation unqualified(n: Int64) -> Int64
        requires n < lim
        = n
      operation sub(n: Int64) -> Int64
        requires n - 1 >= 0
        = n
      provides Spec
    end
  end
`sub` loads. `qualified` and `unqualified` are refused: "'probe2.Impl' overrides 'probe2.Spec.qualified' but does not refine it: it strengthens the precondition — the override `requires` a condition the spec operation does not", and the same for `unqualified`.
NOT READ: why. Whether `Spec.lim` written in `Impl` is stored as another term than the spec's `lim` (a member access rather than the reference), whether the const is substituted on one side, and what the bare `lim` in `Impl` resolves to (it loads, so to something).
WHY IT MATTERS. A provider cannot restate a precondition that names a const. It can leave it out, a weaker precondition being a refinement, which is what anthill-traces' model does; but where an `ensures` restates one of that clause's variables, JR3AD's rule then refuses the override, and nothing restates it.
WHAT IS ASKED. A restated clause naming the spec sort's const matches the spec's clause: written qualified (`Spec.lim`) at least. The bare name in the provider either reaches the spec's const or is refused as unknown, not loaded as another thing. The same in the `ensures` leg.
DONE WHEN. (1) The probe's `qualified` loads. (2) Controls refused: another const, and a literal in the const's place. (3) `unqualified` decided and stated, with a row. (4) An `ensures` naming a const, a row. (5) The back-out measured, and said at the rows.

