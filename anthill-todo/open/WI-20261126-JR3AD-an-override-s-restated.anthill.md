## Attributes

- id: WI-20261126-JR3AD-an-override-s-restated
- created: 2026-11-26T06:13:59Z

- status: Open
- status_agent: claude
- status_at: 2026-11-26T06:13:59Z

- acceptance: cargo-test

## Description

An override's restated contract clause that holds a variable never matches the spec's: compare the clauses up to a renaming of the operation's variables
WHO NEEDS IT. anthill-traces (private) runs a hand-written model of a spec sort through the interpreter (its WI-20261122-4067S): a carrier that `provides` the spec, with bodies. The spec's operations carry `ensures`, which a provider must restate (an override that leaves one out is refused as weakening the postcondition). Many of its clauses hold a variable: a written `?x` shared by two clauses of the operation (`ensures has(s, C(id: ?c, owner: owner)), p(s, result, ?c)`), or the loader's fillers for the fields an entity pattern leaves out (`ensures has(result, C(id: x, status: DONE))`). Measured on that spec: 20 restated clauses across its nine state-changing operations are refused, every one of them holding a variable, and no other clause is; no provider of it can load.
WHAT HAPPENS. Read from code (33aca57e7): the contract legs of the override check (kb/typing/signature.rs:3954-4007) compare each spec `ensures` clause with the override's by `views_structurally_equal`, after `substitute_clause(kb, c, &align)`, which maps the parameters and the `result` binder. Nothing maps variables. A variable is one per written `?name` per operation and a filler is fresh per pattern, so the override's clause holds variables of its own and is never structurally equal to the spec's. The `requires` leg compares the same way (an override restating a `requires` clause with a variable would be refused as strengthening the precondition: read, not measured).
MEASURED 2026-11-26, the loader through anthill-traces' binary, built on 2eed52a9e:
  namespace probe
    import anthill.prelude.{Int64}
    entity Pt(x: Int64, y: Int64)
    rule holds(?a, ?b) :- true
    sort Spec
      operation ground(n: Int64) -> Int64
        ensures holds(result, n)
      operation named(n: Int64) -> Int64
        ensures holds(result, ?k)
      operation filled(n: Int64) -> Pt
        ensures holds(result, Pt(x: n))
    end
    sort Impl
      entity mk
      operation ground(n: Int64) -> Int64
        ensures holds(result, n)
        = n
      operation named(n: Int64) -> Int64
        ensures holds(result, ?k)
        = n
      operation filled(n: Int64) -> Pt
        ensures holds(result, Pt(x: n))
        = Pt(x: n, y: 0)
      provides Spec
    end
  end
`ground` loads. `named` and `filled` are refused: "'probe.Impl' overrides 'probe.Spec.named' but does not refine it: it weakens the postcondition — the override does not `ensure` a condition the spec operation promises", and the same for `filled`.
WHY IT MATTERS. As with the `result` binder before its alignment (WI-347's C8 rows, wi347_override_refinement_test.rs:265-305): a spec operation whose `ensures` holds a variable has no possible provider, however faithfully it is restated.
WHAT IS ASKED. Compare the clauses up to a renaming of variables, and ONE renaming for the whole operation, a spec variable corresponding to the same override variable in every clause: a written `?x` is shared by every clause of the operation that writes it, `requires` and `ensures` alike, and restating two clauses that share it with two unrelated variables says less (`exists x. p(x) and q(x)` against `exists x. p(x) and exists y. q(y)`). The loader's fillers, fresh per pattern, are covered by the same renaming. The check stays syntactic: a renaming is one-to-one, so a clause logically stronger but written otherwise (`p(?x, ?x)` for `p(?a, ?b)`) is still refused, as any other is. Where several renamings fit, finding one is a search; whether a greedy one (the spec's clauses in order, each extending the renaming) is enough, and what it misses, is to be stated.
DONE WHEN. (1) Each loads: an `ensures` restated with a written variable; one with a pattern's fillers; two clauses sharing a variable, restated sharing one. (2) Controls refused: the two shared clauses restated with two unrelated variables; a variable restated as a constant, and a constant as a variable; a renaming that is not one-to-one. (3) The `requires` leg read the same way, with a row. (4) The back-out measured, and said at the rows: which fail without the renaming, and which pass either way by design.

