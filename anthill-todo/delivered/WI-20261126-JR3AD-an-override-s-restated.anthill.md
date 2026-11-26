## Attributes

- id: WI-20261126-JR3AD-an-override-s-restated
- created: 2026-11-26T06:13:59Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-26T06:56:33Z

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

## Changes

### 2026-11-26T06:56:31Z — feedback — user

Implemented 2026-11-26 (71ddb65f2). The override check's contract legs compare each clause up to ONE renaming of the operation's clause variables, shared by both legs and one-to-one (kb/typing/contract_renaming.rs: contract_misfits; views_equal_matching_vars in term_view.rs, of which views_structurally_equal is now the identity case). A clause variable is a flex variable no signature binds (ClauseVariables::of_pair: param, result and effect types, the operations' type parameters, the declaring sorts' parameters); those keep their identity.
THE SEARCH (the ticket's question): not greedy. Backtracking over each owed clause's counterparts, fewest first; a ground clause is settled by its first counterpart without the search. Greedy (each clause's first fitting counterpart kept) refuses a faithful restatement where every clause has two counterparts: spec holds(n, ?a), holds(n, ?b), holds(?b, result) against holds(n, ?x), holds(n, ?y), holds(?x, result), holds(?z, result) (a_restatement_greedy_matching_misses_loads, RED under greedy). Complete within 100 000 attempts (CONTRACT_RENAMING_BUDGET); a pigeonhole (ten same-shape spec clauses, nine in the override) explores every partial correspondence and is REFUSED for running out, with its own reason, never passed; four against three is ruled out within the bound.
REFUSALS: a clause with no counterpart under any renaming, as before (one each, strengthened precondition / weakened postcondition); clauses each restated on their own but under no one renaming ("only under different renamings of their variables"), once; budget exhausted, once.
FOUND BY /code-review, fixed inline: (1) an override that drops a precondition holding a variable its ensures shares (requires holds(n, ?k) ensures holds(result, ?k) restated as ensures holds(result, ?j)) loaded: the renaming must keep a variable a spec requires binds bound by an override requires (keeps_preconditions_variables), refused as a weakened postcondition naming it; a dropped precondition over a variable no ensures shares still loads. (2) PRE-EXISTING: the ensures leg never applied the type-parameter variable alignment the requires leg does, so ensures holds(result, ?q) over b: Box[T = ?q] was refused where the requires form loaded; both legs and the result-binder discharge question now read the aligned clauses. (3) The clause-variable walk is gated on a clause existing, as the result binder is. (4) The result-binder discharge (59CDQ) reads the same comparison, so a return-type mismatch behind a variable-holding clause is named.
DONE: tests/include/wi_jr3ad_contract_clause_renaming_test.rs (wi_tests), 21 rows; each that loads also runs Spec.f through the provider (7). (1) written variable, pattern fillers, two clauses sharing a variable restated sharing one (one clause of two goals, two clauses, other order), across requires and ensures, greedy miss, ten by ten, ensures over a parameter type's variable. (2) Controls refused: shared restated by two (and across legs), variable as constant, constant as variable, not one-to-one within a clause and across clauses, a variable the signature binds not renamed, dropped precondition. (3) requires leg: restated with a variable loads, a variable as a constant refused. (4) Back-outs measured on a binary of the file alone, eight, each listed at the file's head: renaming out -> 14 RED, 7 GREEN by design; signature variables renamed -> 1; one-to-one out -> 3; per-clause renamings -> 5; greedy -> 2; discharge by identity -> 1; precondition binding out -> 1; ensures alignment out -> 1.
SPEC: kernel-language.md §8.7 states the rule (one renaming, one-to-one, signature variables kept, a precondition's variable kept bound, the bounded search), wording approved by the user 2026-11-26.
Gate: workspace 12812 passed, 0 failed; scripts/families.sh green, no verdicts moved. Scaland not run (no Scala touched; acceptance cargo-test).

