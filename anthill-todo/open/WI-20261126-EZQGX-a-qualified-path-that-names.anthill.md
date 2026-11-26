## Attributes

- id: WI-20261126-EZQGX-a-qualified-path-that-names
- created: 2026-11-26T09:10:20Z

- status: Open
- status_agent: user
- status_at: 2026-11-26T09:10:20Z

- acceptance: cargo-test

## Description

A qualified path that names nothing in a contract clause loads clean: `requires below(n, Spec.limm)` (`Spec` declares no `limm`) loads on an operation no spec stands over, while the same `Spec.limm` in an operation body is refused.
FOUND by /code-review of WI-20261126-78B4M (86be3521a); pre-existing, and left out of 78B4M on purpose (below).
MEASURED 2026-11-26 on 74d52327c, through the CLI:
  `operation h(n: Int64) -> Int64 requires below(n, Spec.limm) = n`   LOADS (rule below(?a, ?b) :- true; sort Spec declares const lim)
  the same clause on an override of a spec op whose clause is `below(n, lim)`   refused, but only as 'it strengthens the precondition'
  `operation h(n: Int64) -> Int64 = n + Spec.limm`   refused: '`gp3.Spec.limm` names nothing: the sort `gp3.Spec` declares no `limm`. Fix the spelling.' (DottedNameNamesNothing)
  `ensures below(result, nosuchns.lim)`   refused since 78B4M, at the ROOT: its bare `nosuchns` resolves to nothing.
WHY: in a contract clause the chain stays the converter's field_access(Ref(Spec), Ident(limm)). Its selector is a member NAME, which 78B4M's UnresolvedContractName does not judge. 78B4M's qualified rung (Loader::contract_clause_qualified_reference) answers only when the whole name resolves to a const, a constructor or a sort. So a misspelt member of a sort or namespace is a datum no value equals, compared structurally by override refinement.
WHY 78B4M DID NOT TAKE IT: telling 'names nothing' from a legitimate read needs the operation-body ladder's distinctions. A field read on a value prefix (a const, a nullary op, a parameter: `lim.x`, `p.x`) and a LENT member (`Sort.member` a provision lends, which Loader::try_lending_sort_dot reads in a body) both have a prefix that resolves and a whole name that does not. judge_head_dotted_name is the clause-head twin; it reads clause parameters and binders, which a contract clause's operation parameters are not.
WHAT IS ASKED: a dotted path in a contract clause's data slot whose prefix is a sort or a namespace, which is no value and lends no member of that name, and whose whole name resolves to nothing, is refused at load as the body refuses it (DottedNameNamesNothing or its contract twin).
DONE WHEN: (1) the LOADS row above is refused, and the override row refused for the name rather than only as a strengthening; (2) controls load: `p.x` on a parameter, `lim.x` on a const of an entity type, a lent member read qualified, a provides-conversion member (`Numeric.add`-style); (3) the back-out measured and said at the rows.

