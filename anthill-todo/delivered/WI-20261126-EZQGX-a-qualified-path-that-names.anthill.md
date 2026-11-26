## Attributes

- id: WI-20261126-EZQGX-a-qualified-path-that-names
- created: 2026-11-26T09:10:20Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-26T09:45:31Z

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

## Changes

### 2026-11-26T09:45:29Z — feedback — user

Implemented 2026-11-26 (76196564c). FIX (kb/load.rs): Loader::refuse_contract_clause_path_naming_nothing, asked beside 78B4M's qualified rung on each node of a contract clause's DATA slot. A minted dotted chain rooted at no binding is refused as LoadError::DottedNameNamesNothing — the wording an operation body's Spec.limm gets — when its whole name has no answer (qualified_name_resolves), no prefix is a value (name_has_value_prefix) or read through a requirement's name, its immediate prefix resolves, and that prefix is a namespace or a sort declaring its members. The last two are the typer's own predicates (typing::namespace_only, typing::declares_its_members, made pub(crate)), so the clause and the body agree. Not refused: a member a provision of the sort lends (sort_lending_member); a constructor's field; a type parameter's or a requirement's member. A prefix that does not resolve is left to the inner node (a longer path is reported once at its missing segment) or to 78B4M's bare-name refusal (the first segment). A type alias that owns no members is read as its sort (alias_head), as the body reads it: CA.T loads, CA.Tt is refused naming P.
MEASURED that the parameter-rooted read is no hazard: p.x beside a namespace p with a const x stays the field read, the parameter shadowing the root.
DONE: tests/include/wi_ezqgx_contract_clause_path_names_nothing_test.rs (wi_tests), 13 rows. (1) The ticket's row is refused on a plain operation, located at the name; a namespace's member; the ensures list; the override row refused for the name beside the strengthening; Spec.nosuch.deep once, at Spec.nosuch; a comparison over it once; a first segment naming nothing once (78B4M's refusal). An aliased sort's member and an internal member are refused (below). (2) Controls load and run: p.x, result.x, Spec.origin.x, Spec.lim, inner.k; a lent member (A.viaDefault under provides Mk); CA.T; R.zero, F.zero, Colour.red.shade, Numeric.add. (3) Back-outs measured on a binary of this file and 78B4M's, each listed at the file's head: refusal out -> 7 RED, controls and 3 rows GREEN by design (the comparison row: a comparison's operand is typed as a projection and was refused already, so it pins one report); lending exemption out -> 1; alias judged among its own members -> 2; every alias let through -> 1; hidden name let through -> 1; unresolved prefix reported at the outer node -> 2.
/code-review (xhigh, 5 findings): fixed — every type alias was let through (CA.Tt loaded), now read as its sort; a member internal hides loaded in a contract clause while the body refuses it, now ForbiddenInternalAccess as a clause head's is. Not reproduced — a longer path inside a comparison reported twice (one report each, measured). PRE-EXISTING, not fixed: a qualified name naming nothing in a GOAL slot (requires Spec.limm) loads — the goal check sees the declared field_access functor; a compound term whose functor names nothing in a contract clause argument (requires n < nosuch(1), Spec.limm()) loads — a rule body and a head refuse it, a contract clause has no twin.
SPEC: kernel-language.md §5.4 states it (refused naming the missing segment; internal as that access; an alias read as its sort; what is no such name).
Gate: workspace 12850 passed, 0 failed; scripts/families.sh green, no verdicts moved. Scaland not run (no Scala touched; acceptance cargo-test).

