## Attributes

- id: WI-20260925-SHED7-inductive-relations-proposal
- created: 2026-09-25T06:38:27Z

- status: Open
- status_agent: user
- status_at: 2026-09-25T06:38:27Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

FILLABLE AND SORTDOMAIN (proposal 067 + proposal 060 §2.3). `anthill.reflect.Fillable` (067) is the INTERFACE a solver requires: ONE rule, `fill(?x)` — fills ?x with a value of T, generating in mode (out), checking in mode (in); a MONOID under `combine` (ordered concatenation) and `empty`. `SortDomain provides Fillable` (060 §2.3): the implementation the loader derives for every sort with constructors, and its `fill` IS the sort's domain. A typed head means `rule p(?x: T) :- body` ≡ `rule p(?x) :- body, SortDomain[T].fill(?x)`. WI-20260911-5G28A's S3b and later steps build on it (user, 2026-09-25). Filed as "inductive relations"; the design settled on Fillable the same day, so the slug is older than the name.

WHY. For a caller's rigid X the type is a name, not a domain, so the domain reaches a clause as a dictionary (060-typedomains, 060-implementation §7.3). MEASURED on 861b3013, S3a's route answers wrongly: `rule el(?x: T) :- true` in `sort Wrap[T]` answers NOTHING for `Wrap.el(7)` and `Wrap.el([red()])`, and undecided for `[1, 2]`, `none()`, `[]` — each should be one definite row. And MiniSat cannot be written over an abstract collection builder: over List it works (tiny-sat) because the program names the shape; a solver written once must require `Fillable` and reach it through the dictionary its caller hands in.

SCOPE, in order (067 §6):
1. 060 §2.3's decisions — what 5G28A's S3b needs: the spec; SortDomain's `fill` derived PER ENTITY (`SortDomain[List] = combine(SortDomain[List.nil], SortDomain[List.cons])`, applied by the loader) and PER FIELD (the sort itself: the recursion; a parameter: a condition of the provision, filled through its SortDomain; a concrete type: must be Fillable); inside a case the recursive fields first, the cases with no recursive field first (WI-743's two rules, measured); a primitive's `fill` is the waiting type check; a condition is resolved when `fill` READS it and a read WAITS while its type is unpinned (`[]` is a `List[?]`); `fill` found through the provisions — SortOpsTable rows for a spec's rule members — replacing S3a's name lookup `typing::sort_domain_relation`; the type-keyed `domain(?x, T)` / `domain_member(?x, T)` / `domain_leaf` retire into it.
2. 067 §5 question 3 (the monoid's home, `combine` at run time), decided with the user.
3. 067 §4's generalization — MiniSat over a collection builder — as the acceptance, once 067 §5 questions 1 (the collection pattern) and 2 (free cells, labelling) are decided with the user.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven): the six `Wrap.el` rows — red(), 7, [red()], [1, 2], none(), [] — one definite answer each; `q(?h) :- Wrap.same([?h], [red()])` (rule same(?a: T, ?b: T) in sort Wrap[T]) answers red, green; S3a's rigid rows (3 / 2); the S3b flips — `Wrap[T = Colour].dom.takeN(5)` = 3, `List[T = Letter]`'s value face `.takeN(5)` = 5; wi_5g28a_rule_head_type_variables_test's pinned rows (answers 1, mismatched 0, two_calls 1, nested_row 1, anylist with no definite row). Controls: the classic-mini examples (tiny-sat 2, alphabet-words 27 / 12 / 100, map-colouring 6).
