## Attributes

- id: WI-20260926-QCJ0B-set-s-operations-have-no
- created: 2026-09-26T09:50:55Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T09:50:55Z

- acceptance: cargo-test

- tags: proposal-068

## Description

`Set`'S OPERATIONS HAVE NO IMPLEMENTATION, SO A COMPARISON OVER THEM IS DECIDED BY SPELLING — `intersection({1,2}, {2}) = {2}` answers false definitely, and `not(...)` over it proves a falsehood.

MEASURED (068's problem section, `main` at fa32695e; sets written as `insert`/`empty` chains; (total, definite)):
  insert(insert(empty(),1),2) = insert(insert(empty(),2),1)   (1, 1)   truth 1
  intersection({1,2}, {2}) = {2}                              (0, 0)   truth 1
  not(intersection({1,2}, {2}) = {2})                         (1, 1)   truth 0 — NAF proves a falsehood
  union({1}, {2}) = {1, 2}                                    (0, 0)   truth 1

WHY. `Set.empty` / `insert` / `union` / `intersection` / `difference` have no body, no host mapping and no provider. `Set`'s equality works by rules that match UNEVALUATED `insert` / `empty` terms in their heads — symbolic algebra, which `reduce_operand` deliberately never dispatches (WI-1057; `is_unreduced_op_call`'s doc). `union` / `intersection` / `difference` have no rule that normalizes them, so a comparison over one falls to the structural compare and answers false. An abstract spec without an implementation is legitimate (068 §2.3, user) — the defect is the DEFINITE verdict.

AFTER 068 STEP A2 (WI-20260926-K4JGC) every comparison over an unquoted `Set` application is UNREDUCED — undecided — including the `insert`/`empty` ones that answer correctly today: the five `wi616_semantic_eq_test` rows WI-1057 measured.

DECIDE WITH THE USER — the library route (068 §2.3):
 (a) an IMPLEMENTATION, so `Set`'s operations run;
 (b) keep the algebra SYMBOLIC and QUOTE it (068 §1.3): its rules match quoted terms, `rule contains(↑insert(?, ?y), ?x)`, which needs WI-189's `↑` bracket and WI-190's holes;
 (c) both — an implementation for values, the quoted algebra for reasoning about terms.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven): the four rows above answer their truth column — or UNDECIDED, never false, where the route leaves an operation unimplemented; after A2 the five wi616 rows answer their truth or undecided, stated per row. CONTROLS: `SortedSet`'s rows unchanged; `Set`'s `eq` / `contains` / `subset` rules' own tests restated for the chosen route.

## Changes

### 2026-09-30T04:03:39Z — feedback — user

ROWS FROM WI-20260926-K4JGC (user, 2026-09-30). (1) THE POPULATION IS WIDER THAN wi616's FIVE: after K4JGC, 18 rows assert UNDECIDED over the insert/empty algebra and are this ticket's acceptance to restore — wi616_semantic_eq_test (Set section, 4 rows + larger_set), wi625_eval_semantic_eq_test (6 eval-side rows: PartialEq.eq/neq and Set.eq over insert chains, refused loudly 'could not be decided'), wi625_sld_eval_bridge_test::typed_op_body_eq_over_set_evaluates_via_bridge (a TYPED op body's eq over Set), wi939_contains_rename_test (set_contains / set_equality — the contains rename's composition row), wi880_reflect_mapping_test::a_nested_host_call_reduces (its algebra guard) and wi_vpewk_host_op_operand_test::symbolic_algebra_at_an_operand_is_still_left_as_data. (2) PRE-EXISTING, measured on main at dc576716 before K4JGC: a rule-body set LITERAL never reaches Set.eq's insert-headed rules — rule l1(1) :- {1, 2} = {2, 1} answers NO solutions (a definite refutation; not(...) over it would prove a falsehood), while kernel-language §8.3 says eq({1,2}, {2,1}) holds. SetLiteral stays a reflect SetLiteral term (convert.rs BuildFrame::SetLiteral), not an insert chain. Whichever route this ticket takes must cover the literal too.

