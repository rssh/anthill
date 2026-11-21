## Attributes

- id: WI-20261121-G8E02-a-failed-goal-says-nothing
- created: 2026-11-21T13:06:45Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T13:06:45Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A FAILED GOAL SAYS NOTHING ABOUT WHY: `query` answers `no solutions` and names no subgoal, so a specification that checks a value has to restate the names of its own rules to report which one fails.

FOUND while modelling a shop's state as a value (the setting of WI-20261115-32WQJ). Each invariant of the state is a named rule over it (`rule product_has_positive_price(ShopState(products: ?ps)) :- (forall ?p in ?ps: ?p.price > 0)`), and validity is their conjunction. A test of a bad state must check that the state fails in the rule it is meant to break, and in no other. The query gives no such answer, so the model adds `violation(?s, "product_has_positive_price") :- !product_has_positive_price(?s)` for each of its 34 invariants: one line per rule that only repeats the rule's name as a string. No KB constraint is involved: the state is a value, never a fact.

MEASURED on a4fb58dc9 (debug CLI of 2026-11-21):
  1 `good(1)` over `rule good(?x) :- pos(?x), big(?x), even(?x)` (`pos`: `?x > 0`, `big`: `?x > 5`, `even`: `?x % 2 = 0`): `no solutions`. `big(1)` and `even(1)` fail; nothing says so.
  2 `all_big([7, 3, 9])` over `rule all_big(?xs) :- (forall ?y in ?xs: ?y > 5)`: `no solutions`. The element 3 breaks it; nothing says so.
  3 `query` has no option that explains a failure (`--mode`, `--match`, `--max-depth`, `--max-steps`), and the resolver has no trace switch.
  4 control: a conditional answer already names what is undecided, as its residual.

PROPOSED: an explanation of a failed goal, `query --explain`.
- It is a tree of frames, each named by its goal as instantiated, so a rule call is named by its head: `product_has_positive_price(ShopState(…))`. A frame also shows the rule's description where it has one. A frame that would print a large value elides it past a size limit.
- A rule call: each clause tried, and why its body failed.
- A conjunction: the first conjunct that fails under the bindings of the ones before it. After a failure, the explanation goes on with every later conjunct that is ground under those bindings, so a conjunction of independent checks (validity as a conjunction of invariants) reports every one that fails, not only the first.
- A bounded `forall`: each element whose body fails, as the binding of the binder. A bounded `some`: that no element satisfies the body.
- A negation `!G` that fails: the answer of `G`.
- A comparison or other builtin: its evaluated operands (`3 > 5`).
- A call into the stdlib is one frame, not its body. A depth limit bounds the tree.
- `--explain-format json` prints the same tree for a test harness.
- DECIDE WITH THE USER: whether the explanation goes on past the first failure as above; whether an in-language form is wanted as well (a reflective relation a rule can ask, so a test asserts the failing rule by its symbol rather than parsing output).

RELATED: WI-20261121-MVQP8 (generated labels for unlabeled constraints). `check` could print the same explanation for a violated constraint's consequent.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven):
- row 1 explains `good(1)` by `big(1)` (`1 > 5`) and `even(1)` (`1 % 2 = 0`); `pos(1)` is not listed;
- row 2 explains `all_big([7, 3, 9])` by `?y = 3` (`3 > 5`);
- a rule with two clauses that both fail lists both;
- `!q` that fails where `q` holds shows `q`'s answer;
- the JSON form carries the same tree as the text form;
- a successful query, and a conditional one, print as they do today;
- back-out: without the explanation, rows 1 and 2 print only `no solutions`.

