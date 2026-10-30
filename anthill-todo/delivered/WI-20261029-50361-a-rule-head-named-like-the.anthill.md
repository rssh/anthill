## Attributes

- id: WI-20261029-50361-a-rule-head-named-like-the
- created: 2026-10-29T22:47:17Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-30T00:07:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RULE HEAD NAMED LIKE THE LAST SEGMENT OF ITS NAMESPACE LANDS ITS CLAUSES ON THE NAMESPACE'S SYMBOL, in silence. Found under WI-20260913-P9QBF while writing a fixture (namespace rstl.cut with rule cut :- … answered no row through rstl.cut.cut). MEASURED on 50518b13 with the CLI: in namespace probe.zed, rule zed :- Link(from: 1, to: 2) loads clean, the query probe.zed.zed is refused ('does not resolve to a known functor') and the query probe.zed answers true; the same for rule zed(?x) :- item(?x) (probe.zed(?x) answers), for fact zed, and for rule zed beside fact zed(2) — two arities on one symbol, the namespace's. From another namespace, import probe.zed.{zed} is refused: unresolved import 'probe.zed.zed'. CONTROL: a DECLARED entity zed(x: Int64) in the same namespace is probe.zed.zed and fact zed(x: 1) lands on it. WHY: a rule head introduces a predicate only when it 'resolves to nothing in the finished program' (kernel-language §5.1, the table of what a namespace entry may introduce; §8.6's ladder); inside probe.zed the bare zed resolves to the namespace itself, so the head introduces nothing and the clause lands on probe.zed — a namespace, which is no relation. THE QUESTION, for the user: is the namespace's own name a head a clause may land on? Either (a) it is not — the namespace is no predicate, so zed introduces probe.zed.zed as in any other namespace; or (b) the head is refused at load, naming the namespace it resolves to and the qualified spelling that introduces. Either way the silent landing goes. CHECK FIRST: whether any loaded file (stdlib, examples, tests) has a clause landing on a namespace symbol today. ACCEPTANCE: the four shapes above and the import get the chosen verdict; the declared-entity control is unchanged; cargo-test green via scripts/test.sh.

## Changes

### 2026-10-30T06:40:54Z — feedback — claude

Second part, decided with the user: a namespace is not a goal. NamespaceAsGoal refuses a goal naming one in a rule body (every proved slot), a constraint, a contract clause, an effect guard and an anthill query pattern (1d71da46). Found on the way and fixed: a query goal slot did not read a dotted paren-less name as the name it spells (not(ns.flag) answered true). Left: a query an operation body runs is not checked.

### 2026-10-30T07:13:41Z — feedback — claude

Third part, decided with the user: an equation whose subject names a namespace or a const is refused (EquationSubjectNamesNoFunction; <=> or a guarded =, in the rule and fact spellings, bare, applied and qualified). Before, rule zed(1) <=> 2 beside namespace probe.zed made zed(1) answer 2. Written inside the namespace, the subject still introduces its own symbol. A sort is left as it is (user: requires Foo is a requirement).

