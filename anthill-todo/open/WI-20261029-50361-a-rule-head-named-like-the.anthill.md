## Attributes

- id: WI-20261029-50361-a-rule-head-named-like-the
- created: 2026-10-29T22:47:17Z

- status: Open
- status_agent: claude
- status_at: 2026-10-29T22:47:17Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RULE HEAD NAMED LIKE THE LAST SEGMENT OF ITS NAMESPACE LANDS ITS CLAUSES ON THE NAMESPACE'S SYMBOL, in silence. Found under WI-20260913-P9QBF while writing a fixture (namespace rstl.cut with rule cut :- … answered no row through rstl.cut.cut). MEASURED on 50518b13 with the CLI: in namespace probe.zed, rule zed :- Link(from: 1, to: 2) loads clean, the query probe.zed.zed is refused ('does not resolve to a known functor') and the query probe.zed answers true; the same for rule zed(?x) :- item(?x) (probe.zed(?x) answers), for fact zed, and for rule zed beside fact zed(2) — two arities on one symbol, the namespace's. From another namespace, import probe.zed.{zed} is refused: unresolved import 'probe.zed.zed'. CONTROL: a DECLARED entity zed(x: Int64) in the same namespace is probe.zed.zed and fact zed(x: 1) lands on it. WHY: a rule head introduces a predicate only when it 'resolves to nothing in the finished program' (kernel-language §5.1, the table of what a namespace entry may introduce; §8.6's ladder); inside probe.zed the bare zed resolves to the namespace itself, so the head introduces nothing and the clause lands on probe.zed — a namespace, which is no relation. THE QUESTION, for the user: is the namespace's own name a head a clause may land on? Either (a) it is not — the namespace is no predicate, so zed introduces probe.zed.zed as in any other namespace; or (b) the head is refused at load, naming the namespace it resolves to and the qualified spelling that introduces. Either way the silent landing goes. CHECK FIRST: whether any loaded file (stdlib, examples, tests) has a clause landing on a namespace symbol today. ACCEPTANCE: the four shapes above and the import get the chosen verdict; the declared-entity control is unchanged; cargo-test green via scripts/test.sh.

