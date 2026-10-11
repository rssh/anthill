## Attributes

- id: WI-20261011-BVG8M-a-proof-in-a-scope-that-has-a
- created: 2026-10-11T20:31:12Z

- status: Open
- status_agent: user
- status_at: 2026-10-11T20:31:12Z

- acceptance: cargo-test

## Description

A PROOF IN A SCOPE THAT HAS A `requires` IS REFUSED: THE IMPLICIT CITE OF THE SCOPE'S REQUIREMENT CANNOT BE LOWERED — build the lowering of a requirement's record (proposal 030's γ.4 is the reader and not the citation), or decide what a proof is handed until it is. Found while delivering WI-20261011-S8CYD and not that ticket's: it is so before that change and after it.

REPRODUCED 2026-10-11 (docs/measurements/test-infrastructure/proof-record-names-2026-10-11.txt §8 (a)), `anthill prove <file> --no-cache`, z3 on the path:
`namespace test.imp  import anthill.prelude.PartialEq.{eq}  import anthill.prelude.PartialOrd.{gt}  import anthill.prelude.{Int64}  sort Scope  sort T = ?  requires anthill.prelude.Eq[T = T]  entity Cfg(scale: Int64)  fact Cfg(scale: 5)  rule r(?marker) :- Cfg(scale: ?s), gt(?s, 99), eq(?marker, ?s)  proof r by z3(logic: "LIA") end  end  end`
gives `error: test.imp.Scope.r: cite 'test.imp.Scope.requires.anthill.prelude.Eq[T = test.imp.Scope.T]' (in proof 'test.imp.Scope.r') could not be lowered under its translation policy: rule '…' not found`, 0 proved, 1 failed. THE CONTROL: the same file with the `requires` line taken out — `✓ test.impc.Scope.r: proved (z3: unsat)`. The proof needs no law of `Eq`; it is refused for standing where a requirement is in scope. On the tree before S8CYD the refusal is the same, of the old name (`test.imp.Scope.requires.Eq_T`).

WHY, read off the code (rustland/anthill-cli/src/prove.rs, rustland/anthill-smt-gen/src/lib.rs and policy.rs): `implicit_cites_for` hands `dispatch_z3` the requirement records of every enclosing scope of the proof's rule — by each record's witness, since S8CYD; `render_cited_lemmas` asks `cite_status`, which answers Discharged for a ScopeAxiom, and then lowers the cite through `render_cited_lemma_under_policy` to `lift_rule_to_implication_clause(kb, cited)`, which looks up the RULE of that name (`kb.program_clauses_by_qn`) and finds none: a requirement's record is no rule. So every cite of a `requires` record is an EmitError, before the solver is asked anything. The standard library has 42 requirements, in 28 scopes. NOT MEASURED: a `by` strategy other than z3; the steps of a structured proof; a proof in a scope NESTED under one that has a `requires` (the walk is outer to inner, so it should be refused the same way). No example and no test has a proof under a `requires`: `prove::s8cyd_implicit_cite_tests` pins WHICH records a proof is handed, and says at its site that nothing drives a proof through with them.

WHAT A REQUIREMENT'S RECORD STATES (proposal 030, 'Per-clause registration'): the conjunction of the required spec's laws, instantiated at the clause's bindings. Lowering it is lifting those laws, not a rule of the record's name. COUNT FIRST: what in the KB a LAW of a spec is (a rule of the spec's sort with a `-:` conclusion? every rule declared there?), and which of the specs the library's 42 requirements name have one — `EffectsRuntime` 18, `Iterable` 5, `Eq` 4, `PartialEq` 3, `Ring`, `PartialOrd` and `FiniteCollection` 2 each, `WeakOrd`, `Numeric`, `Modifiable`, `Lattice`, `logic.Minimal`, `logic.Constructive` 1 each. A requirement of a spec with no law lowers to nothing.

TO DECIDE with the user, on that count: (1) what a law of a spec is, for lifting, and how the clause's bindings reach the lifted clause — the scope's own parameter `T` is abstract; (2) until the lowering is built, and for a spec with no law, whether an IMPLICIT cite that lowers to nothing is dropped — a missing hypothesis can only lose an `unsat`, the direction `render_cited_lemma_under_policy` already takes for `Inline` — or stays the refusal it is; (3) whether a specialization record (`<X-qn>.provides.<PE>.<SE>`) is lowered the same way, at the provision's bindings; (4) the spelling of an EXPLICIT cite of a requirement from outside its scope: proposal 030 had `using a.S.requires.Eq_T`, which was an unresolved name at load before S8CYD and is no identifier now — the proposal says 'not built' there.

THE CONTROL: a proof under a `requires` whose goal NEEDS a law of the required spec proves, and with the implicit cite backed out it does not — said at its site; the dry-run document shows the law as an `(assert (forall …))`; a proof under a `requires` that needs no law proves (the reproduction above); a proof under a requirement of a spec with no law proves; `prove::s8cyd_implicit_cite_tests` gains a row that drives a proof. `anthill prove` over examples/webots-modelling/lf1 gives the 14 verdicts it gives.

DONE WHEN: the reproduction proves; what a requirement's record lowers to is decided, built and recorded in proposal 030, γ.4's mark with it; the control rows fail when the lowering is backed out; the gate is green.

