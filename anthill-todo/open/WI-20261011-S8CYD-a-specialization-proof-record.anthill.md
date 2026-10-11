## Attributes

- id: WI-20261011-S8CYD-a-specialization-proof-record
- created: 2026-10-11T16:04:54Z

- status: Open
- status_agent: user
- status_at: 2026-10-11T16:04:54Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A SPECIALIZATION PROOF RECORD IS NAMED BY ITS SPEC'S SHORT NAME, AND WITHOUT ITS BINDINGS, SO TWO PROVISIONS CAN SHARE ONE `rule` — name it by the spec's FULLY QUALIFIED name (user, 2026-10-11), and decide what the bindings owe the name. Found by /code-review of WI-20261011-ZVPXS and reproduced; not that ticket's — it changed how the names are looked up, not what they are.

HOW A NAME IS MADE TODAY (`load::register_specialization_witnesses`, rustland/anthill-core/src/kb/load.rs): `<X-qn>.provides.<A-short>.<SE>` — the provider by its qualified name, the spec by its LAST SEGMENT (`last_segment(kb.qualified_name_of(spec_sym))`), and `<SE>` the law's flattened name, made of short names too (`flatten_spec`). The bindings the provision is AT are in the witness's `substitution` and not in the name — and there as short names (`concrete_sort: "P"` for `test.sg.P`). And a pass does not add what it emits to the names it reads, so two rows of one load that make the same name both emit.

REPRODUCED 2026-10-11 with a temporary listing of every ProofRecord (docs/measurements/test-infrastructure/specialization-witnesses-2026-10-11.txt §11):
(1) TWO SPECS OF ONE SHORT NAME — `test.sa.Conv` and `test.sb.Conv`, each `requires anthill.prelude.Eq[T = T]`, and `test.sc.A` providing both: one call, or one later load of both, leaves TWO records named `test.sc.A.provides.Conv.Eq_T`, one with `parametric: "test.sa.Conv.requires.Eq_T"` and one with `test.sb.…`.
(2) ONE SPEC AT TWO BINDINGS — `sort W  provides Tag[T = P]  provides Tag[T = Q]`, `Tag` requiring `Eq[T = T]`: TWO records named `test.sg.W.provides.Tag.Eq_T`, differing in `substitution` alone. The qualified name does not tell these apart.
(3) ONE CALL AND TWO LOADS DISAGREE — a pass emits no record whose name the registry holds, so with the second provision of (1) written in a LATER load (`namespace test.sc.A  provides test.sb.Conv[T = test.sc.A]  end`) that load emits NOTHING for it: one record, where one call over the same files leaves two.
READ, NOT REPRODUCED: the same shape one pass up — `register_requires_axiom_witnesses` names a scope axiom `<scope-qn>.requires.<SE>` with `<SE>` of short names, so a sort requiring two specs of one short name at the same bindings names both alike (WI-390 met this for bindings that differ in a denoted literal).

WHO READS A RECORD BY ITS NAME, to be moved with it: the three witness passes (the test that a record is there, and `requires_law_records`, which takes a spec's laws as the names under `<spec-qn>.requires.`); `anthill check` (`check_specialization_witness`, `proof_record_exists`); `anthill prove` (`implicit_cites_for`, which splits at `.requires.` and leaves out a remainder with a `.` in it — a qualified name inside `<SE>` or after `provides.` meets that rule); a `using` that cites a record, and a cached sidecar keyed by one. COUNT FIRST how many names the stdlib, the examples and the tests cite as text.

TO DECIDE with the user before building, on that count: the FORM of the name with a qualified spec in it (dots inside what is one segment today); whether the bindings go into the name, which is what (2) needs, or the record's identity becomes name plus substitution; and whether `<SE>` and the witness's `substitution` take qualified names with it. Where the names are specified (proposal 030; kernel-language.md if it says anything of them) changes with the decision — a spec change, discussed first.

THE CONTROL: a row for each of (1), (2), (3) asserting two records under two names, in one call and with the second provision in a later load — each FAILS today; and the listing of every ProofRecord in three loads (the stdlib alone, a later load, the two in one call), before and after, compared: every name moves by the rule and nothing else does (127 records after the stdlib's own load today, no two of them sharing a name). `anthill check` and `anthill prove` over the examples give the verdicts they gave.

DONE WHEN: the three reproductions give two records under two names in one call and in two loads; the form is decided, recorded here and where the names are specified; every reader of a name is moved with it; the gate is green under all three recipes.

