## Attributes

- id: WI-20261104-J9SSG-proposal-060-1-a-rule-s
- created: 2026-11-04T15:09:13Z

- status: Open
- status_agent: claude
- status_at: 2026-11-04T15:09:13Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-060.1, typing

## Description

PROPOSAL 060.1 — A RULE'S DICTIONARIES ARE WRITTEN (user, 2026-11-04, decided while closing WI-20261102-ATVC1; docs/proposals/060.1-written-rule-requirements.md). A rule takes a dictionary only where its clause writes require[X], as an operation takes one only where it writes requires X: a rule-body call needing a dictionary at a type variable is refused unless its clause writes require[X] for it (a call at a concrete type needs none), and a goal passes its callee the requirements the callee writes, each taken from the requirement its caller writes at the goal's argument types, refused where the caller writes none, naming the require[…] to write. The inference of a rule body's requirements (WI-20260925-P7VP4, both demand kinds) and ATVC1's forward slots are withdrawn; ATVC1's citation marker stays and carries the written requirements. WHY (user): one rule an author reads off the text, chosen over 'explicit only between rules', which leaves a callee's requirement invisible. MEASURED on 6c6df13a: rule outer(?a, ?b, ?c) :- cmp(?a, ?b, ?c) takes WeakOrd through a slot nobody wrote; evenS/oddS (each calling the other) pass nothing between them, so isEven[A = Int64, WeakOrd = Descending]([5, 3, 1, 0]) answers 0, not 1; a tried design that collected a recursion's slots (named by the dictionary each holds, routed again until stable) needed a fallback for reads no name covers and still passed nothing, silently, through rule triA(?l) :- triB(?l), whose ?l nothing types — isTri[Descending]([5, 3]) answers 0 before and after it. STAGES (060.1 §7): (1) the anchor at a type variable inside a head type (§2) — rule skipN(?l: List[T = ?e]) :- require[WeakOrd[T = ?e]], … is refused today, 'expected a typed head binding whose bound provides WeakOrd … got … List provide no WeakOrd' — and a spec's own laws read the spec at its own parameter (§3; Ord's constraint compare_congruent is the one stdlib rule body the inference reads at a type variable, measured); additive, nothing refused yet. (2) the refusal (§1), the inference and the forward slots withdrawn (§5), and every program of the suite, the examples and anthill-todo that relied on them rewritten to write its requirements, each rewritten row driven to the answer it gave before; ATVC1's rows through outer, outer2, the connectives and the recursion rewritten so, and evenS/oddS answering 1 / 0 at a list the default search depth allows (isSorted[Descending]([5, 3, 1, 0]) is search_truncated at max_depth 100 on 6c6df13a). OPEN (060.1 §8): the domain read of an inferred column; a requirement at a rule's own sort parameter in a sort that requires it; two written requirements at one type. ACCEPTANCE: rows per stage, each back-out named at its row; kernel-language §5.3/§8.1 and 060 §3 brought in line with 060.1 §6 once its text is agreed; full workspace green.

