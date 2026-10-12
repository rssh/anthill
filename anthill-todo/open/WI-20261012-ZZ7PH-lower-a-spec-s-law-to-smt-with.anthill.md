## Attributes

- id: WI-20261012-ZZ7PH-lower-a-spec-s-law-to-smt-with
- created: 2026-10-12T06:09:58Z

- status: Open
- status_agent: user
- status_at: 2026-10-12T06:09:58Z

- acceptance: cargo-test

## Description

LOWER A SPEC'S LAW TO SMT, WITH THE SCOPE'S ABSTRACT PARAMETER AS ITS OWN SMT SORT — so a proof under a `requires` that needs a law of the required spec proves, and a claim about the abstract carrier is no longer answered of the reals. What is left of proposal 030's γ.4; decided with WI-20261011-BVG8M (user, 2026-10-12; proposal 030, 'What a requirement's record lowers to') and not built there.

WHAT IS THERE (BVG8M): a `by z3` proof is handed the `requires` clauses of its enclosing scopes (`prove::implicit_cites_for`, over `load::requires_clauses_of`), each resolved to the laws of the spec it requires (`KnowledgeBase::spec_laws`), and is handed NO hypothesis: `prove::tell_laws_left_out` names the laws in a warning, once a run for each requirement. 11 of the standard library's 42 requirement records name a spec with a law — Eq 1 (4 records), PartialEq 1 (3), Ring 2 (2), WeakOrd 9 (1), Lattice 9 (1): 21 equations, 1 constraint (docs/measurements/test-infrastructure/requirement-cites-2026-10-12.txt §2).

WHAT STANDS BETWEEN A LAW AND AN `(assert (forall …))`, each measured there: (1) THE HEAD — an equation is stored `anthill.kernel.unify(lhs, rhs)`, which `classify_head` refuses ('rule head shape not supported'); a constraint is a `Constraint(head(…), guard(…))` fact. An equation lowers to `(= lhs rhs)`, and a side that is `Bool`-valued is a condition, not an arithmetic term. (2) THE OPERATIONS — 18 of the 21 equations and the constraint name `neq`, `compare`, `max`, `min`, `lub`, `glb` or `less`, which have no row in `SMT_BUILTINS`. A spec's operation with no theory row is an UNINTERPRETED FUNCTION, declared once in the consumer's document and used by the law and by the proof's body alike — `lift_rule_to_implication_clause` returns clause text today and has nowhere to put a declaration. (3) THE CARRIER — every variable is `(declare-const … Real)` or `(forall ((v Real)) …)`, `PartialEq.eq` lowers to `=` and `PartialOrd.gt` to `>`. The abstract parameter is ITS OWN SORT (`declare-sort`), the spec's operations on it uninterpreted, `eq` included, and a variable has that sort by its bound (`?a: T`).

AND WHAT BVG8M FOUND AND DID NOT FIX, which (3) answers: A VERDICT UNDER A REQUIREMENT IS ABOUT THE REALS. `rule refl_like: gte(?a, ?a) :- gte(?a, ?b)` under `requires PartialOrd[T = T]` proves — the document is two `Real` constants, `(>= var_1 var_0)` and the negated `(>= var_1 var_1)` — with no law to leave out and nothing said, and the same rule in a sort that requires nothing proves too. The refusal BVG8M removed kept that population from running, by accident. `wi_bvg8m_requirement_cite_test::a_verdict_under_a_requirement_is_about_the_reals` holds the document as it is and is the row this turns.

COUNT FIRST: what a stored rule keeps of a variable's bound, and what the typer knows of a rule variable that has none; which variables of the proofs in examples/ and the suites range over an abstract parameter (lf1's are all scalars); how many `prove_*` rows and lf1 documents move by a byte when a variable can have a sort other than `Real` — the aim is none.

TO DECIDE with the user, on that count: (a) a variable with NO bound in a rule under a scope that has an abstract parameter — refused, read off the typer, or `Real` as today; (b) a requirement at a CONCRETE binding (`requires Eq[T = Int64]`) — the theory's own operations, or the carrier's through its provision; and whether a law that is a theorem of the theory there is emitted at all; (c) TWO requirements of one spec at two parameters of one scope — which instance a body's `weight(?a)` is, when `?a` has no bound; (d) a `constraint`'s name in the warning: it is a declaration's and not on the stored clause, so BVG8M counts it (`1 constraint`); labelling the clause would also change what `using <that name>` resolves to; (e) whether the laws of what a required spec requires or provides in turn come along — NOT in this ticket unless said: BVG8M decided a spec's own laws, and `the_laws_of_what_a_spec_provides_in_turn_are_not_read` holds that `requires Ord[T]` names `Ord.compare_eq` alone.

THE CONTROL: `rule irreflexive(?a: T) :- neq(?a, ?a)` under `requires Eq[T = T]` proves (the body is unsat by `eq_refl` and PartialEq's `neq` law — which says whether (e) is needed for it), and with the laws left out it does not; under `requires PartialEq[T = T]` alone it does NOT prove — reflexivity is `Eq`'s law, and `eq` as `=` gives it for nothing today; `refl_like` above does not prove under `requires PartialOrd[T = T]`; the dry-run document shows each lowered law as an `(assert (forall …))` over the declared sort, and `a_law_left_out_changes_nothing_in_the_document` is the row that changes; the warning is gone for a law that lowers and stays for one that does not; a proof under a requirement of a spec with no law, lf1's 14 verdicts and every `prove_*` row are as they are.

DONE WHEN: the control rows hold and each fails when its part is backed out; proposal 030's γ.4 is ✓ or says what is still left; the gate is green.

