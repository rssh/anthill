## Attributes

- id: WI-20261012-1P005-a-variable-a-premise-names
- created: 2026-10-12T21:16:35Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-14T12:32:36Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A VARIABLE A PREMISE NAMES BEFORE THE EQUATION THAT DEFINES IT IS LEFT OUT OF A LIFT'S QUANTIFIER — and is then the consumer's variable of the same index: a false claim proves by citing a true, trusted lemma. Of the family of WI-20261012-BR7P3 (a name of one frame taken for another's); found while reviewing WI-20261012-CDHSQ, reproduced on the tree before it (bcad34e8) and as it delivered (docs/measurements/test-infrastructure/lemma-premise-2026-10-12.txt §7 (iii)).

WHAT IS THERE: `process_body_goal` writes a goal's assertion with each variable as it is bound WHEN THE GOAL IS READ, and `?v = <expr>` binds `?v` from there on. A goal read before the equation has the variable by its own name, and `note_free_vars` then leaves that name out of the free variables — it is bound — so in a satisfiability check it is not declared, and in a lift it is not quantified.

MEASURED, `anthill prove --no-cache`:
  rule lemma: gte(?a, 0.0) :- gte(?kn, 1.0), ?kn = ?a + 1.0        -- true: kn = a + 1 and kn >= 1
  rule user: gte(?x, 0.0) :- lte(?x, 100.0), gte(?w, 1.0)          -- false at x = -5, w = 1
  proof user using lemma by z3 end
With `proof lemma by z3 end` the lemma's own document names a constant it does not declare — `? lemma: unknown (… "unknown constant var_0")` — which is loud, and the lemma cannot be cited. With `proof lemma by trust(…) end` the lift is `(forall ((var_1 Real)) (=> (>= var_0 1.0) (>= var_1 0.0)))`, its `var_0` free, the consumer's `?w` is `var_0`, and `✓ user: proved`. With the equation written first the lift is `(=> (>= (+ var_1 1.0) 1.0) (>= var_1 0.0))` and `user` is a COUNTEREXAMPLE.

The same holds of every binder that comes after a use — an entity's field, a fact matched, a one-argument rule's value — and, since CDHSQ, of a relation written for a premise as of a comparison.

TO DECIDE with the user: (a) REFUSE a clause in which a goal names a variable a later goal binds, saying which; (b) apply the binding to what was already written (the assertions of the frame, by token); (c) read the binders first. And whether it is done with BR7P3 — one account of which name is whose — or before it.

THE CONTROL: `user` above does not prove with the lemma trusted, and proves when backed out; the lemma proved `by z3` has a verdict or a refusal that names the variable, not a solver error; lf1's documents are as they are, or each that is not is listed.

DONE WHEN: the control rows hold and fail when backed out; the documents that moved are listed; the gate is green.

## Changes

### 2026-10-14T12:32:35Z — feedback — user

DELIVERED (6f5262ce, rows in d8163f8e) — the user, 2026-10-14: deliver it with its rows. Closed by WI-20261014-FHEEK: every place a variable is given a value goes through bind_variable, which equates a variable the document has already written — option (b), as an equation rather than a substitution into what was written; the binders after a use are read where they stand. THE CONTROL: user (the ticket's program, lemma trusted) is a COUNTEREXAMPLE, and PROVED with the equation substituting again; the lemma by z3 proves (was 'unknown constant var_0'). Each binder: equation, entity's field, fact, one-argument value, equation after a relation written for a premise — lemma by z3 proved for each; the lift of eq and rel quantifies the variable ((forall ((var_0 Real) (var_1 Real)) (=> (and (>= var_0 1.0) (= var_0 (+ var_1 1.0))) …))) and their users are COUNTEREXAMPLES. The entity variant's user is the solver's 'unknown constant cap': the lift names the field constant and the consumer does not declare it — so does a lemma whose entity premise comes first, on d7a8ffcb as now; not of this ticket, put to the user. lf1's documents byte for byte (FHEEK's §5). 3 rows (wi_1p005_binder_after_use_test), back-outs in its header; docs/measurements/test-infrastructure/inlined-names-2026-10-14.txt §9. Gate 9818/0.

