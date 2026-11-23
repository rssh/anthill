## Attributes

- id: WI-20261123-5MMGP-public-entry-point-the
- created: 2026-11-23T20:51:49Z

- status: Open
- status_agent: user
- status_at: 2026-11-23T20:51:49Z

- acceptance: cargo-test, scaland-sbt-test

## Description

Public entry point: the refutation of a typed query whose variables are its own (proof mode outside the crate)
WHO NEEDS IT. anthill-traces (its WI-20261122-5B123) explains a violated contract clause by its failing sub-goal. It builds the clause's goals term to term, with parameters and 'result' replaced by values, and resolves them with execute_typed_logical_query_with (WI-20261122-96QKW). For a violated clause it asks for the refutation through SLDProof.of(!g, ?p) (WI-20261121-G8E02).
WHAT IS THERE. MEASURED 2026-11-23 on 234cbe830 (kb/sld_proof.rs last changed in 88e83f4ae, an ancestor of 2ab7ca823), with SLDProof.of(anthill.kernel.not(g), ?p) built term to term, ?p a fresh global variable (fresh_var), as a one-goal LogicalQuery to execute_typed_logical_query_with:
- g ground, a rule over a record value broken in one conjunct of its body: one definite answer, ?p = refuted(...) down to the failing forall element. A ground lookup rule_e(S, e) over member, with e absent: refuted down to refuted(member(e, nil), []).
- g = has_e(S, E(id: 2, status: C)), a lookup whose entity pattern leaves fields out. The loader fills those fields with fresh variables, so g is not ground: one answer with one residual goal, and ?p unbound. As kernel-language §8.3 specifies, it waits while g has an unbound variable (read from code: step_sld_proof_of -> negand_is_ground -> delay_goal).
The search in proof mode is crate-private: resolve_lazy_goal_with_proof (kb/resolve.rs), SearchStream::drain_with_proofs, and ProofRecorder::refutation (kb/sld_proof.rs). A grep by name for 'pub fn .*proof' in anthill-core/src found no public entry for it.
WHY IT MATTERS. In a query, nothing outside the query can bind its variables. So a complete search with no answer establishes that no binding satisfies the goals, and the proof recorder already builds that refutation for a negation's sub-search. A client can reach it only through !g, which waits on any free variable. Most lookups in a contract carry such variables: every entity pattern that leaves a field out, and every ?x that two clauses share (one group of goals joined by ?c). For all of these anthill-traces can only say that no proof came back.
WHAT IS ASKED. A public entry, for example KnowledgeBase::refute_typed_logical_query_with(q: &Value, options: &ExecuteOptions) -> Result<Refutation, LowerError>, or an equivalent on the stream:
- q is typed as execute_typed_logical_query_with types it, and refused the same way (LowerError::QueryRefused);
- the search runs in proof mode at the caller's budget, reading the query's variables as its own;
- the result is Refuted(the SLDProof.refuted term of the query's goals), when the search ends complete with no answer; Answered, when it has a definite answer; or Undecided, with the limit (SearchLimit), the fault, or only conditional answers, plus the steps taken and out_of_fuel, as SearchStream::stats gives them.
For several goals, the refutation names on each branch the goal the branch failed at: the shape of a conjunction's refutation is anthill's to choose, and is stated in the entry's doc.
WHAT IS NOT ASKED. A change to how !g or SLDProof.of reads an unbound variable: that would be a language change, and a Rust entry adds none. Proof mode stays off for every other search.
DONE WHEN. Rows driven from outside the crate:
(1) a lookup by a partial entity pattern that matches no element gives Refuted, its leaf the lookup's refutation at nil;
(2) a ground goal gives the same refutation term as SLDProof.of(!g, ?p) (the control: the two agree);
(3) two goals sharing a variable, where the first has two answers and the second fails for each, give Refuted with a step per branch;
(4) a query with an answer gives Answered;
(5) a step budget too small gives Undecided naming SearchLimit::Steps; a goal whose search faults gives Undecided with the fault;
(6) a query the typer refuses gives QueryRefused;
(7) execute_typed_logical_query_with takes the same steps and gives the same answers as before (the control).

