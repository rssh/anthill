# Future: Refutation as evidence — what two-sided type theory offers anthill

> **Stub** (2026-08-08) — to be extended. Unnumbered (see [README](README.md)).

## Basis

> Celia Mengyue Li, Steven Ramsay. *Logical Foundations of Two-Sided Type
> Theory*. **arXiv:[2607.14325](https://arxiv.org/abs/2607.14325)**, 15 Jul 2026
> (81 pp., formatted for submission; no journal-ref, so cite as a preprint).

Two-sided type systems (Ramsay & Walpole, *Ill-Typed Programs Don't Evaluate*,
POPL'24, [10.1145/3632909](https://doi.org/10.1145/3632909)) generalise the
typing judgement to a sequent `M₁:A₁, …, Mₖ:Aₖ ⊢ N₁:B₁, …, Nₘ:Bₘ`: assumptions
about **arbitrary terms**, and **any number** of conclusions — including zero,
where `add(x, λy.y) : Nat ⊢` certifies the program is defective (it is
meaningful *because the right side is empty*; the "or diverges" slack the
reading allows attaches to the right-hand conclusions).

This paper supplies the propositions-as-types reading: **bilateral logic**.
Wansing's 2Int has two mutually inductive primitive judgements, proof and *dual
proof*; Nelson's strong negation `~A` is added on top, and (Wansing's design)
has **no term former** — the same term is the evidence, transported across the
turnstile. Three systems: `2λInt`, `2λInt~` (both shown to correspond exactly to
2Int and its strong-negation extension, Thm 3.15 / Cor 3.16), and `2λHOL`.
**Only `2λHOL`** is proved consistent, strongly normalising, and to satisfy the
existence property and its dual — the two propositional systems carry
correspondence results only.

Two ideas carry over:

- **Constructive refutation** (Prawitz, p.5): refuting `A ∧ B` by deriving
  absurdity from it does not say *which* conjunct failed. Genuine refutation has
  its own rules, structured by the connective.
- **Dual Existence Property** (Thm 7.8(ii)): a refutation of `∀a:K. A` yields a
  witness `B` and a refutation of `A[B/a]`. Example 7.11 — refuting reachability
  yields the edge-closed set omitting the target, i.e. the inductive invariant.
  Example 7.10 is equality: a refutation of `A =ₖ B` is a property `P` together
  with **a proof of `P A` and a refutation of `P B`** — note the second half is
  itself a refutation, not an absence.

**The load-bearing discipline** (§8): on the left, `M : A` means *M is a
refutation of A*. The paper is explicit that this **supersedes** the earlier
POPL'24 reading ("M is not a term of type A") and that the strengthening "is
necessary for the soundness of our rules". A channel that admits "we could not
prove it" reproduces exactly the unsoundness §8 warns against.

## What it says about anthill

**One thing, narrow and real.** `Eq`'s reflexivity law is never discharged per
instance (`stdlib/anthill/prelude/eq.anthill`: "documentation-only … NOT
discharged per instance"), so nothing inspects reflexivity and nothing stops a
carrier claiming a lawfulness it lacks. `provides Eq[Float]` is blocked *only*
because `NonEq[Float]` is declared and the WI-658 exclusion fires. That is
refutation earning its place: **the checkable shadow of an unchecked law, used
to refuse a false claim at the declaration.** It is a declaration-side
exclusion, not a use-site mechanism.

`NonEq` even has the Skolemised shape the Dual Existence Property predicts —
`eq.anthill` calls its witness operation "the constructive form of
`∃x. eq(x, x) = false`". *Caveat, measured:* the witness is
`rule nonEqRefl() <=> nan` with no `[simp]`, and an untagged equational rule is
**inert** (kernel-language.md §5.3), with no host `operation_map` entry. So the
witness is not executable today; what blocks `provides Eq[Float]` is the
declaration plus the load check, not a computation.

**The use-site question is settled the other way.** Deriving `Eq` congruently
from a composite's parts and reading that goal positively — 058 §3.10 — is the
answer there, and WI-869 has since measured it at `pair.anthill`. A negative
channel is not needed for it. One spec's worth of hand-rolled refutation does
not justify a general channel; this stays speculative until a second instance
appears.

## Ideas worth keeping, each with its real gap

- **`Disproved` deserves a status peer.** `ProofResult` already has
  `Disproved(counterexample, solver)`, and the SMT backend already produces it:
  `"sat" => Verdict::Disproved(…)` reaches `ProofRecord.result =
  Failed(Disproved(…))`. Nothing is discarded — the earlier claim here that it
  was is **wrong**. The real gaps are three: the parsed model is thrown away and
  raw stdout is wrapped as one string against a `Term`-typed field;
  `produce_models` defaults false and no shipped `.anthill` passes
  `z3(model: true)`, so the stored counterexample is literally `"sat"`; and
  `ObligationStatus` is `Pending | Discharged(result) | Failed(result)` — three
  members, with `Discharged` already *carrying* a `ProofResult`, so
  `Discharged(Disproved(…))` is representable and the interesting question is
  which of the three a refutation belongs under, not "add a variant". Note also
  that an SMT `sat` is non-entailment **relative to the axioms at check time**;
  KB growth can invalidate it, so it is not straightforwardly "stable".
- **A monotone alternative to NAF.** A refutation goal succeeding only on
  positive evidence is monotone, where `not(G)` is not. What licenses `not`
  today is *not* stratification — there is none in the tree (zero hits for
  `stratif`/`stratum`; kernel-language.md's claim is stale). It is a groundness
  gate, delay-and-rotate, a definite/residual/truncated verdict, and a depth
  bound. Any payoff must be measured against that, not against a component that
  was never built.
- **Coimplication as a shape for the partial/total splits.** In the paper a
  proof of `A ≻ B` is **a refutation of `A` together with a proof of `B`**
  (Fig. 3 `≻R`; Appendix rule (9)) — so Float's status is `Eq ≻ PartialEq`:
  refutation of lawful `Eq`, proof of `PartialEq`. (An earlier draft here had
  the operands reversed.)

## What is *not* proposed

Disjunctive heads. `kernel-language.md` reserves `;`/`|` for them — but note
anthill **already has multiple conclusions** in head position: multi-head
`H1, H2 :- B` is conjunctive sugar desugaring to N Horn clauses. It is the
*disjunctive* reading that would need a different proof search (hyper-resolution
or tableaux), and nothing here argues for it.

Nor does the higher-order layer transfer. `2λHOL` has type-level λ and ∀ over
kinds, which would contradict the representation note in `CLAUDE.md`; anthill's
types are first-order terms with logical variables. Note the consequence: the
one system carrying the metatheory is the one that does not transfer.

`SDec` (Example 7.12, `∀x:K. P x ∨ ~(P x)`) is sometimes read as the property
licensing NAF. That inference is **not the paper's** — it never mentions
negation as failure, and its footnote 9 declines to assume `A` and `~A` are
inconsistent. `SDec` is also stated with a type-level λ over a predicate
variable, i.e. in the layer above.

## Open

- Whether a second spec ever wants a witnessed refutation. Until one does,
  `NonEq` is a one-off and should stay one.
- The three `Disproved` gaps above — the model-term one is the prerequisite;
  the others are cheap once a structured counterexample exists.
