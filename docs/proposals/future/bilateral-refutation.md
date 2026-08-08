# Future: Bilateral refutation — negative evidence as a first-class channel

> **Stub** (2026-08-06) — to be extended. Unnumbered (see [README](README.md)).

## Idea

Anthill already carries **four hand-rolled instances of one mechanism**:
*a refutation is evidence, and it is not the same thing as failure-to-prove.*
Each was invented locally, for a local problem, under a local name. Name the
mechanism once and they condense.

1. **`NonEq`** (`stdlib/anthill/prelude/eq.anthill:43`). A carrier declares its
   equality non-reflexive by **exhibiting a witness** — `nonEqRefl()` returns a
   `w` with `eq(w, w) = false`. The file already says what this is: "the
   constructive form of `∃x. eq(x, x) = false` (Anthill has no `∃` in rule
   bodies, so the existential is Skolemized to a nullary witness operation)."
   `Eq` ⊥ `NonEq` is checked at load (WI-658); a carrier providing **neither** is
   unconstrained. The `Map[K = Float]` refusal is deliberately *negative* — it
   fires on a witnessed `NonEq`, never on an absent `Eq`
   (`docs/kernel-language.md:2043`).
2. **`ProofResult.Disproved(counterexample: Term, solver: String)`**
   (`stdlib/anthill/prelude/meta.anthill`, the `ProofResult` enum) — a refutation with its witness,
   already a distinct constructor.
3. **The `⊥`-headed denial** (`docs/kernel-language.md:994`) — a clause with no
   positive conclusion.
4. **Typing judgements as goals.** `(?x: T)` desugars to a
   `TypeOf(occ: ?x, type: T)` body goal (`rustland/anthill-core/src/parse/convert.rs:3727`),
   and hypothetical goals push antecedents as scoped assumptions resolved as
   `Candidate::Assumption` (`kb/resolve.rs:296`, `:1483`). Assumptions about
   arbitrary *positioned* terms, not just variables — proposal 022's occurrences.

A fifth signal is the **third outcome anthill keeps rediscovering without
naming**: `=` on a non-ground operand *suspends*; an overriding carrier buried
in non-overriding structure *suspends*; an over-budget compare "degrades to
*undecided*, never to a wrong verdict" (`docs/kernel-language.md:2049`–`2051`).
Proved / refuted / undetermined is not a degradation — it is the honest state of
a system that does not assume excluded middle.

## Basis

> Celia Mengyue Li, Steven Ramsay. *Logical Foundations of Two-Sided Type
> Theory*. **Journal of the ACM**, 2026. arXiv:[2607.14325](https://arxiv.org/abs/2607.14325).

Two-sided type systems (Ramsay & Walpole, *Ill-Typed Programs Don't Evaluate*,
POPL'24, [10.1145/3632909](https://doi.org/10.1145/3632909)) generalise the
typing judgement to a sequent `M₁:A₁, …, Mₖ:Aₖ ⊢ N₁:B₁, …, Nₘ:Bₘ` — assumptions
about **arbitrary terms**, and **any number** of conclusions, including zero
(`add(x, λy.y) : Nat ⊢` is a certificate that the program is defective). The
JACM paper supplies the propositions-as-types reading: **bilateral logic**.
Wansing's 2Int has two mutually inductive primitive judgements, proof and *dual
proof*; Nelson's strong negation `~A` switches sides of the turnstile with **no
term former** (the same term is the evidence). New systems `2λInt`, `2λInt~`,
`2λHOL` (two-sided Geuvers' λHOL), proved consistent, strongly normalising, and
satisfying the existence property **and its dual**.

Two results carry the design:

- **Constructive refutation** (Prawitz, quoted at p.5): refuting `A ∧ B` by
  deriving absurdity from it does *not* say which conjunct failed. Genuine
  refutation has its own rules, structured by the connective.
- **Dual Existence Property** (Thm 7.8(ii)): a refutation of `∀a:K. A` *directly
  yields* a witness `B` and a refutation of `A[B/a]`. Their Example 7.11 —
  refuting reachability yields the edge-closed set omitting the target, i.e. the
  inductive invariant. Example 7.10 is equality: intuitionistic `¬(A =ₖ B)` has
  uninformative content, whereas a refutation *is* a property satisfied by `A`
  and not `B`.

**The load-bearing discipline** (paper §8): on the left, `M : A` means *M is a
refutation of A* — strictly **stronger** than "M is not of type A", and the
strengthening is what makes their rules sound. `NonEq` already honours it (a
witness, not an absence). Any generalisation must; a `refutes` channel that
quietly admits "we could not prove it" would be unsound in exactly the way the
paper documents.

## What it condenses

- **`Eq`/`NonEq` — settled, and mostly *against* a negative channel.** See
  [proposal 058 §3.9](../058-modular-instances.md). The use-site question is
  answered positively: derive `Eq` congruently from the parts (`provides
  Eq[Pair[A,B]] :- Eq[A], Eq[B]`) and let the check read that, discharging an
  abstract parameter by the enclosing `requires` as an assumption. A negative
  channel is *not* needed for it — the earlier framing here was wrong.

  What survives is narrow and worth keeping: `eq_refl` is never discharged per
  instance, so nothing stops a carrier claiming a lawfulness it lacks, and
  `NonEq[Float]` is the only thing blocking `provides Eq[Float]` today
  (`eq.anthill:39`). That is a **declaration**-side exclusion, needing a witness
  because `eq(w,w) = false` is a computation while the universal law is not.
  Refutation earns its place as the checkable shadow of an unchecked law — not
  as a way to answer questions the positive channel can answer itself.
- **Monotone negation.** `not(G)` is NAF: closed-world, needs stratification
  (`docs/kernel-language.md:2060`), needs the static allowedness check for `<=>`
  under negation (WI-525), and is the operator that breaks proposal 053's
  monotonicity. A refutation goal — succeeds only on positive negative evidence
  — is **monotone**: no stratification, safe under incremental assertion, no
  retract guard. That is a payoff on machinery already built.
- **`Disproved` out of `Failed`.** `ObligationStatus` is two-valued —
  `Discharged | Failed(result)` (`stdlib/anthill/realization/realization.anthill:293`)
  — so a counterexample-with-witness files alongside `Timeout` and `Unknown`. A
  counterexample is *stable* under KB growth; a timeout is not. Correspondingly
  the SMT encoding documents only the `unsat` direction
  (`docs/kernel-language.md:1048`): a `sat` model **is** a refutation term and
  should be registered as evidence, not discarded as a non-proof.
- **Coimplication as the shape of the partial/total splits.** `A ≻ B` ("A but
  not B") is proved by a pair: a proof of `A` and a refutation of `B`. Float's
  actual status is `PartialEq ≻ Eq`, and the pair is exactly
  (`provides PartialEq[Float]`, `nonEqRefl() = nan`). The `PartialEq`/`Eq` and
  `PartialOrd`/`Ord` splits of proposal library/004 are one algebraic form,
  not a family of hand-cut pairs.
- **Strong decidability as the property that licenses NAF.** The paper's
  Example 7.12: `SDec_K P = ∀x:K. P x ∨ ~(P x)` — every input yields a proof
  *or* a refutation. That is the semantic condition under which
  negation-as-failure is sound as refutation. Stratification is the syntactic
  approximation anthill uses today.

## Staying Horn — what is *not* proposed

The head-side `Δ` (multiple conclusions) would break SLD's single-goal-stack
model; it needs hyper-resolution or tableaux. `docs/kernel-language.md:1042`
reserves `;`/`|` in head position for a future disjunctive-head proposal — **do
not cash that reservation on the strength of this paper.**

It is not necessary. In 2Int, dual proof is itself rule-defined and *mutually
inductive with* proof. So refutation reifies as a **positive predicate over a
dual index** — `refutes(S, C)` beside `S[C]` — and everything stays Horn: SLD,
the clause store, and the discrimination tree (which keys on structure, never on
identity) apply unchanged. What must be added is the mutual recursion between
the two families and the never-both check — which for `Eq`/`NonEq` already
exists (WI-658), scoped to one spec.

One consequence worth stating: `docs/kernel-language.md:1053` refuses to make
denials citable because "the body has no satisfying instance, which has no
determinate conclusion to lift as `body ⇒ head`." Under the bilateral reading
that is a consequence of having one citation form, not a fact about denials — a
dual proof is evidence, cited to *refute*. Whether to add a dual citation is
open; it is not a prerequisite for anything above.

## Scope / open work

- **The `Eq` half is settled and is not on this list** — WI-869 shipped
  per-provision conditions (058 §3.8) and measured the result at
  `stdlib/anthill/prelude/pair.anthill`: `Set[T = Pair[Float, Int64]]` still
  loads, "not an over-claim any more … but no POSITIVE use-site check for
  `requires Eq` exists." The answer is 058 §3.9's congruent positive
  derivation, not a refutation channel. What is left for refutation there is
  only the declaration-side exclusion, below.
- The `refutes S[C]` surface, **if** a second spec ever needs it: spelling,
  where the Skolem witness operation is declared, and how it relates to
  `provides`. `NonEq` is the sole instance today, and one instance does not
  justify a channel — this stays speculative until a second one appears.
- Generic `S ⊥ refutes S` exclusion replacing the per-spec check (WI-658) —
  worth doing only alongside that second instance.
- Interaction with proposal 053 (fact monotonicity): a refutation is monotone,
  so it should need no retract guard — confirm against the per-functor default.
- `SDec` declaration and check, and whether it can replace stratification as the
  NAF soundness criterion or only supplement it.
- Whether the `ObligationStatus` change is separable. **It is** — promoting
  `Disproved` to a status peer of `Discharged`, and keeping the SMT `sat` model
  as evidence, is the smallest slice with independent value and no dependency on
  the rest.

## Does not transfer

`2λHOL` is higher-order: type-level λ, ∀ over kinds, β-conversion **of types**.
Anthill's types are first-order terms with logical variables and unification.
Importing that layer would also contradict the representation note in
`CLAUDE.md` (hash-consing is inappropriate for binders), and none of the above
needs it — the applicable content is the *judgement shape and the refutation
discipline*, not the higher-order machinery.

Their `M : A` also means "evaluates to a value of type `A`, **or diverges**" —
that slack is what makes `add(x, λy.y) : Nat ⊢` a meaningful certificate.
Anthill's typing is sort membership plus spec provision, so the certificates say
something different; the effect and finiteness work is where the two would have
to meet.

## Promotion

Assign a main-sequence proposal number and move out of `future/` when scheduled.
