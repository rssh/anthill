import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.Defs.Rule
import LeanLand.Kernel.Subst.Subst
import LeanLand.Kernel.KB.FactEntry
import LeanLand.Kernel.KB.Query

/-!
# Denial Checking

A denial `⊥ :- B₁, …, Bₙ` is violated when all body atoms are provable.
KB consistency means no denial is violated.
-/

namespace Anthill.Kernel

/-- All body atoms are satisfied under some substitution. -/
def bodySatisfied (kb : KnowledgeBase) (body : List ATerm) : Prop :=
  ∃ σ : Subst, ∀ atom, atom ∈ body → query kb (applySubst σ atom) ≠ []

/-- A denial is violated if it is a denial and its body is satisfied. -/
def denialViolated (kb : KnowledgeBase) (r : ARule) : Prop :=
  r.head = .bottom ∧ bodySatisfied kb r.body

/-- The KB is consistent w.r.t. a set of denials if none is violated. -/
def kbConsistent (kb : KnowledgeBase) (denials : List ARule) : Prop :=
  ∀ d, d ∈ denials → ¬ denialViolated kb d

/-- No query matches in an empty KB. -/
theorem query_empty_kb (p : ATerm) : query emptyKB p = [] := by
  simp [query, activeFacts, activeFactsAux, emptyKB]

end Anthill.Kernel
