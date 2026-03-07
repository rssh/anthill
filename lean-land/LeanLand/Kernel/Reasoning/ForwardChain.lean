import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.Defs.Rule
import LeanLand.Kernel.Subst.Subst
import LeanLand.Kernel.KB.FactEntry
import LeanLand.Kernel.KB.Query

/-!
# Forward Chaining (Single Step)

Given a set of derivation rules, one forward-chaining step derives
all new facts whose bodies are satisfied.
-/

namespace Anthill.Kernel

/-- The set of facts derivable in one forward-chaining step. -/
def derivableFacts (kb : KnowledgeBase) (rules : List ARule) : ATerm → Prop :=
  fun t => ∃ r σ,
    r ∈ rules ∧
    r.head ≠ .bottom ∧
    r.body ≠ [] ∧
    (∀ atom, atom ∈ r.body → query kb (applySubst σ atom) ≠ []) ∧
    t = applySubst σ r.head

end Anthill.Kernel
