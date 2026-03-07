import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.Subst.Subst
import LeanLand.Kernel.Subst.Unify
import LeanLand.Kernel.KB.FactEntry
import LeanLand.Kernel.KB.FactOps

/-!
# Query

Pattern matching against the KB via one-way unification.
-/

namespace Anthill.Kernel

/-- Match a pattern against a fact entry via unification. -/
def matchFact (pattern : ATerm) (entry : FactEntry) : Sum Subst UnifyError :=
  unify Subst.empty pattern entry.term

/-- Query the KB: find all active facts matching a pattern, returning
    fact ids and resulting substitutions. -/
def query (kb : KnowledgeBase) (pattern : ATerm) : List (FactId × Subst) :=
  (activeFacts kb).filterMap fun (fid, entry) =>
    match matchFact pattern entry with
    | .inl σ => some (fid, σ)
    | .inr _ => none

end Anthill.Kernel

