import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.KB.FactEntry

/-!
# Fresh Variables

Allocate fresh variable ids from the KB counter.
-/

namespace Anthill.Kernel

/-- Allocate a fresh variable id, incrementing the KB counter. -/
def freshVar (kb : KnowledgeBase) : KnowledgeBase × VarId :=
  ({ kb with nextVar := kb.nextVar + 1 }, kb.nextVar)

end Anthill.Kernel

