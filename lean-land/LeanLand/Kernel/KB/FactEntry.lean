import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.Defs.Sort

/-!
# Fact Entry and Knowledge Base

Core structures: a fact entry stores a term with its sort, domain,
optional metadata, and retraction flag.  The knowledge base holds
facts, subsort pairs, sort registrations, and a fresh variable counter.
-/

namespace Anthill.Kernel

/-- Unique identifier for a fact in the KB. -/
abbrev FactId := Nat

/-- A single fact entry in the knowledge base. -/
structure FactEntry where
  term      : ATerm
  sort      : SortId
  domain    : SortId
  metadata  : Option ATerm
  retracted : Bool
  deriving BEq

/-- The knowledge base. -/
structure KnowledgeBase where
  facts    : List FactEntry
  subsort  : List (SortId × SortId)  -- (child, parent) pairs
  sorts    : List (SortId × SortKind)
  nextVar  : Nat

/-- An empty knowledge base. -/
def emptyKB : KnowledgeBase :=
  { facts := [], subsort := [], sorts := [], nextVar := 0 }

end Anthill.Kernel

