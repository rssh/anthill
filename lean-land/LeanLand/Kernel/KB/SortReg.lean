import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.Defs.Sort
import LeanLand.Kernel.KB.FactEntry
import LeanLand.Kernel.KB.Subsort

/-!
# Sort Registration

Register sorts, subsort pairs, and constructor subsorts into the KB.
-/

namespace Anthill.Kernel

/-- Register a sort with its kind. -/
def registerSort (kb : KnowledgeBase) (s : SortId) (k : SortKind) : KnowledgeBase :=
  { kb with sorts := kb.sorts ++ [(s, k)] }

/-- Register a subsort relationship (child, parent). -/
def registerSubsort (kb : KnowledgeBase) (child parent : SortId) : KnowledgeBase :=
  { kb with subsort := kb.subsort ++ [(child, parent)] }

/-- Register each constructor as a subsort of the parent. -/
def registerConstructorSubsorts (kb : KnowledgeBase) (parent : SortId) : List ATerm → KnowledgeBase
  | [] => kb
  | ctor :: rest =>
    let kb1 := registerSort kb ctor .constructor
    let kb2 := registerSubsort kb1 ctor parent
    registerConstructorSubsorts kb2 parent rest

end Anthill.Kernel
