import LeanLand.Kernel.Defs.Term

/-!
# Sorts

Sort kinds and the sort-id type alias.  Sort identifiers are just terms
(types-are-terms principle).
-/

namespace Anthill.Kernel

/-- Kind of a sort declaration. -/
inductive SortKind where
  | abstract
  | defined
  | constructor
  deriving Repr, BEq, DecidableEq

/-- Sort identifiers are terms. -/
abbrev SortId := ATerm

end Anthill.Kernel

