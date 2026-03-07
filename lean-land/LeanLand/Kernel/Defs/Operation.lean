import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Sort
import LeanLand.Kernel.Defs.Effect

/-!
# Operations

An operation has a name, typed parameters, return sort, pre/post-conditions,
and declared effects.
-/

namespace Anthill.Kernel

/-- An operation declaration. -/
structure Operation where
  name     : Symbol
  params   : List (Symbol × SortId)
  ret      : SortId
  preconditions : List ATerm
  ensures  : List ATerm
  effects  : List Effect
  deriving BEq

end Anthill.Kernel

