import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Term

/-!
# Builtins

Builtins are operations dispatched directly by the resolver, not via
KB fact matching.  Each builtin is identified by its qualified name and
has a specific execution semantics.
-/

namespace Anthill.Kernel

/-- Tag identifying a builtin operation. -/
inductive BuiltinTag where
  | nonVar        -- `anthill.reflect.nonvar(?x)`: succeeds if ?x is non-variable
  | ground        -- `anthill.reflect.ground(?x)`: succeeds if ?x is fully ground
  | qualifiedName -- `qualified_name(?sym, ?result)`: Symbol → full name string
  | shortName     -- `short_name(?sym, ?result)`: Symbol → last segment string
  | lookupSymbol  -- `lookup_symbol(?name, ?result)`: String → Symbol
  deriving Repr, BEq, DecidableEq

/-- Result of evaluating a builtin. -/
inductive BuiltinResult where
  | success             : BuiltinResult
  | successWithBindings : (VarId → Option ATerm) → BuiltinResult
  | delay               : BuiltinResult
  | failure             : BuiltinResult

end Anthill.Kernel

