/-!
# Literals

Literal values carried by `Const` terms.  Uses `Float` for floating-point
(no Mathlib dependency; a rational type could replace this if needed).
Note: `Float` does not support `DecidableEq` due to NaN semantics.
-/
namespace Anthill.Kernel

/-- Literal values carried by `Const` terms. -/
inductive Literal where
  | litInt    : Int → Literal
  | litFloat  : Float → Literal
  | litString : String → Literal
  | litBool   : Bool → Literal
  deriving Repr, BEq

end Anthill.Kernel
