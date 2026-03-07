import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Term

/-!
# Free Variables

Compute the set of free variable ids in a term.
-/

namespace Anthill.Kernel
end Anthill.Kernel

mutual
partial def Anthill.Kernel.fv : Anthill.Kernel.ATerm → List Anthill.Kernel.VarId
  | .const _      => []
  | .var v        => [v]
  | .fn _ args    => args.flatMap Anthill.Kernel.fvArg
  | .ref _        => []
  | .quoted _ _   => []
  | .bottom       => []

partial def Anthill.Kernel.fvArg : Anthill.Kernel.FnArg → List Anthill.Kernel.VarId
  | .positional t => Anthill.Kernel.fv t
  | .named _ t    => Anthill.Kernel.fv t
end

namespace Anthill.Kernel

/-- A term is ground if it has no free variables. -/
def ground (t : ATerm) : Bool :=
  (fv t).isEmpty

end Anthill.Kernel
