import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.Subst.FreeVars

/-!
# Occurs Check

Syntactic occurs check: does variable `v` occur anywhere in term `t`?
Used after chasing, so no substitution parameter is needed.
-/

namespace Anthill.Kernel
end Anthill.Kernel

mutual
partial def Anthill.Kernel.occursIn (v : Anthill.Kernel.VarId) : Anthill.Kernel.ATerm → Bool
  | .const _      => false
  | .var w        => v == w
  | .fn _ args    => args.any (Anthill.Kernel.occursInArg v)
  | .ref _        => false
  | .quoted _ _   => false
  | .bottom       => false

partial def Anthill.Kernel.occursInArg (v : Anthill.Kernel.VarId) : Anthill.Kernel.FnArg → Bool
  | .positional t => Anthill.Kernel.occursIn v t
  | .named _ t    => Anthill.Kernel.occursIn v t
end

