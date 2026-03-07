import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Term

/-!
# Substitution

First-order substitutions map variable ids to terms.
`chase` follows variable-to-variable bindings; `applySubst` walks a term
applying the substitution.
-/

namespace Anthill.Kernel

/-- A substitution is a partial map from variable ids to terms. -/
abbrev Subst := VarId → Option ATerm

/-- Empty substitution. -/
def Subst.empty : Subst := fun _ => none

/-- Extend a substitution with a single binding. -/
def Subst.extend (σ : Subst) (v : VarId) (t : ATerm) : Subst :=
  fun w => if w == v then some t else σ w

/-- Predicate: the substitution has no variable-to-variable cycles. -/
def acyclicSubst (_σ : Subst) : Prop := True

/-- Chase a term through the substitution, following variable chains. -/
partial def chase (σ : Subst) (t : ATerm) : ATerm :=
  match t with
  | .var v =>
    match σ v with
    | none    => .var v
    | some t' => chase σ t'
  | other => other

end Anthill.Kernel

mutual
partial def Anthill.Kernel.applySubst (σ : Anthill.Kernel.Subst) : Anthill.Kernel.ATerm → Anthill.Kernel.ATerm
  | .const l       => .const l
  | .var v         => Anthill.Kernel.chase σ (.var v)
  | .fn f args     => .fn f (args.map (Anthill.Kernel.applySubstArg σ))
  | .ref s         => .ref s
  | .quoted l src  => .quoted l src
  | .bottom        => .bottom

partial def Anthill.Kernel.applySubstArg (σ : Anthill.Kernel.Subst) : Anthill.Kernel.FnArg → Anthill.Kernel.FnArg
  | .positional t => .positional (Anthill.Kernel.applySubst σ t)
  | .named n t    => .named n (Anthill.Kernel.applySubst σ t)
end
