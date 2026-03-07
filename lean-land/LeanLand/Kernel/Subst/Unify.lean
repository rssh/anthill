import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.Subst.Subst
import LeanLand.Kernel.Subst.OccursCheck

/-!
# Unification

First-order unification with occurs check.  Positional argument lists
are unified pairwise; named arguments are matched by name.
-/

namespace Anthill.Kernel

/-- Reasons unification can fail. -/
inductive UnifyError where
  | clash
  | occursCheck
  | arityMismatch
  deriving Repr, BEq

end Anthill.Kernel

open Anthill.Kernel in
mutual
partial def Anthill.Kernel.unify (σ : Subst) (t1 t2 : ATerm) : Sum Subst UnifyError :=
  match t1, t2 with
  | .var v, _ =>
    let t2' := chase σ t2
    match t2' with
    | .var w => if v == w then .inl σ else .inl (σ.extend v t2')
    | _ => if occursIn v t2' then .inr .occursCheck else .inl (σ.extend v t2')
  | _, .var v =>
    let t1' := chase σ t1
    match t1' with
    | .var w => if v == w then .inl σ else .inl (σ.extend v t1')
    | _ => if occursIn v t1' then .inr .occursCheck else .inl (σ.extend v t1')
  | .const l1, .const l2 =>
    if l1 == l2 then .inl σ else .inr .clash
  | .fn f1 args1, .fn f2 args2 =>
    if f1 == f2 && args1.length == args2.length
    then Anthill.Kernel.unifyArgs σ args1 args2
    else .inr .clash
  | .ref s1, .ref s2 =>
    if s1 == s2 then .inl σ else .inr .clash
  | .bottom, .bottom => .inl σ
  | _, _ => .inr .clash

partial def Anthill.Kernel.unifyArgs (σ : Subst) (as1 as2 : List FnArg) : Sum Subst UnifyError :=
  match as1, as2 with
  | [], [] => .inl σ
  | .positional t1 :: r1, .positional t2 :: r2 =>
    match Anthill.Kernel.unify σ t1 t2 with
    | .inl σ' => Anthill.Kernel.unifyArgs σ' r1 r2
    | .inr e  => .inr e
  | .named n1 t1 :: r1, .named n2 t2 :: r2 =>
    if n1 == n2 then
      match Anthill.Kernel.unify σ t1 t2 with
      | .inl σ' => Anthill.Kernel.unifyArgs σ' r1 r2
      | .inr e  => .inr e
    else .inr .clash
  | _, _ => .inr .arityMismatch
end

