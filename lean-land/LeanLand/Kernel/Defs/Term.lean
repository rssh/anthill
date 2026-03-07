import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Literal

/-!
# Terms

The universal representation in the kernel language.  Sorts are themselves
terms (types-are-terms principle).  The `A` prefix avoids clashes with
Lean's built-in `Term` type.

`ATerm` and `FnArg` are mutually inductive.
-/

namespace Anthill.Kernel

mutual
/-- Function argument: positional or named. -/
inductive FnArg where
  | positional : ATerm → FnArg
  | named      : Symbol → ATerm → FnArg

/-- Anthill term — the universal representation in the kernel. -/
inductive ATerm where
  | const  : Literal → ATerm
  | var    : VarId → ATerm
  | fn     : Symbol → List FnArg → ATerm
  | ref    : Symbol → ATerm
  | quoted : (lang : String) → (src : String) → ATerm
  | bottom : ATerm
end

end Anthill.Kernel

-- BEq for mutual inductives — must be at top level for mutual forward refs
mutual
partial def Anthill.Kernel.beqATerm : Anthill.Kernel.ATerm → Anthill.Kernel.ATerm → Bool
  | .const l1,      .const l2      => l1 == l2
  | .var v1,        .var v2        => v1 == v2
  | .fn f1 args1,   .fn f2 args2   => f1 == f2 && Anthill.Kernel.beqFnArgList args1 args2
  | .ref s1,        .ref s2        => s1 == s2
  | .quoted l1 s1,  .quoted l2 s2  => l1 == l2 && s1 == s2
  | .bottom,        .bottom        => true
  | _,              _              => false

partial def Anthill.Kernel.beqFnArg : Anthill.Kernel.FnArg → Anthill.Kernel.FnArg → Bool
  | .positional t1,  .positional t2  => Anthill.Kernel.beqATerm t1 t2
  | .named n1 t1,    .named n2 t2    => n1 == n2 && Anthill.Kernel.beqATerm t1 t2
  | _,               _               => false

partial def Anthill.Kernel.beqFnArgList : List Anthill.Kernel.FnArg → List Anthill.Kernel.FnArg → Bool
  | [], [] => true
  | a :: as, b :: bs => Anthill.Kernel.beqFnArg a b && Anthill.Kernel.beqFnArgList as bs
  | _, _ => false
end

instance : BEq Anthill.Kernel.ATerm where beq := Anthill.Kernel.beqATerm
instance : BEq Anthill.Kernel.FnArg where beq := Anthill.Kernel.beqFnArg

namespace Anthill.Kernel

/-- Encode a list of terms as cons/nil chain (used by reflect types). -/
def listToCons : List ATerm → ATerm
  | []      => .fn "nil" []
  | x :: xs => .fn "cons" [.named "head" x, .named "tail" (listToCons xs)]

end Anthill.Kernel
