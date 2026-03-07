/-!
# Trust Levels

Trust is attached to facts, not agents.  The ordering captures verification
strength; `axiom` and `decision` sit outside the main chain.
-/
namespace Anthill.Kernel

/-- Trust level attached to facts. -/
inductive Trust where
  | proved
  | verified
  | tested   : Nat → Trust
  | empirical
  | proposed
  | stale
  | axiom
  | decision
  deriving Repr, BEq

/-- Rank function: lower number = higher trust. -/
def trustRank : Trust → Nat
  | .proved     => 0
  | .verified   => 1
  | .tested _   => 2
  | .empirical  => 3
  | .proposed   => 4
  | .stale      => 5
  | .axiom      => 0
  | .decision   => 0

/-- Whether a trust level is on the main verification chain. -/
def onVerificationChain : Trust → Bool
  | .axiom    => false
  | .decision => false
  | _         => true

/-- Ordering on the main verification chain. -/
def trustLe (t1 t2 : Trust) : Bool :=
  onVerificationChain t1 && onVerificationChain t2 &&
  (trustRank t1 < trustRank t2 ||
   (trustRank t1 == trustRank t2 &&
    match t1, t2 with
    | .tested n1, .tested n2 => n1 ≥ n2
    | _, _ => true))

scoped infixl:50 " ≤ₜ " => trustLe

/-- Proved is at least as trusted as every chain member. -/
theorem proved_top (t : Trust) (h : onVerificationChain t = true) :
    trustLe .proved t = true := by
  cases t <;> simp_all [trustLe, trustRank, onVerificationChain]

/-- More tests ⟹ more trust among `tested` levels. -/
theorem tested_monotone (h : n1 ≥ n2) :
    trustLe (.tested n1) (.tested n2) = true := by
  simp [trustLe, trustRank, onVerificationChain]
  omega

end Anthill.Kernel
