import LeanLand.Kernel.Defs.Term

/-!
# Rules (Horn Clauses)

A rule has an optional name, a head term, and a list of body terms.
- Derivation rule: non-Bottom head, non-empty body.
- Ground assertion (fact): non-Bottom head, empty body.
- Denial (integrity constraint): head = Bottom.
-/

namespace Anthill.Kernel

/-- An anthill rule (Horn clause). -/
structure ARule where
  name : Option Symbol
  head : ATerm
  body : List ATerm
  deriving BEq

def ARule.isFact (r : ARule) : Bool :=
  r.body.isEmpty && r.head != .bottom

def ARule.isDenial (r : ARule) : Bool :=
  r.head == .bottom

def ARule.isDerivation (r : ARule) : Bool :=
  !r.body.isEmpty && r.head != .bottom

/-- Every rule is exactly one of fact, denial, or derivation. -/
theorem rule_trichotomy (r : ARule) :
    r.head = .bottom ∨
    (r.head ≠ .bottom ∧ r.body = []) ∨
    (r.head ≠ .bottom ∧ r.body ≠ []) := by
  by_cases h : r.head = .bottom
  · left; exact h
  · by_cases hb : r.body = []
    · right; left; exact ⟨h, hb⟩
    · right; right; exact ⟨h, hb⟩

end Anthill.Kernel

