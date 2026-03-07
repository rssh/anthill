import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.KB.FactEntry

/-!
# Subsort Relation

The subsort relation is the reflexive-transitive closure of the declared
subsort pairs.  We define `RTClosure` locally (no Mathlib dependency).
-/

namespace Anthill.Kernel

/-- Reflexive-transitive closure of a relation on a type with BEq. -/
inductive RTClosure (R : List (α × α)) : α → α → Prop where
  | refl  : RTClosure R a a
  | step  : (a, b) ∈ R → RTClosure R b c → RTClosure R a c

/-- The raw subsort relation (direct pairs). -/
def subsortRel (kb : KnowledgeBase) : List (SortId × SortId) :=
  kb.subsort

/-- Is `s1` a subtype of `s2` (via reflexive-transitive closure)? -/
def isSubtype (kb : KnowledgeBase) (s1 s2 : SortId) : Prop :=
  RTClosure kb.subsort s1 s2

/-- Subtype is reflexive. -/
theorem isSubtype_refl (kb : KnowledgeBase) (s : SortId) :
    isSubtype kb s s :=
  RTClosure.refl

/-- Subtype is transitive. -/
theorem isSubtype_trans (kb : KnowledgeBase) (a b c : SortId)
    (h1 : isSubtype kb a b) (h2 : isSubtype kb b c) :
    isSubtype kb a c := by
  induction h1 with
  | refl => exact h2
  | step hab _ ih => exact RTClosure.step hab (ih h2)

end Anthill.Kernel

