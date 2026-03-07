import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.KB.FactEntry

/-!
# Fact Operations

find, assert, retract, and activeFacts on the knowledge base, plus
key lemmas (idempotence, validity, preservation).
-/

namespace Anthill.Kernel

/-- Find an active fact matching term, sort, and domain. -/
def findFactAux : List FactEntry → Nat → ATerm → SortId → SortId → Option FactId
  | [], _, _, _, _ => none
  | e :: es, idx, t, s, d =>
    if e.term == t && e.sort == s && e.domain == d && !e.retracted
    then some idx
    else findFactAux es (idx + 1) t s d

def findExistingFact (kb : KnowledgeBase) (t : ATerm) (s d : SortId) : Option FactId :=
  findFactAux kb.facts 0 t s d

/-- Assert a fact.  If an identical active fact exists, return its id (idempotent). -/
def assertFact (kb : KnowledgeBase) (t : ATerm) (s d : SortId) (m : Option ATerm)
    : KnowledgeBase × FactId :=
  match findExistingFact kb t s d with
  | some fid => (kb, fid)
  | none =>
    let fid := kb.facts.length
    let entry : FactEntry := { term := t, sort := s, domain := d, metadata := m, retracted := false }
    let kb' := { kb with facts := kb.facts ++ [entry] }
    (kb', fid)

/-- Retract a fact by id (mark as retracted). -/
def retract (kb : KnowledgeBase) (fid : FactId) : KnowledgeBase :=
  let facts' := kb.facts.mapIdx fun i e =>
    if i == fid then { e with retracted := true } else e
  { kb with facts := facts' }

/-- Active (non-retracted) facts with their ids. -/
def activeFactsAux (acc : List (FactId × FactEntry)) (idx : Nat) : List FactEntry → List (FactId × FactEntry)
  | [] => acc.reverse
  | e :: es => if !e.retracted then activeFactsAux ((idx, e) :: acc) (idx + 1) es
               else activeFactsAux acc (idx + 1) es

def activeFacts (kb : KnowledgeBase) : List (FactId × FactEntry) :=
  activeFactsAux [] 0 kb.facts

-- Lemmas

/-- Asserting a fact preserves or extends the store by exactly one. -/
theorem assertFact_preserves_or_extends (kb : KnowledgeBase) (t : ATerm) (s d : SortId) (m : Option ATerm) :
    let (kb', _) := assertFact kb t s d m
    kb'.facts.length = kb.facts.length ∨ kb'.facts.length = kb.facts.length + 1 := by
  simp only [assertFact]
  split
  · left; rfl
  · right; simp [List.length_append]

/-- Asserting an existing fact is idempotent. -/
theorem assertFact_idempotent {kb : KnowledgeBase} {t : ATerm} {s d : SortId} {fid : FactId}
    (m : Option ATerm) :
    findExistingFact kb t s d = some fid →
    assertFact kb t s d m = (kb, fid) := by
  intro h
  simp [assertFact, h]

end Anthill.Kernel
