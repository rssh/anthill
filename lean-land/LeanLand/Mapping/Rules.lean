/-!
# Rule Mapping

How anthill rules compile to Lean 4 theorems and instances.

| Anthill                              | Lean 4                              |
|--------------------------------------|-------------------------------------|
| `rule eq: a = b`                    | `@[simp] theorem`                   |
| `fact Eq{T = Int}`                  | `instance : Eq Int`                 |
| `constraint C :- G`                 | `theorem` (impossibility proof)     |
-/

namespace Anthill.Mapping.Rules

-- Example: rule as simp theorem
-- anthill: `rule double_zero: double(0) = 0`
@[simp] theorem double_zero : (0 : Int) * 2 = 0 := by omega

-- Example: fact as instance
-- anthill: `fact Eq{T = Int}`
-- (Int already has BEq in Lean, so this is just illustrative)
instance : BEq Int where
  beq a b := a == b

-- Example: constraint as impossibility theorem
-- anthill: `constraint no_negative_age :- age(?x, ?a), less_than(?a, 0)`
-- This would be a theorem stating the constraint body is unsatisfiable.
-- In Lean: expressed as a theorem that the conjunction implies False.
-- (Illustrative; actual encoding depends on the KB representation.)

end Anthill.Mapping.Rules
