/-!
# Sort Mapping

How anthill sort declarations compile to Lean 4 constructs.

| Anthill                         | Lean 4                              |
|---------------------------------|-------------------------------------|
| `sort T = ?` (type parameter)  | `variable (T : Type)`               |
| `sort T = Int` (type alias)    | `abbrev T := Int`                   |
| `sort S { entity C₁, C₂ }`    | `inductive S \| C₁ \| C₂`          |
| `entity E(f: A)` (standalone)  | `structure E where f : A`           |
| `sort S { entity C(x: A) }`   | `inductive S` + `structure C`       |
-/

namespace Anthill.Mapping.Sorts

-- Example: abstract sort (type parameter)
-- anthill: `sort T = ?`
-- Lean:    `variable (T : Type)`

-- Example: type alias
-- anthill: `sort Age = Int`
abbrev Age := Int

-- Example: enumeration sort
-- anthill: `sort Color { entity Red; entity Green; entity Blue }`
inductive Color where
  | red
  | green
  | blue
  deriving Repr, BEq, DecidableEq

-- Example: entity with fields (standalone)
-- anthill: `entity Point(x: Int, y: Int)`
structure Point where
  x : Int
  y : Int
  deriving Repr, BEq

-- Example: sort with entity constructors carrying data
-- anthill: `sort Shape { entity Circle(radius: Int); entity Rect(w: Int, h: Int) }`
inductive Shape where
  | circle (radius : Int)
  | rect   (w : Int) (h : Int)
  deriving Repr, BEq

end Anthill.Mapping.Sorts
