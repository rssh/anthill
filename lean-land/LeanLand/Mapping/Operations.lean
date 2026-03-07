/-!
# Operation Mapping

How anthill operations compile to Lean 4 definitions and class methods.

| Anthill                                      | Lean 4                            |
|----------------------------------------------|-----------------------------------|
| `operation f(a: A) -> B` (standalone)       | `def f (a : A) : B`              |
| `operation f(a: A) -> B` (in sort S)        | method in `class S`               |
| `requires P(a)` on operation                | proof argument `(h : P a)`       |
| `ensures Q(result)` on operation            | subtype return `{ b : B // Q b }` |
-/

namespace Anthill.Mapping.Operations

-- Example: standalone operation
-- anthill: `operation double(n: Int) -> Int`
def double (n : Int) : Int := n * 2

-- Example: operation with precondition
-- anthill: `operation safeDivide(a: Int, b: Int) -> Int requires nonzero(b)`
def safeDivide (a b : Int) (_h : b ≠ 0) : Int := a / b

-- Example: operation with postcondition
-- anthill: `operation abs(n: Int) -> Int ensures non_negative(result)`
def abs' (n : Int) : { r : Int // r ≥ 0 } :=
  if h : n ≥ 0 then ⟨n, h⟩ else ⟨-n, by omega⟩

-- Example: operations as class methods
-- anthill: `sort Eq { sort T = ?; operation eq(a: T, b: T) -> Bool }`
class Eq' (T : Type) where
  eq : T → T → Bool

-- anthill: `sort Ordered { requires Eq{T}; operation compare(a: T, b: T) -> Int }`
class Ordered (T : Type) extends Eq' T where
  compare : T → T → Int

end Anthill.Mapping.Operations
