import LeanLand.Kernel.Defs.Term

/-!
# Full Worked Examples

Complete anthill → Lean 4 translations demonstrating all mapping rules together.
-/

namespace Anthill.Mapping.Examples

/-!
## Example 1: Stack

```anthill
namespace Stack {
  sort T = ?

  sort Stack {
    entity Empty
    entity Push(top: T, rest: Stack)

    operation push(s: Stack, val: T) -> Stack
    operation pop(s: Stack) -> Stack
      requires non_empty(s)
    operation peek(s: Stack) -> T
      requires non_empty(s)

    rule push_pop: pop(push(s, v)) = s
    rule push_peek: peek(push(s, v)) = v
  }
}
```
-/

inductive Stack (T : Type) where
  | empty : Stack T
  | push  : (top : T) → (rest : Stack T) → Stack T
  deriving Repr, BEq

namespace Stack

def push' (s : Stack T) (val : T) : Stack T := .push val s

def pop : Stack T → Stack T
  | .empty      => .empty
  | .push _ rest => rest

def peek : Stack T → Option T
  | .empty     => none
  | .push t _  => some t

@[simp] theorem push_pop (s : Stack T) (v : T) :
    pop (push' s v) = s := rfl

@[simp] theorem push_peek (s : Stack T) (v : T) :
    peek (push' s v) = some v := rfl

end Stack

/-!
## Example 2: Comparable with spec satisfaction

```anthill
namespace Prelude {
  sort Eq {
    sort T = ?
    operation eq(a: T, b: T) -> Bool
  }
  sort Ordered {
    sort T = ?
    requires Eq{T}
    operation compare(a: T, b: T) -> Int
  }
  fact Eq{T = Int}
  fact Ordered{T = Int}
}
```
-/

class Eq₂ (T : Type) where
  eq : T → T → Bool

class Ordered₂ (T : Type) extends Eq₂ T where
  compare : T → T → Int

instance : Eq₂ Int where
  eq a b := a == b

instance : Ordered₂ Int where
  compare a b := if a < b then -1 else if a > b then 1 else 0

/-!
## Example 3: Effectful counter

```anthill
namespace Counter {
  sort KB { entity kb }
  operation increment() -> Int
    effects (Modify{kb})
  operation get_count() -> Int
    effects (Read{kb})
}
```
-/

def counterIncrement : StateM Int Int := do
  let n ← get
  let n' := n + 1
  set n'
  return n'

def counterGetCount : StateM Int Int := get

end Anthill.Mapping.Examples
