/-!
# Effect Mapping

How anthill effect declarations map to Lean 4 monad transformer stacks.

| Anthill                    | Lean 4                              |
|----------------------------|-------------------------------------|
| `effects (Error{E})`     | `Except E`                          |
| `effects (Modify{S})`    | `StateM S`                          |
| `effects (Read{S})`      | `ReaderM S`                         |
| `effects (Emit{E})`      | writer pattern (e.g., `StateM (List E)`) |
| combined effects          | monad transformer stack             |
-/

namespace Anthill.Mapping.Effects

-- Example: operation with Error effect
-- anthill: `operation parseNum(s: String) -> Int effects (Error{String})`
def parseNum (s : String) : Except String Int :=
  match s.toInt? with
  | some n => .ok n
  | none   => .error s!"not a number: {s}"

-- Example: operation with Modify effect
-- anthill: `operation increment(counter: String) -> Unit effects (Modify{Nat})`
def increment : StateM Nat Unit :=
  modify (· + 1)

-- Example: combined Error + State
-- anthill: `operation withdraw(amount: Int) -> Unit effects (Modify{Int}, Error{String})`
def withdraw (amount : Int) : StateT Int (Except String) Unit := do
  let balance ← get
  if balance ≥ amount then
    set (balance - amount)
  else
    throw s!"insufficient balance"

end Anthill.Mapping.Effects
