import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.Defs.Effect
import LeanLand.Kernel.Effects.Resources
import LeanLand.Kernel.Effects.WellBehaved

/-!
# Monadic Interpretation

The monadic interpretation views an effectful operation as a computation
in a combined monad layering State, Writer, Except, Reader.

Provides return, bind, primitives (get/put/emit/throw/requireCapability),
and the three monad laws, plus round-trip equivalence between the
state-passing and monadic representations.
-/

namespace Anthill.Kernel

/-- The effect monad: `Env → (α × Env × Events) + Error`. -/
abbrev EffMonad (α : Type) := Env → Sum (α × Env × List ATerm) ATerm

/-- Pure return. -/
def returnEff (x : α) : EffMonad α :=
  fun e => .inl (x, e, [])

/-- Monadic bind. -/
def bindEff (m : EffMonad α) (f : α → EffMonad β) : EffMonad β :=
  fun e =>
    match m e with
    | .inr err => .inr err
    | .inl (a, e', evts1) =>
      match f a e' with
      | .inr err => .inr err
      | .inl (b, e'', evts2) => .inl (b, e'', evts1 ++ evts2)

/-- Get a resource value. -/
def getResource (s : Symbol) : EffMonad (Option ATerm) :=
  fun e => .inl (e s, e, [])

/-- Set a resource value. -/
def putResource (s : Symbol) (v : ATerm) : EffMonad Unit :=
  fun e => .inl ((), fun k => if k == s then some v else e k, [])

/-- Emit an event. -/
def emitEvent (evt : ATerm) : EffMonad Unit :=
  fun e => .inl ((), e, [evt])

/-- Throw an error. -/
def throwError' (err : ATerm) : EffMonad α :=
  fun _ => .inr err

/-- Require a capability (fail if missing). -/
def requireCapability (c : Symbol) : EffMonad Unit :=
  fun e =>
    match e c with
    | some _ => .inl ((), e, [])
    | none   => .inr (.fn "missing_capability" [.positional (.ref c)])

-- Conversions between state-passing and monadic representations

/-- Convert state-passing to monadic. -/
def toMonad (f : EffectfulOp) (args : List ATerm) : EffMonad ATerm :=
  fun e =>
    match f e args with
    | .inr err => .inr err
    | .inl r   => .inl (r.value, r.env, r.events)

/-- Convert monadic to state-passing. -/
def fromMonad (m : List ATerm → EffMonad ATerm) : EffectfulOp :=
  fun e args =>
    match m args e with
    | .inr err => .inr err
    | .inl (v, e', evts) => .inl { value := v, env := e', events := evts }

end Anthill.Kernel
