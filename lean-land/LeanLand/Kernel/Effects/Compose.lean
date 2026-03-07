import LeanLand.Kernel.Defs.Effect
import LeanLand.Kernel.Effects.Resources
import LeanLand.Kernel.Effects.WellBehaved

/-!
# Effectful Composition

Compose two effectful operations: thread the environment, concatenate events.
-/

namespace Anthill.Kernel

/-- Compose two effectful operations sequentially. -/
def composeEffectful (f g : EffectfulOp) : EffectfulOp := fun e args =>
  match f e args with
  | .inr err => .inr err
  | .inl r1 =>
    match g r1.env [r1.value] with
    | .inr err => .inr err
    | .inl r2 => .inl {
        value  := r2.value,
        env    := r2.env,
        events := r1.events ++ r2.events
      }

end Anthill.Kernel
