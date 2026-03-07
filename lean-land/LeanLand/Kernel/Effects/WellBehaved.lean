import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Effect
import LeanLand.Kernel.Defs.Operation
import LeanLand.Kernel.Effects.Resources

/-!
# Well-Behavedness

An effectful operation respects its declared effects when it only modifies
the resources listed in its Modifies effects, and all required capabilities
are present.
-/

namespace Anthill.Kernel

/-- An effectful operation respects its effect-env condition. -/
def respectsEffectEnv (effs : List Effect) (eBefore eAfter : Env) : Prop :=
  ∀ s, s ∉ modifiesResources effs → eAfter s = eBefore s

/-- A pure (effect-free) operation preserves the entire environment. -/
theorem pure_effect_env (e : Env) : respectsEffectEnv [] e e := by
  intro s _
  rfl

/-- Effect-env weakening: declaring more effects makes the constraint easier to satisfy. -/
theorem effect_env_weaken {effs1 effs2 : List Effect} {e1 e2 : Env}
    (hsub : ∀ e, e ∈ effs1 → e ∈ effs2)
    (h : respectsEffectEnv effs1 e1 e2) :
    respectsEffectEnv effs2 e1 e2 := by
  intro s hs
  apply h
  intro hmem
  apply hs
  simp only [modifiesResources, List.mem_filterMap] at *
  obtain ⟨e, he1, he2⟩ := hmem
  exact ⟨e, hsub e he1, he2⟩

/-- All required capabilities are present in the environment. -/
def capabilitiesPresent (effs : List Effect) (e : Env) : Prop :=
  ∀ c, c ∈ requiredCapabilities effs → e c ≠ none

/-- An implementation is well-behaved w.r.t. its operation spec. -/
def wellBehaved (spec : Operation) (impl : EffectfulOp) : Prop :=
  ∀ e args res,
    capabilitiesPresent spec.effects e →
    impl e args = .inl res →
    respectsEffectEnv spec.effects e res.env

end Anthill.Kernel

