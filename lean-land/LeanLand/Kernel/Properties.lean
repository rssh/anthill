import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Literal
import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.Defs.Sort
import LeanLand.Kernel.Defs.Trust
import LeanLand.Kernel.Defs.Rule
import LeanLand.Kernel.Defs.Effect
import LeanLand.Kernel.Defs.Operation
import LeanLand.Kernel.Defs.Visibility
import LeanLand.Kernel.Defs.Reflect
import LeanLand.Kernel.Defs.Builtin
import LeanLand.Kernel.Subst.Subst
import LeanLand.Kernel.Subst.FreeVars
import LeanLand.Kernel.Subst.OccursCheck
import LeanLand.Kernel.Subst.Unify
import LeanLand.Kernel.KB.FactEntry
import LeanLand.Kernel.KB.Subsort
import LeanLand.Kernel.KB.FactOps
import LeanLand.Kernel.KB.Query
import LeanLand.Kernel.KB.SortReg
import LeanLand.Kernel.KB.ModuleLoad
import LeanLand.Kernel.KB.FreshVar
import LeanLand.Kernel.Effects.Resources
import LeanLand.Kernel.Effects.WellBehaved
import LeanLand.Kernel.Effects.Compose
import LeanLand.Kernel.Effects.Monad
import LeanLand.Kernel.Reasoning.Denial
import LeanLand.Kernel.Reasoning.ForwardChain

/-!
# Properties

Re-exports of key definitions and theorems from the kernel formalization.

Proved theorems:
- **Trust**: `proved_top`, `tested_monotone`
- **Rules**: `rule_trichotomy`
- **Effects**: `pure_effect_env`
- **KB facts**: `assertFact_preserves_or_extends`, `assertFact_idempotent`
- **Subsort**: `isSubtype_refl`, `isSubtype_trans`
- **Denial**: `query_empty_kb`
-/
