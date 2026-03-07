import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Term

/-!
# Effects

Effects give operations a state-passing interpretation.  An effect is
an open (kind, target) pair.  The well-known kinds Modifies, Reads, Emits,
Errors, Requires are defined in stdlib; additional effect kinds may be
introduced by libraries.
-/

namespace Anthill.Kernel

/-- An effect declaration: (kind, target) pair. -/
structure Effect where
  kind   : Symbol
  target : Symbol
  deriving Repr, BEq, DecidableEq

/-- Well-known effect constructors. -/
abbrev effModifies (s : Symbol) : Effect := ⟨"Modifies", s⟩
abbrev effReads    (s : Symbol) : Effect := ⟨"Reads", s⟩
abbrev effEmits    (s : Symbol) : Effect := ⟨"Emits", s⟩
abbrev effErrors   (s : Symbol) : Effect := ⟨"Errors", s⟩
abbrev effRequires (s : Symbol) : Effect := ⟨"Requires", s⟩

/-- The environment maps resource names to their current state (as terms). -/
abbrev Env := Symbol → Option ATerm

/-- Result of a successful effectful operation. -/
structure EffectfulResult where
  value  : ATerm
  env    : Env
  events : List ATerm

/-- An effectful operation: takes env and args, returns success or error. -/
abbrev EffectfulOp := Env → List ATerm → Sum EffectfulResult ATerm

end Anthill.Kernel

