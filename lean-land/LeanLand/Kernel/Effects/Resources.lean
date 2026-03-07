import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Effect

/-!
# Resource Projections

Extract resource sets from effect lists.
Reads is always a superset of Modifies (you read what you mutate).
-/

namespace Anthill.Kernel

def readsResources (effs : List Effect) : List Symbol :=
  effs.filterMap fun e =>
    if e.kind == "Reads" || e.kind == "Modifies" then some e.target else none

def modifiesResources (effs : List Effect) : List Symbol :=
  effs.filterMap fun e =>
    if e.kind == "Modifies" then some e.target else none

def emitsEvents (effs : List Effect) : List Symbol :=
  effs.filterMap fun e =>
    if e.kind == "Emits" then some e.target else none

def requiredCapabilities (effs : List Effect) : List Symbol :=
  effs.filterMap fun e =>
    if e.kind == "Requires" then some e.target else none

def errorTypes (effs : List Effect) : List Symbol :=
  effs.filterMap fun e =>
    if e.kind == "Errors" then some e.target else none

end Anthill.Kernel
