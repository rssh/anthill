import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Sort
import LeanLand.Kernel.Defs.Rule
import LeanLand.Kernel.Defs.Operation

/-!
# Visibility and Namespaces

Module items and module bodies are mutually inductive.
A `ModuleBody` represents either a namespace or a sort-with-body declaration.
-/

namespace Anthill.Kernel

/-- Visibility of a module. -/
inductive Visibility where
  | «internal»
  | «export»
  | «public»

mutual
/-- A single item inside a module. -/
inductive ModuleItem where
  | sort      : SortId → SortKind → ModuleItem
  | entity    : ATerm → ModuleItem
  | rule      : ARule → ModuleItem
  | operation : Operation → ModuleItem
  | «requires»  : ATerm → ModuleItem
  | subModule : ModuleBody → ModuleItem

/-- A module body: namespace or sort-with-body.
    `primarySort = some s` means sort-with-body; `none` means namespace. -/
inductive ModuleBody where
  | mk (name : Symbol) (primarySort : Option SortId)
       (items : List ModuleItem) (visibility : Visibility) : ModuleBody
end

namespace ModuleBody

def name : ModuleBody → Symbol
  | .mk n _ _ _ => n

def primarySort : ModuleBody → Option SortId
  | .mk _ ps _ _ => ps

def items : ModuleBody → List ModuleItem
  | .mk _ _ is _ => is

def visibility : ModuleBody → Visibility
  | .mk _ _ _ v => v

end ModuleBody

/-- Extract direct entity terms from a list of module items. -/
def directEntities : List ModuleItem → List ATerm
  | [] => []
  | .entity e :: rest => e :: directEntities rest
  | _ :: rest => directEntities rest

/-- Determine sort kind from module items: Defined if entities present, else Abstract. -/
def determineSortKind (items : List ModuleItem) : SortKind :=
  if (directEntities items).isEmpty then .abstract else .defined

end Anthill.Kernel
