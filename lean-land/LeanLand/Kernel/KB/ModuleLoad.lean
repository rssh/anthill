import LeanLand.Kernel.Defs.Term
import LeanLand.Kernel.Defs.Sort
import LeanLand.Kernel.Defs.Rule
import LeanLand.Kernel.Defs.Effect
import LeanLand.Kernel.Defs.Operation
import LeanLand.Kernel.Defs.Visibility
import LeanLand.Kernel.Defs.Reflect
import LeanLand.Kernel.KB.FactEntry
import LeanLand.Kernel.KB.FactOps
import LeanLand.Kernel.KB.SortReg

/-!
# Module Loading

Load module items and bodies into the knowledge base.  This corresponds
to the loader phase that converts parsed declarations into KB facts.
-/

namespace Anthill.Kernel
end Anthill.Kernel

open Anthill.Kernel in
mutual
/-- Load a single module item into the KB within a given scope. -/
partial def Anthill.Kernel.loadModuleItem (kb : KnowledgeBase) (sc : SortId) : ModuleItem → KnowledgeBase
  | .sort s k => registerSort kb s k
  | .entity e => (assertFact kb e (.fn "Entity" []) sc none).1
  | .rule r   => (assertFact kb r.head (.fn "Rule" []) sc none).1
  | .operation oper =>
    let nameRef := ATerm.ref oper.name
    let sortCtx := match sc with
      | .fn s [] => optionSome (.ref s)
      | _ => optionNone
    let paramTerms := oper.params.map fun (n, t) => fieldInfoTerm n t
    let effectTerms := oper.effects.map fun e => ATerm.fn e.kind [.positional (.ref e.target)]
    let oi := opInfoTerm nameRef sortCtx paramTerms oper.ret effectTerms
    (assertFact kb oi (.fn "Operation" []) sc none).1
  | .«requires» t =>
    (assertFact kb (.fn "Requires" [.positional t]) (.fn "Requirement" []) sc none).1
  | .subModule mb => Anthill.Kernel.loadModuleBody kb mb

/-- Load a list of module items. -/
partial def Anthill.Kernel.loadModuleItems (kb : KnowledgeBase) (sc : SortId) : List ModuleItem → KnowledgeBase
  | [] => kb
  | i :: rest => Anthill.Kernel.loadModuleItems (Anthill.Kernel.loadModuleItem kb sc i) sc rest

/-- Load a module body (namespace or sort-with-body). -/
partial def Anthill.Kernel.loadModuleBody (kb : KnowledgeBase) : ModuleBody → KnowledgeBase
  | .mk name ps items _vis =>
    let scope := ATerm.fn name []
    let kb1 := match ps with
      | none   => (assertFact kb scope (.fn "Namespace" []) scope none).1
      | some s => registerConstructorSubsorts (registerSort kb s (determineSortKind items)) s (directEntities items)
    let kb2 := Anthill.Kernel.loadModuleItems kb1 scope items
    match ps with
    | none => kb2
    | some s =>
      let hasEntities := directEntities items != []
      let defTerm := if hasEntities then s else .var kb2.nextVar
      let ctorRefs := (directEntities items).map fun
        | .fn f _ => ATerm.ref f
        | e => e
      let si : SortInfo := {
        name := .ref name,
        definition := defTerm,
        constructors := ctorRefs,
        operations := [],
        parameters := [],
        requires := []
      }
      (assertFact kb2 (sortInfoTerm si) (.fn "Sort" []) scope none).1
end
