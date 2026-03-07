import LeanLand.Kernel.Defs.Symbol
import LeanLand.Kernel.Defs.Term

/-!
# Reflect Types

Structured fact shapes emitted by the loader and queried by the
reflection API.  Mirrors `stdlib/anthill/reflect/reflect.anthill`.
-/

namespace Anthill.Kernel

/-- Structural decomposition of constants. -/
inductive LiteralRepr where
  | intLiteral    : Int → LiteralRepr
  | floatLiteral  : Float → LiteralRepr
  | stringLiteral : String → LiteralRepr
  | boolLiteral   : Bool → LiteralRepr
  deriving Repr

/-- Structural decomposition of a term for introspection.
    Name fields in `fnRepr` and `refRepr` are Symbol references
    (stored as `Ref sym` terms). -/
inductive TermRepr where
  | constRepr  : LiteralRepr → TermRepr
  | varRepr    : String → TermRepr
  | fnRepr     : ATerm → List TermRepr → TermRepr
  | refRepr    : ATerm → TermRepr
  | quotedRepr : String → String → TermRepr

/-- Structured fact emitted for each sort-with-body declaration.
    All name fields are Symbol references; list fields use cons/nil encoding. -/
structure SortInfo where
  name         : ATerm
  definition   : ATerm
  constructors : List ATerm
  operations   : List ATerm
  parameters   : List ATerm
  requires     : List ATerm

/-- Build a `SortInfo` fact term with named arguments. -/
def sortInfoTerm (si : SortInfo) : ATerm :=
  .fn "SortInfo" [
    .named "name" si.name,
    .named "definition" si.definition,
    .named "constructors" (listToCons si.constructors),
    .named "operations" (listToCons si.operations),
    .named "parameters" (listToCons si.parameters),
    .named "requires" (listToCons si.requires)
  ]

/-- Build a `FieldInfo` term for an operation parameter. -/
def fieldInfoTerm (name : Symbol) (typeTerm : ATerm) : ATerm :=
  .fn "FieldInfo" [
    .named "name" (.const (.litString name)),
    .named "type_name" typeTerm
  ]

/-- Build an `OperationInfo` fact term. -/
def opInfoTerm (nameRef sortCtx : ATerm) (paramTerms : List ATerm)
    (returnTerm : ATerm) (effectTerms : List ATerm) : ATerm :=
  .fn "OperationInfo" [
    .named "name" nameRef,
    .named "sort_context" sortCtx,
    .named "params" (listToCons paramTerms),
    .named "return_type" returnTerm,
    .named "effects" (listToCons effectTerms)
  ]

/-- Option encoding helpers. -/
def optionSome (v : ATerm) : ATerm := .fn "some" [.named "value" v]
def optionNone : ATerm := .fn "none" []

end Anthill.Kernel

