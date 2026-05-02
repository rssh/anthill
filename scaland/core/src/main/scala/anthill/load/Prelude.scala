package anthill.load

import anthill.kb.{KnowledgeBase, SortKind, BuiltinTag}
import anthill.intern.{SymbolKind, ScopeInclusion, TermSymbol}
import anthill.term.{Term, TermId}

/** Register prelude sorts and builtins into the KB. */
object Prelude:

  private val kernelMetaSorts = IndexedSeq(
    "Sort", "Entity", "Fact", "Rule", "Operation", "Namespace",
    "Constraint", "EntityOf", "Param", "Field"
  )

  def register(kb: KnowledgeBase): Unit =
    registerStdlibScopes(kb)
    registerPrimitiveSorts(kb)
    registerKernelMetaSorts(kb)
    registerExprSorts(kb)
    registerStandardBuiltins(kb)
    registerStructuralOps(kb)
    registerGlobalParents(kb)

  private def registerStdlibScopes(kb: KnowledgeBase): Unit =
    val globalScope = kb.makeNameTerm("_global")

    val anthillSym = kb.symbols.define("anthill", "anthill", SymbolKind.Namespace, globalScope.raw)
    val anthillScope = kb.makeNameTermFromSym(anthillSym)
    kb.symbols.addExport(globalScope.raw, "anthill")

    val preludeSym = kb.symbols.define("prelude", "anthill.prelude", SymbolKind.Namespace, anthillScope.raw)
    kb.makeNameTermFromSym(preludeSym)
    kb.symbols.addExport(anthillScope.raw, "prelude")

    val reflectSym = kb.symbols.define("reflect", "anthill.reflect", SymbolKind.Namespace, anthillScope.raw)
    kb.makeNameTermFromSym(reflectSym)
    kb.symbols.addExport(anthillScope.raw, "reflect")

    val typingSym = kb.symbols.define("typing", "anthill.reflect.typing", SymbolKind.Namespace,
      kb.resolveQualifiedNameTerm("anthill.reflect").raw)
    kb.symbols.addExport(kb.resolveQualifiedNameTerm("anthill.reflect").raw, "typing")

  private def registerPrimitiveSorts(kb: KnowledgeBase): Unit =
    val preludeScope = kb.resolveQualifiedNameTerm("anthill.prelude")
    for name <- IndexedSeq("Int", "BigInt", "Float", "String", "Bool") do
      val qualName = s"anthill.prelude.$name"
      val sym = kb.symbols.define(name, qualName, SymbolKind.Sort, preludeScope.raw)
      val sortTerm = kb.makeNameTermFromSym(sym)
      kb.registerSort(sortTerm, SortKind.Defined)
      kb.symbols.addExport(preludeScope.raw, name)

  private def registerKernelMetaSorts(kb: KnowledgeBase): Unit =
    val reflectScope = kb.resolveQualifiedNameTerm("anthill.reflect")
    for name <- kernelMetaSorts do
      val qualName = s"anthill.reflect.$name"
      val sym = kb.symbols.define(name, qualName, SymbolKind.Sort, reflectScope.raw)
      val sortTerm = kb.makeNameTermFromSym(sym)
      kb.registerSort(sortTerm, SortKind.Defined)
      kb.symbols.addExport(reflectScope.raw, name)

  /** Register Expr, Pattern, TypedExpr sorts and their entities. */
  private def registerExprSorts(kb: KnowledgeBase): Unit =
    val reflectScope = kb.resolveQualifiedNameTerm("anthill.reflect")

    // Helper to define a sort with enclosing scope
    def defineSort(shortName: String, qualName: String, parentScope: TermId): TermId =
      val sym = kb.symbols.define(shortName, qualName, SymbolKind.Sort, parentScope.raw)
      val sortTerm = kb.makeNameTermFromSym(sym)
      kb.registerSort(sortTerm, SortKind.Defined)
      kb.symbols.addExport(parentScope.raw, shortName)
      kb.symbols.addParent(sortTerm.raw,
        ScopeInclusion(parentScope.raw, parentScope.raw, isEnclosing = true))
      sortTerm

    // Helper to define an entity in a sort scope
    def defineEntity(shortName: String, qualName: String, scopeTerm: TermId): Unit =
      kb.symbols.define(shortName, qualName, SymbolKind.Entity, scopeTerm.raw)
      kb.symbols.addExport(scopeTerm.raw, shortName)

    // Helper to define a standalone entity in reflect scope
    def defineReflectEntity(shortName: String): Unit =
      kb.symbols.define(shortName, s"anthill.reflect.$shortName", SymbolKind.Entity, reflectScope.raw)
      kb.symbols.addExport(reflectScope.raw, shortName)

    // anthill.reflect.Expr sort + entities
    val exprTerm = defineSort("Expr", "anthill.reflect.Expr", reflectScope)
    for name <- IndexedSeq("match_expr", "if_expr", "let_expr", "lambda", "apply",
      "constructor", "var_ref", "int_lit", "bigint_lit", "float_lit", "string_lit", "bool_lit") do
      defineEntity(name, s"anthill.reflect.Expr.$name", exprTerm)

    // anthill.reflect.Pattern sort + entities
    val patternTerm = defineSort("Pattern", "anthill.reflect.Pattern", reflectScope)
    for name <- IndexedSeq("var_pattern", "tuple_pattern", "named_tuple_pattern",
      "constructor_pattern", "literal_pattern", "wildcard") do
      defineEntity(name, s"anthill.reflect.Pattern.$name", patternTerm)

    // Standalone entities
    defineReflectEntity("MatchBranch")
    defineReflectEntity("ApplyArg")

    // Reflect metadata entities (mirrors Rust register_prelude)
    defineReflectEntity("SortInfo")
    defineReflectEntity("FieldInfo")
    defineReflectEntity("OperationInfo")
    defineReflectEntity("EntityInfo")
    defineReflectEntity("SortRequiresInfo")
    defineReflectEntity("SortView")

    // Collection literal entities (Proposal 019)
    // Used by the parser; the typing process (Proposal 011) desugars to concrete constructors
    defineReflectEntity("SetLiteral")
    defineReflectEntity("TupleLiteral")
    defineReflectEntity("ListLiteral")

    // anthill.reflect.TypedExpr sort
    val typedExprTerm = defineSort("TypedExpr", "anthill.reflect.TypedExpr", reflectScope)
    defineEntity("typed", "anthill.reflect.TypedExpr.typed", typedExprTerm)

    // Global imports for reflect entities
    val globalScope = kb.makeNameTerm("_global")
    for name <- IndexedSeq("SortInfo", "FieldInfo", "OperationInfo", "EntityInfo",
        "SortRequiresInfo", "SortView", "SetLiteral", "TupleLiteral", "ListLiteral") do
      kb.tryResolveSymbol(s"anthill.reflect.$name").foreach { sym =>
        kb.symbols.addImport(globalScope.raw, name, sym)
      }

  private def registerStandardBuiltins(kb: KnowledgeBase): Unit =
    val builtinDefs = IndexedSeq(
      ("anthill.reflect.nonvar", BuiltinTag.NonVar),
      ("anthill.reflect.ground", BuiltinTag.Ground),
      ("anthill.reflect.qualified_name", BuiltinTag.QualifiedName),
      ("anthill.reflect.short_name", BuiltinTag.ShortName),
      ("anthill.reflect.lookup_symbol", BuiltinTag.LookupSymbol),
      ("anthill.reflect.not", BuiltinTag.Not),
      ("anthill.reflect.typing.is_entity_of", BuiltinTag.IsEntityOf),
      ("anthill.reflect.typing.extract_sort_ref", BuiltinTag.ExtractSort),
      ("anthill.reflect.resolve_sort_instantiation_param", BuiltinTag.ResolveSortInstParam),
      ("anthill.reflect.scope", BuiltinTag.Scope),
      ("anthill.reflect.kind", BuiltinTag.Kind),
      ("anthill.reflect.field_access", BuiltinTag.FieldAccess),
    )

    for (qualName, tag) <- builtinDefs do
      val short = qualName.split('.').last
      val nsPrefix = qualName.substring(0, qualName.lastIndexOf('.'))
      kb.tryResolveSymbol(nsPrefix) match
        case Some(nsSym) =>
          val nsScope = kb.makeNameTermFromSym(nsSym)
          val sym = kb.symbols.define(short, qualName, SymbolKind.Operation, nsScope.raw)
          kb.symbols.addExport(nsScope.raw, short)
          kb.registerBuiltin(sym, tag)
        case None =>
          val sym = kb.intern(qualName)
          kb.registerBuiltin(sym, tag)

  /** Register structural operator names as prelude-level operations.
    * These correspond to Pratt table functor mappings that don't belong to any specific sort.
    */
  private def registerStructuralOps(kb: KnowledgeBase): Unit =
    val preludeScope = kb.resolveQualifiedNameTerm("anthill.prelude")
    for name <- IndexedSeq("eq", "neq", "or", "and", "not", "arrow",
        "lt", "lte", "gt", "gte", "div", "mod", "pow", "neg") do
      val qualName = s"anthill.prelude.$name"
      kb.symbols.define(name, qualName, SymbolKind.Operation, preludeScope.raw)
      kb.symbols.addExport(preludeScope.raw, name)

  /** Add anthill.prelude and anthill.reflect as parents of _global,
    * making their exports visible everywhere.
    */
  private def registerGlobalParents(kb: KnowledgeBase): Unit =
    val globalScope = kb.makeNameTerm("_global")
    val preludeScope = kb.resolveQualifiedNameTerm("anthill.prelude")
    kb.symbols.addParent(globalScope.raw, ScopeInclusion(preludeScope.raw, 0, isEnclosing = false))
    val reflectScope = kb.resolveQualifiedNameTerm("anthill.reflect")
    kb.symbols.addParent(globalScope.raw, ScopeInclusion(reflectScope.raw, 0, isEnclosing = false))
