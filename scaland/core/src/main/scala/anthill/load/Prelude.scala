package anthill.load

import anthill.kb.{KnowledgeBase, SortKind, BuiltinTag}
import anthill.intern.{SymbolKind, ScopeId, ScopeInclusion}

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
    registerBuiltinTags(kb)
    registerGlobalParents(kb)

  /** The stdlib's namespace spine, created before any file is scanned.
    *
    * WI-992: these are the scopes a dotted declaration (`sort anthill.prelude.Eq`) now
    * lands in — `Loader.ensureNamespacePath` reuses them rather than synthesizing its
    * own — so they must have the SHAPE the loader gives a namespace it creates, and one
    * half was missing: the ENCLOSING parent. Without it nothing declared inside
    * `anthill.prelude` could see `_global`, and a miss there is silent (`resolveName`
    * interns and carries on). It never bit before because these scopes were only ever
    * searched INTO, through the `_global` parent links `registerGlobalParents` adds —
    * a file writing `namespace anthill.reflect` minted a SECOND symbol, keyed by the
    * dotted spelling in `_global`, and put its declarations there instead. */
  private def registerStdlibScopes(kb: KnowledgeBase): Unit =
    def defineNamespace(short: String, qualName: String, enclosing: ScopeId): ScopeId =
      val scope = ScopeId.of(kb.symbols.define(short, qualName, SymbolKind.Namespace, enclosing))
      kb.symbols.addParent(scope, ScopeInclusion(enclosing, isEnclosing = true))
      scope

    val anthillScope = defineNamespace("anthill", "anthill", kb.globalScope)
    defineNamespace("prelude", "anthill.prelude", anthillScope)
    val reflectScope = defineNamespace("reflect", "anthill.reflect", anthillScope)
    defineNamespace("typing", "anthill.reflect.typing", reflectScope)

  private def registerPrimitiveSorts(kb: KnowledgeBase): Unit =
    val preludeScope = kb.scopeByQualifiedName("anthill.prelude")
    for name <- IndexedSeq("Int64", "BigInt", "Float", "String", "Bool") do
      val qualName = s"anthill.prelude.$name"
      val sym = kb.symbols.define(name, qualName, SymbolKind.Sort, preludeScope)
      kb.registerSort(kb.makeNameTermFromSym(sym), SortKind.Defined)

  private def registerKernelMetaSorts(kb: KnowledgeBase): Unit =
    val reflectScope = kb.scopeByQualifiedName("anthill.reflect")
    for name <- kernelMetaSorts do
      val qualName = s"anthill.reflect.$name"
      val sym = kb.symbols.define(name, qualName, SymbolKind.Sort, reflectScope)
      kb.registerSort(kb.makeNameTermFromSym(sym), SortKind.Defined)

  /** Register Expr, Pattern, TypedExpr sorts and their entities. */
  private def registerExprSorts(kb: KnowledgeBase): Unit =
    val reflectScope = kb.scopeByQualifiedName("anthill.reflect")

    // Helper to define a sort with enclosing scope. The sort is also linked
    // as a non-enclosing parent of its parent scope so its entity variants
    // (added via defineEntity → addExposed) resolve bare from the enclosing
    // scope — the variant-exposure mechanism (proposal 044 job 2).
    def defineSort(shortName: String, qualName: String, parentScope: ScopeId): ScopeId =
      val sym = kb.symbols.define(shortName, qualName, SymbolKind.Sort, parentScope)
      val sortScope = ScopeId.of(sym)
      kb.registerSort(kb.makeNameTermFromSym(sym), SortKind.Defined)
      kb.symbols.addParent(sortScope, ScopeInclusion(parentScope, isEnclosing = true))
      kb.symbols.addParent(parentScope, ScopeInclusion(sortScope, isEnclosing = false))
      sortScope

    // Helper to define an entity (variant) in a sort scope — exposed to the
    // enclosing scope via the sort's variant-exposure link.
    def defineEntity(shortName: String, qualName: String, scope: ScopeId): Unit =
      kb.symbols.define(shortName, qualName, SymbolKind.Entity, scope)
      kb.symbols.addExposed(scope, shortName)

    // Helper to define a standalone entity directly in the reflect scope.
    // Visible by default (reflect is a parent of _global with empty `exposed`).
    def defineReflectEntity(shortName: String): Unit =
      kb.symbols.define(shortName, s"anthill.reflect.$shortName", SymbolKind.Entity, reflectScope)

    // anthill.reflect.Expr sort + entities
    val exprScope = defineSort("Expr", "anthill.reflect.Expr", reflectScope)
    for name <- IndexedSeq("match_expr", "if_expr", "let_expr", "lambda_expr", "apply",
      "constructor", "var_ref", "int_lit", "bigint_lit", "float_lit", "string_lit", "bool_lit") do
      defineEntity(name, s"anthill.reflect.Expr.$name", exprScope)

    // anthill.reflect.Pattern sort + entities
    val patternScope = defineSort("Pattern", "anthill.reflect.Pattern", reflectScope)
    for name <- IndexedSeq("var_pattern", "tuple_pattern", "named_tuple_pattern",
      "constructor_pattern", "literal_pattern", "wildcard") do
      defineEntity(name, s"anthill.reflect.Pattern.$name", patternScope)

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
    val typedExprScope = defineSort("TypedExpr", "anthill.reflect.TypedExpr", reflectScope)
    defineEntity("typed", "anthill.reflect.TypedExpr.typed", typedExprScope)

    // Global imports for reflect entities
    val globalScope = kb.globalScope
    for name <- IndexedSeq("SortInfo", "FieldInfo", "OperationInfo", "EntityInfo",
        "SortRequiresInfo", "SortView", "SetLiteral", "TupleLiteral", "ListLiteral") do
      kb.tryResolveSymbol(s"anthill.reflect.$name").foreach { sym =>
        kb.symbols.addImport(globalScope, name, sym)
      }

  private def registerBuiltinTags(kb: KnowledgeBase): Unit =
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
          val sym = kb.symbols.define(short, qualName, SymbolKind.Operation, ScopeId.of(nsSym))
          kb.registerBuiltinTag(sym, tag)
        case None =>
          val sym = kb.intern(qualName)
          kb.registerBuiltinTag(sym, tag)

  /** Add anthill.prelude and anthill.reflect as parents of _global,
    * making their exports visible everywhere.
    */
  private def registerGlobalParents(kb: KnowledgeBase): Unit =
    val globalScope = kb.globalScope
    val preludeScope = kb.scopeByQualifiedName("anthill.prelude")
    kb.symbols.addParent(globalScope, ScopeInclusion(preludeScope, isEnclosing = false))
    val reflectScope = kb.scopeByQualifiedName("anthill.reflect")
    kb.symbols.addParent(globalScope, ScopeInclusion(reflectScope, isEnclosing = false))
