package anthill.load

import anthill.kb.{KnowledgeBase, SortKind, BuiltinTag}
import anthill.intern.SymbolKind

/** Register prelude sorts and builtins into the KB.
  *
  * Creates the anthill namespace hierarchy and primitive sorts (Int, Float, String, Bool),
  * then registers standard builtins.
  */
object Prelude:

  /** Well-known kernel meta sorts. */
  private val kernelMetaSorts = IndexedSeq(
    "Sort", "Entity", "Fact", "Rule", "Operation", "Namespace",
    "Constraint", "EntityOf", "Param", "Field"
  )

  /** Register the prelude: primitive sorts + namespace hierarchy + builtins. */
  def register(kb: KnowledgeBase): Unit =
    registerStdlibScopes(kb)
    registerPrimitiveSorts(kb)
    registerKernelMetaSorts(kb)
    registerStandardBuiltins(kb)

  private def registerStdlibScopes(kb: KnowledgeBase): Unit =
    val globalScope = kb.makeNameTerm("_global")

    // anthill namespace
    val anthillSym = kb.symbols.define("anthill", "anthill", SymbolKind.Namespace, globalScope.raw)
    val anthillScope = kb.makeNameTermFromSym(anthillSym)
    kb.symbols.addExport(globalScope.raw, "anthill")

    // anthill.prelude
    val preludeSym = kb.symbols.define("prelude", "anthill.prelude", SymbolKind.Namespace, anthillScope.raw)
    val preludeScope = kb.makeNameTermFromSym(preludeSym)
    kb.symbols.addExport(anthillScope.raw, "prelude")

    // anthill.reflect
    val reflectSym = kb.symbols.define("reflect", "anthill.reflect", SymbolKind.Namespace, anthillScope.raw)
    val reflectScope = kb.makeNameTermFromSym(reflectSym)
    kb.symbols.addExport(anthillScope.raw, "reflect")

    // anthill.reflect.typing
    val typingSym = kb.symbols.define("typing", "anthill.reflect.typing", SymbolKind.Namespace, reflectScope.raw)
    kb.symbols.addExport(reflectScope.raw, "typing")

  private def registerPrimitiveSorts(kb: KnowledgeBase): Unit =
    val preludeScope = kb.resolveQualifiedNameTerm("anthill.prelude")
    for name <- IndexedSeq("Int", "Float", "String", "Bool") do
      val qualName = s"anthill.prelude.$name"
      val sym = kb.symbols.define(name, qualName, SymbolKind.Sort, preludeScope.raw)
      val sortTerm = kb.makeNameTermFromSym(sym)
      kb.registerSort(sortTerm, SortKind.Defined)
      kb.symbols.addExport(preludeScope.raw, name)

  private def registerKernelMetaSorts(kb: KnowledgeBase): Unit =
    val globalScope = kb.makeNameTerm("_global")
    for name <- kernelMetaSorts do
      val qualName = s"anthill.reflect.$name"
      val reflectScope = kb.resolveQualifiedNameTerm("anthill.reflect")
      val sym = kb.symbols.define(name, qualName, SymbolKind.Sort, reflectScope.raw)
      val sortTerm = kb.makeNameTermFromSym(sym)
      kb.registerSort(sortTerm, SortKind.Defined)
      kb.symbols.addExport(reflectScope.raw, name)

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
      // Find or create the symbol
      val short = qualName.split('.').last
      // Find the namespace scope
      val nsPrefix = qualName.substring(0, qualName.lastIndexOf('.'))
      kb.tryResolveSymbol(nsPrefix) match
        case Some(nsSym) =>
          val nsScope = kb.makeNameTermFromSym(nsSym)
          val sym = kb.symbols.define(short, qualName, SymbolKind.Operation, nsScope.raw)
          kb.symbols.addExport(nsScope.raw, short)
          kb.registerBuiltin(sym, tag)
        case None =>
          // Namespace not found — fallback intern
          val sym = kb.intern(qualName)
          kb.registerBuiltin(sym, tag)
