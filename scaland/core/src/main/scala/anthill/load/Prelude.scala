package anthill.load

import anthill.kb.{KnowledgeBase, SortKind, BuiltinTag}
import anthill.intern.{SymbolKind, TermSymbol, ImportOrigin}

/** Register prelude sorts and builtins into the KB. */
object Prelude:

  private val kernelMetaSorts = IndexedSeq(
    "Sort", "Entity", "Fact", "Rule", "Operation", "Namespace",
    "Constraint", "EntityOf", "Param", "Field"
  )

  /** The stdlib's namespace spine, as a VALUE (WI-990) — the one thing
    * [[registerStdlibScopes]] produces and every later step consumes.
    *
    * The steps used to re-derive these scopes by qualified name from the KB
    * (`scopeByQualifiedName("anthill.prelude")`), which THREW on a miss into a `Unit`
    * return: a step run before the spine existed aborted KB bootstrap with a stack trace,
    * and nothing but the statement order inside [[register]] kept that unreachable. Eight
    * lines away [[registerBuiltinTags]] met the identical condition and DEGRADED instead —
    * two policies for one condition in one file. Passing the scopes makes the condition
    * unrepresentable: a step cannot be called before the spine exists, because it cannot
    * be called without it. `PreludeScopesTest` asserts that as a compile error.
    *
    * `private[load]` for that test alone — nothing outside this file constructs one.
    *
    * FOUR fields, not five: the enclosing `anthill` namespace is a step on the way to the
    * other four and no later step reads it, so it stays a local. A field with no reader is
    * a field nothing can catch being wrong — and all four have the SAME type, so a
    * positional slip between them would type-check. `kernel` joined them in
    * WI-20260820-MH90F, which made that argument one slip stronger, so every construction
    * and every read of this record is in this file and within a screen of the other.
    *
    * `S` is the KB's scope type (WI-1004) — the record is held outside the table that
    * issues one, so it names the table the way [[anthill.intern.SymbolDef]] does. */
  private[load] case class StdlibScopes[S](
    prelude: S, reflect: S, reflectTyping: S, kernel: S)

  def register(kb: KnowledgeBase): Unit =
    val scopes = registerStdlibScopes(kb)
    registerPrimitiveSorts(kb, scopes)
    registerKernelMetaSorts(kb, scopes)
    registerExprSorts(kb, scopes)
    registerBuiltinTags(kb, scopes)
    registerGlobalParents(kb, scopes)

  /** The stdlib's namespace spine, created before any file is scanned.
    *
    * WI-992: these are the scopes a dotted declaration (`sort anthill.prelude.Eq`) now
    * lands in — `Loader.ensureNamespacePath` reuses them rather than synthesizing its
    * own — so they must have the SHAPE the loader gives a namespace it creates, and one
    * half was missing: the ENCLOSING parent. Without it nothing declared inside
    * `anthill.prelude` could see `<global>`, and a miss there is silent (`resolveName`
    * interns and carries on). It never bit before because these scopes were only ever
    * searched INTO, through the `<global>` parent links `registerGlobalParents` adds —
    * a file writing `namespace anthill.reflect` minted a SECOND symbol, keyed by the
    * dotted spelling in `<global>`, and put its declarations there instead. */
  // `private[load]` for `PreludeScopesTest` alone (with `registerPrimitiveSorts` below):
  // the two together are the shape its `typeCheckErrors` snippets need — a producer and
  // one consumer. The other four steps stay `private`; they take the same argument.
  private[load] def registerStdlibScopes(kb: KnowledgeBase): StdlibScopes[kb.ScopeId] =
    def defineNamespace(short: String, qualName: String, enclosing: kb.ScopeId): kb.ScopeId =
      val scope = kb.symbols.scopeOf(
        kb.symbols.define(short, qualName, SymbolKind.Namespace, enclosing))
      kb.symbols.addParent(scope, enclosing, isEnclosing = true)
      scope

    val anthillScope = defineNamespace("anthill", "anthill", kb.globalScope)
    val preludeScope = defineNamespace("prelude", "anthill.prelude", anthillScope)
    val reflectScope = defineNamespace("reflect", "anthill.reflect", anthillScope)
    val typingScope = defineNamespace("typing", "anthill.reflect.typing", reflectScope)
    // WI-20260820-MH90F: `not` is a RESOLVER PRIMITIVE and lives with the others, so
    // the spine needs `anthill.kernel` before `registerBuiltinTags` can define it there.
    // `kernel.anthill` re-opens this scope rather than minting a second one (WI-992).
    val kernelScope = defineNamespace("kernel", "anthill.kernel", anthillScope)
    StdlibScopes(preludeScope, reflectScope, typingScope, kernelScope)

  /** Define `short` in `scope`, with the qualified name DERIVED from the scope (WI-990).
    *
    * Every definition in this file used to write the qualified name as a literal beside
    * the scope it passed — `s"anthill.prelude.$name"` next to `scopes.prelude`, at ~30
    * sites — so the two could disagree with nothing to notice, and the name that keys
    * `byQualifiedName` is an IDENTITY, not a decoration. One derivation makes the pair
    * unable to diverge, and it is the same rule the loader joins with
    * ([[Loader.makeQualified]]), not a second copy of it.
    *
    * Deriving through [[KnowledgeBase.qualifiedNameOf]] and NOT `scopeDisplayName`: the
    * latter is documented as the name to call a scope in a DIAGNOSTIC (WI-957), and
    * WI-987 proposes changing what it renders for the synthetic global scope. A key must
    * not move when a message does. */
  private def defineIn(
    kb: KnowledgeBase, scope: kb.ScopeId, short: String, kind: SymbolKind
  ): TermSymbol =
    kb.symbols.define(
      short,
      Loader.makeQualified(kb.qualifiedNameOf(kb.symbols.symbolOf(scope)), short),
      kind, scope)

  // `private[load]` for `PreludeScopesTest` — see `registerStdlibScopes` above.
  private[load] def registerPrimitiveSorts(kb: KnowledgeBase, scopes: StdlibScopes[kb.ScopeId]): Unit =
    for name <- IndexedSeq("Int64", "BigInt", "Float", "String", "Bool") do
      val sym = defineIn(kb, scopes.prelude, name, SymbolKind.Sort)
      kb.registerSort(kb.makeNameTermFromSym(sym), SortKind.Defined)

  private def registerKernelMetaSorts(kb: KnowledgeBase, scopes: StdlibScopes[kb.ScopeId]): Unit =
    for name <- kernelMetaSorts do
      val sym = defineIn(kb, scopes.reflect, name, SymbolKind.Sort)
      kb.registerSort(kb.makeNameTermFromSym(sym), SortKind.Defined)

  /** Register Expr, Pattern, TypedExpr sorts and their entities. */
  private def registerExprSorts(kb: KnowledgeBase, scopes: StdlibScopes[kb.ScopeId]): Unit =
    val reflectScope = scopes.reflect

    // Helper to define a sort with enclosing scope. The sort is also linked
    // as a non-enclosing parent of its parent scope so its entity variants
    // (added via defineEntity → addExposed) resolve bare from the enclosing
    // scope — the variant-exposure mechanism (proposal 044 job 2).
    def defineSort(shortName: String, parentScope: kb.ScopeId): kb.ScopeId =
      val sym = defineIn(kb, parentScope, shortName, SymbolKind.Sort)
      val sortScope = kb.symbols.scopeOf(sym)
      kb.registerSort(kb.makeNameTermFromSym(sym), SortKind.Defined)
      kb.symbols.addParent(sortScope, parentScope, isEnclosing = true)
      // WI-M460D — the exposure link says so on the link (`exposed` filters it and no
      // other). Written before any `defineEntity` fills `exposed`, which is why it is
      // added unconditionally here: an empty `exposed` disables the filter anyway.
      kb.symbols.addExposureParent(parentScope, sortScope)
      sortScope

    // Helper to define an entity (variant) in a sort scope — exposed to the
    // enclosing scope via the sort's variant-exposure link.
    def defineEntity(shortName: String, scope: kb.ScopeId): Unit =
      defineIn(kb, scope, shortName, SymbolKind.Entity)
      kb.symbols.addExposed(scope, shortName)

    // Helper to define a standalone entity directly in the reflect scope.
    // Visible by default (reflect is a parent of <global> with empty `exposed`).
    // RETURNS its symbol (WI-990): the global-import loop below used to look these
    // names back up by string and drop a miss through `Option.foreach` — a definition
    // and a re-lookup of the same name, with the same silent degrade the WI removed
    // from `registerBuiltinTags`. Handing the symbol forward has no miss to drop.
    def defineReflectEntity(shortName: String): TermSymbol =
      defineIn(kb, reflectScope, shortName, SymbolKind.Entity)

    // THIS BLOCK HAS NO PRODUCER — the vocabulary is registered, nothing in scaland emits
    // it. These are the REFLECT ENTITIES (the spec vocabulary — `stdlib/anthill/reflect/
    // reflect.anthill` declares the same `var_pattern` / `wildcard` / `MatchBranch`), the
    // TARGET of a translation from the parser's PARSE-TIME MARKERS (`pattern_var`,
    // `pattern_wildcard`, `match_branch`, …, see `anthill.parse.ExprMarker`) that
    // rustland performs in `convert_expr_term`. Scaland's copy of it was ported ahead of
    // any consumer and WI-1007 deleted it, so this is the target vocabulary of a
    // translation this tree does not perform. Registered anyway, mirroring rustland's
    // `register_prelude` and reachable BY NAME like any declared entity.
    //
    // WI-1009 CLOSED THE HAZARD, which was not the orphans: four spellings here —
    // `match_expr` / `if_expr` / `let_expr` / `lambda_expr` — are ALSO marker names, and
    // `reallocTerm` resolves every functor by name, so a marker in a rule body used to
    // capture the entity symbol of its spelling (leaking as an undeclared predicate where
    // the two vocabularies happened to disagree). The loader now refuses a marker by its
    // PROVENANCE before any name is read, so nothing here is reachable except by being
    // written — which is why adding to this list is safe again. `ExprLoaderTest` drives
    // both halves; do not weaken that refusal to a name test, which is the shape this
    // collision defeats.
    val exprScope = defineSort("Expr", reflectScope)
    for name <- IndexedSeq("match_expr", "if_expr", "let_expr", "lambda_expr", "apply",
      "constructor", "var_ref", "int_lit", "bigint_lit", "float_lit", "string_lit", "bool_lit") do
      defineEntity(name, exprScope)

    val patternScope = defineSort("Pattern", reflectScope)
    for name <- IndexedSeq("var_pattern", "tuple_pattern", "named_tuple_pattern",
      "constructor_pattern", "literal_pattern", "wildcard") do
      defineEntity(name, patternScope)

    // Standalone entities
    defineReflectEntity("MatchBranch")
    defineReflectEntity("ApplyArg")

    // Reflect metadata entities (mirrors Rust register_prelude)
    val metadataEntities = IndexedSeq("SortInfo", "FieldInfo", "OperationInfo", "EntityInfo",
      "SortRequiresInfo", "SortView").map(n => (n, defineReflectEntity(n)))

    // Collection literal entities (Proposal 019)
    // Used by the parser; the typing process (Proposal 011) desugars to concrete constructors
    val literalEntities = IndexedSeq("SetLiteral", "TupleLiteral", "ListLiteral")
      .map(n => (n, defineReflectEntity(n)))

    // anthill.reflect.TypedExpr sort
    val typedExprScope = defineSort("TypedExpr", reflectScope)
    defineEntity("typed", typedExprScope)

    // Global imports for reflect entities. WI-1074 — Builtin: registered by the
    // bootstrap, written in no file, so local to none — this is scaland's `<global>`
    // ruling, mirroring rustland's `register_implicit_prelude_effects`.
    val globalScope = kb.globalScope
    for (name, sym) <- metadataEntities ++ literalEntities do
      kb.symbols.addImport(globalScope, name, sym, ImportOrigin.Builtin)

  /** A kernel operation is DEFINED in its namespace scope, always (WI-990).
    *
    * The scope used to be re-derived here from the qualified name, with a degrade arm for
    * the miss: `kb.intern(qualName)` registered the tag on a symbol whose whole spelling
    * was `anthill.kernel.not`, in no scope at all — so `not(...)` would resolve to
    * nothing and the builtin would be unreachable BY NAME, with nothing said. The scope is
    * now passed in, so the miss has no arm to take.
    *
    * The list is in definition order, so the symbol ids it allocates are the ones it
    * always allocated. */
  private def registerBuiltinTags(kb: KnowledgeBase, scopes: StdlibScopes[kb.ScopeId]): Unit =
    val reflect = scopes.reflect
    val typing = scopes.reflectTyping
    val kernel = scopes.kernel
    val builtinDefs = IndexedSeq(
      (reflect, "nonvar", BuiltinTag.NonVar),
      (reflect, "ground", BuiltinTag.Ground),
      (reflect, "qualified_name", BuiltinTag.QualifiedName),
      (reflect, "short_name", BuiltinTag.ShortName),
      (reflect, "lookup_symbol", BuiltinTag.LookupSymbol),
      (kernel, "not", BuiltinTag.Not),
      (typing, "is_entity_of", BuiltinTag.IsEntityOf),
      (typing, "extract_sort_ref", BuiltinTag.ExtractSort),
      (reflect, "resolve_sort_instantiation_param", BuiltinTag.ResolveSortInstParam),
      (reflect, "scope", BuiltinTag.Scope),
      (reflect, "kind", BuiltinTag.Kind),
      (reflect, "field_access", BuiltinTag.FieldAccess),
    )

    for (scope, short, tag) <- builtinDefs do
      val sym = defineIn(kb, scope, short, SymbolKind.Operation)
      kb.registerBuiltinTag(sym, tag)
      // WI-20260820-MH90F: `anthill.kernel` is deliberately NOT a `<global>` parent (see
      // `registerGlobalParents`), so a kernel builtin carries its own single-symbol
      // import. `not` is written BARE in rule bodies (`:- not(...)` in typing.anthill)
      // and had that reach through the `reflect` parent until it moved namespaces; this
      // preserves exactly that one name and widens nothing. Keyed on the SCOPE, so a
      // later kernel builtin gets the same reach without a second decision.
      if scope == kernel then
        kb.symbols.addImport(kb.globalScope, short, sym, ImportOrigin.Builtin)

  /** Add anthill.prelude and anthill.reflect as parents of <global>,
    * making their exports visible everywhere.
    *
    * `anthill.kernel` is NOT parented here, though `registerStdlibScopes` now defines it
    * (WI-20260820-MH90F). Its members are reached through their OPERATORS (`<=>` → `unify`,
    * `===` → `struct_eq`, `|` → `or`, a bare `!` → `cut`) or by qualified name; bulk-parenting the
    * namespace would additionally put those short names into every user scope as ambiguity
    * candidates, which is a wider change than moving one symbol. The one member spelled bare
    * — `not` — imports itself, in `registerBuiltinTags` above.
    */
  private def registerGlobalParents(kb: KnowledgeBase, scopes: StdlibScopes[kb.ScopeId]): Unit =
    val globalScope = kb.globalScope
    kb.symbols.addParent(globalScope, scopes.prelude, isEnclosing = false)
    kb.symbols.addParent(globalScope, scopes.reflect, isEnclosing = false)
