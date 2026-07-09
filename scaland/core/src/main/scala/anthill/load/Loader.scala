package anthill.load

import anthill.kb.{KnowledgeBase, SortKind}
import anthill.intern.{TermSymbol, SymbolTable, SymbolKind, SymbolDef, ScopeInclusion, ResolveResult}
import anthill.term.{Term, TermId, Var, VarId, Literal}
import anthill.parse.*
import anthill.span.Span

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

/** Load errors. */
enum LoadError:
  case UnresolvedName(name: String, span: Span, scopeName: String)
  case UnresolvedImport(path: String, span: Span)
  case AmbiguousSymbol(name: String, candidates: IndexedSeq[String], span: Span, scopeName: String)
  case Other(message: String)

/** IR → KB loading.
  *
  * Converts parsed files into KnowledgeBase terms and facts.
  * Two phases: scanDefinitions (define all names) then load (fill KB).
  */
object Loader:

  /** Scan all parsed files to define symbols and build scope chain. */
  def scanDefinitions(kb: KnowledgeBase, files: IndexedSeq[ParsedFile]): ArrayBuffer[LoadError] =
    val globalScope = kb.makeNameTerm("_global")
    val errors = ArrayBuffer.empty[LoadError]

    // Pass 1: Define all names
    for file <- files do
      scanItemsPass1(kb, file.items, file.symbols, file.terms, globalScope, "")

    // Pass 2: Process requires and imports
    for file <- files do
      scanItemsPass2(kb, file.items, file.symbols, globalScope, "", errors)

    // Post-pass: auto-import prelude sort contents into global scope
    autoImportPrelude(kb, globalScope)

    errors

  /** Load a parsed file into the KB (Phase 2 — after scanDefinitions). */
  def load(kb: KnowledgeBase, file: ParsedFile): ArrayBuffer[LoadError] =
    val globalScope = kb.makeNameTerm("_global")
    val errors = ArrayBuffer.empty[LoadError]
    loadItems(kb, file.items, file.symbols, file.terms, globalScope, "", errors)
    errors

  /** Load multiple files: scan first, then load all. */
  def loadAll(kb: KnowledgeBase, files: IndexedSeq[ParsedFile]): ArrayBuffer[LoadError] =
    val errors = scanDefinitions(kb, files)
    for file <- files do
      errors ++= load(kb, file)
    errors

  // ── Pass 1: Define names ─────────────────────────────────────

  private def scanItemsPass1(
    kb: KnowledgeBase,
    items: Iterable[Item],
    fileSym: SymbolTable,
    fileTerms: SimpleTermStore,
    scopeTerm: TermId,
    prefix: String
  ): Unit =
    for item <- items do
      item match
        case Item.NamespaceItem(ns) =>
          val shortName = joinSegments(fileSym, ns.name.segments)
          val qualName = makeQualified(prefix, shortName)
          val sym = kb.symbols.define(shortName, qualName, SymbolKind.Namespace, scopeTerm.raw)
          val nsTerm = kb.makeNameTermFromSym(sym)
          // Enclosing scope. (Model C / proposal 044: names visible by default;
          // the `export` statement was removed in WI-291.)
          kb.symbols.addParent(nsTerm.raw, ScopeInclusion(scopeTerm.raw, 0, isEnclosing = true))
          scanItemsPass1(kb, ns.items, fileSym, fileTerms, nsTerm, qualName)

        case Item.SortWithBodyItem(sort) =>
          val shortName = joinSegments(fileSym, sort.name.segments)
          val qualName = makeQualified(prefix, shortName)
          val sym = kb.symbols.define(shortName, qualName, SymbolKind.Sort, scopeTerm.raw)
          val sortTerm = kb.makeNameTermFromSym(sym)
          kb.registerSort(sortTerm, SortKind.Defined)
          kb.symbols.addParent(sortTerm.raw, ScopeInclusion(scopeTerm.raw, 0, isEnclosing = true))
          // Variant exposure (proposal 044 job 2): a sort exposes ONLY its
          // entity-variant names to the enclosing scope, linked as a
          // non-enclosing parent — so bare `Open` resolves to `WorkStatus.Open`
          // while operations never leak as bare names. (Names are visible by
          // default; the `export` statement was removed in WI-291.)
          val variants = sort.items.collect {
            case Item.EntityItem(e) => joinSegments(fileSym, e.name.segments)
          }
          for v <- variants do kb.symbols.addExposed(sortTerm.raw, v)
          if variants.nonEmpty then
            kb.symbols.addParent(scopeTerm.raw, ScopeInclusion(sortTerm.raw, 0, isEnclosing = false))
          // WI-452 (§5.4): a MARKED structured param (`sort [F] { … }`, the
          // higher-kinded carrier of `sort Spec[F[T]]`) is a NON-RIGID type
          // parameter of the enclosing sort — register it like the `sort T = ?`
          // abstract-sort arm below. An UNMARKED `sort F { … }` stays a concrete
          // nested sort. (scaland emits no `SortAlias` backing-var fact — it has
          // no typer; the type-param marker is what the resolver and codegen read.)
          if sort.isTypeParam && isSortScope(kb, scopeTerm) then
            kb.symbols.addTypeParam(scopeTerm.raw, shortName)
          scanItemsPass1(kb, sort.items, fileSym, fileTerms, sortTerm, qualName)

        case Item.AbstractSortItem(sort) =>
          val shortName = joinSegments(fileSym, sort.name.segments)
          val qualName = makeQualified(prefix, shortName)
          val sym = kb.symbols.define(shortName, qualName, SymbolKind.Sort, scopeTerm.raw)
          val sortTerm = kb.makeNameTermFromSym(sym)
          kb.registerSort(sortTerm, SortKind.Abstract)
          // `sort T = ?` inside a SortWithBody (or enum) declares a type
          // parameter local to the enclosing sort. The resolver uses this
          // marker to keep T from leaking into ambient name-resolution from
          // sibling sorts that share the same canonical parameter name.
          sort.definition match
            case _: TypeExpr.Variable if isSortScope(kb, scopeTerm) =>
              kb.symbols.addTypeParam(scopeTerm.raw, shortName)
            case _ => ()

        case Item.EntityItem(entity) =>
          val shortName = joinSegments(fileSym, entity.name.segments)
          val qualName = makeQualified(prefix, shortName)
          val sym = kb.symbols.define(shortName, qualName, SymbolKind.Entity, scopeTerm.raw)
          val entityTerm = kb.makeNameTermFromSym(sym)
          kb.registerSort(entityTerm, SortKind.Constructor)
          kb.registerEntityOf(entityTerm, scopeTerm)
          // Register entity fields
          val fields = entity.fields.map(f => fileSym.name(f.name)).map(kb.intern)
          kb.registerEntityFields(sym, fields)

        case Item.OperationItem(op) =>
          val shortName = joinSegments(fileSym, op.name.segments)
          val qualName = makeQualified(prefix, shortName)
          defineSymbolOnce(kb, shortName, qualName, SymbolKind.Operation, scopeTerm)

        case Item.OperationBlockItem(block) =>
          for op <- block.entries do
            val shortName = joinSegments(fileSym, op.name.segments)
            val qualName = makeQualified(prefix, shortName)
            defineSymbolOnce(kb, shortName, qualName, SymbolKind.Operation, scopeTerm)

        case Item.ConstItem(c) =>
          // Proposal 039 / WI-084: define the constant's symbol (pass 1, like
          // operations). Monomorphic + carrier-independent — no params or
          // type-params to scan. scaland records only the symbol; the declared
          // type + optional body are not loaded (no typer/eval to consume them),
          // mirroring how operation bodies/effects are left inert here.
          val shortName = joinSegments(fileSym, c.name.segments)
          val qualName = makeQualified(prefix, shortName)
          defineSymbolOnce(kb, shortName, qualName, SymbolKind.Const, scopeTerm)

        case Item.RuleItem(rule) =>
          rule.label.foreach { label =>
            val shortName = joinSegments(fileSym, label.segments)
            val qualName = makeQualified(prefix, shortName)
            kb.symbols.define(shortName, qualName, SymbolKind.Rule, scopeTerm.raw)
          }

        case Item.RuleBlockItem(block) =>
          for rule <- block.entries do
            rule.label.foreach { label =>
              val shortName = joinSegments(fileSym, label.segments)
              val qualName = makeQualified(prefix, shortName)
              kb.symbols.define(shortName, qualName, SymbolKind.Rule, scopeTerm.raw)
            }

        case _ => // Other items don't define symbols in pass 1

  /** Define a symbol of `kind` unless its qualified name is already
    * registered — mirrors rustland's `is_new` reuse gate (load.rs:1110, the
    * entity arm). Shared by operations and consts. A kernel operation such as
    * `anthill.reflect.not` is FIRST
    * registered as a builtin by `Prelude.registerStandardBuiltins` (into the
    * prelude's `anthill.reflect` scope); the stdlib then ALSO declares
    * `operation not(...)` in reflect.anthill. Because scaland scans a re-opened
    * namespace into a fresh scope (it does not yet reuse the prelude's scope),
    * a plain `define` here would mint a SECOND `anthill.reflect.not` symbol in a
    * different scope — and a bare rule-body use (`:- not(...)` in typing.anthill)
    * would then collect both via `resolveInScope` and report `AmbiguousSymbol`
    * (WI-212). Reusing the already-registered symbol keeps exactly one. */
  private def defineSymbolOnce(
    kb: KnowledgeBase,
    shortName: String,
    qualName: String,
    kind: SymbolKind,
    scopeTerm: TermId
  ): Unit =
    if !kb.symbols.byQualifiedName.contains(qualName) then
      kb.symbols.define(shortName, qualName, kind, scopeTerm.raw)

  // ── Pass 2: Process requires/imports ─────────────────────────

  private def scanItemsPass2(
    kb: KnowledgeBase,
    items: Iterable[Item],
    fileSym: SymbolTable,
    scopeTerm: TermId,
    prefix: String,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    for item <- items do
      item match
        case Item.NamespaceItem(ns) =>
          val shortName = joinSegments(fileSym, ns.name.segments)
          val qualName = makeQualified(prefix, shortName)
          val nsSym = kb.symbols.byQualifiedName.get(qualName)
          nsSym.foreach { sym =>
            val nsTerm = kb.makeNameTermFromSym(sym)
            processImports(kb, ns.imports, fileSym, nsTerm, errors)
            scanItemsPass2(kb, ns.items, fileSym, nsTerm, qualName, errors)
          }

        case Item.SortWithBodyItem(sort) =>
          val shortName = joinSegments(fileSym, sort.name.segments)
          val qualName = makeQualified(prefix, shortName)
          val sortSym = kb.symbols.byQualifiedName.get(qualName)
          sortSym.foreach { sym =>
            val sortTerm = kb.makeNameTermFromSym(sym)
            processImports(kb, sort.imports, fileSym, sortTerm, errors)
            scanItemsPass2(kb, sort.items, fileSym, sortTerm, qualName, errors)
          }

        case Item.RequiresDeclItem(req) =>
          processRequires(kb, req, fileSym, scopeTerm, errors)

        case _ =>

  private def processImports(
    kb: KnowledgeBase,
    imports: Iterable[Import],
    fileSym: SymbolTable,
    scopeTerm: TermId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    for imp <- imports do
      val pathStr = joinSegments(fileSym, imp.path.segments)
      kb.symbols.byQualifiedName.get(pathStr) match
        case Some(sym) =>
          imp.kind match
            case ImportKind.Plain =>
              val short = fileSym.name(imp.path.last)
              kb.symbols.addImport(scopeTerm.raw, short, sym)
            case ImportKind.Selective(names) =>
              for n <- names do
                val name = joinSegments(fileSym, n.segments)
                val symTerm = kb.makeNameTermFromSym(sym)
                val found = kb.symbols.resolveInScope(name, symTerm.raw) match
                  case ResolveResult.Found(s) => Some(s)
                  // Fall back to direct fully-qualified lookup — covers
                  // top-level multi-segment sort decls like
                  // `enum anthill.prelude.Pair` whose symbol is registered at
                  // global with the dotted name and never gets attached to
                  // the `anthill.prelude` namespace's exports.
                  case _ => kb.symbols.byQualifiedName.get(s"$pathStr.$name")
                    // Last resort: an entity exported by the namespace but
                    // defined one scope deeper, e.g. `execution_platform`
                    // declared inside `sort ExecutionPlatform` of namespace
                    // `anthill.realization.platform` (qualified name
                    // `…platform.ExecutionPlatform.execution_platform`).
                    // Mirrors rustland's `find_in_nested_scope`.
                    .orElse(findInNestedScope(kb, pathStr, name))
                found match
                  case Some(s) => kb.symbols.addImport(scopeTerm.raw, name, s)
                  case None => errors += LoadError.UnresolvedName(name, n.span, pathStr)
            case ImportKind.Wildcard =>
              val parentTerm = kb.makeNameTermFromSym(sym)
              kb.symbols.addParent(scopeTerm.raw,
                ScopeInclusion(parentTerm.raw, 0, isEnclosing = false))
        case None =>
          errors += LoadError.UnresolvedImport(pathStr, imp.path.span)

  /** Resolve a selectively-imported name that lives one scope level below
    * the imported namespace — e.g. an entity declared inside a `sort`/`enum`
    * within the namespace. Without this, `import anthill.realization.platform.{
    * execution_platform}` fails because the entity's qualified name is
    * `…platform.ExecutionPlatform.execution_platform` (one intermediate
    * segment), not `…platform.execution_platform`. Mirrors rustland's
    * `find_in_nested_scope`: requires exactly one intermediate segment and a
    * unique match (ambiguity → None). */
  private def findInNestedScope(
    kb: KnowledgeBase, basePath: String, short: String
  ): Option[TermSymbol] =
    val prefix = s"$basePath."
    val suffix = s".$short"
    val matches = kb.symbols.byQualifiedName.iterator.collect {
      case (qname, sym)
        // The length guard rules out an overlapping prefix/suffix (e.g.
        // base="a", short="b", qname="a.b"), which would make the substring
        // bounds invalid; such a qname is the exact `base.short` already
        // handled by the direct lookup, so it has no intermediate segment.
        if qname.startsWith(prefix) && qname.endsWith(suffix) &&
           qname.length >= prefix.length + suffix.length &&
           {
             val middle = qname.substring(prefix.length, qname.length - suffix.length)
             middle.nonEmpty && !middle.contains('.')
           } => sym
    }.toSet
    if matches.size == 1 then Some(matches.head) else None

  private def processRequires(
    kb: KnowledgeBase,
    req: RequiresDecl,
    fileSym: SymbolTable,
    scopeTerm: TermId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    req.typeExpr match
      case TypeExpr.Simple(name) =>
        val nameStr = joinSegments(fileSym, name.segments)
        kb.symbols.byQualifiedName.get(nameStr) match
          case Some(sym) =>
            val parentTerm = kb.makeNameTermFromSym(sym)
            kb.symbols.addParent(scopeTerm.raw,
              ScopeInclusion(parentTerm.raw, 0, isEnclosing = false))
          case None =>
            errors += LoadError.UnresolvedName(nameStr, name.span, "requires")
      case _ => // Parameterized requires — TODO

  // ── Phase 2: Load items into KB ─────────────────────────────

  private def loadItems(
    kb: KnowledgeBase,
    items: Iterable[Item],
    fileSym: SymbolTable,
    fileTerms: SimpleTermStore,
    scopeTerm: TermId,
    prefix: String,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    for item <- items do
      item match
        case Item.NamespaceItem(ns) =>
          val shortName = joinSegments(fileSym, ns.name.segments)
          val qualName = makeQualified(prefix, shortName)
          kb.symbols.byQualifiedName.get(qualName).foreach { sym =>
            val nsTerm = kb.makeNameTermFromSym(sym)
            loadItems(kb, ns.items, fileSym, fileTerms, nsTerm, qualName, errors)
          }

        case Item.SortWithBodyItem(sort) =>
          val shortName = joinSegments(fileSym, sort.name.segments)
          val qualName = makeQualified(prefix, shortName)
          kb.symbols.byQualifiedName.get(qualName).foreach { sym =>
            val sortTerm = kb.makeNameTermFromSym(sym)
            loadItems(kb, sort.items, fileSym, fileTerms, sortTerm, qualName, errors)
          }

        case Item.FactItem(fact) =>
          val kbTerm = reallocTerm(kb, fileTerms, fileSym, fact.term, scopeTerm, errors)
          val sortSort = findSortTerm(kb, "anthill.reflect.Fact")
          kb.assertFact(kbTerm, sortSort, scopeTerm)

        case Item.RuleItem(rule) =>
          val sortSort = findSortTerm(kb, "anthill.reflect.Rule")
          loadRuleHeads(kb, rule, fileTerms, fileSym, scopeTerm, sortSort, errors)

        case Item.RuleBlockItem(block) =>
          val sortSort = findSortTerm(kb, "anthill.reflect.Rule")
          for rule <- block.entries do
            loadRuleHeads(kb, rule, fileTerms, fileSym, scopeTerm, sortSort, errors)

        case Item.EntityItem(entity) =>
          val shortName = joinSegments(fileSym, entity.name.segments)
          val qualName = makeQualified(prefix, shortName)
          kb.symbols.byQualifiedName.get(qualName).foreach { sym =>
            val entityTerm = kb.makeNameTermFromSym(sym)
            // Assert EntityOf fact
            val entityOfSort = findSortTerm(kb, "anthill.reflect.EntityOf")
            val entityOfSym = kb.intern("entity_of")
            val entityOfFact = kb.alloc(Term.Fn(entityOfSym, IArray(entityTerm, scopeTerm), IArray.empty))
            kb.assertFact(entityOfFact, entityOfSort, scopeTerm)
          }

        case Item.ProofItem(p) =>
          loadProof(kb, p, fileSym, scopeTerm)

        case Item.ProvidesClauseItem(pc) =>
          loadProvidesClause(kb, pc, fileSym, scopeTerm)

        case Item.ProvidesBlockItem(pb) =>
          loadProvidesBlock(kb, pb, fileTerms, fileSym, scopeTerm, errors)

        case _ => // Other items

  /** Load a rule under the proposal-032 grammar. `rule.heads` may be a single
    * positive head, multiple positive heads (conjunctive sugar), or a single
    * `Bottom` (denial). Mixing `Bottom` with positive heads is rejected.
    *
    * Translation:
    *   - single positive head            → one horn rule, head IS the KB head
    *   - labeled multi-head (positive)   → N horn rules, one per head, sharing body
    *   - unlabeled multi-head (positive) → error: needs a label for citation handle
    *   - single `Bottom` (denial)        → one rule with `Term.Bottom` as head
    *
    * (Scaland's KB has no `conclusion` field, so the rust transitional
    * translation that synthesizes a 0-arg label-functor as the KB head with
    * user heads moved to conclusion is collapsed into the literal conjunctive
    * expansion above. Citation infrastructure is not yet ported.)
    */
  private def loadRuleHeads(
    kb: KnowledgeBase,
    rule: Rule,
    fileTerms: SimpleTermStore,
    fileSym: SymbolTable,
    scopeTerm: TermId,
    sortSort: TermId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    val vm = HashMap.empty[Int, VarId] // shared across heads + body
    val hasBottom = rule.heads.exists { case RuleHead.Bottom => true; case _ => false }
    val positiveHeads = rule.heads.collect { case RuleHead.TermHead(t) => t }

    if hasBottom && rule.heads.length > 1 then
      errors += LoadError.Other(
        "denial heads (`⊥`) cannot be combined with positive heads in a multi-head rule")
      return

    if positiveHeads.length > 1 && rule.label.isEmpty then
      errors += LoadError.Other(
        "multi-head rule requires a label so the rule has a unique citation handle " +
        "(e.g. `rule my_law: H1, H2 :- B`)")
      return

    val kbBody = rule.body.map(_.map(b =>
      reallocTerm(kb, fileTerms, fileSym, b, scopeTerm, errors, vm))).getOrElse(IndexedSeq.empty)

    if hasBottom then
      val botTerm = kb.alloc(Term.Bottom)
      kb.assertRule(botTerm, kbBody, sortSort, scopeTerm)
    else
      // One horn rule per head, sharing body (and shared var scope via vm).
      for headId <- positiveHeads do
        val kbHead = reallocTerm(kb, fileTerms, fileSym, headId, scopeTerm, errors, vm)
        kb.assertRule(kbHead, kbBody, sortSort, scopeTerm)

  // ── Proof / Provides loaders (proposal 025 + 031) ────────────

  private def loadProof(
    kb: KnowledgeBase,
    p: anthill.parse.ProofDecl,
    fileSym: SymbolTable,
    scopeTerm: TermId
  ): Unit =
    val targetStr = joinSegments(fileSym, p.target.segments)
    val targetTerm = kb.alloc(Term.Const(Literal.StringLit(targetStr)))
    val strategyStr = p.strategy.map(s => fileSym.name(s.name)).getOrElse("derivation")
    val strategyTerm = kb.alloc(Term.Const(Literal.StringLit(strategyStr)))
    val proofSym = kb.intern("proof_decl")
    val proofTerm = kb.alloc(Term.Fn(proofSym, IArray.empty,
      IArray(
        (kb.intern("target"), targetTerm),
        (kb.intern("strategy"), strategyTerm))))
    val proofSort = kb.makeNameTerm("ProofRecord")
    kb.assertFact(proofTerm, proofSort, scopeTerm)

  private def loadProvidesClause(
    kb: KnowledgeBase,
    pc: anthill.parse.ProvidesClause,
    fileSym: SymbolTable,
    scopeTerm: TermId
  ): Unit =
    // Lossy: parameterized bindings (e.g. `Stack[T = Int]` vs `Stack[T = String]`)
    // collapse to the bare spec name. The witness pipeline (WI-157) replaces
    // this with a structured term that preserves bindings.
    val specStr = specName(fileSym, pc.spec)
    val specTerm = kb.alloc(Term.Const(Literal.StringLit(specStr)))
    val provSym = kb.intern("provides_clause")
    val provTerm = kb.alloc(Term.Fn(provSym, IArray.empty,
      IArray(
        (kb.intern("sort_ref"), scopeTerm),
        (kb.intern("spec"), specTerm))))
    val provSort = kb.makeNameTerm("Requirement")
    kb.assertFact(provTerm, provSort, scopeTerm)

  private def loadProvidesBlock(
    kb: KnowledgeBase,
    pb: anthill.parse.ProvidesBlock,
    fileTerms: SimpleTermStore,
    fileSym: SymbolTable,
    scopeTerm: TermId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    if fileSym.name(pb.language) != "anthill" then return
    val ruleSort = findSortTerm(kb, "anthill.reflect.Rule")
    val factSort = findSortTerm(kb, "anthill.reflect.Fact")
    for item <- pb.items do item match
      case ProvidesItem.RuleI(r) =>
        loadRuleHeads(kb, r, fileTerms, fileSym, scopeTerm, ruleSort, errors)
      case ProvidesItem.RuleBlockI(rb) =>
        for r <- rb.entries do
          loadRuleHeads(kb, r, fileTerms, fileSym, scopeTerm, ruleSort, errors)
      case ProvidesItem.FactI(f) =>
        val kbTerm = reallocTerm(kb, fileTerms, fileSym, f.term, scopeTerm, errors)
        kb.assertFact(kbTerm, factSort, scopeTerm)
      case ProvidesItem.ProofI(p) =>
        loadProof(kb, p, fileSym, scopeTerm)
      case ProvidesItem.ArtifactI(_)
         | ProvidesItem.CarrierI(_)
         | ProvidesItem.NamespaceMapI(_) =>

  private def specName(fileSym: SymbolTable, te: TypeExpr): String = te match
    case TypeExpr.Simple(n) => joinSegments(fileSym, n.segments)
    case TypeExpr.Parameterized(n, _) => joinSegments(fileSym, n.segments)
    case _ => "<spec>"

  // ── Term reallocation ─────────────────────────────────────────

  /** WI-582: whether `fn` is the parser-emitted typed-pattern marker
    * `typed_var(?x, type: T)` — matched by functor name AND its exact shape
    * (exactly one positional arg plus a `type` named arg). Mirrors rustland's
    * three-condition guard (`load.rs`): matching by name ALONE would crash on a
    * user functor `typed_var()` (`posArgs(0)` out of bounds) and silently strip
    * `typed_var(a, b)` to `a`. A non-marker `typed_var` falls through to normal
    * loading. */
  private def isTypedVarMarker(fn: Term.Fn, fileSym: SymbolTable): Boolean =
    fileSym.name(fn.functor) == "typed_var" &&
      fn.posArgs.length == 1 &&
      fn.namedArgs.exists { case (k, _) => fileSym.name(k) == "type" }

  /** Re-allocate a parse-time term into the KB's hash-consed store.
    * Uses varMap to share VarIds within a rule scope (same parse-time VarId → same KB VarId).
    */
  private def reallocTerm(
    kb: KnowledgeBase,
    fileTerms: SimpleTermStore,
    fileSym: SymbolTable,
    termId: TermId,
    scopeTerm: TermId,
    errors: ArrayBuffer[LoadError],
    varMap: HashMap[Int, VarId] = HashMap.empty
  ): TermId =
    fileTerms.get(termId) match
      case Term.Const(lit) => kb.alloc(Term.Const(lit))
      case Term.Var(v) =>
        // Map parse-time VarId to a fresh KB VarId (preserves sharing within
        // scope). Parse terms carry only `Global` vars; `assertRule`/`assertFact`
        // later close them to DeBruijn (WI-637). A DeBruijn/Rigid here is a bug
        // upstream — fail loudly rather than mis-map it.
        val vid = v match
          case Var.Global(g) => g
          case other =>
            throw new IllegalStateException(
              s"reallocTerm: parse term carries a non-Global var ($other); the parser emits only Global")
        val kbVid = varMap.getOrElseUpdate(vid.id, {
          val name = fileSym.name(vid.name)
          val kbSym = kb.intern(name)
          kb.freshVar(kbSym)
        })
        kb.alloc(Term.Var(Var.Global(kbVid)))
      case fn: Term.Fn if isTypedVarMarker(fn, fileSym) =>
        // WI-582: strip the typed-pattern marker `typed_var(?x, type: T)` back to
        // the bare `?x`. The parser wraps a `?x: T` rule-LHS arg as this marker;
        // rustland installs T as a per-DeBruijn `Type` bound and keeps the head
        // structurally bare so the discrimination tree indexes it identically to
        // an untyped head. scaland has no typer to enforce the bound, so we DROP
        // the type and keep only the bare variable — sound-conservative (the head
        // still matches the untyped form). Mirrors rustland's strip minus the
        // bound install.
        reallocTerm(kb, fileTerms, fileSym, fn.posArgs(0), scopeTerm, errors, varMap)
      case fn: Term.Fn =>
        val name = fileSym.name(fn.functor)
        val kbFunctor = resolveName(kb, name, scopeTerm, errors)
        val kbPos = IArray.from(fn.posArgs.map(id => reallocTerm(kb, fileTerms, fileSym, id, scopeTerm, errors, varMap)))
        val kbNamed = IArray.from(fn.namedArgs.map { (sym, id) =>
          val kbKeySym = kb.intern(fileSym.name(sym))
          (kbKeySym, reallocTerm(kb, fileTerms, fileSym, id, scopeTerm, errors, varMap))
        })
        kb.alloc(Term.Fn(kbFunctor, kbPos, kbNamed))
      case Term.Ref(sym) =>
        val name = fileSym.name(sym)
        val kbSym = resolveName(kb, name, scopeTerm, errors)
        kb.alloc(Term.Ref(kbSym))
      case Term.Ident(sym) =>
        val name = fileSym.name(sym)
        val kbSym = resolveName(kb, name, scopeTerm, errors)
        kb.alloc(Term.Ident(kbSym))
      case Term.Bottom => kb.alloc(Term.Bottom)

  /** Resolve a name in scope, falling back to intern for user-defined predicates. */
  private def resolveName(kb: KnowledgeBase, name: String, scopeTerm: TermId, errors: ArrayBuffer[LoadError]): TermSymbol =
    kb.symbols.byQualifiedName.get(name) match
      case Some(sym) => sym
      case None =>
        kb.symbols.resolveInScope(name, scopeTerm.raw) match
          case ResolveResult.Found(sym) => sym
          case ResolveResult.Ambiguous(candidates) =>
            val qualNames = candidates.map(c => kb.symbols.get(c) match
              case SymbolDef.Resolved(_, q, _, _) => q
              case SymbolDef.Unresolved(n) => n
            ).toIndexedSeq
            errors += LoadError.AmbiguousSymbol(name, qualNames, Span.empty, "")
            kb.intern(name)
          case ResolveResult.NotFound =>
            kb.intern(name)

  /** Auto-import prelude sort contents into global scope.
    * Adds each sort defined directly under anthill.prelude as a parent of _global,
    * making their exported operations (add, sub, mul, etc.) globally visible.
    *
    * Skips the primitive type sorts (Bool/Int/Float/BigInt/String) — their
    * operations conflict with the kernel builtins (`anthill.reflect.not`,
    * etc.) that Prelude.registerStandardBuiltins already imports at global.
    * Mirrors rustland's `register_prelude`, which only imports explicit
    * global aliases instead of bulk-parenting every prelude sort.
    */
  private def autoImportPrelude(kb: KnowledgeBase, globalScope: TermId): Unit =
    val preludePrefix = "anthill.prelude."
    // Skip primitive type sorts (their ops collide with kernel builtins)
    // AND typeclass sorts whose generic ops collide with each other —
    // Iteration/Collection/IndexedSeq/Set/Map/LogicalStream all expose
    // `empty` / `insert` / `Effect`, and `Monad` exposes the very common
    // `map` / `flatMap` / `pure`. These should be reached via explicit
    // `import` clauses (as `option.anthill` imports `Monad`), mirroring
    // rustland's explicit-only global aliases.
    val skip = Set(
      "Bool", "Int64", "Float", "BigInt", "String",
      "Iteration", "Collection", "IndexedSeq", "Set", "Map", "LogicalStream",
      "Monad")
    for (qualName, sym) <- kb.symbols.byQualifiedName do
      if qualName.startsWith(preludePrefix) then
        val afterPrelude = qualName.substring(preludePrefix.length)
        if !afterPrelude.contains('.') && !skip.contains(afterPrelude) then
          val sortTerm = kb.makeNameTermFromSym(sym)
          kb.symbols.addParent(globalScope.raw, ScopeInclusion(sortTerm.raw, 0, isEnclosing = false))

  private def findSortTerm(kb: KnowledgeBase, qualName: String): TermId =
    kb.symbols.byQualifiedName.get(qualName) match
      case Some(sym) => kb.makeNameTermFromSym(sym)
      case None => kb.makeNameTerm(qualName)

  // ── Helpers ─────────────────────────────────────────────────

  private def joinSegments(symbols: SymbolTable, segments: IndexedSeq[TermSymbol]): String =
    segments.map(symbols.name).mkString(".")

  private def isSortScope(kb: KnowledgeBase, scope: TermId): Boolean =
    kb.getTerm(scope) match
      case f: Term.Fn if f.posArgs.isEmpty && f.namedArgs.isEmpty =>
        kb.symbols.get(f.functor) match
          case SymbolDef.Resolved(_, _, SymbolKind.Sort, _) => true
          case _ => false
      case _ => false

  private def makeQualified(prefix: String, name: String): String =
    if prefix.isEmpty then name else s"$prefix.$name"

  // ── List / Option builders ────────────────────────────────────

  private def buildList(kb: KnowledgeBase, items: IndexedSeq[TermId]): TermId =
    val nilSym = kb.tryResolveSymbol("anthill.prelude.List.nil").getOrElse(kb.intern("nil"))
    val consSym = kb.tryResolveSymbol("anthill.prelude.List.cons").getOrElse(kb.intern("cons"))
    val headKey = kb.intern("head")
    val tailKey = kb.intern("tail")
    var list = kb.alloc(Term.Fn(nilSym, IArray.empty, IArray.empty))
    var i = items.length - 1
    while i >= 0 do
      list = kb.alloc(Term.Fn(consSym, IArray.empty, IArray((headKey, items(i)), (tailKey, list))))
      i -= 1
    list

  private def buildNone(kb: KnowledgeBase): TermId =
    val noneSym = kb.tryResolveSymbol("anthill.prelude.Option.none").getOrElse(kb.intern("none"))
    kb.alloc(Term.Fn(noneSym, IArray.empty, IArray.empty))

  private def buildSome(kb: KnowledgeBase, value: TermId): TermId =
    val someSym = kb.tryResolveSymbol("anthill.prelude.Option.some").getOrElse(kb.intern("some"))
    val valueKey = kb.intern("value")
    kb.alloc(Term.Fn(someSym, IArray.empty, IArray((valueKey, value))))

  // ── Expression conversion ─────────────────────────────────────

  /** Convert a parse-time expression term into the KB's Expr representation.
    * Dispatches on functor name to restructure positional args into named args.
    */
  private def convertExprTerm(
    kb: KnowledgeBase, fileTerms: SimpleTermStore, fileSym: SymbolTable,
    parseId: TermId, scopeTerm: TermId, errors: ArrayBuffer[LoadError],
    varMap: HashMap[Int, VarId]
  ): TermId =
    fileTerms.get(parseId) match
      case fn: Term.Fn =>
        val name = fileSym.name(fn.functor)
        name match
          case "match_expr" => loadMatchExpr(kb, fileTerms, fileSym, fn.posArgs, scopeTerm, errors, varMap)
          case "match_branch" => loadMatchBranch(kb, fileTerms, fileSym, fn.posArgs, scopeTerm, errors, varMap)
          case "if_expr" => loadIfExpr(kb, fileTerms, fileSym, fn.posArgs, scopeTerm, errors, varMap)
          case "let_expr" => loadLetExpr(kb, fileTerms, fileSym, fn.posArgs, scopeTerm, errors, varMap)
          case "lambda_expr" => loadLambdaExpr(kb, fileTerms, fileSym, fn.posArgs, scopeTerm, errors, varMap)
          case "pattern_var" => loadPatternVar(kb, fileTerms, fileSym, fn.posArgs, scopeTerm, errors, varMap)
          case "pattern_wildcard" => loadPatternWildcard(kb)
          case "pattern_literal" => loadPatternLiteral(kb, fileTerms, fileSym, fn.posArgs, scopeTerm, errors, varMap)
          case "pattern_constructor" => loadPatternConstructor(kb, fileTerms, fileSym, fn.posArgs, scopeTerm, errors, varMap)
          case "pattern_tuple" => loadPatternTuple(kb, fileTerms, fileSym, fn.posArgs, scopeTerm, errors, varMap)
          // WI-582: strip a `typed_var(?x, type: T)` marker back to the bare `?x`
          // here too (a typed arg in an expression body), matching `reallocTerm`.
          // Guarded on the exact marker shape (name + 1 pos + `type` named) — a
          // non-marker `typed_var` falls through to `loadApplyOrConstructor`.
          case "typed_var" if isTypedVarMarker(fn, fileSym) =>
            exprRec((kb, fileTerms, fileSym, scopeTerm, errors, varMap), fn.posArgs(0))
          case _ => loadApplyOrConstructor(kb, fileTerms, fileSym, fn.functor, fn.posArgs, fn.namedArgs, scopeTerm, errors, varMap)
      case Term.Const(_) => loadLiteralExpr(kb, fileTerms, fileSym, parseId, scopeTerm, errors, varMap)
      case Term.Ident(_) => loadVarRef(kb, fileTerms, fileSym, parseId, scopeTerm, errors, varMap)
      case _ => reallocTerm(kb, fileTerms, fileSym, parseId, scopeTerm, errors, varMap)

  // Shorthand for recursive call parameters
  private type Ctx = (KnowledgeBase, SimpleTermStore, SymbolTable, TermId, ArrayBuffer[LoadError], HashMap[Int, VarId])
  private def exprRec(ctx: Ctx, parseId: TermId): TermId =
    convertExprTerm(ctx._1, ctx._2, ctx._3, parseId, ctx._4, ctx._5, ctx._6)

  private def loadMatchExpr(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = (kb, ft, fs, scope, errors, vm)
    val scrutinee = exprRec(ctx, posArgs(0))
    val branches = IArray.tabulate(posArgs.length - 1)(i => exprRec(ctx, posArgs(i + 1)))
    val branchList = buildList(kb, branches.toIndexedSeq)
    val matchSym = kb.resolveSymbol("anthill.reflect.Expr.match_expr")
    kb.alloc(Term.Fn(matchSym, IArray.empty,
      IArray((kb.intern("scrutinee"), scrutinee), (kb.intern("branches"), branchList))))

  private def loadMatchBranch(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = (kb, ft, fs, scope, errors, vm)
    val pattern = exprRec(ctx, posArgs(0))
    val body = exprRec(ctx, posArgs(1))
    val guard = buildNone(kb)
    val branchSym = kb.resolveSymbol("anthill.reflect.MatchBranch")
    kb.alloc(Term.Fn(branchSym, IArray.empty,
      IArray((kb.intern("pattern"), pattern), (kb.intern("guard"), guard), (kb.intern("body"), body))))

  private def loadIfExpr(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = (kb, ft, fs, scope, errors, vm)
    val cond = exprRec(ctx, posArgs(0))
    val thenBranch = exprRec(ctx, posArgs(1))
    val elseBranch = exprRec(ctx, posArgs(2))
    val ifSym = kb.resolveSymbol("anthill.reflect.Expr.if_expr")
    kb.alloc(Term.Fn(ifSym, IArray.empty,
      IArray((kb.intern("cond"), cond), (kb.intern("then_branch"), thenBranch), (kb.intern("else_branch"), elseBranch))))

  private def loadLetExpr(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = (kb, ft, fs, scope, errors, vm)
    val pattern = exprRec(ctx, posArgs(0))
    val value = exprRec(ctx, posArgs(1))
    val body = exprRec(ctx, posArgs(2))
    val letSym = kb.resolveSymbol("anthill.reflect.Expr.let_expr")
    kb.alloc(Term.Fn(letSym, IArray.empty,
      IArray((kb.intern("pattern"), pattern), (kb.intern("value"), value), (kb.intern("body"), body))))

  private def loadLambdaExpr(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = (kb, ft, fs, scope, errors, vm)
    val param = exprRec(ctx, posArgs(0))
    val body = exprRec(ctx, posArgs(1))
    val lambdaSym = kb.resolveSymbol("anthill.reflect.Expr.lambda_expr")
    kb.alloc(Term.Fn(lambdaSym, IArray.empty,
      IArray((kb.intern("param"), param), (kb.intern("body"), body))))

  private def loadVarRef(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    parseId: TermId, scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val nameRef = ft.get(parseId) match
      case Term.Ident(sym) =>
        val kbSym = kb.intern(fs.name(sym))
        kb.alloc(Term.Ref(kbSym))
      case _ => reallocTerm(kb, ft, fs, parseId, scope, errors, vm)
    val varRefSym = kb.resolveSymbol("anthill.reflect.Expr.var_ref")
    kb.alloc(Term.Fn(varRefSym, IArray.empty, IArray((kb.intern("name"), nameRef))))

  private def loadLiteralExpr(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    parseId: TermId, scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    ft.get(parseId) match
      case Term.Const(lit) =>
        val (entityName, valueTerm) = lit match
          case Literal.IntLit(n) => ("anthill.reflect.Expr.int_lit", kb.alloc(Term.Const(Literal.IntLit(n))))
          case Literal.BigIntLit(n) => ("anthill.reflect.Expr.bigint_lit", kb.alloc(Term.Const(Literal.BigIntLit(n))))
          case Literal.FloatLit(f) => ("anthill.reflect.Expr.float_lit", kb.alloc(Term.Const(Literal.FloatLit(f))))
          case Literal.StringLit(s) => ("anthill.reflect.Expr.string_lit", kb.alloc(Term.Const(Literal.StringLit(s))))
          case Literal.BoolLit(b) => ("anthill.reflect.Expr.bool_lit", kb.alloc(Term.Const(Literal.BoolLit(b))))
        val entitySym = kb.resolveSymbol(entityName)
        kb.alloc(Term.Fn(entitySym, IArray.empty, IArray((kb.intern("value"), valueTerm))))
      case _ => reallocTerm(kb, ft, fs, parseId, scope, errors, vm)

  private def loadApplyOrConstructor(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    parseFunctor: TermSymbol, posArgs: IArray[TermId], namedArgs: IArray[(TermSymbol, TermId)],
    scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = (kb, ft, fs, scope, errors, vm)
    val kbFunctor = resolveName(kb, fs.name(parseFunctor), scope, errors)
    val isEntity = kb.symbols.get(kbFunctor) match
      case SymbolDef.Resolved(_, _, SymbolKind.Entity, _) => true
      case _ => false

    val applyArgSym = kb.resolveSymbol("anthill.reflect.ApplyArg")
    val argNameKey = kb.intern("name")
    val argValueKey = kb.intern("value")

    val argTerms = scala.collection.mutable.ArrayBuffer.empty[TermId]
    for tid <- posArgs do
      val value = exprRec(ctx, tid)
      val none = buildNone(kb)
      argTerms += kb.alloc(Term.Fn(applyArgSym, IArray.empty,
        IArray((argNameKey, none), (argValueKey, value))))
    for (sym, tid) <- namedArgs do
      val value = exprRec(ctx, tid)
      val nameRef = kb.alloc(Term.Ref(kb.intern(fs.name(sym))))
      val someName = buildSome(kb, nameRef)
      argTerms += kb.alloc(Term.Fn(applyArgSym, IArray.empty,
        IArray((argNameKey, someName), (argValueKey, value))))
    val argsList = buildList(kb, argTerms.toIndexedSeq)
    val nameRef = kb.alloc(Term.Ref(kbFunctor))

    if isEntity then
      val ctorSym = kb.resolveSymbol("anthill.reflect.Expr.constructor")
      kb.alloc(Term.Fn(ctorSym, IArray.empty,
        IArray((kb.intern("name"), nameRef), (kb.intern("args"), argsList))))
    else
      val applySym = kb.resolveSymbol("anthill.reflect.Expr.apply")
      kb.alloc(Term.Fn(applySym, IArray.empty,
        IArray((kb.intern("fn"), nameRef), (kb.intern("args"), argsList))))

  // ── Pattern conversion ───────────────────────────────────────

  private def loadPatternVar(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val nameRef = ft.get(posArgs(0)) match
      case Term.Ident(sym) =>
        val kbSym = kb.intern(fs.name(sym))
        kb.alloc(Term.Ref(kbSym))
      case _ => reallocTerm(kb, ft, fs, posArgs(0), scope, errors, vm)
    val typeAnn = buildNone(kb)
    val varPatternSym = kb.resolveSymbol("anthill.reflect.Pattern.var_pattern")
    kb.alloc(Term.Fn(varPatternSym, IArray.empty,
      IArray((kb.intern("name"), nameRef), (kb.intern("type_ann"), typeAnn))))

  private def loadPatternWildcard(kb: KnowledgeBase): TermId =
    val wildcardSym = kb.resolveSymbol("anthill.reflect.Pattern.wildcard")
    kb.alloc(Term.Fn(wildcardSym, IArray.empty, IArray.empty))

  private def loadPatternLiteral(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val value = reallocTerm(kb, ft, fs, posArgs(0), scope, errors, vm)
    val litPatternSym = kb.resolveSymbol("anthill.reflect.Pattern.literal_pattern")
    kb.alloc(Term.Fn(litPatternSym, IArray.empty, IArray((kb.intern("value"), value))))

  private def loadPatternConstructor(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = (kb, ft, fs, scope, errors, vm)
    val nameRef = ft.get(posArgs(0)) match
      case Term.Ident(sym) =>
        val kbSym = resolveName(kb, fs.name(sym), scope, errors)
        kb.alloc(Term.Ref(kbSym))
      case _ => reallocTerm(kb, ft, fs, posArgs(0), scope, errors, vm)
    val subPatterns = IArray.tabulate(posArgs.length - 1)(i => exprRec(ctx, posArgs(i + 1)))
    val argsList = buildList(kb, subPatterns.toIndexedSeq)
    val ctorPatternSym = kb.resolveSymbol("anthill.reflect.Pattern.constructor_pattern")
    kb.alloc(Term.Fn(ctorPatternSym, IArray.empty,
      IArray((kb.intern("name"), nameRef), (kb.intern("args"), argsList))))

  private def loadPatternTuple(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: TermId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = (kb, ft, fs, scope, errors, vm)
    val elements = IArray.tabulate(posArgs.length)(i => exprRec(ctx, posArgs(i)))
    val elementsList = buildList(kb, elements.toIndexedSeq)
    val tuplePatternSym = kb.resolveSymbol("anthill.reflect.Pattern.tuple_pattern")
    kb.alloc(Term.Fn(tuplePatternSym, IArray.empty, IArray((kb.intern("elements"), elementsList))))
