package anthill.load

import anthill.kb.{KnowledgeBase, SortKind}
import anthill.intern.{TermSymbol, SymbolTable, SymbolKind, SymbolDef, ScopeInclusion, ResolveResult}
import anthill.term.{Term, TermId, VarId}
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
          kb.symbols.addExport(scopeTerm.raw, shortName)
          // Enclosing scope
          kb.symbols.addParent(nsTerm.raw, ScopeInclusion(scopeTerm.raw, 0, isEnclosing = true))
          // Exports
          for exp <- ns.exports do
            kb.symbols.addExport(nsTerm.raw, joinSegments(fileSym, exp.segments))
          scanItemsPass1(kb, ns.items, fileSym, fileTerms, nsTerm, qualName)

        case Item.SortWithBodyItem(sort) =>
          val shortName = joinSegments(fileSym, sort.name.segments)
          val qualName = makeQualified(prefix, shortName)
          val sym = kb.symbols.define(shortName, qualName, SymbolKind.Sort, scopeTerm.raw)
          val sortTerm = kb.makeNameTermFromSym(sym)
          kb.registerSort(sortTerm, SortKind.Defined)
          kb.symbols.addExport(scopeTerm.raw, shortName)
          kb.symbols.addParent(sortTerm.raw, ScopeInclusion(scopeTerm.raw, 0, isEnclosing = true))
          for exp <- sort.exports do
            kb.symbols.addExport(sortTerm.raw, joinSegments(fileSym, exp.segments))
          scanItemsPass1(kb, sort.items, fileSym, fileTerms, sortTerm, qualName)

        case Item.AbstractSortItem(sort) =>
          val shortName = joinSegments(fileSym, sort.name.segments)
          val qualName = makeQualified(prefix, shortName)
          val sym = kb.symbols.define(shortName, qualName, SymbolKind.Sort, scopeTerm.raw)
          val sortTerm = kb.makeNameTermFromSym(sym)
          kb.registerSort(sortTerm, SortKind.Abstract)
          kb.symbols.addExport(scopeTerm.raw, shortName)

        case Item.EntityItem(entity) =>
          val shortName = joinSegments(fileSym, entity.name.segments)
          val qualName = makeQualified(prefix, shortName)
          val sym = kb.symbols.define(shortName, qualName, SymbolKind.Entity, scopeTerm.raw)
          val entityTerm = kb.makeNameTermFromSym(sym)
          kb.registerSort(entityTerm, SortKind.Constructor)
          kb.registerEntityOf(entityTerm, scopeTerm)
          kb.symbols.addExport(scopeTerm.raw, shortName)
          // Register entity fields
          val fields = entity.fields.map(f => fileSym.name(f.name)).map(kb.intern)
          kb.registerEntityFields(sym, fields)

        case Item.OperationItem(op) =>
          val shortName = joinSegments(fileSym, op.name.segments)
          val qualName = makeQualified(prefix, shortName)
          kb.symbols.define(shortName, qualName, SymbolKind.Operation, scopeTerm.raw)
          kb.symbols.addExport(scopeTerm.raw, shortName)

        case Item.OperationBlockItem(block) =>
          for op <- block.entries do
            val shortName = joinSegments(fileSym, op.name.segments)
            val qualName = makeQualified(prefix, shortName)
            kb.symbols.define(shortName, qualName, SymbolKind.Operation, scopeTerm.raw)
            kb.symbols.addExport(scopeTerm.raw, shortName)

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
                kb.symbols.resolveInScope(name, symTerm.raw) match
                  case ResolveResult.Found(found) =>
                    kb.symbols.addImport(scopeTerm.raw, name, found)
                  case _ =>
                    errors += LoadError.UnresolvedName(name, n.span, pathStr)
            case ImportKind.Wildcard =>
              val parentTerm = kb.makeNameTermFromSym(sym)
              kb.symbols.addParent(scopeTerm.raw,
                ScopeInclusion(parentTerm.raw, 0, isEnclosing = false))
        case None =>
          errors += LoadError.UnresolvedImport(pathStr, imp.path.span)

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
          val vm = HashMap.empty[Int, VarId] // shared across head+body
          rule.head match
            case RuleHead.TermHead(headId) =>
              val kbHead = reallocTerm(kb, fileTerms, fileSym, headId, scopeTerm, errors, vm)
              val kbBody = rule.body.map(_.map(b =>
                reallocTerm(kb, fileTerms, fileSym, b, scopeTerm, errors, vm))).getOrElse(IndexedSeq.empty)
              kb.assertRule(kbHead, kbBody, sortSort, scopeTerm)
            case RuleHead.Bottom =>
              val kbBody = rule.body.map(_.map(b =>
                reallocTerm(kb, fileTerms, fileSym, b, scopeTerm, errors, vm))).getOrElse(IndexedSeq.empty)
              val botTerm = kb.alloc(Term.Bottom)
              kb.assertRule(botTerm, kbBody, sortSort, scopeTerm)

        case Item.RuleBlockItem(block) =>
          val sortSort = findSortTerm(kb, "anthill.reflect.Rule")
          for rule <- block.entries do
            val vm = HashMap.empty[Int, VarId]
            rule.head match
              case RuleHead.TermHead(headId) =>
                val kbHead = reallocTerm(kb, fileTerms, fileSym, headId, scopeTerm, errors, vm)
                val kbBody = rule.body.map(_.map(b =>
                  reallocTerm(kb, fileTerms, fileSym, b, scopeTerm, errors, vm))).getOrElse(IndexedSeq.empty)
                kb.assertRule(kbHead, kbBody, sortSort, scopeTerm)
              case RuleHead.Bottom => // TODO

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

        case _ => // Other items

  // ── Term reallocation ─────────────────────────────────────────

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
      case Term.Var(vid) =>
        // Map parse-time VarId to a fresh KB VarId (preserves sharing within scope)
        val kbVid = varMap.getOrElseUpdate(vid.id, {
          val name = fileSym.name(vid.name)
          val kbSym = kb.intern(name)
          kb.freshVar(kbSym)
        })
        kb.alloc(Term.Var(kbVid))
      case fn: Term.Fn =>
        val name = fileSym.name(fn.functor)
        val kbFunctor = resolveName(kb, name, scopeTerm)
        val kbPos = IArray.from(fn.posArgs.map(id => reallocTerm(kb, fileTerms, fileSym, id, scopeTerm, errors, varMap)))
        val kbNamed = IArray.from(fn.namedArgs.map { (sym, id) =>
          val kbKeySym = kb.intern(fileSym.name(sym))
          (kbKeySym, reallocTerm(kb, fileTerms, fileSym, id, scopeTerm, errors, varMap))
        })
        kb.alloc(Term.Fn(kbFunctor, kbPos, kbNamed))
      case Term.Ref(sym) =>
        val name = fileSym.name(sym)
        val kbSym = resolveName(kb, name, scopeTerm)
        kb.alloc(Term.Ref(kbSym))
      case Term.Ident(sym) =>
        val name = fileSym.name(sym)
        val kbSym = resolveName(kb, name, scopeTerm)
        kb.alloc(Term.Ident(kbSym))
      case Term.Bottom => kb.alloc(Term.Bottom)

  /** Resolve a name in scope, falling back to intern. */
  private def resolveName(kb: KnowledgeBase, name: String, scopeTerm: TermId): TermSymbol =
    kb.symbols.byQualifiedName.get(name) match
      case Some(sym) => sym
      case None =>
        kb.symbols.resolveInScope(name, scopeTerm.raw) match
          case ResolveResult.Found(sym) => sym
          case _ => kb.intern(name)

  private def findSortTerm(kb: KnowledgeBase, qualName: String): TermId =
    kb.symbols.byQualifiedName.get(qualName) match
      case Some(sym) => kb.makeNameTermFromSym(sym)
      case None => kb.makeNameTerm(qualName)

  // ── Helpers ─────────────────────────────────────────────────

  private def joinSegments(symbols: SymbolTable, segments: IndexedSeq[TermSymbol]): String =
    segments.map(symbols.name).mkString(".")

  private def makeQualified(prefix: String, name: String): String =
    if prefix.isEmpty then name else s"$prefix.$name"
