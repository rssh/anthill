package anthill.intern

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}


/** Per-scope data: locals, imports, exports, parent inclusions, type params. */
class Scope:
  val locals: HashMap[String, TermSymbol] = HashMap.empty
  val imports: HashMap[String, TermSymbol] = HashMap.empty
  val exports: HashSet[String] = HashSet.empty
  val parents: ArrayBuffer[ScopeInclusion] = ArrayBuffer.empty
  val typeParams: HashSet[String] = HashSet.empty

/** Symbol table — maps strings to compact TermSymbol(Int) handles,
  * with optional resolution metadata (kind, scope, qualified name).
  */
class SymbolTable:
  private val defs = ArrayBuffer.empty[SymbolDef]
  private val internMap = HashMap.empty[String, TermSymbol]
  val byQualifiedName: HashMap[String, TermSymbol] = HashMap.empty
  private val scopes = HashMap.empty[Int, Scope]

  /** Intern a name, returning a TermSymbol. Creates an Unresolved entry
    * if the name hasn't been seen before (deduplicated).
    */
  def intern(s: String): TermSymbol =
    internMap.getOrElseUpdate(s, {
      val sym = TermSymbol.fromRaw(defs.length)
      defs += SymbolDef.Unresolved(s)
      sym
    })

  /** Define a new resolved symbol in a scope. If the same shortName
    * already exists in the scope, returns the existing symbol (merge behavior).
    */
  def define(shortName: String, qualifiedName: String, kind: SymbolKind, scopeRaw: Int): TermSymbol =
    val scope = scopes.getOrElseUpdate(scopeRaw, Scope())
    scope.locals.get(shortName) match
      case Some(existing) => existing
      case None =>
        val sym = TermSymbol.fromRaw(defs.length)
        defs += SymbolDef.Resolved(shortName, qualifiedName, kind, scopeRaw)
        scope.locals(shortName) = sym
        byQualifiedName(qualifiedName) = sym
        sym

  def addExport(scopeRaw: Int, name: String): Unit =
    scopes.getOrElseUpdate(scopeRaw, Scope()).exports += name

  def addTypeParam(scopeRaw: Int, name: String): Unit =
    scopes.getOrElseUpdate(scopeRaw, Scope()).typeParams += name

  def addImport(scopeRaw: Int, shortName: String, sym: TermSymbol): Unit =
    scopes.getOrElseUpdate(scopeRaw, Scope()).imports(shortName) = sym

  def addParent(scopeRaw: Int, inclusion: ScopeInclusion): Unit =
    scopes.getOrElseUpdate(scopeRaw, Scope()).parents += inclusion

  def scope(scopeRaw: Int): Option[Scope] = scopes.get(scopeRaw)

  def scopeMut(scopeRaw: Int): Scope =
    scopes.getOrElseUpdate(scopeRaw, Scope())

  /** Resolve a name within a scope. */
  def resolveInScope(name: String, scopeRaw: Int): ResolveResult =
    val visited = HashSet.empty[Int]
    resolveRecursive(name, scopeRaw, visited)

  private def resolveRecursive(name: String, scopeRaw: Int, visited: HashSet[Int]): ResolveResult =
    if !visited.add(scopeRaw) then return ResolveResult.NotFound // cycle

    scopes.get(scopeRaw) match
      case None => ResolveResult.NotFound
      case Some(scope) =>
        // 1. Local
        scope.locals.get(name).foreach(sym => return ResolveResult.Found(sym))
        // 1b. Imports
        scope.imports.get(name).foreach(sym => return ResolveResult.Found(sym))

        // 2. Collect eligible parent scopes
        val eligibleParents = scope.parents.filter { p =>
          if p.isEnclosing then true
          else scopes.get(p.parentScopeRaw) match
            case None => true
            case Some(parent) =>
              !parent.typeParams.contains(name) &&
              (parent.exports.isEmpty || parent.exports.contains(name))
        }.map(_.parentScopeRaw)

        val matches = ArrayBuffer.empty[TermSymbol]
        for parentScope <- eligibleParents do
          resolveRecursive(name, parentScope, visited) match
            case ResolveResult.Found(sym) => matches += sym
            case ResolveResult.Ambiguous(candidates) => matches ++= candidates
            case ResolveResult.NotFound =>

        // Deduplicate via HashSet (avoids double map/copy)
        val seen = HashSet.empty[Int]
        val deduped = matches.filter(s => seen.add(TermSymbol.raw(s)))

        deduped.length match
          case 0 => ResolveResult.NotFound
          case 1 => ResolveResult.Found(deduped(0))
          case _ => ResolveResult.Ambiguous(deduped.toVector)

  /** Get the display name of a symbol. */
  def name(sym: TermSymbol): String =
    defs(sym.raw) match
      case SymbolDef.Unresolved(n)         => n
      case SymbolDef.Resolved(shortName, _, _, _) => shortName

  /** Alias for name(). */
  def resolve(sym: TermSymbol): String = name(sym)

  /** Get the full SymbolDef. */
  def get(sym: TermSymbol): SymbolDef = defs(sym.raw)

  /** Check if a symbol is resolved. */
  def isResolved(sym: TermSymbol): Boolean =
    defs(sym.raw) match
      case _: SymbolDef.Resolved => true
      case _                     => false

  def size: Int = defs.length
