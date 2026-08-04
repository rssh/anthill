package anthill.intern

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}


/** Per-scope data: locals, imports, exposed variants, parent inclusions,
  * type params.
  *
  * `exposed` holds the names this scope leaks to its enclosing scope through a
  * (non-enclosing) variant-exposure parent link — a sort's entity-variant
  * short names ONLY (proposal 044 job 2). An empty set disables the filter
  * (the scope is reachable only via `requires`/wildcard, which see all of it).
  * Names are visible by default; the `export` statement was removed in WI-291. */
class Scope:
  val locals: HashMap[String, TermSymbol] = HashMap.empty
  val imports: HashMap[String, TermSymbol] = HashMap.empty
  val exposed: HashSet[String] = HashSet.empty
  val parents: ArrayBuffer[ScopeInclusion] = ArrayBuffer.empty
  val typeParams: HashSet[String] = HashSet.empty

/** Symbol table — maps strings to compact TermSymbol(Int) handles,
  * with optional resolution metadata (kind, scope, qualified name).
  *
  * WI-976: every scope-keyed entry point takes a [[ScopeId]]. It used to take a raw
  * `Int` — nine of them — so the table could not tell a scope from a term id from an
  * array index, and each caller carried the promise instead.
  */
class SymbolTable:
  private val defs = ArrayBuffer.empty[SymbolDef]
  private val internMap = HashMap.empty[String, TermSymbol]
  val byQualifiedName: HashMap[String, TermSymbol] = HashMap.empty
  private val scopes = HashMap.empty[ScopeId, Scope]

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
  def define(shortName: String, qualifiedName: String, kind: SymbolKind, scopeId: ScopeId): TermSymbol =
    val scope = scopes.getOrElseUpdate(scopeId, Scope())
    scope.locals.get(shortName) match
      case Some(existing) => existing
      case None =>
        val sym = TermSymbol.fromRaw(defs.length)
        defs += SymbolDef.Resolved(shortName, qualifiedName, kind, scopeId)
        scope.locals(shortName) = sym
        byQualifiedName(qualifiedName) = sym
        sym

  /** Mark a name as exposed from a scope to its enclosing scope via the
    * variant-exposure parent link (populated from entity variants only). */
  def addExposed(scopeId: ScopeId, name: String): Unit =
    scopes.getOrElseUpdate(scopeId, Scope()).exposed += name

  def addTypeParam(scopeId: ScopeId, name: String): Unit =
    scopes.getOrElseUpdate(scopeId, Scope()).typeParams += name

  def addImport(scopeId: ScopeId, shortName: String, sym: TermSymbol): Unit =
    scopes.getOrElseUpdate(scopeId, Scope()).imports(shortName) = sym

  def addParent(scopeId: ScopeId, inclusion: ScopeInclusion): Unit =
    scopes.getOrElseUpdate(scopeId, Scope()).parents += inclusion

  def scope(scopeId: ScopeId): Option[Scope] = scopes.get(scopeId)

  /** Resolve a name within a scope. */
  def resolveInScope(name: String, scopeId: ScopeId): ResolveResult =
    val visited = HashSet.empty[ScopeId]
    resolveRecursive(name, scopeId, visited)

  private def resolveRecursive(
    name: String, scopeId: ScopeId, visited: HashSet[ScopeId]
  ): ResolveResult =
    if !visited.add(scopeId) then return ResolveResult.NotFound // cycle

    scopes.get(scopeId) match
      case None => ResolveResult.NotFound
      case Some(scope) =>
        // 1. Local
        scope.locals.get(name).foreach(sym => return ResolveResult.Found(sym))
        // 1b. Imports
        scope.imports.get(name).foreach(sym => return ResolveResult.Found(sym))

        // 2. Collect eligible parent scopes
        val eligibleParents = scope.parents.filter { p =>
          if p.isEnclosing then true
          else scopes.get(p.parent) match
            case None => true
            case Some(parent) =>
              !parent.typeParams.contains(name) &&
              (parent.exposed.isEmpty || parent.exposed.contains(name))
        }.map(_.parent)

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
