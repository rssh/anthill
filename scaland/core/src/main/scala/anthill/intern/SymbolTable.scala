package anthill.intern

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}


/** Symbol table — maps strings to compact TermSymbol(Int) handles,
  * with optional resolution metadata (kind, scope, qualified name).
  *
  * WI-976: every scope-keyed entry point takes a [[ScopeId]]. It used to take a raw
  * `Int` — nine of them — so the table could not tell a scope from a term id from an
  * array index, and each caller carried the promise instead.
  */
class SymbolTable:

  /** THE IDENTITY OF A SCOPE — the thing a name is resolved against, and A MEMBER OF THE
    * TABLE THAT ISSUES IT (WI-1004), so `st1.ScopeId` and `st2.ScopeId` are distinct
    * types and `st2.resolveInScope(n, aScopeOfSt1)` does not compile.
    *
    * WI-976: scope-hood used to be UNTYPED. A scope was a bare `Int` in nine
    * [[SymbolTable]] methods, in [[SymbolDef.Resolved]] and in [[ScopeInclusion]], and a
    * bare `anthill.term.TermId` at every `KnowledgeBase` and loader entry point — so a
    * scope, an arbitrary term and an arbitrary integer were ONE type, and "this TermId is
    * a scope" was a claim every caller re-made at runtime. `KnowledgeBase.scopeFunctor`
    * re-derived scope-hood structurally and answered `None`; `scopeDisplayName` THREW on
    * that answer. Neither arm was reachable in fact — the nullary name term was the only
    * shape any producer built — which is the definition of a runtime check standing in
    * for a type.
    *
    * A SCOPE IS A SYMBOL. [[scopeOf]] is the sole mint and it is total over its table's
    * symbols, so [[symbolOf]] is a projection, not a query: no `Option`, no term store,
    * nothing to refuse, and so nothing for a caller to re-decide.
    *
    * TOTAL OVER A TABLE'S SYMBOLS IS THE POINT, not a weakening of it. The scope graph is
    * OPEN — a scope's entry is created lazily, so every symbol of that table is a
    * potential scope and its KIND is nothing the mint could require. What this type
    * carries is a ROLE plus a TABLE, not a capability: it says the value came from a
    * symbol rather than from an integer or an arbitrary term, and from WHICH table's
    * symbols — which is the whole of what was being promised by hand before.
    *
    * The scope's TERM form — `Term.Fn(symbol, [], [])`, what an `entity_of` fact and a
    * rule's domain carry — is recovered by `KnowledgeBase.scopeTerm`, which goes through
    * the one name-term producer (`makeNameTermFromSym`, WI-962). Scope → term is a
    * function; this type is what makes the other direction unnecessary.
    *
    * WHY A MEMBER AND NOT A TOP-LEVEL OPAQUE TYPE (WI-1004). A `TermSymbol` is an index
    * into one table's `defs`, and the loader threads TWO tables side by side — `kb.symbols`
    * and the parse-time `fileSym` — through nearly every signature. WI-990 moved the mint
    * onto the table so every site WRITES which table it means, and refused an
    * out-of-range symbol; but that refusal points the wrong way, because `fileSym` is
    * SMALL and `kb.symbols` LARGE, so a parse-time symbol read as a KB scope is always in
    * range and always passed. Membership is what a check could not be: the table is in
    * the TYPE, so the hand-off is rejected before any index is looked at.
    *
    * WHAT IT COST. A record that holds a scope has to say which table's, and there are two
    * ways: move INSIDE the owner, or take a type parameter. [[Scope]] and [[ScopeInclusion]]
    * moved here and `RuleEntry` moved into `KnowledgeBase`; [[SymbolDef]] takes a parameter
    * because it is pattern-matched by unqualified name at ~20 sites, which a member enum
    * would make `kb.symbols.SymbolDef.Resolved(…)` at every one. Beyond that, dependent
    * method types (`def f(kb: KnowledgeBase, scope: kb.ScopeId)`) through the loader —
    * which is a consequence of `Loader` being an `object` that threads `kb` through ~48
    * signatures, not of this type: a `Loader` pinned to one `kb` would spell every one of
    * them plain `ScopeId` again. That refactor is real and is NOT what this WI did.
    *
    * It cost NO tag on `TermSymbol`, which is the invasive thing it looked like it would
    * need: tagging the symbol would reach the term store and the discrimination tree,
    * which key on `TermSymbol` and have no table to speak of.
    *
    * WHAT REMAINS OPEN: a foreign symbol handed to the RIGHT table's mint.
    * `kb.symbols.scopeOf(fileSym.intern("x"))` still type-checks, because [[scopeOf]] takes
    * a bare `TermSymbol` and there is nothing on it to check. Closing it needs the symbol
    * to carry its table — either globally (the term store and discrim tree again) or as a
    * second table-owned opaque type returned by `intern`/`define`/`byQualifiedName` and
    * widened explicitly at each term boundary, which is ~100 sites. `ScopeIdentityTest`
    * asserts that limit rather than implying it is closed. */
  opaque type ScopeId = TermSymbol

  /** Per-scope data: locals, imports, exposed variants, parent inclusions,
    * type params.
    *
    * `exposed` holds the names this scope leaks to its enclosing scope through a
    * (non-enclosing) variant-exposure parent link — a sort's entity-variant
    * short names ONLY (proposal 044 job 2). An empty set disables the filter
    * (the scope is reachable only via `requires`/wildcard, which see all of it).
    * Names are visible by default; the `export` statement was removed in WI-291.
    *
    * Inner (WI-1004) because `parents` names [[ScopeId]], which is this table's. */
  class Scope:
    val locals: HashMap[String, TermSymbol] = HashMap.empty
    val imports: HashMap[String, TermSymbol] = HashMap.empty
    val exposed: HashSet[String] = HashSet.empty
    val parents: ArrayBuffer[ScopeInclusion] = ArrayBuffer.empty
    val typeParams: HashSet[String] = HashSet.empty

  /** A parent link in the scope graph (WI-976: `parent` is a scope identity, not the raw
    * `Int` a caller had to promise was one).
    *
    * Inner and BUILT ONLY BY [[addParent]] (WI-1004). It was a top-level record, which
    * once `parent` became this table's [[ScopeId]] meant a type parameter — on a two-field
    * bundle whose fifteen construction sites were all the immediate argument of
    * `addParent` and whose only reader is `resolveRecursive` below. Naming the fields at
    * the one method that takes them says the same thing without a public generic type.
    *
    * The record used to carry a third field, `instantiationTermRaw: Int` — a raw term id,
    * written by every producer and read by NONE, here and in rustland alike (`kb/load.rs`
    * says so at its own writers). WI-976 dropped it rather than retype it: parity was the
    * only argument for keeping it, and that same change already moved `parent` from a
    * TermId raw to a symbol, so the two records had stopped agreeing regardless. What was
    * left was an untyped term id inside the record whose untypedness that ticket exists to
    * remove. The rustland twin is WI-984. */
  case class ScopeInclusion(parent: ScopeId, isEnclosing: Boolean)

  private val defs = ArrayBuffer.empty[SymbolDef[ScopeId]]
  private val internMap = HashMap.empty[String, TermSymbol]
  val byQualifiedName: HashMap[String, TermSymbol] = HashMap.empty
  private val scopes = HashMap.empty[ScopeId, Scope]

  /** This scope's entry, created on first write — the ONE place a `Scope` is built, for
    * the five writers below.
    *
    * Spelled out rather than `scopes.getOrElseUpdate(scopeId, Scope())` (WI-1004): the
    * default is BY-NAME, so once `Scope` became an inner class the thunk captured `this`
    * and each of those five sites allocated a fresh `Function0` on EVERY call, hit or miss
    * — 1918 of them over a stdlib load. Measured in the bytecode: the `invokedynamic`
    * went from `apply:()Lscala/Function0;` to `apply:(Lanthill/intern/SymbolTable;)…`.
    * This form pays one extra hash on the MISS path instead, and there are 151 misses. */
  private def scopeEntry(scopeId: ScopeId): Scope =
    scopes.get(scopeId) match
      case Some(scope) => scope
      case None =>
        val scope = Scope()
        scopes(scopeId) = scope
        scope

  /** THE mint for a [[ScopeId]] (WI-990) — on the table, because a `TermSymbol` is an
    * index into ONE table's `defs` and means nothing anywhere else. It was a companion
    * method, total over `TermSymbol` and therefore silent about which table the symbol
    * came from, while the loader threads two. Every mint now WRITES the table it means.
    *
    * The range check is what a table can actually decide, and it is the case that was
    * MEASURED: a symbol from a bigger table reached `qualifiedNameOf` and threw
    * `IndexOutOfBoundsException` from inside a display path, and `scopeTerm` built a name
    * term for whatever symbol shared that index. It is refused HERE instead, naming the
    * table's size, because the mint is where the mistake is.
    *
    * IT IS STILL ONE-DIRECTIONAL — see [[ScopeId]]'s "WHAT REMAINS OPEN", which is the
    * argument's one home. What matters HERE is the consequence: the check is
    * LOAD-BEARING, not vestigial. WI-1004 closed every USE of a scope at another table,
    * and this mint is what it did not close, so the bound below is the only thing standing
    * between a foreign symbol and an `IndexOutOfBoundsException` inside a display path.
    *
    * `ScopeIdentityTest` asserts all of it — the mint's location and the cross-table
    * hand-off as compile errors, the range refusal at runtime, and the residual hole. */
  def scopeOf(sym: TermSymbol): ScopeId =
    val raw = TermSymbol.raw(sym)
    if raw < 0 || raw >= defs.length then
      throw new IllegalArgumentException(
        s"scopeOf: symbol #$raw is past this symbol table's ${defs.length} entries — " +
        "a symbol only means anything in the table that issued it")
    sym

  /** The symbol that names `scope`. Total by construction — see [[scopeOf]]. A method on
    * the table rather than an extension on the type (WI-1004): the projection is only
    * meaningful relative to the table that issued the scope, and this is the spelling that
    * says so at the call site. Named for the SYMBOL layer, not the term layer (`functor`
    * would be the word if a scope were a term, which is exactly what [[ScopeId]] denies). */
  def symbolOf(scope: ScopeId): TermSymbol = scope

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
    val scope = scopeEntry(scopeId)
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
    scopeEntry(scopeId).exposed += name

  def addTypeParam(scopeId: ScopeId, name: String): Unit =
    scopeEntry(scopeId).typeParams += name

  def addImport(scopeId: ScopeId, shortName: String, sym: TermSymbol): Unit =
    scopeEntry(scopeId).imports(shortName) = sym

  /** Link `parent` into `scopeId`'s parent chain. `isEnclosing` is named at every call
    * site because the two kinds read the same and resolve differently — an ENCLOSING
    * parent is searched whole, a non-enclosing one only through its `exposed` filter. */
  def addParent(scopeId: ScopeId, parent: ScopeId, isEnclosing: Boolean): Unit =
    scopeEntry(scopeId).parents += ScopeInclusion(parent, isEnclosing)

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
  def get(sym: TermSymbol): SymbolDef[ScopeId] = defs(sym.raw)

  /** Check if a symbol is resolved. */
  def isResolved(sym: TermSymbol): Boolean =
    defs(sym.raw) match
      case _: SymbolDef.Resolved[?] => true
      case _                     => false

  def size: Int = defs.length
