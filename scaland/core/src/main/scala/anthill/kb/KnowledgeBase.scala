package anthill.kb

import anthill.intern.{GLOBAL_SCOPE_NAME, TermSymbol, SymbolTable, SymbolKind, SymbolDef, Decl}
import anthill.term.{Term, TermId, TermStore, Var, VarId, Literal}
import anthill.subst.Substitution
import anthill.discrim.SubstTree

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

class KnowledgeBase:
  val terms: TermStore = TermStore()
  val symbols: SymbolTable = SymbolTable()

  private[anthill] val loadBoundary = anthill.load.LoadBoundaryState()

  /** THE KB PINS ONE TABLE (WI-1004). A scope identity is a member of the [[SymbolTable]]
    * that issued it, and a KB has exactly one — so `kb.ScopeId` is `kb.symbols.ScopeId`
    * and the two spellings are interchangeable. That settles the question the ticket asked
    * first: everything the KB stores a scope in — `byDomain_`, [[RuleEntry]]`.domain` — is
    * fixed at this one table, rather than each clause carrying a table of its own. */
  type ScopeId = symbols.ScopeId

  /** A stored clause. INSIDE the KB (WI-1004) so `domain` can name [[ScopeId]] directly:
    * as a top-level class it would need a type parameter, and one that could never vary,
    * since the KB is its only constructor and its only reader. */
  private class RuleEntry(
    val head: TermId,
    val body: IndexedSeq[TermId],
    val sort: TermId,
    // The SCOPE the clause was declared in (WI-983) — see [[assertRule]].
    val domain: ScopeId,
    val meta: Option[TermId],
    // Number of distinct DeBruijn vars closed over head+body (WI-637). 0 for a
    // truly ground fact — those take the resolver's raw-bind fast path; arity>0
    // rules (incl. bodyless facts with vars) open through `withFreshVars`.
    val arity: Int = 0,
    var retracted: Boolean = false
  )

  private val rules = ArrayBuffer.empty[RuleEntry]

  private val bySort_ = HashMap.empty[Int, ArrayBuffer[RuleId]]
  private val byFunctor_ = HashMap.empty[Int, ArrayBuffer[RuleId]]
  // WI-983: keyed on the SCOPE, not on a term id. The sibling indices key on a raw
  // because their key is a term — this one's is not, and the key type is where that
  // gets said. Rustland's twin is `HashMap<Symbol, Vec<RuleId>>` (`kb/mod.rs`).
  private val byDomain_ = HashMap.empty[ScopeId, ArrayBuffer[RuleId]]

  // The DECLARATION tables (WI-20261020-80VNX): keyed by `Decl`, which drops a type face,
  // so a constructor's type `red[]` answers what `red`'s declaration answers. They were
  // keyed by the name TERM's id, which a face — a different term — would have missed.
  private val sortEntities_ = HashMap.empty[Decl, ArrayBuffer[TermId]]
  private val entityParent_ = HashMap.empty[Decl, TermSymbol]
  private val sortInfo_ = HashMap.empty[Decl, SortKind]

  private val discrim: SubstTree[RuleId] = SubstTree()

  private val builtins_ = HashMap.empty[Int, BuiltinTag]
  private val entityFields_ = HashMap.empty[Decl, IndexedSeq[TermSymbol]]
  private val constructorSymbols_ = HashSet.empty[Decl]
  private var nextVar: Int = 0
  private val sortBaseSubst_ = HashMap.empty[Decl, IndexedSeq[(TermSymbol, TermId)]]
  private val quotedFields_ = HashMap.empty[Decl, HashSet[TermSymbol]]

  // ── Term allocation ─────────────────────────────────────────

  /** WI-20260902-CZJ2N — ONE STORAGE FORM FOR A NULLARY APPLICATION: `Term.Fn(f, [], [])`
    * is stored as `Term.Ref(f)`, so `rule holds :- b(1)` and `rule holds() :- b(1)` are one
    * term and one predicate, as §5.3/§8.6 say in words.
    *
    * FOR EVERY NAME (WI-20261020-80VNX; rustland's `nullary_name_canons_to_ref`, JB6RS
    * step 6). This used to exempt a name with a TYPE reading, on rustland's WI-391 / WI-387
    * ground that `Ref(S)` was the dispatch wildcard and a nullary `Fn(S)` the concrete spec
    * identity; scaland has no dispatch, and rustland read the wildcard off the symbol's
    * role instead (WI-20260829-7QVD5), so `Shape()` and `Shape` are one term now — the
    * distinction the split was last measured holding up, a constructor's TYPE against its
    * INSTANCE, is carried by the type faces ([[typeFaceOf]]), decided by the context and
    * not by the parentheses (kernel-language.md §4.4, §6). It also retires the
    * contradiction the JB6RS ticket measured here: the discrimination tree keyed `Ref(S)`
    * and `Fn(S)` alike while `Substitution.unifyMatch` refused the pair, so a candidate the
    * tree retrieved the unifier undid.
    *
    * ONE EXCEPTION, by QUALIFIED name: the three collection-literal forms of
    * `anthill.reflect` are the vocabulary a term encodes a literal in, and their empty
    * application is the empty literal's node — `()` is `TupleLiteral()` — which is not
    * their bare name. A user's own entity spelled like one is an ordinary entity, and so
    * is a form's TYPE FACE: `ListLiteral[]` is the type, one term with the bare face. */
  def alloc(term: Term): TermId = term match
    case Term.Fn(functor, pos, named) if pos.isEmpty && named.isEmpty &&
        (functor.isTypeFace || !isReflectLiteralForm(functor)) =>
      terms.alloc(Term.Ref(functor))
    case _ => terms.alloc(term)

  /** Is `sym` one of the three collection-literal forms [[alloc]]'s canon exempts? By
    * qualified name alone. Rustland also asks for the free-standing entity's two kinds,
    * which its stdlib always declares there; scaland's `Prelude` registers the three as
    * `Entity` only before any stdlib is loaded, so a kind test would make `()` the empty
    * tuple in one KB and the bare name in another. */
  private def isReflectLiteralForm(sym: TermSymbol): Boolean =
    symbols.get(sym) match
      case SymbolDef.Resolved(_, qualified, _, _) => KnowledgeBase.reflectLiteralForms.contains(qualified)
      case SymbolDef.Unresolved(_) => false

  /** WI-20261020-80VNX (rustland's `is_type_value_head`) — does `sym` name ONLY a type: a
    * constructor's type face, or a sort with no constructor of its name? Such a name has
    * no reading as an application, so `S(…)` is refused where it is written
    * ([[anthill.load.LoadError.SortAppliedAsData]]) and its type is written `S[…]`
    * (kernel-language.md §4.4). An eponymous or free-standing entity has a constructor of
    * its name (`Entity`), and is applied as one.
    *
    * Rustland's loader lets a sort and an OPERATION share a name, and gives that sort a
    * type face as it gives a constructor one (WI-20261022-7EXEY), so its plain symbol is
    * the operation. Scaland's does not: an operation at a sort's address is a duplicate
    * declaration (`Loader.checkDeclarations`) and a body-less rule there is refused as
    * adding nothing, so no symbol of a clean load is a sort and something else to apply
    * (measured). */
  def namesOnlyAType(sym: TermSymbol): Boolean =
    sym.isTypeFace || {
      val d = symbols.get(sym)
      d.hasKind(SymbolKind.Sort) && !d.hasKind(SymbolKind.Entity)
    }

  /** The TYPE FACE of `sym`'s declaration — the symbol a TYPE CONTEXT names it by — when
    * that declaration is of kind `Entity`; the declaration's own symbol otherwise
    * (WI-20261020-80VNX; rustland's `type_face_of` / `type_context_face`).
    *
    * A constructor — a sort-nested `entity red`, an eponymous `sort Foo … entity Foo(…) …
    * end`, a free-standing `entity Foo(…)` — is a sort in its own right (§6.3), so it has
    * two readings, its instance and its type, and only such a declaration gets a second
    * identity. A sort with no constructor of its name (`Int64`, `Cell`) has exactly one
    * face, which is why this never puts the bit on one (kernel-language.md §4.4). The kind
    * is read, not the constructor registry, because the kind is stamped in pass 1 before
    * any term is built. THE way to a face outside `intern`; idempotent. */
  def typeFaceOf(sym: TermSymbol): TermSymbol =
    val decl = sym.plain
    if symbols.get(decl).hasKind(SymbolKind.Entity) then decl.typeFace else decl

  def intern(s: String): TermSymbol = symbols.intern(s)

  /** The kind reflection's `kind` reports for `sym`: the first declaration's keyword, and
    * for a constructor's TYPE FACE `Sort` — `red[]` is a type, `red` the entity
    * (WI-20261020-80VNX; rustland's `reflect_kind`). Display only, as `primaryKind` is. */
  def reflectKind(sym: TermSymbol): Option[SymbolKind] =
    if sym.isTypeFace then Some(SymbolKind.Sort) else symbols.get(sym).primaryKind

  def freshVar(name: TermSymbol): VarId =
    val id = nextVar
    nextVar += 1
    VarId(id, name)

  def resolveSym(sym: TermSymbol): String = symbols.name(sym)

  def qualifiedNameOf(sym: TermSymbol): String =
    symbols.get(sym) match
      case SymbolDef.Resolved(_, qualifiedName, _, _) => qualifiedName
      case SymbolDef.Unresolved(name) => name

  // ── Scopes ──────────────────────────────────────────────────

  /** The synthetic scope a file's top-level declarations land in. A `val` naming the one
    * spelling, not a general `scopeNamed(name: String)`: every call site wanted this
    * scope, and a mint taking an arbitrary string would reopen for `String` the hole
    * [[ScopeId]] closes for `Int` — `scopeNamed("Wodget")` compiles and denotes a scope
    * that resolves nothing.
    *
    * A `val` and not a `def` because `intern` WRITES: as a `def` this read-shaped member
    * grew the symbol table on every call, so merely inspecting a KB (a dump, a
    * diagnostic) allocated a symbol and shifted every id after it. Minting once at
    * construction is also the cheaper answer — the loader asks for it per file.
    *
    * The spelling is [[anthill.intern.GLOBAL_SCOPE_NAME]], shared with rustland and, since
    * WI-987, a name NO DECLARATION CAN TAKE. It was `_global` — a legal identifier in both
    * grammars — so `namespace _global` defined a SECOND scope rendering identically, and a
    * diagnostic naming a scope named either one of them. Why the sentinel closes that
    * without a check is at the constant.
    *
    * A `val` naming a symbol, so `symbols.scopeOf(symbols.intern(GLOBAL_SCOPE_NAME))` names
    * this same scope: the KB's ONE mint (WI-990) is total over the symbol universe and this
    * scope is in it. Its predecessor `scopeByQualifiedName` — a second mint, over
    * QUALIFIED names — could not name this one at all (the sentinel is interned and never
    * defined) and THREW on a miss with no error channel, into four `Unit`-returning
    * `Prelude` steps whose ordering was the only thing keeping it unreachable. It is
    * gone: `Prelude` now takes the stdlib scopes as a value from the step that creates
    * them, so there is no name to miss. */
  val globalScope: ScopeId =
    symbols.scopeOf(symbols.intern(GLOBAL_SCOPE_NAME))

  /** A scope's TERM form — for the four callers that must hand a scope where a TERM is
    * what fits: the `entity_of` and `provides_clause` facts embed one as an argument,
    * `registerEntityOf` records one as an entity's parent, and reflect's `scope` builtin
    * binds one as an answer. A clause's DOMAIN was spelled here too, at six loader sites,
    * and is one no longer — it is a [[ScopeId]] (WI-983), which is what leaves the
    * remaining four all genuine.
    *
    * `registerEntityOf`'s reads as the enclosing scope and IS the parent sort, because
    * WI-985 gated its one caller on the scope being a sort. An `entity` written directly
    * under a namespace — which the spec permits — records no parent at all rather than
    * recording the namespace as one; the same rule for the rule form is stated at
    * `stdlib/anthill/reflect/typing.anthill`, whose `entity_of` guard depends on it.
    *
    * THE direction that is a function (WI-976): it goes through [[makeNameTermFromSym]],
    * the one name-term producer, so scope-as-term stays the nullary shape [[ScopeId]]
    * presumes; recovering a scope FROM a term is what the type makes unnecessary. */
  def scopeTerm(scope: ScopeId): TermId =
    makeNameTermFromSym(symbols.symbolOf(scope))

  /** The name to call `scope` in a diagnostic (WI-957) — its QUALIFIED name where the
    * scope is a declared one, and the interned spelling ([[anthill.intern.GLOBAL_SCOPE_NAME]])
    * for the synthetic global scope, which is not a declaration and has no qualified name.
    * Those two never collide (WI-987): the sentinel is no identifier, so no qualified name
    * is spelled like it.
    *
    * It lives HERE, next to [[qualifiedNameOf]], and not in the loader that first needed
    * it (WI-962): "what do we call this scope in a diagnostic" gets ONE answer for every
    * raise site, rather than a helper per site — which is how the `requires` site came to
    * name no scope at all.
    *
    * TOTAL (WI-976) — it used to take a bare `TermId` and throw on one that was no scope.
    * See [[anthill.intern.SymbolTable.ScopeId]] for why that arm has no replacement. */
  def scopeDisplayName(scope: ScopeId): String =
    qualifiedNameOf(symbols.symbolOf(scope))

  def getTerm(id: TermId): Term = terms.get(id)

  // ── Rule assertion / retraction ─────────────────────────────

  /** Assert a rule into `domain` — the SCOPE it was declared in (WI-983).
    *
    * The slot used to be a `TermId`, so every caller spelled the scope as its term form
    * on the spot and the KB stored a term it never looked inside: the domain is an index
    * key here and an identity in [[assertFact]]'s dedup, nothing more. A scope's term
    * form is a real thing with real readers ([[scopeTerm]]) — this slot was simply never
    * one of them, and typing it says so: passing a term where a scope belongs is now a
    * compile error rather than a convention. Rustland has stored `domain: Symbol`
    * throughout, so this is the parity direction as well. */
  def assertRule(
    head: TermId, body: IndexedSeq[TermId],
    sort: TermId, domain: ScopeId, meta: Option[TermId] = None
  ): RuleId =
    // WI-637: close the rule's Global head/body vars to DeBruijn (positional,
    // first-occurrence order over head then body), so a stored head var is
    // reflexive-only at match time and opened to a fresh Global by
    // `withFreshVars`. Mirrors rustland `assert_rule_debruijn_with_nodes`.
    val order = collectRuleVars(head, body)
    val arity = order.length
    val dbHead = termToDebruijn(head, order)
    val dbBody = if arity == 0 then body else body.map(termToDebruijn(_, order))

    val ruleId = RuleId.fromIndex(rules.length)
    rules += RuleEntry(dbHead, dbBody, sort, domain, meta, arity)

    bySort_.getOrElseUpdate(TermId.raw(sort), ArrayBuffer.empty) += ruleId
    byDomain_.getOrElseUpdate(domain, ArrayBuffer.empty) += ruleId

    // WI-20260902-CZJ2N — INDEX THE NULLARY HEAD TOO. `rule holds()` and `rule holds`
    // are one term now, stored as `Term.Ref`, so the `Term.Fn`-only read filed NEITHER
    // spelling's clause under its functor — `byFunctor` answered empty and nothing said
    // so. `headFunctorOf` is the one reader for "which functor does this head name".
    headFunctorOf(dbHead).foreach { f =>
      byFunctor_.getOrElseUpdate(TermSymbol.raw(f), ArrayBuffer.empty) += ruleId
    }

    discrim.insertPattern(terms, dbHead, ruleId)
    ruleId

  def assertFact(
    term: TermId, sort: TermId, domain: ScopeId, meta: Option[TermId] = None
  ): RuleId =
    bySort_.get(TermId.raw(sort)) match
      case Some(ids) =>
        for rid <- ids do
          val entry = rules(rid.index)
          if !entry.retracted &&
             TermId.raw(entry.head) == TermId.raw(term) &&
             // Compared through the raws, like the head above it, and not as
             // `entry.domain == domain`: `ScopeId`, `TermSymbol` and `TermId` all erase
             // to `Int` and this build does not run `-language:strictEquality`, so a
             // cross-type `==` compiles clean and answers on raw indices. Extracting
             // first puts the type check where a wrong operand cannot reach.
             TermSymbol.raw(symbols.symbolOf(entry.domain)) ==
               TermSymbol.raw(symbols.symbolOf(domain)) &&
             entry.body.isEmpty then
            return rid
      case None =>
    assertRule(term, IndexedSeq.empty, sort, domain, meta)

  def retract(id: RuleId): Unit =
    val entry = rules(id.index)
    if entry.retracted then return
    entry.retracted = true
    bySort_.get(TermId.raw(entry.sort)).foreach(_.filterInPlace(_ != id))
    byDomain_.get(entry.domain).foreach(_.filterInPlace(_ != id))
    // Insert and retract must read the head the same way, or a retract leaves the
    // clause in the bucket (WI-20260902-CZJ2N).
    headFunctorOf(entry.head).foreach { f =>
      byFunctor_.get(TermSymbol.raw(f)).foreach(_.filterInPlace(_ != id))
    }

  // ── Sort management ─────────────────────────────────────────

  def registerSort(sortTerm: TermId, kind: SortKind): Unit =
    sortInfo_(declarationOf(sortTerm, "registerSort")) = kind

  def registerEntityOf(entity: TermId, parent: TermId): Unit =
    // WI-20260902-CZJ2N — READ THE FUNCTOR OFF EITHER SPELLING (`nullaryName`). A nullary
    // entity term is stored as `Term.Ref`, so a `Term.Fn`-only read stopped marking any
    // 0-ary constructor at all — silently, since `isConstructorSymbol` answering `false`
    // is a legal answer everywhere it is asked. Rustland keys this index by SYMBOL for
    // the same reason (WI-697).
    val entityDecl = declarationOf(entity, "registerEntityOf")
    val parentDecl = declarationOf(parent, "registerEntityOf")
    sortEntities_.getOrElseUpdate(parentDecl, ArrayBuffer.empty) += entity
    entityParent_(entityDecl) = parentDecl.symbol
    constructorSymbols_ += entityDecl

  /** Is `sub` an entity of the sort `sup`? Reflexive; otherwise both are NAMES and they are
    * compared as DECLARATIONS (WI-20261020-80VNX): `sup` may name the parent by its type
    * face, and a constructor's instance is an entity of its OWN type — `red` of `red[]`,
    * as an eponymous `Foo` of `Foo[]` — which held while the two were one term. Mirrors
    * rustland's `is_entity_of_view`. An APPLIED constructor is not a name and answers
    * false here, as before. */
  def isEntityOf(sub: TermId, sup: TermId): Boolean =
    TermId.raw(sub) == TermId.raw(sup) || ((nullaryName(sub), nullaryName(sup)) match
      case (Some(subSym), Some(supSym)) =>
        // Of its own type only when `sub` names an ENTITY's declaration: two spellings of
        // some other name are not an entity and its sort.
        (symbols.get(subSym).hasKind(SymbolKind.Entity) && supSym.plain == subSym.plain) ||
          entityParent_.get(Decl.of(subSym)).contains(supSym.plain)
      case _ => false)

  /** Get the parent sort of an entity (1-level, non-transitive), as its name term. */
  def entityParentSort(entity: TermId): Option[TermId] =
    nullaryName(entity).flatMap(s => entityParent_.get(Decl.of(s))).map(makeNameTermFromSym)

  /** Is `functor` a constructor NESTED in a sort — the head of an instance? FALSE for a
    * type face (WI-20261020-80VNX): an application of `red`'s face is the TYPE `red[…]`,
    * never a construction. A caller asking about the DECLARATION says `.plain`. */
  def isConstructorSymbol(functor: TermSymbol): Boolean =
    !functor.isTypeFace && constructorSymbols_.contains(Decl.of(functor))

  /** The symbol a NAME term spells, or `None` for any other term (an application, a
    * variable, a literal). A nullary `Term.Fn` is no name: [[alloc]] stores every name's
    * nullary application bare, so the one that is left is a reflect form's empty-literal
    * VALUE — `[]` — and not the name `ListLiteral`. */
  private def nullaryName(term: TermId): Option[TermSymbol] = terms.get(term) match
    case Term.Ref(s) => Some(s)
    case Term.Ident(s) => Some(s)
    case _ => None

  /** The declaration a NAME term names, for a declaration-table WRITE: a type face is not
    * a declaration, and a term that names nothing has no key — both refused loudly. */
  private def declarationOf(term: TermId, what: String): Decl =
    nullaryName(term) match
      case Some(s) if !s.isTypeFace => Decl.of(s)
      case other => throw IllegalArgumentException(
        s"$what: ${terms.get(term)} names no declaration${if other.isDefined then " (a type face)" else ""}")

  // ── Query ───────────────────────────────────────────────────

  def bySort(sort: TermId): ArrayBuffer[RuleId] =
    val result = ArrayBuffer.empty[RuleId]
    bySort_.get(TermId.raw(sort)).foreach { ids =>
      for rid <- ids if !rules(rid.index).retracted do result += rid
    }
    nullaryName(sort).flatMap(s => sortEntities_.get(Decl.of(s))).foreach { children =>
      for child <- children do
        bySort_.get(TermId.raw(child)).foreach { ids =>
          for rid <- ids if !rules(rid.index).retracted do result += rid
        }
    }
    result

  /** The functor a rule/fact HEAD names, in either spelling. WI-20260902-CZJ2N: a
    * nullary head is stored as `Term.Ref`, so a `Term.Fn`-only read misses it. `None` for
    * a head that names no functor (a variable, a literal, `⊥`). */
  private def headFunctorOf(head: TermId): Option[TermSymbol] =
    terms.get(head) match
      case Term.Fn(functor, _, _) => Some(functor)
      case Term.Ref(sym)          => Some(sym)
      case _                      => None

  def byFunctor(sym: TermSymbol): ArrayBuffer[RuleId] =
    byFunctor_.get(TermSymbol.raw(sym))
      .map(_.filter(rid => !rules(rid.index).retracted))
      .getOrElse(ArrayBuffer.empty)

  /** Every live clause declared in `domain` — the scope-keyed peer of [[bySort]] and
    * [[byFunctor]]. */
  def byDomain(domain: ScopeId): ArrayBuffer[RuleId] =
    byDomain_.get(domain)
      .map(_.filter(rid => !rules(rid.index).retracted))
      .getOrElse(ArrayBuffer.empty)

  // ── Rule accessors ───────────────────────────────────────────

  def ruleHead(id: RuleId): TermId = rules(id.index).head
  def ruleBody(id: RuleId): IndexedSeq[TermId] = rules(id.index).body
  def ruleSort(id: RuleId): TermId = rules(id.index).sort
  def ruleDomain(id: RuleId): ScopeId = rules(id.index).domain
  def ruleMeta(id: RuleId): Option[TermId] = rules(id.index).meta

  def factTerm(id: RuleId): TermId = ruleHead(id)
  def factSort(id: RuleId): TermId = ruleSort(id)
  def factDomain(id: RuleId): ScopeId = ruleDomain(id)

  // ── Counting ─────────────────────────────────────────────────

  def factCount: Int = rules.count(r => !r.retracted && r.body.isEmpty)
  def ruleCount: Int = rules.count(r => !r.retracted && r.body.nonEmpty)

  // ── Sort queries ─────────────────────────────────────────────

  def sortKind(sortTerm: TermId): Option[SortKind] =
    nullaryName(sortTerm).flatMap(s => sortInfo_.get(Decl.of(s)))

  def sortBaseSubst(sym: TermSymbol): Option[IndexedSeq[(TermSymbol, TermId)]] =
    sortBaseSubst_.get(Decl.of(sym))

  def setSortBaseSubst(sym: TermSymbol, subst: IndexedSeq[(TermSymbol, TermId)]): Unit =
    require(!sym.isTypeFace, "setSortBaseSubst: a type face is not a declaration")
    sortBaseSubst_(Decl.of(sym)) = subst

  def sortChildren(sortTerm: TermId): IndexedSeq[TermId] =
    nullaryName(sortTerm).flatMap(s => sortEntities_.get(Decl.of(s)))
      .map(_.toIndexedSeq).getOrElse(IndexedSeq.empty)

  // ── Term matching ─────────────────────────────────────────────

  def matchTerm(pattern: TermId, target: TermId): Option[Substitution] =
    val tree = SubstTree[Unit]()
    tree.insertPattern(terms, target, ())
    // One-directional matching: a repeated pattern var matches only
    // structurally-IDENTICAL target subterms (WI-637 `unifyRebind = false`).
    val results = tree.queryResolved(terms, pattern, _ => target, unifyRebind = false)
    results.find((_, s) => !s.isContradiction).map(_._2)

  def query(pattern: TermId): ArrayBuffer[(RuleId, Substitution)] =
    // SLD head selection IS unification: a repeated head var (or repeated query
    // var, WI-512) unifies its two matched subterms (WI-637 `unifyRebind =
    // true`), so `unbox0(box(v: ?v), ?v)` queried `unbox0(box(v: some(?x)),
    // some(42))` binds `?x = 42` instead of false-failing as a contradiction.
    val candidates = discrim.queryResolved(terms, pattern, rid => rules(rid.index).head, unifyRebind = true)
    val results = ArrayBuffer.empty[(RuleId, Substitution)]
    for (rid, subst) <- candidates do
      if !rules(rid.index).retracted && !subst.isContradiction then
        results += ((rid, subst))
    // Stable-sort: facts (empty body) before rules (non-empty body).
    // The discrimination tree uses HashMap internally, so candidate order
    // is non-deterministic. DFS resolution depends on trying ground facts
    // before recursive rules to find base-case solutions first.
    results.sortInPlaceBy((rid, _) => if rules(rid.index).body.isEmpty then 0 else 1)
    results

  def queryRules(pattern: TermId): ArrayBuffer[(RuleId, Substitution)] =
    query(pattern).filter((rid, _) => rules(rid.index).body.nonEmpty)

  // ── Variable operations ─────────────────────────────────────

  def collectVars(term: TermId): ArrayBuffer[VarId] =
    val vars = ArrayBuffer.empty[VarId]
    val seen = HashSet.empty[Int]
    collectVarsRec(term, vars, seen)
    vars

  private def collectVarsRec(term: TermId, vars: ArrayBuffer[VarId], seen: HashSet[Int]): Unit =
    terms.get(term) match
      case Term.Var(v) =>
        val vid = v.varId
        if seen.add(vid.id) then vars += vid
      case fn: Term.Fn[TermId] =>
        fn.posArgs.foreach(id => collectVarsRec(id, vars, seen))
        fn.namedArgs.foreach((_, id) => collectVarsRec(id, vars, seen))
      case _ =>

  /** Collect all vars from a rule's head + body (shared by standardizeApart/withFreshVars). */
  private def collectRuleVars(head: TermId, body: IndexedSeq[TermId]): ArrayBuffer[VarId] =
    val vars = ArrayBuffer.empty[VarId]
    val seen = HashSet.empty[Int]
    collectVarsRec(head, vars, seen)
    for b <- body do collectVarsRec(b, vars, seen)
    vars

  /** Map over Fn children, returning the same TermId if nothing changed (avoids allocation). */
  private def mapFnChildren(term: TermId, f: TermId => TermId): TermId =
    terms.get(term) match
      case fn: Term.Fn[TermId] =>
        var changed = false
        val newPos = IArray.tabulate(fn.posArgs.length) { i =>
          val old = fn.posArgs(i); val r = f(old)
          if TermId.raw(r) != TermId.raw(old) then changed = true
          r
        }
        val newNamed = IArray.tabulate(fn.namedArgs.length) { i =>
          val (sym, old) = fn.namedArgs(i); val r = f(old)
          if TermId.raw(r) != TermId.raw(old) then changed = true
          (sym, r)
        }
        if changed then alloc(Term.Fn(fn.functor, newPos, newNamed)) else term
      case _ => term

  def applySubst(term: TermId, subst: Substitution): TermId =
    terms.get(term) match
      case Term.Var(v) => subst.resolve(v.varId).getOrElse(term)
      case _: Term.Fn[TermId] => mapFnChildren(term, id => applySubst(id, subst))
      case _ => term

  def walk(term: TermId, subst: Substitution): TermId =
    var current = term
    var continue = true
    while continue do
      terms.get(current) match
        case Term.Var(v) =>
          subst.resolve(v.varId) match
            case Some(bound) =>
              if TermId.raw(bound) == TermId.raw(current) then continue = false
              else current = bound
            case None => continue = false
        case _ => continue = false
    current

  def reify(term: TermId, subst: Substitution): TermId =
    val walked = walk(term, subst)
    terms.get(walked) match
      case Term.Var(_) => walked
      case _: Term.Fn[TermId] => mapFnChildren(walked, id => reify(id, subst))
      case _ => walked

  /** Number of DeBruijn vars a rule closes over head+body (WI-637); 0 for a
    * fully-ground rule/fact. */
  def ruleArity(id: RuleId): Int = rules(id.index).arity

  /** Close `Var.Global` vars in `term` to `Var.DeBruijn`, indexed against
    * `order` (distinct Globals in first-occurrence order): the last var in
    * `order` gets index 0 (innermost binder), mirroring rustland
    * `term_to_debruijn`. Vars not in `order`, or already DeBruijn/Rigid, are
    * left untouched. */
  private def termToDebruijn(term: TermId, order: collection.Seq[VarId]): TermId =
    terms.get(term) match
      case Term.Var(Var.Global(vid)) =>
        val pos = order.indexWhere(_ == vid)
        if pos >= 0 then alloc(Term.Var(Var.DeBruijn(order.length - 1 - pos))) else term
      case Term.Var(_) => term
      case _: Term.Fn[TermId] => mapFnChildren(term, id => termToDebruijn(id, order))
      case _ => term

  /** Open a DeBruijn term: replace `DeBruijn(i)` with `Global(freshVars(i))`
    * (rustland `term_from_debruijn`). An out-of-range index or a Global/Rigid
    * var is left untouched. */
  def termFromDebruijn(term: TermId, freshVars: IndexedSeq[VarId]): TermId =
    terms.get(term) match
      case Term.Var(Var.DeBruijn(idx)) =>
        if idx < freshVars.length then alloc(Term.Var(Var.Global(freshVars(idx)))) else term
      case Term.Var(_) => term
      case _: Term.Fn[TermId] => mapFnChildren(term, id => termFromDebruijn(id, freshVars))
      case _ => term

  /** Does `vid` occur (chased through `subst`) in the term rooted at `term`?
    * Guards `withFreshVars` against binding a cyclic query-var link (WI-624). */
  private def occursInTerm(vid: VarId, term: TermId, subst: Substitution): Boolean =
    terms.get(walk(term, subst)) match
      case Term.Var(v) => v.varId.id == vid.id
      case fn: Term.Fn[TermId] =>
        fn.posArgs.exists(occursInTerm(vid, _, subst)) ||
          fn.namedArgs.exists((_, t) => occursInTerm(vid, t, subst))
      case _ => false

  def standardizeApart(id: RuleId): (TermId, IndexedSeq[TermId]) =
    val entry = rules(id.index)
    if entry.arity == 0 then (entry.head, entry.body)
    else
      val underscore = intern("_")
      val freshVars = IndexedSeq.tabulate(entry.arity)(_ => freshVar(underscore))
      val newHead = termFromDebruijn(entry.head, freshVars)
      val newBody = entry.body.map(termFromDebruijn(_, freshVars))
      (newHead, newBody)

  /** Open a rule for a discrim head-match (WI-637), mirroring rustland
    * `with_fresh_vars`. Allocate `arity` fresh Globals for the head/body
    * DeBruijn vars; then in two passes over `treeSubst`:
    *   1. a SYNTHETIC-DeBruijn entry (a matched head-var position, keyed by
    *      `Var.varId`'s reserved range) → `bodyRename` (its fresh Global ← the
    *      concrete query value it matched);
    *   2. a query-var entry → `answerLinks`, DeBruijn-opened then routed through
    *      `bodyRename` so a nonlinear head's concrete match reaches the caller
    *      var — occurs-checked so a cyclic link (`p(box(v: g(?q)), ?q)`) flags
    *      the whole match contradictory (the resolver drops the candidate)
    *      rather than looping `reify`.
    * `arity == 0` (a fully-ground rule) degenerates: no fresh vars, empty
    * `bodyRename`, every entry a direct query-var link. */
  def withFreshVars(id: RuleId, treeSubst: Substitution): (IndexedSeq[TermId], Substitution) =
    val entry = rules(id.index)
    val arity = entry.arity
    val body = entry.body

    val underscore = intern("_")
    val freshVars = IndexedSeq.tabulate(arity)(_ => freshVar(underscore))

    val bodyRename = Substitution()
    for (tsVid, boundTerm) <- treeSubst.bindings do
      Var.syntheticDebruijnIndex(tsVid, arity) match
        case Some(dbIndex) if dbIndex < freshVars.length =>
          bodyRename.bind(freshVars(dbIndex), boundTerm)
        case _ =>

    val answerLinks = Substitution()
    for (tsVid, boundTerm) <- treeSubst.bindings do
      if Var.syntheticDebruijnIndex(tsVid, arity).isEmpty then
        val opened = termFromDebruijn(boundTerm, freshVars)
        if bodyRename.isEmpty then
          answerLinks.bind(tsVid, opened)
        else
          val linked = applySubst(opened, bodyRename)
          // Don't bind a cyclic link (it would loop later occurs-walks / reify);
          // the contradiction flag already dooms this candidate.
          if occursInTerm(tsVid, linked, answerLinks) then answerLinks.markContradiction()
          else answerLinks.bind(tsVid, linked)

    val freshBody = body.map(b => applySubst(termFromDebruijn(b, freshVars), bodyRename))
    (freshBody, answerLinks)

  def applySubstEach(goals: IndexedSeq[TermId], subst: Substitution): IndexedSeq[TermId] =
    goals.map(g => applySubst(g, subst))

  // ── Helpers ─────────────────────────────────────────────────

  /** THE producer of a name term, and so of every SCOPE term (WI-962) — the spellings
    * above ([[makeNameTerm]], [[scopeTerm]]) differ only in how they get the symbol, and
    * all go through here. One producer is one thing to keep true, which is what lets
    * [[ScopeId]] presume the shape instead of re-deriving it. */
  /** A NAME term for `sym` — a nullary application, in whichever spelling [[alloc]]
    * stores.
    *
    * WI-20260902-CZJ2N: routes through [[alloc]], where it called `terms.alloc` directly
    * and so stepped around the nullary canon. A canon a caller can bypass is a second
    * spelling waiting to happen — rustland's `resolve_qualified_name_term` had exactly
    * this bypass and WI-1023 had to teach its `Map` key path to tolerate the third
    * spelling it left in the store. */
  def makeNameTermFromSym(sym: TermSymbol): TermId =
    // The bare `Ref`, built as one: for a reflect collection-literal form the nullary
    // APPLICATION is the empty literal (`[]`), which is not the form's name
    // (WI-20261020-80VNX).
    alloc(Term.Ref(sym))

  def makeNameTerm(name: String): TermId =
    makeNameTermFromSym(symbols.intern(name))

  def resolveSymbol(name: String): TermSymbol =
    tryResolveSymbol(name).getOrElse(
      throw new IllegalStateException(s"resolveSymbol: '$name' is not a resolved symbol"))

  def tryResolveSymbol(name: String): Option[TermSymbol] =
    symbols.byQualifiedName.get(name)

  def hasQualifiedName(name: String): Boolean =
    symbols.byQualifiedName.contains(name)

  // ── Rule classification ─────────────────────────────────────

  /** Check if a rule is an equation: head functor is "eq" or "unify" (the
    * `<=>` head, proposal 049) with 2 positional args and an empty body. The
    * classification is *type-independent* — purely the head shape — so a
    * migrated `<=>` equation (WI-526) is recognized identically to a legacy
    * `=` one. Recognized by SHORT NAME rather than symbol identity: a loaded
    * functor resolves to the *Resolved* `anthill.prelude.Eq.eq` /
    * `anthill.kernel.unify` symbol, whose short name is "eq"/"unify" — not the
    * bare interned symbol. Mirrors rustland's `KnowledgeBase::is_equation`
    * (WI-528). ERF7T also admits the absolute parse carrier, measured by
    * KnowledgeBaseTest's address row, which fails without that admission. */
  def isEquation(id: RuleId): Boolean =
    val entry = rules(id.index)
    if entry.body.nonEmpty || entry.retracted then return false
    terms.get(entry.head) match
      case fn: Term.Fn[TermId] =>
        val name = symbols.name(fn.functor)
        (name == "eq" || name == "unify" || name == anthill.parse.Pratt.unifyFunctor) && fn.posArgs.length == 2
      case _ => false

  // ── Name-level substitution ──────────────────────────────────

  def substTerm(term: TermId, from: TermId, to: TermId): TermId =
    if TermId.raw(term) == TermId.raw(from) then return to
    mapFnChildren(term, id => substTerm(id, from, to))

  def substTermMulti(term: TermId, bindings: IndexedSeq[(TermId, TermId)]): TermId =
    var t = term
    for (from, to) <- bindings do t = substTerm(t, from, to)
    t

  // ── Entity field registry ──────────────────────────────────

  def registerEntityFields(functor: TermSymbol, fields: IndexedSeq[TermSymbol]): Unit =
    require(!functor.isTypeFace, "registerEntityFields: a type face is not a declaration")
    entityFields_(Decl.of(functor)) = fields

  /** WI-20261020-80VNX — record that `entity`'s field `field` is declared
    * `anthill.reflect.Term`, so it holds a QUOTED pattern (see `Loader.QuotedFieldPass`). */
  def registerQuotedField(entity: TermSymbol, field: TermSymbol): Unit =
    require(!entity.isTypeFace, "registerQuotedField: a type face is not a declaration")
    quotedFields_.getOrElseUpdate(Decl.of(entity), HashSet.empty) += field

  /** Is `field` of an application of `functor` a QUOTED one? Never for a type face: the
    * bindings of `Foo[…]` are type parameters, not fields. */
  def isQuotedField(functor: TermSymbol, field: TermSymbol): Boolean =
    !functor.isTypeFace && quotedFields_.get(Decl.of(functor)).exists(_.contains(field))

  /** The field names `functor`'s DECLARATION registers — a type face's are its
    * constructor's. Whether an application of `functor` CONSTRUCTS is a different question:
    * a face's never does. */
  def entityFieldNames(functor: TermSymbol): Option[IndexedSeq[TermSymbol]] =
    entityFields_.get(Decl.of(functor))

  // ── Builtin dispatch ────────────────────────────────────────

  def registerBuiltinTag(sym: TermSymbol, tag: BuiltinTag): Unit =
    builtins_(TermSymbol.raw(sym)) = tag

  /** The builtin tag a GOAL's functor carries, in either spelling.
    *
    * WI-20260902-CZJ2N: a NULLARY goal is stored as `Term.Ref`, so the `Term.Fn`-only
    * read answered `None` for `:- not` and every other 0-ary builtin goal — and an
    * untagged builtin goal "resolves and does nothing", which is the silence
    * `PreludeScopesTest` exists to catch from the other side. */
  def getBuiltin(goal: TermId): Option[BuiltinTag] =
    headFunctorOf(goal).flatMap(builtinOf)

  /** The builtin tag a SYMBOL carries — [[getBuiltin]]'s answer for a goal that is not a
    * term yet, which is what the loader has while it is still building one. */
  def builtinOf(functor: TermSymbol): Option[BuiltinTag] =
    builtins_.get(TermSymbol.raw(functor))

  /** The POSITIONAL slots of `functor` the resolver evaluates as GOALS TO PROVE, and
    * nothing else — empty for a plain predicate or a data constructor. Mirrors rustland's
    * `KnowledgeBase::goal_arg_slots`.
    *
    * Primitives are keyed on their dispatch tags. The derived kernel `or` / `and`
    * rules have no tag, so compare their resolved symbols, never a user's short name.
    * NARC7: the loader must check constants in the same slots the resolver proves. */
  def goalArgSlots(functor: TermSymbol, posArity: Int): Set[Int] =
    builtinOf(functor) match
      case Some(BuiltinTag.Not) if posArity >= 1 => Set(0)
      case Some(BuiltinTag.PushChoice | BuiltinTag.PushAnd) if posArity == 2 => Set(0, 1)
      case _ if posArity == 2 && Seq("anthill.kernel.or", "anthill.kernel.and")
          .exists(name => tryResolveSymbol(name).contains(functor)) => Set(0, 1)
      case _ => Set.empty

object KnowledgeBase:
  /** The collection-literal forms of `anthill.reflect` whose empty application is a node
    * of its own — see `alloc`. */
  private val reflectLiteralForms: Set[String] = Set(
    "anthill.reflect.TupleLiteral", "anthill.reflect.ListLiteral", "anthill.reflect.SetLiteral")

// ── BuiltinTag ────────────────────────────────────────────────

enum BuiltinTag:
  case NonVar, Ground, QualifiedName, ShortName, LookupSymbol
  case IsEntityOf, ExtractSort, Not, PushChoice, PushAnd
  case ResolveSortInstParam, Scope, Kind, FieldAccess
