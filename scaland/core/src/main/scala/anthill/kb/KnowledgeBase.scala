package anthill.kb

import anthill.intern.{TermSymbol, SymbolTable, SymbolKind, SymbolDef}
import anthill.term.{Term, TermId, TermStore, Var, VarId, Literal}
import anthill.subst.Substitution
import anthill.discrim.SubstTree

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

class KnowledgeBase:
  val terms: TermStore = TermStore()
  val symbols: SymbolTable = SymbolTable()

  private val rules = ArrayBuffer.empty[RuleEntry]

  private val bySort_ = HashMap.empty[Int, ArrayBuffer[RuleId]]
  private val byFunctor_ = HashMap.empty[Int, ArrayBuffer[RuleId]]
  private val byDomain_ = HashMap.empty[Int, ArrayBuffer[RuleId]]

  private val sortEntities_ = HashMap.empty[Int, ArrayBuffer[TermId]]
  private val entityParent_ = HashMap.empty[Int, TermId]
  private val sortInfo_ = HashMap.empty[Int, SortKind]

  private val discrim: SubstTree[RuleId] = SubstTree()

  private val builtins_ = HashMap.empty[Int, BuiltinTag]
  private val entityFields_ = HashMap.empty[Int, IndexedSeq[TermSymbol]]
  private val constructorSymbols_ = HashSet.empty[Int]
  private var nextVar: Int = 0
  private val sortBaseSubst_ = HashMap.empty[Int, IndexedSeq[(TermSymbol, TermId)]]

  // ── Term allocation ─────────────────────────────────────────

  def alloc(term: Term): TermId = terms.alloc(term)

  def intern(s: String): TermSymbol = symbols.intern(s)

  def freshVar(name: TermSymbol): VarId =
    val id = nextVar
    nextVar += 1
    VarId(id, name)

  def resolveSym(sym: TermSymbol): String = symbols.name(sym)

  def qualifiedNameOf(sym: TermSymbol): String =
    symbols.get(sym) match
      case SymbolDef.Resolved(_, qualifiedName, _, _) => qualifiedName
      case SymbolDef.Unresolved(name) => name

  def getTerm(id: TermId): Term = terms.get(id)

  // ── Rule assertion / retraction ─────────────────────────────

  def assertRule(
    head: TermId, body: IndexedSeq[TermId],
    sort: TermId, domain: TermId, meta: Option[TermId] = None
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
    byDomain_.getOrElseUpdate(TermId.raw(domain), ArrayBuffer.empty) += ruleId

    terms.get(dbHead) match
      case fn: Term.Fn =>
        byFunctor_.getOrElseUpdate(TermSymbol.raw(fn.functor), ArrayBuffer.empty) += ruleId
      case _ =>

    discrim.insertPattern(terms, dbHead, ruleId)
    ruleId

  def assertFact(
    term: TermId, sort: TermId, domain: TermId, meta: Option[TermId] = None
  ): RuleId =
    bySort_.get(TermId.raw(sort)) match
      case Some(ids) =>
        for rid <- ids do
          val entry = rules(rid.index)
          if !entry.retracted &&
             TermId.raw(entry.head) == TermId.raw(term) &&
             TermId.raw(entry.domain) == TermId.raw(domain) &&
             entry.body.isEmpty then
            return rid
      case None =>
    assertRule(term, IndexedSeq.empty, sort, domain, meta)

  def retract(id: RuleId): Unit =
    val entry = rules(id.index)
    if entry.retracted then return
    entry.retracted = true
    bySort_.get(TermId.raw(entry.sort)).foreach(_.filterInPlace(_ != id))
    byDomain_.get(TermId.raw(entry.domain)).foreach(_.filterInPlace(_ != id))
    terms.get(entry.head) match
      case fn: Term.Fn =>
        byFunctor_.get(TermSymbol.raw(fn.functor)).foreach(_.filterInPlace(_ != id))
      case _ =>

  // ── Sort management ─────────────────────────────────────────

  def registerSort(sortTerm: TermId, kind: SortKind): Unit =
    sortInfo_(TermId.raw(sortTerm)) = kind

  def registerEntityOf(entity: TermId, parent: TermId): Unit =
    sortEntities_.getOrElseUpdate(TermId.raw(parent), ArrayBuffer.empty) += entity
    entityParent_(TermId.raw(entity)) = parent
    terms.get(entity) match
      case fn: Term.Fn => constructorSymbols_ += TermSymbol.raw(fn.functor)
      case _ =>

  def isEntityOf(sub: TermId, sup: TermId): Boolean =
    TermId.raw(sub) == TermId.raw(sup) ||
    entityParent_.get(TermId.raw(sub)).exists(p => TermId.raw(p) == TermId.raw(sup))

  /** Get the parent sort of an entity (1-level, non-transitive). */
  def entityParentSort(entity: TermId): Option[TermId] =
    entityParent_.get(TermId.raw(entity))

  /** Check if a functor symbol is a constructor (entity with a parent sort). */
  def isConstructorSymbol(functor: TermSymbol): Boolean =
    constructorSymbols_.contains(TermSymbol.raw(functor))

  // ── Query ───────────────────────────────────────────────────

  def bySort(sort: TermId): ArrayBuffer[RuleId] =
    val result = ArrayBuffer.empty[RuleId]
    bySort_.get(TermId.raw(sort)).foreach { ids =>
      for rid <- ids if !rules(rid.index).retracted do result += rid
    }
    sortEntities_.get(TermId.raw(sort)).foreach { children =>
      for child <- children do
        bySort_.get(TermId.raw(child)).foreach { ids =>
          for rid <- ids if !rules(rid.index).retracted do result += rid
        }
    }
    result

  def byFunctor(sym: TermSymbol): ArrayBuffer[RuleId] =
    byFunctor_.get(TermSymbol.raw(sym))
      .map(_.filter(rid => !rules(rid.index).retracted))
      .getOrElse(ArrayBuffer.empty)

  def byDomain(domain: TermId): ArrayBuffer[RuleId] =
    byDomain_.get(TermId.raw(domain))
      .map(_.filter(rid => !rules(rid.index).retracted))
      .getOrElse(ArrayBuffer.empty)

  // ── Rule accessors ───────────────────────────────────────────

  def ruleHead(id: RuleId): TermId = rules(id.index).head
  def ruleBody(id: RuleId): IndexedSeq[TermId] = rules(id.index).body
  def ruleSort(id: RuleId): TermId = rules(id.index).sort
  def ruleDomain(id: RuleId): TermId = rules(id.index).domain
  def ruleMeta(id: RuleId): Option[TermId] = rules(id.index).meta

  def factTerm(id: RuleId): TermId = ruleHead(id)
  def factSort(id: RuleId): TermId = ruleSort(id)
  def factDomain(id: RuleId): TermId = ruleDomain(id)

  // ── Counting ─────────────────────────────────────────────────

  def factCount: Int = rules.count(r => !r.retracted && r.body.isEmpty)
  def ruleCount: Int = rules.count(r => !r.retracted && r.body.nonEmpty)

  // ── Sort queries ─────────────────────────────────────────────

  def sortKind(sortTerm: TermId): Option[SortKind] = sortInfo_.get(TermId.raw(sortTerm))

  def sortBaseSubst(sym: TermSymbol): Option[IndexedSeq[(TermSymbol, TermId)]] =
    sortBaseSubst_.get(TermSymbol.raw(sym))

  def setSortBaseSubst(sym: TermSymbol, subst: IndexedSeq[(TermSymbol, TermId)]): Unit =
    sortBaseSubst_(TermSymbol.raw(sym)) = subst

  def sortChildren(sortTerm: TermId): IndexedSeq[TermId] =
    sortEntities_.get(TermId.raw(sortTerm)).map(_.toIndexedSeq).getOrElse(IndexedSeq.empty)

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
      case fn: Term.Fn =>
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
      case fn: Term.Fn =>
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
      case _: Term.Fn => mapFnChildren(term, id => applySubst(id, subst))
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
      case _: Term.Fn => mapFnChildren(walked, id => reify(id, subst))
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
      case _: Term.Fn => mapFnChildren(term, id => termToDebruijn(id, order))
      case _ => term

  /** Open a DeBruijn term: replace `DeBruijn(i)` with `Global(freshVars(i))`
    * (rustland `term_from_debruijn`). An out-of-range index or a Global/Rigid
    * var is left untouched. */
  def termFromDebruijn(term: TermId, freshVars: IndexedSeq[VarId]): TermId =
    terms.get(term) match
      case Term.Var(Var.DeBruijn(idx)) =>
        if idx < freshVars.length then alloc(Term.Var(Var.Global(freshVars(idx)))) else term
      case Term.Var(_) => term
      case _: Term.Fn => mapFnChildren(term, id => termFromDebruijn(id, freshVars))
      case _ => term

  /** Does `vid` occur (chased through `subst`) in the term rooted at `term`?
    * Guards `withFreshVars` against binding a cyclic query-var link (WI-624). */
  private def occursInTerm(vid: VarId, term: TermId, subst: Substitution): Boolean =
    terms.get(walk(term, subst)) match
      case Term.Var(v) => v.varId.id == vid.id
      case fn: Term.Fn =>
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

  def makeNameTerm(name: String): TermId =
    val sym = symbols.intern(name)
    terms.alloc(Term.Fn(sym, IArray.empty, IArray.empty))

  def makeNameTermFromSym(sym: TermSymbol): TermId =
    terms.alloc(Term.Fn(sym, IArray.empty, IArray.empty))

  def resolveQualifiedNameTerm(name: String): TermId =
    val sym = symbols.byQualifiedName.get(name).getOrElse(symbols.intern(name))
    terms.alloc(Term.Fn(sym, IArray.empty, IArray.empty))

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
    * (WI-528). */
  def isEquation(id: RuleId): Boolean =
    val entry = rules(id.index)
    if entry.body.nonEmpty || entry.retracted then return false
    terms.get(entry.head) match
      case fn: Term.Fn =>
        val name = symbols.name(fn.functor)
        (name == "eq" || name == "unify") && fn.posArgs.length == 2
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
    entityFields_(TermSymbol.raw(functor)) = fields

  def entityFieldNames(functor: TermSymbol): Option[IndexedSeq[TermSymbol]] =
    entityFields_.get(TermSymbol.raw(functor))

  // ── Builtin dispatch ────────────────────────────────────────

  def registerBuiltin(sym: TermSymbol, tag: BuiltinTag): Unit =
    builtins_(TermSymbol.raw(sym)) = tag

  def getBuiltin(goal: TermId): Option[BuiltinTag] =
    terms.get(goal) match
      case fn: Term.Fn => builtins_.get(TermSymbol.raw(fn.functor))
      case _ => None

// ── BuiltinTag ────────────────────────────────────────────────

enum BuiltinTag:
  case NonVar, Ground, QualifiedName, ShortName, LookupSymbol
  case IsEntityOf, ExtractSort, Not
  case ResolveSortInstParam, Scope, Kind, FieldAccess
