package anthill.discrim

import anthill.intern.TermSymbol
import anthill.subst.Substitution
import anthill.term.{Literal, Term, TermId, TermStore, VarId}
import scala.collection.mutable.{ArrayBuffer, HashMap}

// ── DiscrimKey — concrete edge labels ───────────────────────────

enum DiscrimKey:
  case Functor(sym: TermSymbol)
  case Arity(n: Int)
  case NamedKey(sym: TermSymbol)
  case Positional
  case Lit(lit: Literal)
  case IdentKey(sym: TermSymbol)
  case Bottom

/** WI-20260902-CZJ2N — THE NULLARY SPELLING OF AN APPLICATION, for the six walks below.
  *
  * A bare `Term.Ref(f)` IS the nullary application `f()`, so it keys under the SAME path
  * as one: `Functor(f)` then `Arity(0)`. `DiscrimKey.RefKey` was a second key space for
  * the same thing, and it is what made a fact written `holds` invisible to a goal written
  * `holds()` — the walks here read `Term` directly rather than through `TermView`, so no
  * view-layer canon could have reached them.
  *
  * SPELLED AS AN EXPLICIT ARM AT EACH WALK, not as an `unapply` extractor covering both:
  * Scala's exhaustivity checker cannot see through an extractor, and every `match` over
  * `Term` in this file is deliberately wildcard-free so that a new variant is a compile
  * error rather than a silent mis-index. `Term.Ident` keeps its own key — an UNRESOLVED
  * name is not an application of anything.
  */
private inline def NULLARY_ARITY: Int = 0

// ── DiscrimNode — tree node ─────────────────────────────────────

private class DiscrimNode[L]:
  val concrete: HashMap[DiscrimKey, DiscrimNode[L]] = HashMap.empty
  val varEdges: ArrayBuffer[(VarId, DiscrimNode[L])] = ArrayBuffer.empty
  val leaves: ArrayBuffer[L] = ArrayBuffer.empty

  def isEmpty: Boolean = concrete.isEmpty && varEdges.isEmpty && leaves.isEmpty

// ── SubstTree — top-level structure ─────────────────────────────

class SubstTree[L]:
  private val root: DiscrimNode[L] = DiscrimNode()

  // ── Insert ground ───────────────────────────────────────────

  def insertGround(terms: TermStore, termId: TermId, leaf: L): Unit =
    val node = insertWalk(root, terms, termId)
    node.leaves += leaf

  private def insertWalk(node: DiscrimNode[L], terms: TermStore, termId: TermId): DiscrimNode[L] =
    terms.get(termId) match
      case Term.Fn(functor, posArgs, namedArgs) =>
        val arity = posArgs.length + namedArgs.length
        val n1 = node.concrete.getOrElseUpdate(DiscrimKey.Functor(functor), DiscrimNode())
        val n2 = n1.concrete.getOrElseUpdate(DiscrimKey.Arity(arity), DiscrimNode())
        insertWalkArgs(n2, terms, posArgs, namedArgs)
      case Term.Ref(sym) =>
        val n1 = node.concrete.getOrElseUpdate(DiscrimKey.Functor(sym), DiscrimNode())
        n1.concrete.getOrElseUpdate(DiscrimKey.Arity(NULLARY_ARITY), DiscrimNode())
      case Term.Const(lit) =>
        node.concrete.getOrElseUpdate(DiscrimKey.Lit(lit), DiscrimNode())
      case Term.Ident(sym) =>
        node.concrete.getOrElseUpdate(DiscrimKey.IdentKey(sym), DiscrimNode())
      case Term.Bottom =>
        node.concrete.getOrElseUpdate(DiscrimKey.Bottom, DiscrimNode())
      case Term.Var(_) => node

  private def insertWalkArgs(
    node: DiscrimNode[L], terms: TermStore,
    pos: IArray[TermId], named: IArray[(TermSymbol, TermId)]
  ): DiscrimNode[L] =
    var cur = node
    var i = 0
    while i < pos.length do
      cur = cur.concrete.getOrElseUpdate(DiscrimKey.Positional, DiscrimNode())
      cur = insertWalk(cur, terms, pos(i))
      i += 1
    i = 0
    while i < named.length do
      val (sym, id) = named(i)
      cur = cur.concrete.getOrElseUpdate(DiscrimKey.NamedKey(sym), DiscrimNode())
      cur = insertWalk(cur, terms, id)
      i += 1
    cur

  // ── Insert pattern (with variables) ─────────────────────────

  def insertPattern(terms: TermStore, patternId: TermId, leaf: L): Unit =
    val node = insertPatternWalk(root, terms, patternId)
    node.leaves += leaf

  private def insertPatternWalk(node: DiscrimNode[L], terms: TermStore, termId: TermId): DiscrimNode[L] =
    terms.get(termId) match
      case Term.Var(v) =>
        // Key the var edge on the var's VarId (synthetic for a DeBruijn head
        // var, real for a Global) so a repeated var reuses one edge (WI-637).
        val vid = v.varId
        val pos = node.varEdges.indexWhere(_._1 == vid)
        if pos >= 0 then node.varEdges(pos)._2
        else
          val child = DiscrimNode[L]()
          node.varEdges += ((vid, child))
          child
      case Term.Fn(functor, posArgs, namedArgs) =>
        val arity = posArgs.length + namedArgs.length
        val n1 = node.concrete.getOrElseUpdate(DiscrimKey.Functor(functor), DiscrimNode())
        val n2 = n1.concrete.getOrElseUpdate(DiscrimKey.Arity(arity), DiscrimNode())
        insertPatternWalkArgs(n2, terms, posArgs, namedArgs)
      case Term.Ref(sym) =>
        val n1 = node.concrete.getOrElseUpdate(DiscrimKey.Functor(sym), DiscrimNode())
        n1.concrete.getOrElseUpdate(DiscrimKey.Arity(NULLARY_ARITY), DiscrimNode())
      case Term.Const(lit) =>
        node.concrete.getOrElseUpdate(DiscrimKey.Lit(lit), DiscrimNode())
      case Term.Ident(sym) =>
        node.concrete.getOrElseUpdate(DiscrimKey.IdentKey(sym), DiscrimNode())
      case Term.Bottom =>
        node.concrete.getOrElseUpdate(DiscrimKey.Bottom, DiscrimNode())

  private def insertPatternWalkArgs(
    node: DiscrimNode[L], terms: TermStore,
    pos: IArray[TermId], named: IArray[(TermSymbol, TermId)]
  ): DiscrimNode[L] =
    var cur = node
    var i = 0
    while i < pos.length do
      cur = cur.concrete.getOrElseUpdate(DiscrimKey.Positional, DiscrimNode())
      cur = insertPatternWalk(cur, terms, pos(i))
      i += 1
    i = 0
    while i < named.length do
      val (sym, id) = named(i)
      cur = cur.concrete.getOrElseUpdate(DiscrimKey.NamedKey(sym), DiscrimNode())
      cur = insertPatternWalk(cur, terms, id)
      i += 1
    cur

  // ── Remove ground ─────────────────────────────────────────────

  def removeGround(terms: TermStore, termId: TermId, leaf: L)(using PartialFunction[L, Boolean]): Unit =
    removeWalkTerm(root, terms, termId, leaf)

  private def removeWalkTerm(node: DiscrimNode[L], terms: TermStore, termId: TermId, leaf: L)(
    using eq: PartialFunction[L, Boolean]
  ): Boolean =
    // Simplified: just find and remove leaf from tree traversal
    terms.get(termId) match
      case Term.Fn(functor, posArgs, namedArgs) =>
        removeWalkApp(node, terms, functor, posArgs, namedArgs, leaf)
      case Term.Ref(sym) =>
        removeWalkApp(node, terms, sym, IArray.empty, IArray.empty, leaf)
      case Term.Const(lit) => removeAtLeafKey(node, DiscrimKey.Lit(lit), leaf)
      case Term.Ident(sym) => removeAtLeafKey(node, DiscrimKey.IdentKey(sym), leaf)
      case Term.Bottom => removeAtLeafKey(node, DiscrimKey.Bottom, leaf)
      case Term.Var(_) => node.isEmpty

  /** The application arm of [[removeWalkTerm]], shared by the two spellings of an
    * application (WI-20260902-CZJ2N). */
  private def removeWalkApp(
    node: DiscrimNode[L], terms: TermStore, functor: TermSymbol,
    posArgs: IArray[TermId], namedArgs: IArray[(TermSymbol, TermId)], leaf: L
  )(using eq: PartialFunction[L, Boolean]): Boolean =
    val arity = posArgs.length + namedArgs.length
    val fk = DiscrimKey.Functor(functor)
    node.concrete.get(fk) match
      case Some(fnChild) =>
        val ak = DiscrimKey.Arity(arity)
        fnChild.concrete.get(ak) match
          case Some(arChild) =>
            removeWalkArgs(arChild, terms, posArgs, namedArgs, 0, 0, leaf)
            if arChild.isEmpty then fnChild.concrete.remove(ak)
          case None =>
        if fnChild.isEmpty then node.concrete.remove(fk)
      case None =>
    node.isEmpty

  private def removeAtLeafKey(node: DiscrimNode[L], key: DiscrimKey, leaf: L)(
    using eq: PartialFunction[L, Boolean]
  ): Boolean =
    node.concrete.get(key) match
      case Some(child) =>
        val pos = child.leaves.indexWhere(_ == leaf)
        if pos >= 0 then child.leaves.remove(pos)
        if child.isEmpty then node.concrete.remove(key)
      case None =>
    node.isEmpty

  private def removeWalkArgs(
    node: DiscrimNode[L], terms: TermStore,
    pos: IArray[TermId], named: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, leaf: L
  )(using eq: PartialFunction[L, Boolean]): Unit =
    if posIdx >= pos.length && namedIdx >= named.length then
      val idx = node.leaves.indexWhere(_ == leaf)
      if idx >= 0 then node.leaves.remove(idx)
      return

    if posIdx < pos.length then
      node.concrete.get(DiscrimKey.Positional).foreach { mc =>
        removeWalkArgValue(mc, terms, pos(posIdx), pos, named, posIdx + 1, namedIdx, leaf)
        if mc.isEmpty then node.concrete.remove(DiscrimKey.Positional)
      }
    else
      val (sym, id) = named(namedIdx)
      val key = DiscrimKey.NamedKey(sym)
      node.concrete.get(key).foreach { mc =>
        removeWalkArgValue(mc, terms, id, pos, named, posIdx, namedIdx + 1, leaf)
        if mc.isEmpty then node.concrete.remove(key)
      }

  private def removeWalkArgValue(
    node: DiscrimNode[L], terms: TermStore, argTermId: TermId,
    pos: IArray[TermId], named: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, leaf: L
  )(using eq: PartialFunction[L, Boolean]): Unit =
    terms.get(argTermId) match
      case Term.Fn(functor, argPos, argNamed) =>
        removeWalkArgApp(node, terms, functor, argPos, argNamed, pos, named, posIdx, namedIdx, leaf)
      case Term.Ref(sym) =>
        removeWalkArgApp(node, terms, sym, IArray.empty, IArray.empty, pos, named, posIdx, namedIdx, leaf)
      case Term.Const(lit) =>
        removeValueThenContinue(node, DiscrimKey.Lit(lit), terms, pos, named, posIdx, namedIdx, leaf)
      case Term.Ident(sym) =>
        removeValueThenContinue(node, DiscrimKey.IdentKey(sym), terms, pos, named, posIdx, namedIdx, leaf)
      case Term.Bottom =>
        removeValueThenContinue(node, DiscrimKey.Bottom, terms, pos, named, posIdx, namedIdx, leaf)
      case Term.Var(_) => ()

  /** The application arm of [[removeWalkArgValue]], shared by the two spellings of an
    * application (WI-20260902-CZJ2N). */
  private def removeWalkArgApp(
    node: DiscrimNode[L], terms: TermStore, functor: TermSymbol,
    argPos: IArray[TermId], argNamed: IArray[(TermSymbol, TermId)],
    pos: IArray[TermId], named: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, leaf: L
  )(using eq: PartialFunction[L, Boolean]): Unit =
        val arity = argPos.length + argNamed.length
        val fk = DiscrimKey.Functor(functor)
        node.concrete.get(fk).foreach { fnChild =>
          val ak = DiscrimKey.Arity(arity)
          fnChild.concrete.get(ak).foreach { arChild =>
            // Combine inner args with remaining outer args
            val combinedPos = IArray.newBuilder[TermId]
            argPos.foreach(combinedPos += _)
            val combinedNamed = IArray.newBuilder[(TermSymbol, TermId)]
            argNamed.foreach(combinedNamed += _)
            // Inner args processed first, then continue with remaining outer
            removeWalkArgs(arChild, terms, combinedPos.result(), combinedNamed.result(), 0, 0, leaf)
            // Then continue outer
            removeWalkArgs(arChild, terms, pos, named, posIdx, namedIdx, leaf)
            if arChild.isEmpty then fnChild.concrete.remove(ak)
          }
          if fnChild.isEmpty then node.concrete.remove(fk)
        }

  private def removeValueThenContinue(
    node: DiscrimNode[L], key: DiscrimKey, terms: TermStore,
    pos: IArray[TermId], named: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, leaf: L
  )(using eq: PartialFunction[L, Boolean]): Unit =
    node.concrete.get(key).foreach { child =>
      removeWalkArgs(child, terms, pos, named, posIdx, namedIdx, leaf)
      if child.isEmpty then node.concrete.remove(key)
    }

  // ── Query ─────────────────────────────────────────────────────

  def queryRaw(terms: TermStore, queryTerm: TermId): ArrayBuffer[(L, SmallSubst)] =
    val results = ArrayBuffer.empty[(L, SmallSubst)]
    queryNode(root, terms, queryTerm, VarPath.Root, SmallSubst(), results)
    results

  /** `unifyRebind` (WI-637): the SLD head-selection caller (`query`) passes
    * `true` so a repeated pattern var UNIFIES its matched subterms; the
    * one-directional matching caller (`matchTerm`) passes `false` so it demands
    * structural identity. See [[Substitution.bindLeaf]]. */
  def queryResolved(terms: TermStore, queryTerm: TermId, resolveTerm: L => TermId, unifyRebind: Boolean): ArrayBuffer[(L, Substitution)] =
    val raw = queryRaw(terms, queryTerm)
    val results = ArrayBuffer.empty[(L, Substitution)]
    for (leaf, subst) <- raw do
      val factTerm = resolveTerm(leaf)
      results += ((leaf, subst.resolveLeaf(terms, factTerm, unifyRebind)))
    results

  private def queryNode(
    node: DiscrimNode[L], terms: TermStore, queryTerm: TermId,
    path: VarPath, subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)]
  ): Unit =
    terms.get(queryTerm) match
      case Term.Var(v) =>
        val s = subst.withBinding(v.varId, BindValue.Path(path))
        collectAllLeaves(node, s, results)

      case Term.Fn(functor, posArgs, namedArgs) =>
        queryNodeApp(node, terms, queryTerm, functor, posArgs, namedArgs, path, subst, results)
      case Term.Ref(sym) =>
        queryNodeApp(node, terms, queryTerm, sym, IArray.empty, IArray.empty, path, subst, results)

      case Term.Const(lit) =>
        queryLeafKey(node, DiscrimKey.Lit(lit), queryTerm, subst, results)
      case Term.Ident(sym) =>
        queryLeafKey(node, DiscrimKey.IdentKey(sym), queryTerm, subst, results)
      case Term.Bottom =>
        queryLeafKey(node, DiscrimKey.Bottom, queryTerm, subst, results)

  /** The application arm of [[queryNode]], shared by the two spellings of an
    * application (WI-20260902-CZJ2N). */
  private def queryNodeApp(
    node: DiscrimNode[L], terms: TermStore, queryTerm: TermId, functor: TermSymbol,
    posArgs: IArray[TermId], namedArgs: IArray[(TermSymbol, TermId)],
    path: VarPath, subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)]
  ): Unit =
    val arity = posArgs.length + namedArgs.length
    node.concrete.get(DiscrimKey.Functor(functor)).foreach { n1 =>
      n1.concrete.get(DiscrimKey.Arity(arity)).foreach { n2 =>
        // `path` is the prefix to this head's args (Root at top level);
        // each arg's own path extends it (WI-671).
        queryArgs(n2, terms, posArgs, namedArgs, 0, 0, path,
          subst.copy(), results, collectLeavesOnDone)
      }
    }
    for (treeVid, child) <- node.varEdges do
      val branch = subst.withBinding(treeVid, BindValue.TermVal(queryTerm))
      collectAllLeaves(child, branch, results)

  private def queryLeafKey(
    node: DiscrimNode[L], key: DiscrimKey, queryTerm: TermId,
    subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)]
  ): Unit =
    node.concrete.get(key).foreach { child =>
      for leaf <- child.leaves do results += ((leaf, subst.copy()))
    }
    for (treeVid, child) <- node.varEdges do
      val branch = subst.withBinding(treeVid, BindValue.TermVal(queryTerm))
      collectAllLeaves(child, branch, results)

  private type OnDone = (DiscrimNode[L], SmallSubst, ArrayBuffer[(L, SmallSubst)]) => Unit

  private val collectLeavesOnDone: OnDone = (node, subst, results) =>
    for leaf <- node.leaves do results += ((leaf, subst.copy()))

  private def queryArgs(
    node: DiscrimNode[L], terms: TermStore,
    pos: IArray[TermId], named: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, prefix: VarPath,
    subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)],
    onDone: OnDone
  ): Unit =
    if posIdx >= pos.length && namedIdx >= named.length then
      onDone(node, subst, results)
      return

    // Each arg's path extends the container `prefix` by one step, so a query
    // var at any depth records a full root-to-leaf path (WI-671).
    if posIdx < pos.length then
      val argPath = prefix.appended(ArgPos.Positional(posIdx))
      node.concrete.get(DiscrimKey.Positional).foreach { mc =>
        queryArgValue(mc, terms, pos(posIdx), argPath,
          pos, named, posIdx + 1, namedIdx, prefix, subst, results, onDone)
      }
    else
      val (sym, id) = named(namedIdx)
      val argPath = prefix.appended(ArgPos.Named(sym))
      node.concrete.get(DiscrimKey.NamedKey(sym)).foreach { mc =>
        queryArgValue(mc, terms, id, argPath,
          pos, named, posIdx, namedIdx + 1, prefix, subst, results, onDone)
      }

  private def queryArgValue(
    node: DiscrimNode[L], terms: TermStore, argTermId: TermId,
    argPath: VarPath,
    remPos: IArray[TermId], remNamed: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, prefix: VarPath,
    subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)],
    onDone: OnDone
  ): Unit =
    terms.get(argTermId) match
      case Term.Var(v) =>
        val s = subst.withBinding(v.varId, BindValue.Path(argPath))
        skipSubtreeThenContinue(node, terms, remPos, remNamed, posIdx, namedIdx, prefix, s, results, onDone)

      case Term.Fn(functor, argPos, argNamed) =>
        queryArgApp(node, terms, argTermId, functor, argPos, argNamed, argPath,
          remPos, remNamed, posIdx, namedIdx, prefix, subst, results, onDone)
      case Term.Ref(sym) =>
        queryArgApp(node, terms, argTermId, sym, IArray.empty, IArray.empty, argPath,
          remPos, remNamed, posIdx, namedIdx, prefix, subst, results, onDone)

      case Term.Const(lit) =>
        followKeyThenContinue(node, DiscrimKey.Lit(lit), argTermId, terms,
          remPos, remNamed, posIdx, namedIdx, prefix, subst, results, onDone)
      case Term.Ident(sym) =>
        followKeyThenContinue(node, DiscrimKey.IdentKey(sym), argTermId, terms,
          remPos, remNamed, posIdx, namedIdx, prefix, subst, results, onDone)
      case Term.Bottom =>
        followKeyThenContinue(node, DiscrimKey.Bottom, argTermId, terms,
          remPos, remNamed, posIdx, namedIdx, prefix, subst, results, onDone)

  /** The application arm of [[queryArgValue]], shared by the two spellings of an
    * application (WI-20260902-CZJ2N). */
  private def queryArgApp(
    node: DiscrimNode[L], terms: TermStore, argTermId: TermId, functor: TermSymbol,
    argPos: IArray[TermId], argNamed: IArray[(TermSymbol, TermId)], argPath: VarPath,
    remPos: IArray[TermId], remNamed: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, prefix: VarPath,
    subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)],
    onDone: OnDone
  ): Unit =
    val arity = argPos.length + argNamed.length
    node.concrete.get(DiscrimKey.Functor(functor)).foreach { n1 =>
      n1.concrete.get(DiscrimKey.Arity(arity)).foreach { n2 =>
        // Continue the OUTER args with the outer `prefix`; descend the
        // nested compound with `argPath` as its prefix so nested query
        // vars extend the path rather than restart at root (WI-671).
        val nestedCont: OnDone = (nd, s, r) =>
          queryArgs(nd, terms, remPos, remNamed, posIdx, namedIdx, prefix, s, r, onDone)
        queryArgs(n2, terms, argPos, argNamed, 0, 0,
          argPath, subst.copy(), results, nestedCont)
      }
    }
    for (treeVid, child) <- node.varEdges do
      val branch = subst.withBinding(treeVid, BindValue.TermVal(argTermId))
      queryArgs(child, terms, remPos, remNamed, posIdx, namedIdx, prefix, branch, results, onDone)

  private def followKeyThenContinue(
    node: DiscrimNode[L], key: DiscrimKey, queryTerm: TermId, terms: TermStore,
    remPos: IArray[TermId], remNamed: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, prefix: VarPath,
    subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)],
    onDone: OnDone
  ): Unit =
    node.concrete.get(key).foreach { child =>
      queryArgs(child, terms, remPos, remNamed, posIdx, namedIdx, prefix,
        subst.copy(), results, onDone)
    }
    for (treeVid, child) <- node.varEdges do
      val branch = subst.withBinding(treeVid, BindValue.TermVal(queryTerm))
      queryArgs(child, terms, remPos, remNamed, posIdx, namedIdx, prefix,
        branch, results, onDone)

  private def skipSubtreeThenContinue(
    node: DiscrimNode[L], terms: TermStore,
    remPos: IArray[TermId], remNamed: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, prefix: VarPath,
    subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)],
    onDone: OnDone
  ): Unit =
    queryArgs(node, terms, remPos, remNamed, posIdx, namedIdx, prefix,
      subst.copy(), results, onDone)
    for (_, child) <- node.concrete do
      skipSubtreeThenContinue(child, terms, remPos, remNamed, posIdx, namedIdx,
        prefix, subst.copy(), results, onDone)
    for (_, child) <- node.varEdges do
      skipSubtreeThenContinue(child, terms, remPos, remNamed, posIdx, namedIdx,
        prefix, subst.copy(), results, onDone)

  private def collectAllLeaves(
    node: DiscrimNode[L], subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)]
  ): Unit =
    for leaf <- node.leaves do results += ((leaf, subst.copy()))
    for (_, child) <- node.concrete do collectAllLeaves(child, subst.copy(), results)
    for (_, child) <- node.varEdges do collectAllLeaves(child, subst.copy(), results)
