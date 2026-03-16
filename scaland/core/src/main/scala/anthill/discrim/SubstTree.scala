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
  case RefKey(sym: TermSymbol)
  case Bottom

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
      case fn: Term.Fn =>
        val arity = fn.arity
        val n1 = node.concrete.getOrElseUpdate(DiscrimKey.Functor(fn.functor), DiscrimNode())
        val n2 = n1.concrete.getOrElseUpdate(DiscrimKey.Arity(arity), DiscrimNode())
        insertWalkArgs(n2, terms, fn.posArgs, fn.namedArgs)
      case Term.Const(lit) =>
        node.concrete.getOrElseUpdate(DiscrimKey.Lit(lit), DiscrimNode())
      case Term.Ident(sym) =>
        node.concrete.getOrElseUpdate(DiscrimKey.IdentKey(sym), DiscrimNode())
      case Term.Ref(sym) =>
        node.concrete.getOrElseUpdate(DiscrimKey.RefKey(sym), DiscrimNode())
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
      case Term.Var(vid) =>
        val pos = node.varEdges.indexWhere(_._1 == vid)
        if pos >= 0 then node.varEdges(pos)._2
        else
          val child = DiscrimNode[L]()
          node.varEdges += ((vid, child))
          child
      case fn: Term.Fn =>
        val arity = fn.arity
        val n1 = node.concrete.getOrElseUpdate(DiscrimKey.Functor(fn.functor), DiscrimNode())
        val n2 = n1.concrete.getOrElseUpdate(DiscrimKey.Arity(arity), DiscrimNode())
        insertPatternWalkArgs(n2, terms, fn.posArgs, fn.namedArgs)
      case Term.Const(lit) =>
        node.concrete.getOrElseUpdate(DiscrimKey.Lit(lit), DiscrimNode())
      case Term.Ident(sym) =>
        node.concrete.getOrElseUpdate(DiscrimKey.IdentKey(sym), DiscrimNode())
      case Term.Ref(sym) =>
        node.concrete.getOrElseUpdate(DiscrimKey.RefKey(sym), DiscrimNode())
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
      case fn: Term.Fn =>
        val arity = fn.arity
        val fk = DiscrimKey.Functor(fn.functor)
        node.concrete.get(fk) match
          case Some(fnChild) =>
            val ak = DiscrimKey.Arity(arity)
            fnChild.concrete.get(ak) match
              case Some(arChild) =>
                removeWalkArgs(arChild, terms, fn.posArgs, fn.namedArgs, 0, 0, leaf)
                if arChild.isEmpty then fnChild.concrete.remove(ak)
              case None =>
            if fnChild.isEmpty then node.concrete.remove(fk)
          case None =>
        node.isEmpty
      case Term.Const(lit) => removeAtLeafKey(node, DiscrimKey.Lit(lit), leaf)
      case Term.Ident(sym) => removeAtLeafKey(node, DiscrimKey.IdentKey(sym), leaf)
      case Term.Ref(sym) => removeAtLeafKey(node, DiscrimKey.RefKey(sym), leaf)
      case Term.Bottom => removeAtLeafKey(node, DiscrimKey.Bottom, leaf)
      case Term.Var(_) => node.isEmpty

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
      case fn: Term.Fn =>
        val arity = fn.arity
        val fk = DiscrimKey.Functor(fn.functor)
        node.concrete.get(fk).foreach { fnChild =>
          val ak = DiscrimKey.Arity(arity)
          fnChild.concrete.get(ak).foreach { arChild =>
            // Combine inner args with remaining outer args
            val combinedPos = IArray.newBuilder[TermId]
            fn.posArgs.foreach(combinedPos += _)
            val combinedNamed = IArray.newBuilder[(TermSymbol, TermId)]
            fn.namedArgs.foreach(combinedNamed += _)
            // Inner args processed first, then continue with remaining outer
            removeWalkArgs(arChild, terms, combinedPos.result(), combinedNamed.result(), 0, 0, leaf)
            // Then continue outer
            removeWalkArgs(arChild, terms, pos, named, posIdx, namedIdx, leaf)
            if arChild.isEmpty then fnChild.concrete.remove(ak)
          }
          if fnChild.isEmpty then node.concrete.remove(fk)
        }
      case Term.Const(lit) =>
        removeValueThenContinue(node, DiscrimKey.Lit(lit), terms, pos, named, posIdx, namedIdx, leaf)
      case Term.Ident(sym) =>
        removeValueThenContinue(node, DiscrimKey.IdentKey(sym), terms, pos, named, posIdx, namedIdx, leaf)
      case Term.Ref(sym) =>
        removeValueThenContinue(node, DiscrimKey.RefKey(sym), terms, pos, named, posIdx, namedIdx, leaf)
      case Term.Bottom =>
        removeValueThenContinue(node, DiscrimKey.Bottom, terms, pos, named, posIdx, namedIdx, leaf)
      case Term.Var(_) => ()

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

  def queryResolved(terms: TermStore, queryTerm: TermId, resolveTerm: L => TermId): ArrayBuffer[(L, Substitution)] =
    val raw = queryRaw(terms, queryTerm)
    val results = ArrayBuffer.empty[(L, Substitution)]
    for (leaf, subst) <- raw do
      val factTerm = resolveTerm(leaf)
      results += ((leaf, subst.resolveLeaf(terms, factTerm)))
    results

  private def queryNode(
    node: DiscrimNode[L], terms: TermStore, queryTerm: TermId,
    path: VarPath, subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)]
  ): Unit =
    terms.get(queryTerm) match
      case Term.Var(vid) =>
        val s = subst.withBinding(vid, BindValue.Path(path))
        collectAllLeaves(node, s, results)

      case fn: Term.Fn =>
        val arity = fn.arity
        node.concrete.get(DiscrimKey.Functor(fn.functor)).foreach { n1 =>
          n1.concrete.get(DiscrimKey.Arity(arity)).foreach { n2 =>
            queryArgs(n2, terms, fn.posArgs, fn.namedArgs, 0, 0, bindPaths = true,
              subst.copy(), results, collectLeavesOnDone)
          }
        }
        for (treeVid, child) <- node.varEdges do
          val branch = subst.withBinding(treeVid, BindValue.TermVal(queryTerm))
          collectAllLeaves(child, branch, results)

      case Term.Const(lit) =>
        queryLeafKey(node, DiscrimKey.Lit(lit), queryTerm, subst, results)
      case Term.Ident(sym) =>
        queryLeafKey(node, DiscrimKey.IdentKey(sym), queryTerm, subst, results)
      case Term.Ref(sym) =>
        queryLeafKey(node, DiscrimKey.RefKey(sym), queryTerm, subst, results)
      case Term.Bottom =>
        queryLeafKey(node, DiscrimKey.Bottom, queryTerm, subst, results)

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
    posIdx: Int, namedIdx: Int, bindPaths: Boolean,
    subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)],
    onDone: OnDone
  ): Unit =
    if posIdx >= pos.length && namedIdx >= named.length then
      onDone(node, subst, results)
      return

    if posIdx < pos.length then
      val path = if bindPaths then Some(VarPath.Arg(ArgPos.Positional(posIdx))) else None
      node.concrete.get(DiscrimKey.Positional).foreach { mc =>
        queryArgValue(mc, terms, pos(posIdx), path,
          pos, named, posIdx + 1, namedIdx, bindPaths, subst, results, onDone)
      }
    else
      val (sym, id) = named(namedIdx)
      val path = if bindPaths then Some(VarPath.Arg(ArgPos.Named(sym))) else None
      node.concrete.get(DiscrimKey.NamedKey(sym)).foreach { mc =>
        queryArgValue(mc, terms, id, path,
          pos, named, posIdx, namedIdx + 1, bindPaths, subst, results, onDone)
      }

  private def queryArgValue(
    node: DiscrimNode[L], terms: TermStore, argTermId: TermId,
    argPath: Option[VarPath],
    remPos: IArray[TermId], remNamed: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, bindPaths: Boolean,
    subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)],
    onDone: OnDone
  ): Unit =
    terms.get(argTermId) match
      case Term.Var(vid) =>
        val s = argPath match
          case Some(path) => subst.withBinding(vid, BindValue.Path(path))
          case None => subst
        skipSubtreeThenContinue(node, terms, remPos, remNamed, posIdx, namedIdx, bindPaths, s, results, onDone)

      case fn: Term.Fn =>
        val arity = fn.arity
        node.concrete.get(DiscrimKey.Functor(fn.functor)).foreach { n1 =>
          n1.concrete.get(DiscrimKey.Arity(arity)).foreach { n2 =>
            val nestedCont: OnDone = (nd, s, r) =>
              queryArgs(nd, terms, remPos, remNamed, posIdx, namedIdx, bindPaths, s, r, onDone)
            queryArgs(n2, terms, fn.posArgs, fn.namedArgs, 0, 0,
              bindPaths = false, subst.copy(), results, nestedCont)
          }
        }
        for (treeVid, child) <- node.varEdges do
          val branch = subst.withBinding(treeVid, BindValue.TermVal(argTermId))
          queryArgs(child, terms, remPos, remNamed, posIdx, namedIdx, bindPaths, branch, results, onDone)

      case Term.Const(lit) =>
        followKeyThenContinue(node, DiscrimKey.Lit(lit), argTermId, terms,
          remPos, remNamed, posIdx, namedIdx, bindPaths, subst, results, onDone)
      case Term.Ident(sym) =>
        followKeyThenContinue(node, DiscrimKey.IdentKey(sym), argTermId, terms,
          remPos, remNamed, posIdx, namedIdx, bindPaths, subst, results, onDone)
      case Term.Ref(sym) =>
        followKeyThenContinue(node, DiscrimKey.RefKey(sym), argTermId, terms,
          remPos, remNamed, posIdx, namedIdx, bindPaths, subst, results, onDone)
      case Term.Bottom =>
        followKeyThenContinue(node, DiscrimKey.Bottom, argTermId, terms,
          remPos, remNamed, posIdx, namedIdx, bindPaths, subst, results, onDone)

  private def followKeyThenContinue(
    node: DiscrimNode[L], key: DiscrimKey, queryTerm: TermId, terms: TermStore,
    remPos: IArray[TermId], remNamed: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, bindPaths: Boolean,
    subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)],
    onDone: OnDone
  ): Unit =
    node.concrete.get(key).foreach { child =>
      queryArgs(child, terms, remPos, remNamed, posIdx, namedIdx, bindPaths,
        subst.copy(), results, onDone)
    }
    for (treeVid, child) <- node.varEdges do
      val branch = subst.withBinding(treeVid, BindValue.TermVal(queryTerm))
      queryArgs(child, terms, remPos, remNamed, posIdx, namedIdx, bindPaths,
        branch, results, onDone)

  private def skipSubtreeThenContinue(
    node: DiscrimNode[L], terms: TermStore,
    remPos: IArray[TermId], remNamed: IArray[(TermSymbol, TermId)],
    posIdx: Int, namedIdx: Int, bindPaths: Boolean,
    subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)],
    onDone: OnDone
  ): Unit =
    queryArgs(node, terms, remPos, remNamed, posIdx, namedIdx, bindPaths,
      subst.copy(), results, onDone)
    for (_, child) <- node.concrete do
      skipSubtreeThenContinue(child, terms, remPos, remNamed, posIdx, namedIdx,
        bindPaths, subst.copy(), results, onDone)
    for (_, child) <- node.varEdges do
      skipSubtreeThenContinue(child, terms, remPos, remNamed, posIdx, namedIdx,
        bindPaths, subst.copy(), results, onDone)

  private def collectAllLeaves(
    node: DiscrimNode[L], subst: SmallSubst, results: ArrayBuffer[(L, SmallSubst)]
  ): Unit =
    for leaf <- node.leaves do results += ((leaf, subst.copy()))
    for (_, child) <- node.concrete do collectAllLeaves(child, subst.copy(), results)
    for (_, child) <- node.varEdges do collectAllLeaves(child, subst.copy(), results)
