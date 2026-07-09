package anthill.subst

import anthill.intern.TermSymbol
import anthill.term.{Term, TermId, TermStore, VarId}
import scala.collection.mutable.HashMap

/** Substitution — maps logic variables to term ids.
  *
  * Supports parent chaining for nested proof contexts and
  * path compression to keep substitutions flat.
  */
class Substitution(
  val bindings: HashMap[VarId, TermId] = HashMap.empty,
  val parent: Option[Substitution] = None,
  private var contradiction_ : Boolean = false
):

  /** Look up a variable binding, walking parent chain. */
  def resolve(v: VarId): Option[TermId] =
    bindings.get(v).orElse(parent.flatMap(_.resolve(v)))

  /** Bind a variable to a term id.
    * If already bound to a different term, marks the substitution as contradictory.
    */
  def bind(v: VarId, term: TermId): Unit =
    bindings.get(v) match
      case Some(existing) =>
        if TermId.raw(existing) != TermId.raw(term) then
          contradiction_ = true
      case None =>
        bindings(v) = term

  /** WI-637 — the discrimination-tree leaf bind for the RESOLUTION path
    * (`resolveLeaf` with `unifyRebind = true`): like [[bind]], but a re-bind of
    * an already-bound var UNIFIES the existing and incoming terms (structural,
    * occurs-checked) instead of demanding `TermId`-raw identity. SLD rule-head
    * selection IS unification: a repeated head var — or a repeated query var
    * (WI-512 `edge(from: ?n, to: ?n)`) — makes its two matched subterms
    * equal-up-to-unification, so `unbox0(box(v: ?v), ?v)` queried
    * `unbox0(box(v: some(?x)), some(42))` must bind `?x = 42`, not drop the
    * candidate as a contradiction (silent 0 solutions). Mirrors rustland
    * WI-633 (`249f9fd0`) `Substitution::bind_value_unifying`.
    *
    * NB one-directional MATCHING (`KnowledgeBase.matchTerm`) must NOT use this:
    * a nonlinear pattern var there matches only structurally-IDENTICAL
    * subterms; unifying would force the target's own vars equal and silently
    * drop the constraint. That path keeps [[bind]] via
    * [[bindLeaf]]`(unifyRebind = false)`.
    */
  def bindUnifying(terms: TermStore, v: VarId, term: TermId): Unit =
    bindings.get(v) match
      case Some(existing) =>
        if TermId.raw(existing) != TermId.raw(term) && !unifyMatch(terms, existing, term) then
          contradiction_ = true
      case None =>
        bindings(v) = term

  /** Dispatch a discrimination-tree leaf bind by mode (WI-637). `unifyRebind =
    * true` is the RESOLUTION path ([[bindUnifying]]; repeated vars unify);
    * `false` is the one-directional MATCHING path ([[bind]]; repeated pattern
    * vars demand structural identity). The single seam so `resolveLeaf` picks
    * the semantics its caller (`query` for SLD vs `matchTerm`) needs. */
  def bindLeaf(terms: TermStore, v: VarId, term: TermId, unifyRebind: Boolean): Unit =
    if unifyRebind then bindUnifying(terms, v, term)
    else bind(v, term)

  /** WI-637 — the structural unifier behind [[bindUnifying]] (rustland
    * `KnowledgeBase::unify_match_values`). NO reduction and NO delay: the
    * discrim match is structural (an unreduced op-call is concrete structure
    * here, exactly as the tree indexed it). A flex (`Var.Global`) var binds into
    * THIS substitution (occurs-checked, chased through it); a `Var.DeBruijn`
    * (stored rule-head) or `Var.Rigid` var is REFLEXIVE-ONLY — it binds nothing,
    * so it unifies only with the identical var (caught by the fast path) and a
    * distinct rigid var, or a rigid var vs any concrete, fails. This is what
    * keeps a nonlinear QUERY var over two DISTINCT head vars
    * (`pair(from: ?n, to: ?n)` against head `pair(from: ?x, to: ?y)`) a
    * contradiction — `?x`/`?y` are DeBruijn, so unifying them fails rather than
    * silently linking `?x := ?y` (which `withFreshVars` would then drop, an
    * unsound extra solution). Returns `false` on mismatch or occurs violation,
    * in which case `this` may hold partial bindings — [[bindUnifying]] flags the
    * whole substitution contradictory and every consumer drops it. */
  private def unifyMatch(terms: TermStore, aId: TermId, bId: TermId): Boolean =
    val a = chase(terms, aId)
    val b = chase(terms, bId)
    // Hash-consed fast path: structural equality IS `TermId` identity, so a
    // ground-vs-ground re-bind (or `?v` vs `?v`) degrades to the old check.
    if TermId.raw(a) == TermId.raw(b) then true
    else
      (terms.get(a), terms.get(b)) match
        // Only a flex Global var binds; a DeBruijn/Rigid var is reflexive-only.
        case (Term.Var(va), _) if va.isGlobal =>
          if occursIn(terms, va.varId, b) then false else { bindings(va.varId) = b; true }
        case (_, Term.Var(vb)) if vb.isGlobal =>
          if occursIn(terms, vb.varId, a) then false else { bindings(vb.varId) = a; true }
        // A non-Global var on either side (identity already ruled out): a rigid
        // var vs a distinct var or any concrete has no unifier here.
        case (Term.Var(_), _) | (_, Term.Var(_)) => false
        case (Term.Const(la), Term.Const(lb)) => la == lb
        case (Term.Ref(sa), Term.Ref(sb))     => TermSymbol.raw(sa) == TermSymbol.raw(sb)
        case (Term.Ident(sa), Term.Ident(sb)) => TermSymbol.raw(sa) == TermSymbol.raw(sb)
        case (Term.Bottom, Term.Bottom)       => true
        case (fa: Term.Fn, fb: Term.Fn) =>
          if TermSymbol.raw(fa.functor) != TermSymbol.raw(fb.functor) ||
             fa.posArgs.length != fb.posArgs.length ||
             fa.namedArgs.length != fb.namedArgs.length then false
          else
            var ok = true
            var i = 0
            while ok && i < fa.posArgs.length do
              ok = unifyMatch(terms, fa.posArgs(i), fb.posArgs(i))
              i += 1
            // Named args compared pairwise by position, mirroring `Term.Fn`
            // structural equality (scaland builds them in source order, not
            // sorted); a key/order mismatch fails rather than mis-unifies.
            i = 0
            while ok && i < fa.namedArgs.length do
              val (sa, ta) = fa.namedArgs(i)
              val (sb, tb) = fb.namedArgs(i)
              ok = TermSymbol.raw(sa) == TermSymbol.raw(sb) && unifyMatch(terms, ta, tb)
              i += 1
            ok
        // Head-kind mismatch (incl. Const-vs-Ref etc.) has no shared structure.
        case _ => false

  /** Resolve a term's head var through this substitution (no structural
    * descent) — the local peer of [[KnowledgeBase.walk]] used by [[unifyMatch]]
    * / [[occursIn]] so they read bindings produced earlier in the same fold. */
  private def chase(terms: TermStore, id: TermId): TermId =
    var cur = id
    var continue = true
    while continue do
      terms.get(cur) match
        case Term.Var(v) =>
          resolve(v.varId) match
            case Some(bound) if TermId.raw(bound) != TermId.raw(cur) => cur = bound
            case _ => continue = false
        case _ => continue = false
    cur

  /** Occurs check for [[unifyMatch]]: does `v` appear (chased) anywhere in the
    * term rooted at `id`? Guards `?q = box(v: ?q)`-style cyclic binds. */
  private def occursIn(terms: TermStore, v: VarId, id: TermId): Boolean =
    terms.get(chase(terms, id)) match
      case Term.Var(w) => w.varId.id == v.id
      case fn: Term.Fn =>
        fn.posArgs.exists(occursIn(terms, v, _)) ||
          fn.namedArgs.exists((_, t) => occursIn(terms, v, t))
      case _ => false

  /** Whether this substitution contains a contradiction. */
  def isContradiction: Boolean = contradiction_

  /** Force the contradiction flag (WI-637 / WI-624): `withFreshVars` calls this
    * when a query-var link is cyclic, so the resolver drops the candidate
    * exactly as it drops a `bind`-conflict contradiction. */
  def markContradiction(): Unit = contradiction_ = true

  /** True when applying this substitution to any term is a no-op —
    * no bindings here and no parent chain that could supply any. Used
    * by the WI-030 lazy-walk fast path. */
  def isEmpty: Boolean = bindings.isEmpty && parent.forall(_.isEmpty)

  /** Add bindings with path compression.
    * For each (vid, term): scan existing entries where ?w -> Var(vid) and update to ?w -> term,
    * then insert vid -> term. Keeps the substitution always flat.
    */
  def bindCompressed(newBindings: Iterable[(VarId, TermId)], terms: TermStore): Unit =
    for (vid, term) <- newBindings do
      for (key, existingTerm) <- bindings do
        terms.get(existingTerm) match
          case Term.Var(ev) if ev.varId == vid =>
            bindings(key) = term
          case _ =>
      bindings(vid) = term

  /** Create a shallow copy of this substitution. */
  def snapshot(): Substitution =
    new Substitution(bindings.clone(), parent, contradiction_)

object Substitution:
  def apply(): Substitution = new Substitution()

  def withParent(parent: Substitution): Substitution =
    new Substitution(parent = Some(parent))
