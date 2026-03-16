package anthill.subst

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

  /** Whether this substitution contains a contradiction. */
  def isContradiction: Boolean = contradiction_

  /** Add bindings with path compression.
    * For each (vid, term): scan existing entries where ?w -> Var(vid) and update to ?w -> term,
    * then insert vid -> term. Keeps the substitution always flat.
    */
  def bindCompressed(newBindings: Iterable[(VarId, TermId)], terms: TermStore): Unit =
    for (vid, term) <- newBindings do
      for (key, existingTerm) <- bindings do
        terms.get(existingTerm) match
          case Term.Var(ev) if ev == vid =>
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
