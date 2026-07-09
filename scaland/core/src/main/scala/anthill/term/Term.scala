package anthill.term

import anthill.intern.TermSymbol

import scala.collection.immutable.ArraySeq

// ── Handles ─────────────────────────────────────────────────────

opaque type TermId = Int

object TermId:
  def fromRaw(raw: Int): TermId = raw

  extension (id: TermId)
    def index: Int = id
    def raw: Int = id

// ── VarId ───────────────────────────────────────────────────────

/** Unique identity of a logic variable.
  *
  * Within a single rule, all occurrences of `?x` share one VarId.
  * Across rules (or rule instantiations during deduction), `?x` gets
  * a fresh VarId each time — this is the standard "standardize apart" step.
  *
  * Equality and hashCode compare only the `id`, not the `name`.
  */
final case class VarId(id: Int, name: TermSymbol):
  override def hashCode(): Int = id
  override def equals(that: Any): Boolean = that match
    case v: VarId => v.id == this.id
    case _        => false

// ── Var — variable kind (mirrors rustland `kb::term::Var`) ──────

/** A logic variable's kind. Ported from rustland so the two implementations
  * share the concept (WI-637):
  *   - `Global`  — flex ("λProlog" sense): freely unifiable, used during
  *     resolution after a rule's binders are opened, and for query/goal vars.
  *   - `DeBruijn` — the canonical form of a STORED rule's head/body vars
  *     (positional, index 0 = innermost binder). Reflexive-only at match time
  *     (a rule-head var imposes equality on the subterms it matched only by
  *     being opened to a fresh `Global`, not by unifying its two occurrences'
  *     targets); opened to a fresh `Global` by `withFreshVars`.
  *   - `Rigid`   — a skolem witness (eigenvariable) — unifies only with the
  *     same-`VarId` `Rigid`. Scaland has no proof-discharge/typer to mint these
  *     yet, so it is ADT scaffolding for parity; the reflexive-only unifier
  *     already handles it. */
enum Var:
  case Global(id: VarId)
  case DeBruijn(index: Int)
  case Rigid(id: VarId)

  def isGlobal: Boolean = this match { case Var.Global(_) => true; case _ => false }
  def isDeBruijn: Boolean = this match { case Var.DeBruijn(_) => true; case _ => false }
  def isRigid: Boolean = this match { case Var.Rigid(_) => true; case _ => false }

  /** VarId for use as a substitution / discrim key. Global / Rigid return their
    * own id; DeBruijn(n) returns a SYNTHETIC id `Int.MaxValue - n` in a reserved
    * range that fresh vars (counting up from 0) never reach — so a stored
    * DeBruijn head var and a query Global var share one keyspace, exactly as
    * rustland's `Var::as_vid`. */
  def varId: VarId = this match
    case Var.Global(id) => id
    case Var.Rigid(id)  => id
    case Var.DeBruijn(n) => VarId(Int.MaxValue - n, TermSymbol.fromRaw(0))

object Var:
  /** Inverse of [[Var.varId]]'s DeBruijn encoding: if `vid` falls in the
    * reserved synthetic range (`Int.MaxValue - n` for `n` in `0 until arity`),
    * return the DeBruijn index `n`; otherwise `None` (a real Global/Rigid id).
    * The decode `withFreshVars` uses to route a matched head-var position into
    * `body_rename`. `arity == 0` yields `None`. */
  def syntheticDebruijnIndex(vid: VarId, arity: Int): Option[Int] =
    if arity > 0 && vid.id > Int.MaxValue - arity - 1 then Some(Int.MaxValue - vid.id)
    else None

// ── Literal ─────────────────────────────────────────────────────

/** Wrapper for Double that handles NaN equality correctly for hash-consing. */
final class OrderedDouble(val value: Double) extends Comparable[OrderedDouble]:
  override def hashCode(): Int =
    val bits = java.lang.Double.doubleToLongBits(value)
    (bits ^ (bits >>> 32)).toInt
  override def equals(that: Any): Boolean = that match
    case o: OrderedDouble => java.lang.Double.doubleToLongBits(value) == java.lang.Double.doubleToLongBits(o.value)
    case _                => false
  override def compareTo(that: OrderedDouble): Int = java.lang.Double.compare(value, that.value)
  override def toString: String = value.toString

object OrderedDouble:
  def apply(d: Double): OrderedDouble = new OrderedDouble(d)

enum Literal:
  case StringLit(value: String)
  case IntLit(value: Long)
  case BigIntLit(value: BigInt)
  case FloatLit(value: OrderedDouble)
  case BoolLit(value: Boolean)

// ── Term ADT ────────────────────────────────────────────────────

/** A term in the knowledge base.
  *
  * Functor names are a single interned Symbol carrying the fully-qualified
  * name. Infix syntax is desugared to Fn calls in the parser.
  *
  * Term.Fn uses IArray for args and overrides equals/hashCode for structural
  * equality (needed for hash-consing since IArray uses referential equality).
  */
sealed trait Term:
  /** Immediate child TermIds of this term. */
  def subterms: IArray[TermId] = this match
    case Term.Fn(_, posArgs, namedArgs) =>
      val buf = IArray.newBuilder[TermId]
      posArgs.foreach(buf += _)
      namedArgs.foreach((_, id) => buf += id)
      buf.result()
    case _ => IArray.empty

  /** Total arity (positional + named). Only meaningful for Fn terms. */
  def arity: Int = this match
    case Term.Fn(_, posArgs, namedArgs) => posArgs.length + namedArgs.length
    case _ => 0

object Term:
  case class Const(lit: Literal) extends Term
  // Param type fully-qualified: inside `object Term`, a bare `Var` would bind to
  // this nested case class, not the top-level `anthill.term.Var` enum.
  case class Var(v: anthill.term.Var) extends Term
  case object Bottom extends Term
  case class Ref(sym: TermSymbol) extends Term
  case class Ident(sym: TermSymbol) extends Term

  /** Function application with structural equality over IArray contents. */
  final class Fn(
    val functor: TermSymbol,
    val posArgs: IArray[TermId],
    val namedArgs: IArray[(TermSymbol, TermId)]
  ) extends Term:
    override def hashCode(): Int =
      var h = TermSymbol.raw(functor)
      var i = 0
      while i < posArgs.length do
        h = h * 31 + TermId.raw(posArgs(i))
        i += 1
      i = 0
      while i < namedArgs.length do
        val (s, t) = namedArgs(i)
        h = h * 31 + TermSymbol.raw(s)
        h = h * 31 + TermId.raw(t)
        i += 1
      h

    override def equals(that: Any): Boolean = that match
      case fn: Fn =>
        TermSymbol.raw(functor) == TermSymbol.raw(fn.functor) &&
        posArgs.length == fn.posArgs.length &&
        namedArgs.length == fn.namedArgs.length &&
        {
          var i = 0
          var eq = true
          while eq && i < posArgs.length do
            eq = TermId.raw(posArgs(i)) == TermId.raw(fn.posArgs(i))
            i += 1
          i = 0
          while eq && i < namedArgs.length do
            val (s1, t1) = namedArgs(i)
            val (s2, t2) = fn.namedArgs(i)
            eq = TermSymbol.raw(s1) == TermSymbol.raw(s2) && TermId.raw(t1) == TermId.raw(t2)
            i += 1
          eq
        }
      case _ => false

    override def toString: String =
      s"Fn($functor, ${posArgs.toSeq}, ${namedArgs.toSeq})"

  object Fn:
    def apply(functor: TermSymbol, posArgs: IArray[TermId], namedArgs: IArray[(TermSymbol, TermId)]): Fn =
      new Fn(functor, posArgs, namedArgs)

    def unapply(fn: Fn): Some[(TermSymbol, IArray[TermId], IArray[(TermSymbol, TermId)])] =
      Some((fn.functor, fn.posArgs, fn.namedArgs))
