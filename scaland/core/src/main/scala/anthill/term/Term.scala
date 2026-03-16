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
  case class Var(id: VarId) extends Term
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
