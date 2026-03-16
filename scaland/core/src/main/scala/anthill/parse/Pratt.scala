package anthill.parse

import anthill.intern.TermSymbol
import anthill.term.{Term, TermId}

/** Operator precedence parser — converts flat infix chains to nested Fn calls.
  *
  * Input: alternating operands [t0, op0, t1, op1, t2, ...]
  * Output: single TermId with desugared expression.
  */
object Pratt:

  enum Assoc:
    case Left, Right, None

  case class InfixEntry(priority: Int, assoc: Assoc)
  case class PrefixEntry(priority: Int)

  private val infixTable: Map[String, InfixEntry] = Map(
    "|" -> InfixEntry(1, Assoc.Left),
    "or" -> InfixEntry(1, Assoc.Left),
    "&" -> InfixEntry(2, Assoc.Left),
    "and" -> InfixEntry(2, Assoc.Left),
    "=" -> InfixEntry(3, Assoc.None),
    "!=" -> InfixEntry(3, Assoc.None),
    "<" -> InfixEntry(4, Assoc.None),
    "<=" -> InfixEntry(4, Assoc.None),
    ">" -> InfixEntry(4, Assoc.None),
    ">=" -> InfixEntry(4, Assoc.None),
    "+" -> InfixEntry(5, Assoc.Left),
    "-" -> InfixEntry(5, Assoc.Left),
    "*" -> InfixEntry(6, Assoc.Left),
    "/" -> InfixEntry(6, Assoc.Left),
    "%" -> InfixEntry(6, Assoc.Left),
    "mod" -> InfixEntry(6, Assoc.Left),
    "div" -> InfixEntry(6, Assoc.Left),
    "^" -> InfixEntry(7, Assoc.Right),
    "->" -> InfixEntry(8, Assoc.Right),
  )

  private val prefixTable: Map[String, PrefixEntry] = Map(
    "!" -> PrefixEntry(9),
    "not" -> PrefixEntry(9),
    "-" -> PrefixEntry(9),
  )

  def lookupInfix(name: String): Option[InfixEntry] = infixTable.get(name)
  def lookupPrefix(name: String): Option[PrefixEntry] = prefixTable.get(name)

  /** Desugar a flat infix chain.
    *
    * @param operands alternating: [term, op, term, op, term, ...]
    *                 where ops are TermIds of the operator symbols
    * @param terms the SimpleTermStore or function to alloc new terms
    * @param intern function to resolve a TermSymbol to its string name
    * @param allocFn function to allocate a new term
    */
  def desugar(
    operands: IndexedSeq[TermId],
    opSymbols: IndexedSeq[TermSymbol],
    resolve: TermSymbol => String,
    alloc: Term => TermId
  ): TermId =
    if operands.length == 1 then return operands(0)
    assert(operands.length == opSymbols.length + 1,
      s"Expected ${opSymbols.length + 1} operands, got ${operands.length}")
    desugarRec(operands, opSymbols, 0, operands.length - 1, resolve, alloc)

  private def desugarRec(
    operands: IndexedSeq[TermId],
    ops: IndexedSeq[TermSymbol],
    lo: Int, hi: Int,
    resolve: TermSymbol => String,
    alloc: Term => TermId
  ): TermId =
    if lo == hi then return operands(lo)

    // Find the operator with lowest precedence (split point)
    var splitIdx = lo
    var splitPriority = Int.MaxValue
    var splitAssoc = Assoc.Left
    var i = lo
    while i < hi do
      val opName = resolve(ops(i))
      val entry = infixTable.getOrElse(opName, InfixEntry(5, Assoc.Left))
      val shouldSplit = entry.assoc match
        case Assoc.Left => entry.priority <= splitPriority
        case Assoc.Right => entry.priority < splitPriority
        case Assoc.None => entry.priority <= splitPriority
      if shouldSplit then
        splitIdx = i
        splitPriority = entry.priority
        splitAssoc = entry.assoc
      i += 1

    val lhs = desugarRec(operands, ops, lo, splitIdx, resolve, alloc)
    val rhs = desugarRec(operands, ops, splitIdx + 1, hi, resolve, alloc)
    alloc(Term.Fn(ops(splitIdx), IArray(lhs, rhs), IArray.empty))
