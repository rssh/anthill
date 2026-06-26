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

  case class InfixEntry(priority: Int, assoc: Assoc, functor: String)
  case class PrefixEntry(priority: Int, functor: String)

  private val infixTable: Map[String, InfixEntry] = Map(
    "|"   -> InfixEntry(1, Assoc.Left,  "or"),
    "or"  -> InfixEntry(1, Assoc.Left,  "or"),
    "&"   -> InfixEntry(2, Assoc.Left,  "and"),
    "and" -> InfixEntry(2, Assoc.Left,  "and"),
    "="   -> InfixEntry(3, Assoc.None,  "eq"),
    "!="  -> InfixEntry(3, Assoc.None,  "neq"),
    // WI-522 / proposal 049: `<=>` = unify (anthill.kernel.unify). It lexes as one
    // operator token (maximal munch wins `<=>` over `<=`); maps to the `unify`
    // functor, mirroring rustland's pratt.rs. (scaland has no resolver-side
    // builtin_unify; the head/body functor just round-trips.)
    "<=>" -> InfixEntry(3, Assoc.None,  "unify"),
    "<"   -> InfixEntry(4, Assoc.None,  "lt"),
    "<="  -> InfixEntry(4, Assoc.None,  "lte"),
    ">"   -> InfixEntry(4, Assoc.None,  "gt"),
    ">="  -> InfixEntry(4, Assoc.None,  "gte"),
    "+"   -> InfixEntry(5, Assoc.Left,  "add"),
    "-"   -> InfixEntry(5, Assoc.Left,  "sub"),
    "*"   -> InfixEntry(6, Assoc.Left,  "mul"),
    "/"   -> InfixEntry(6, Assoc.Left,  "div"),
    "%"   -> InfixEntry(6, Assoc.Left,  "mod"),
    "mod" -> InfixEntry(6, Assoc.Left,  "mod"),
    "div" -> InfixEntry(6, Assoc.Left,  "div"),
    "^"   -> InfixEntry(7, Assoc.Right, "pow"),
    "->"  -> InfixEntry(8, Assoc.Right, "arrow"),
  )

  private val prefixTable: Map[String, PrefixEntry] = Map(
    "!"   -> PrefixEntry(9, "not"),
    "not" -> PrefixEntry(9, "not"),
    "-"   -> PrefixEntry(9, "neg"),
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
    alloc: Term => TermId,
    intern: String => TermSymbol
  ): TermId =
    if operands.length == 1 then return operands(0)
    assert(operands.length == opSymbols.length + 1,
      s"Expected ${opSymbols.length + 1} operands, got ${operands.length}")
    desugarRec(operands, opSymbols, 0, operands.length - 1, resolve, alloc, intern)

  private def desugarRec(
    operands: IndexedSeq[TermId],
    ops: IndexedSeq[TermSymbol],
    lo: Int, hi: Int,
    resolve: TermSymbol => String,
    alloc: Term => TermId,
    intern: String => TermSymbol
  ): TermId =
    if lo == hi then return operands(lo)

    // Find the operator with lowest precedence (split point)
    var splitIdx = lo
    var splitPriority = Int.MaxValue
    var splitAssoc = Assoc.Left
    var i = lo
    while i < hi do
      val opName = resolve(ops(i))
      val entry = infixTable.getOrElse(opName, InfixEntry(5, Assoc.Left, opName))
      val shouldSplit = entry.assoc match
        case Assoc.Left => entry.priority <= splitPriority
        case Assoc.Right => entry.priority < splitPriority
        case Assoc.None => entry.priority <= splitPriority
      if shouldSplit then
        splitIdx = i
        splitPriority = entry.priority
        splitAssoc = entry.assoc
      i += 1

    val lhs = desugarRec(operands, ops, lo, splitIdx, resolve, alloc, intern)
    val rhs = desugarRec(operands, ops, splitIdx + 1, hi, resolve, alloc, intern)
    val opName = resolve(ops(splitIdx))
    val entry = infixTable.getOrElse(opName, InfixEntry(5, Assoc.Left, opName))
    val functorSym = intern(entry.functor)
    alloc(Term.Fn(functorSym, IArray(lhs, rhs), IArray.empty))
