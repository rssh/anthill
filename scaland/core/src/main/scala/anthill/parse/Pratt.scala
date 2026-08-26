package anthill.parse

import anthill.intern.TermSymbol
import anthill.term.{Term, TermId}
import anthill.span.Span

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

  /** WI-20260825-KD9SW (rustland's twin, same ticket) — THE TWELVE SPEC-OPERATION
    * ADDRESSES A MINTED OPERATOR NAMES.
    *
    * A minted operator carried the SHORT functor (`"add"`) and rustland's
    * `kb::load::PRELUDE_QUALIFIED` said where that lived — two encodings of one fact,
    * the second BELOW scope resolution, so a same-spelled name in scope CAPTURED the
    * operator (driven there: with `import Weird.{add}` in scope, `1 + 2` answered 99).
    *
    * SCALAND HAS NO SUCH TIER, so it never had that capture to fix. What it would have
    * without this change is a DIVERGENCE: the same source would parse to `add(a, b)`
    * here and to `..anthill.prelude.Additive.add(a, b)` there, so the two
    * implementations would disagree about what a program IS. The addresses are mirrored
    * for that reason, and the `..` marker carries the same guarantee it does in
    * rustland's `parse::desugar_target` — unspellable by any identifier, so a marked
    * head can collide with no user declaration.
    *
    * NOT ALL OPERATORS: `or`/`and`/`not` are position-directed and `pow` is owned by no
    * spec, so they stay short — exactly rustland's `SPEC_OP_FUNCTORS` population. */
  val addFunctor:  String = "..anthill.prelude.Additive.add"
  val subFunctor:  String = "..anthill.prelude.Additive.sub"
  val negFunctor:  String = "..anthill.prelude.Additive.neg"
  val mulFunctor:  String = "..anthill.prelude.Multiplicative.mul"
  val divFunctor:  String = "..anthill.prelude.Divisible.div"
  val modFunctor:  String = "..anthill.prelude.EuclideanDomain.mod"
  val eqFunctor:   String = "..anthill.prelude.PartialEq.eq"
  val neqFunctor:  String = "..anthill.prelude.PartialEq.neq"
  val ltFunctor:   String = "..anthill.prelude.PartialOrd.lt"
  val lteFunctor:  String = "..anthill.prelude.PartialOrd.lte"
  val gtFunctor:   String = "..anthill.prelude.PartialOrd.gt"
  val gteFunctor:  String = "..anthill.prelude.PartialOrd.gte"

  private val infixTable: Map[String, InfixEntry] = Map(
    "|"   -> InfixEntry(1, Assoc.Left,  "or"),
    "or"  -> InfixEntry(1, Assoc.Left,  "or"),
    "&"   -> InfixEntry(2, Assoc.Left,  "and"),
    "and" -> InfixEntry(2, Assoc.Left,  "and"),
    "="   -> InfixEntry(3, Assoc.None,  eqFunctor),
    "!="  -> InfixEntry(3, Assoc.None,  neqFunctor),
    // WI-522 / proposal 049: `<=>` = unify (anthill.kernel.unify). It lexes as one
    // operator token (maximal munch wins `<=>` over `<=`); maps to the `unify`
    // functor, mirroring rustland's pratt.rs. (scaland has no resolver-side
    // builtin_unify; the head/body functor just round-trips.)
    "<=>" -> InfixEntry(3, Assoc.None,  "unify"),
    // WI-615 / proposal 051: `===` = structural identity test (anthill.kernel.struct_eq).
    // Lexes as one operator token (maximal munch wins `===` over `==`/`=`); maps to the
    // `struct_eq` functor, mirroring rustland's pratt.rs. (scaland has no resolver-side
    // builtin; the head/body functor just round-trips.)
    "===" -> InfixEntry(3, Assoc.None,  "struct_eq"),
    "<"   -> InfixEntry(4, Assoc.None,  ltFunctor),
    "<="  -> InfixEntry(4, Assoc.None,  lteFunctor),
    ">"   -> InfixEntry(4, Assoc.None,  gtFunctor),
    ">="  -> InfixEntry(4, Assoc.None,  gteFunctor),
    "+"   -> InfixEntry(5, Assoc.Left,  addFunctor),
    "-"   -> InfixEntry(5, Assoc.Left,  subFunctor),
    "*"   -> InfixEntry(6, Assoc.Left,  mulFunctor),
    "/"   -> InfixEntry(6, Assoc.Left,  divFunctor),
    "%"   -> InfixEntry(6, Assoc.Left,  modFunctor),
    "mod" -> InfixEntry(6, Assoc.Left,  modFunctor),
    "div" -> InfixEntry(6, Assoc.Left,  divFunctor),
    "^"   -> InfixEntry(7, Assoc.Right, "pow"),
    "->"  -> InfixEntry(8, Assoc.Right, "arrow"),
  )

  private val prefixTable: Map[String, PrefixEntry] = Map(
    "!"   -> PrefixEntry(9, "not"),
    "not" -> PrefixEntry(9, "not"),
    "-"   -> PrefixEntry(9, negFunctor),
  )

  def lookupInfix(name: String): Option[InfixEntry] = infixTable.get(name)
  def lookupPrefix(name: String): Option[PrefixEntry] = prefixTable.get(name)

  /** The equality-family connectives — every functor the infix desugar mints for a
    * binary equality operator, whatever it MEANS. One SHAPE: the connective at the
    * head, its operands at positions 0 and 1. Derived from `infixTable` rather than
    * restated, so a new spelling cannot drift out of it. Mirrors rustland's
    * `pratt::EQUALITY_FAMILY_FUNCTORS`.
    *
    * This is the list to consult when the question is about the shape rather than the
    * meaning — WHERE a head's `[T]` introducer rides is such a question, and the answer
    * is "the LHS operand" for every member, including the ones that define nothing. */
  private val equalityFamilyFunctors: Set[String] =
    Set("=", "<=>", "===").flatMap(infixTable.get).map(_.functor)

  def isEqualityFamilyFunctor(name: String): Boolean = equalityFamilyFunctors.contains(name)

  /** The EQUATION connectives: the SUBSET of [[equalityFamilyFunctors]] whose minted
    * node, as a bodyless rule head, is a DEFINING EQUATION whose subject sits at
    * position 0. Mirrors rustland's `pratt::EQUATION_FUNCTORS`.
    *
    * IT HAS ONE MEMBER, and the spec's equality table decides which (§"Equality: test
    * vs. bind, structural vs. semantic"): `===` and `=` are the TEST column, `<=>` is
    * the BIND column alone, and only a connective that BINDS can head an equation — the
    * head unifies the redex with the LHS and derives the RHS. `===` left under WI-1090
    * and `=` under WI-888, by the same rule applied to the same table row. Both
    * therefore introduce no subject, and a bodyless head on either is refused
    * ([[Loader.nonDefiningConnectiveHead]]).
    *
    * They were not the same DEFECT, which is why the message branches even though this
    * list does not: a `===` head was silently useless, while an `=` head FIRED (WI-884
    * drove all four connective × attribute combinations). Refusing `=` finishes
    * proposal 049's migration (build step 6, WI-526) rather than repairing a silence. */
  private val equationFunctors: Set[String] =
    Set("<=>").flatMap(infixTable.get).map(_.functor)

  def isEquationFunctor(name: String): Boolean = equationFunctors.contains(name)

  /** The functors `===` and `=` desugar to — the non-defining members of the family,
    * needed by the loader's refusal so it can name the operator back to the author. */
  val structEqFunctor: String =
    infixTable("===").functor
  // `eqFunctor` is a LITERAL above, not derived here: WI-20260825-KD9SW made the table
  // reference it, and a `val` reading `infixTable` initialises after the table — so
  // deriving it would be a circular forward reference (null at class init, silently).


  /** Desugar a flat infix chain.
    *
    * @param operands alternating: [term, op, term, op, term, ...]
    *                 where ops are TermIds of the operator symbols
    * @param ops each operator symbol WITH ITS OWN SOURCE SPAN (WI-957) — the
    *            desugared node's functor (`add` for `+`) is written nowhere, so the
    *            OPERATOR is what a diagnostic about that functor points at. One
    *            paired sequence rather than two positional ones: the pairing is
    *            then structural, so it cannot go one off and need an assert to
    *            catch it.
    * @param resolve function to resolve a TermSymbol to its string name
    * @param alloc function to allocate a new term at a span
    * @param intern function to intern a string as a TermSymbol
    */
  def desugar(
    operands: IndexedSeq[TermId],
    ops: IndexedSeq[(TermSymbol, Span)],
    resolve: TermSymbol => String,
    alloc: (Term, Span) => TermId,
    intern: String => TermSymbol
  ): TermId =
    if operands.length == 1 then return operands(0)
    assert(operands.length == ops.length + 1,
      s"Expected ${ops.length + 1} operands, got ${operands.length}")
    desugarRec(operands, ops, 0, operands.length - 1, resolve, alloc, intern)

  private def desugarRec(
    operands: IndexedSeq[TermId],
    ops: IndexedSeq[(TermSymbol, Span)],
    lo: Int, hi: Int,
    resolve: TermSymbol => String,
    alloc: (Term, Span) => TermId,
    intern: String => TermSymbol
  ): TermId =
    if lo == hi then return operands(lo)

    // Find the operator with lowest precedence (split point)
    var splitIdx = lo
    var splitPriority = Int.MaxValue
    var splitAssoc = Assoc.Left
    var i = lo
    while i < hi do
      val opName = resolve(ops(i)._1)
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
    val (opSym, opSpan) = ops(splitIdx)
    val opName = resolve(opSym)
    val entry = infixTable.getOrElse(opName, InfixEntry(5, Assoc.Left, opName))
    val functorSym = intern(entry.functor)
    alloc(Term.Fn(functorSym, IArray(lhs, rhs), IArray.empty), opSpan)
