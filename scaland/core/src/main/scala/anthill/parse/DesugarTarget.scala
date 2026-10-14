package anthill.parse

/** Parser-created targets name their owners absolutely (ERF7T), so lexical names
  * cannot capture a lowering. ExprMarker provenance remains separate: Scala must
  * still reject expression forms for which it has no lowering.
  * DesugarTargetTest drives the mint sites and shadowing; backing these addresses
  * out fails those rows. Kernel control names never admit short spellings. */
object DesugarTarget:
  val FieldAccess: String = "..anthill.reflect.field_access"
  val HoApply: String = "..anthill.reflect.Expr.ho_apply"
  val DotApply: String = "..anthill.reflect.Expr.dot_apply"
  val SetLiteral: String = "..anthill.reflect.SetLiteral"
  val ListLiteral: String = "..anthill.reflect.ListLiteral"
  val TupleLiteral: String = "..anthill.reflect.TupleLiteral"
  val MatchExpr: String = "..anthill.reflect.Expr.match_expr"
  val IfExpr: String = "..anthill.reflect.Expr.if_expr"
  val LetExpr: String = "..anthill.reflect.Expr.let_expr"
  val LambdaExpr: String = "..anthill.reflect.Expr.lambda_expr"
  val Cut: String = "..anthill.kernel.cut"
  val FindDictionary: String = "..anthill.kernel.find_dictionary"

  val all: IndexedSeq[String] = IndexedSeq(FieldAccess, HoApply, DotApply,
    SetLiteral, ListLiteral, TupleLiteral, MatchExpr, IfExpr, LetExpr, LambdaExpr,
    Cut, FindDictionary)

  def isKernelControl(address: String): Boolean =
    address == Cut || address == FindDictionary

  def qualified(address: String): String =
    anthill.intern.absolutePathTarget(address).getOrElse(
      throw new IllegalArgumentException(s"not an absolute desugar target: $address"))

  def short(address: String): String = qualified(address).split('.').last

  def is(name: String, address: String): Boolean =
    require(!isKernelControl(address) && address != Pratt.unifyFunctor && address != Pratt.structEqFunctor,
      "kernel control targets do not admit short spellings")
    name == address || name == qualified(address) || name == short(address)
