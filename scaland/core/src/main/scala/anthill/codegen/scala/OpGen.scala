package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.{Operation, Param, TypeExpr}

/** Operation → abstract `def`. v1 emits trait-member signatures only;
  * concrete companion objects are deferred to the KB-driven gen.
  *
  * Per `docs/scala-forward-mapping.md` §2.5: when the operation's
  * first argument has the type of the enclosing sort, the receiver
  * is the sort itself (no special syntax in Scala — just a regular
  * parameter); otherwise the op stays a plain method on the trait.
  */
object OpGen:

  def renderAbstract(op: Operation, enclosingTypeParams: IndexedSeq[String], sym: SymbolTable): String =
    val name = Names.scalaMethodName(sym.name(op.name.last))
    val params = op.params.map { p =>
      val pName = Names.scalaFieldName(sym.name(p.name))
      val pTy = TypeGen.render(sym, p.ty)
      s"$pName: $pTy"
    }.mkString("(", ", ", ")")
    val ret = renderReturn(op, sym)
    s"def $name$params: $ret"

  /** scala_std effect mapping (per §2.8): `Error E` wraps return in
    * `Either[E, R]`; `Modify X` returns the updated state by value (no
    * wrapping needed at the type level, just a return-shape convention).
    * Other effects (`Console`, `Requires`) don't reshape the return type.
    */
  private def renderReturn(op: Operation, sym: SymbolTable): String =
    val base = TypeGen.render(sym, op.returnType)
    op.effects.find(e => isErrorEffect(e, sym)) match
      case Some(errEff) =>
        val errTy = errorTypeOf(errEff, sym)
        s"Either[$errTy, $base]"
      case None => base

  private def isErrorEffect(e: anthill.parse.Effect, sym: SymbolTable): Boolean =
    e.typeExpr match
      case TypeExpr.Simple(n) => sym.name(n.last) == "Error"
      case TypeExpr.Parameterized(n, _) => sym.name(n.last) == "Error"
      case _ => false

  private def errorTypeOf(e: anthill.parse.Effect, sym: SymbolTable): String =
    e.typeExpr match
      case TypeExpr.Parameterized(_, bindings) if bindings.length == 1 =>
        TypeGen.render(sym, bindings.head.bound)
      case _ => "Throwable"

end OpGen
