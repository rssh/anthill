package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.{Operation, TypeExpr}

/** Operation → abstract `def`. v1 emits trait-member signatures only;
  * concrete companion objects are deferred to the KB-driven gen.
  *
  * Per `docs/scala-forward-mapping.md` §2.5: when the operation's
  * first argument has the type of the enclosing sort, the receiver
  * is the sort itself (no special syntax in Scala — just a regular
  * parameter); otherwise the op stays a plain method on the trait.
  */
object OpGen:

  def renderAbstract(op: Operation, enclosingScope: TypeScope, sym: SymbolTable): String =
    val name = Names.scalaMethodName(sym.name(op.name.last))
    // WI-1055 A1: an operation's OWN type parameters. `Operation.typeParams` has
    // been in the parse IR since WI-269 and nothing here read it, so
    // `operation pure[A](a: A) -> M[A]` emitted `def pure(a: A): M[A]` with `A`
    // unbound — every operation carrying its own parameters emitted a signature
    // that does not compile.
    val typeParams = op.typeParams.map { tp =>
      // WI-840: a NAMED requirement slot (`requires plus: Monoid[T]`) rides in
      // `typeParams` but names a WITNESS, not a type — the same decision the sort
      // level makes, so the same refusal. No stdlib operation declares one today;
      // refusing keeps `def f[plus]` from becoming silently wrong output the day
      // one does.
      if tp.requirementSlot.isDefined then
        Bootstrap.refuseNamedRequirementSlot(
          s"operation `${sym.name(op.name.last)}`", sym.name(tp.name), tp.span)
      sym.name(tp.name) -> Names.scalaTypeName(sym.name(tp.name))
    }
    val scope = enclosingScope
      .at(s"operation `${sym.name(op.name.last)}`", op.span)
      .withTypeParams(typeParams)
    val tpStr =
      if typeParams.isEmpty then "" else typeParams.map(_._2).mkString("[", ", ", "]")
    val params = op.params.map { p =>
      val pName = Names.scalaFieldName(sym.name(p.name))
      val pTy = TypeGen.render(sym, p.ty, scope)
      s"$pName: $pTy"
    }.mkString("(", ", ", ")")
    val ret = renderReturn(op, scope, sym)
    s"def $name$tpStr$params: $ret"

  /** scala_std effect mapping (per §2.8): `Error E` wraps return in
    * `Either[E, R]`; `Modify X` returns the updated state by value (no
    * wrapping needed at the type level, just a return-shape convention).
    * Other effects (`Console`, `Requires`) don't reshape the return type.
    */
  private def renderReturn(op: Operation, scope: TypeScope, sym: SymbolTable): String =
    val base = TypeGen.render(sym, op.returnType, scope)
    op.effects.find(e => isErrorEffect(e, sym)) match
      case Some(errEff) =>
        val errTy = errorTypeOf(errEff, scope, sym)
        s"Either[$errTy, $base]"
      case None => base

  private def isErrorEffect(e: anthill.parse.Effect, sym: SymbolTable): Boolean =
    e.typeExpr match
      case TypeExpr.Simple(n) => sym.name(n.last) == "Error"
      case TypeExpr.Parameterized(n, _) => sym.name(n.last) == "Error"
      case _ => false

  private def errorTypeOf(
    e: anthill.parse.Effect, scope: TypeScope, sym: SymbolTable
  ): String =
    e.typeExpr match
      case TypeExpr.Parameterized(_, bindings) if bindings.length == 1 =>
        TypeGen.render(sym, bindings.head.bound, scope)
      case _ => "Throwable"

end OpGen
