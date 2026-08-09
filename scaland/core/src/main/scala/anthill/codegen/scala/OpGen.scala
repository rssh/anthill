package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.{Effect, Operation, TypeExpr}

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
    val declared = op.typeParams.map { tp =>
      // WI-840: a NAMED requirement slot (`requires plus: Monoid[T]`) rides in
      // `typeParams` but names a WITNESS, not a type — the same decision the sort
      // level makes, so the same refusal. No stdlib operation declares one today;
      // refusing keeps `def f[plus]` from becoming silently wrong output the day
      // one does.
      if tp.requirementSlot.isDefined then
        Bootstrap.refuseNamedRequirementSlot(
          s"operation `${sym.name(op.name.last)}`", sym.name(tp.name), tp.span)
      sym.name(tp.name)
    }
    // WI-1062: ONE partition of the declared parameters, not two filters — the
    // erased half and the emitted half are the two sides of a single split, and
    // spelling them as independent predicates hid that.
    val rows = rowVariables(op, sym)
    val (effectParams, typeNames) = declared.partition(rows.contains)
    val emitted = typeNames.map(n => (n, Names.scalaTypeName(n)))
    val scope = enclosingScope
      .at(s"operation `${sym.name(op.name.last)}`", op.span)
      .withParams(
        emitted.map((n, s) => n -> ParamBinding.Scala(s, 0)) ++
          effectParams.map(_ -> ParamBinding.Effect))
    val tpStr =
      if emitted.isEmpty then "" else emitted.map(_._2).mkString("[", ", ", "]")
    val params = op.params.map { p =>
      val pName = Names.scalaFieldName(sym.name(p.name))
      val pTy = TypeGen.render(sym, p.ty, scope)
      s"$pName: $pTy"
    }.mkString("(", ", ", ")")
    val ret = renderReturn(op, scope, sym)
    s"def $name$tpStr$params: $ret"

  /** Every name this operation's OWN signature writes in an effect-row position
    * (WI-1062).
    *
    * WHY IT IS INFERRED RATHER THAN DECLARED: a sort marks its effect parameters
    * (`effects E = ?`), and an operation has no such spelling — `operation
    * map[S, Dst, EffS, EffP]` writes its row variables in the same flat list as its
    * type variables. That is not an omission Bootstrap can route around: the
    * emitted `FiniteMappedStream[SrcC, Src, T]` has no slot for `EffP`, so
    * `FiniteMappedStream[SrcC = C, Src = Element, T = Dst, ES = E, EF = EffP]`
    * either drops it or ships a four-argument application of a three-parameter
    * type. Reading which parameters the signature USES as rows is the same thing a
    * reader does, and it is entirely local — the declaration's own text, no KB and
    * no other file (proposal 034).
    *
    * A row VARIABLE only: `{EffP, -Modify[x]}` contributes `EffP` and not `Modify`
    * or `x`, because a parameterized element of a row is a concrete effect LABEL
    * with its own arguments, and `Error[EmptyStream]`'s `EmptyStream` is an
    * ordinary type that must keep placing as one.
    *
    * IT CANNOT OVER-COLLECT — the result is intersected with the operation's own
    * declared parameters, so a name from an enclosing scope that happens to appear
    * in a row is never turned into an effect here.
    *
    * IT CAN UNDER-COLLECT, and that is the standing gap: this walk is SLOT-BLIND
    * where `TypeGen.named` is not. A parameter written only into a
    * declaration-known effect slot — `Stream[T, X]`, never inside a `{…}` row, an
    * `@` annotation or an `effects` clause — is not collected here, so it stays a
    * Scala binder while `TypeGen` erases every use of it, emitting a phantom
    * `[X]`. Harmless (Scala accepts an unused type parameter) but wrong. Every
    * stdlib operation of this shape also writes its rows in a `{…}` or an
    * `effects` clause, which is the ONLY reason the two mechanisms agree today —
    * a corpus coincidence, and no test asserts the correspondence. Closing it
    * means deriving the erased parameters from the same slot resolution
    * `TypeGen` performs, which would also survive a surface marker
    * (`operation map[S, Dst, effects EffP]`) arriving later; that marker needs a
    * proposal, a grammar change and a rustland mirror, so neither is this
    * ticket's.
    */
  private def rowVariables(op: Operation, sym: SymbolTable): Set[String] =
    val fromClause = op.effects.flatMap(e => rowVariablesOf(e.typeExpr, sym))
    val fromTypes = (op.params.map(_.ty) :+ op.returnType).flatMap(inEffectPositions(_, sym))
    (fromClause ++ fromTypes).toSet

  /** The row variables written anywhere INSIDE a type expression's effect
    * positions — a `{…}` argument, a guarded row, an arrow's `@` annotation. */
  private def inEffectPositions(te: TypeExpr, sym: SymbolTable): Set[String] = te match
    case TypeExpr.EffectRow(_) | TypeExpr.EffectGuarded(_, _) => rowVariablesOf(te, sym)
    case TypeExpr.Arrow(params, ret, effects) =>
      (params :+ ret).flatMap(inEffectPositions(_, sym)).toSet ++
        effects.flatMap(rowVariablesOf(_, sym))
    case TypeExpr.Parameterized(_, bindings) =>
      bindings.flatMap(b => inEffectPositions(b.bound, sym)).toSet
    case TypeExpr.TupleType(fields) =>
      fields.flatMap((_, ty) => inEffectPositions(ty, sym)).toSet
    case _ => Set.empty

  /** The row variables of one effect-position expression. */
  private def rowVariablesOf(te: TypeExpr, sym: SymbolTable): Set[String] = te match
    case TypeExpr.Simple(n) => Set(sym.name(n.last))
    case TypeExpr.EffectRow(effects) => effects.flatMap(rowVariablesOf(_, sym)).toSet
    case TypeExpr.EffectGuarded(label, _) => rowVariablesOf(label, sym)
    case _ => Set.empty

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

  private def isErrorEffect(e: Effect, sym: SymbolTable): Boolean =
    e.typeExpr match
      case TypeExpr.Simple(n) => sym.name(n.last) == "Error"
      case TypeExpr.Parameterized(n, _) => sym.name(n.last) == "Error"
      case _ => false

  private def errorTypeOf(e: Effect, scope: TypeScope, sym: SymbolTable): String =
    e.typeExpr match
      case TypeExpr.Parameterized(_, bindings) if bindings.length == 1 =>
        TypeGen.render(sym, bindings.head.bound, scope)
      case _ => "Throwable"

end OpGen
