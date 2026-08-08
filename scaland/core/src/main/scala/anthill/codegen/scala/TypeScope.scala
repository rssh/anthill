package anthill.codegen.scala

import anthill.span.Span

/** The enclosing sort of the declaration being rendered, when there is one.
  *
  * `anthillName` and `scalaName` are kept apart because `Names.scalaTypeName` is
  * many-to-one — `foo_bar` and `fooBar` share an image — so two anthill names
  * that merely converge in Scala are not one symbol. `Bootstrap.shapeOf` keys
  * eponymy on the anthill name for the same reason (§6.3).
  */
case class EnclosingSort(anthillName: String, scalaName: String, params: IndexedSeq[String])

/** Where a written type NAME goes in Scala — decided from the parse IR alone.
  *
  * This is the whole of what Bootstrap knows about a name (proposal 034: no KB,
  * no typer), stated as a closed set so that each answer — including "I can prove
  * this cannot work" — is a CASE rather than a fallthrough.
  */
enum Placement:
  /** A type parameter in scope: the enclosing sort's, or the operation's own.
    * Written arguments pass through, because a higher-kinded parameter (`M[A]`,
    * where the sort declares `M[T]`) legitimately takes them. */
  case TypeParam(scalaName: String)
  /** The enclosing sort's own name. A BARE occurrence gets the sort's parameters
    * re-attached (WI-1055 A3): in anthill they are already in scope, so
    * `operation get(c: Cell) -> V` inside `sort Cell[V]` means `Cell[V]`, and
    * Scala has no bare spelling for that. */
  case Enclosing(sort: EnclosingSort)
  /** A type of KNOWN arity — one this file emits, or a `scala_std` type-map
    * entry. Known arity is what makes an arity MISMATCH detectable (Group B3). */
  case Known(scalaName: String, arity: Int)
  /** Not placed by anything Bootstrap can see, and nothing Bootstrap CAN see says
    * it is wrong: the name is unqualified, unimported, and undeclared here, so
    * anthill resolved it in an enclosing namespace or through the auto-imported
    * prelude.
    *
    * QUALIFIED WITH THE DECLARATION'S OWN PACKAGE, which is right whenever that
    * package is where the name lives — the common case by far, since a file's
    * sibling declarations and (for the prelude itself) the auto-import target are
    * the same package. It is a GUESS when they differ: a file emitting into
    * `anthill.reflect` that reaches a prelude name through the auto-import gets
    * `anthill.reflect.Foo`. No file does that today (the reflect namespace imports
    * explicitly, and an explicit import is [[Unplaceable]] rather than this), and
    * the wrong guess still fails at compile time rather than resolving to
    * something else — but it fails naming a package the reader did not write.
    *

    * NOT A REFUSAL, deliberately: `sort Lattice { requires Eq[T] }` names a sort
    * a sibling file declares, and refusing every such name would take thirteen
    * prelude files out of the tree to catch nothing the closure compile does not
    * already catch (measured). A typo and a real sibling are indistinguishable
    * from here; compiling the generated closure (WI-1020) is what tells them
    * apart.
    *
    * EMITTED FULLY QUALIFIED, which is the part that is not a guess-and-hope.
    * A bare mention also resolves against Scala's root imports, so an ABSENT
    * sibling does not fail — it CAPTURES: `field.anthill`'s `requires Numeric[T]`
    * emitted a bare `Numeric` and compiled green against `scala.math.Numeric`,
    * a type from another library. `pkg.Name` cannot capture, so the sibling is
    * either there or the compiler says which name is missing. */
  case Ambient(qualifiedName: String)
  /** Bootstrap can PROVE a bare mention will not reach the intended type, and says
    * why. The refusal cases of WI-1055 B1. */
  case Unplaceable(reason: String)

/** The names one emitted declaration is rendered against, plus the site a
  * refusal points at.
  *
  * Built per emitted FILE (the name environment) and then narrowed per
  * declaration through [[at]] / [[withTypeParams]], so a refusal can say which
  * operation or field defeated the emitter and not merely which file.
  */
case class TypeScope(
  /** What a refusal names — `operation anthill.prelude.Monad.pure`, `sort Cell`. */
  decl: String,
  /** Where a refusal points when the offending construct carries no name of its
    * own (an anonymous type variable, a written effect row). A construct that
    * DOES have a name is located at that name instead, which is tighter. */
  declSpan: Span,
  /** The Scala package this declaration is emitted into. What makes an import
    * from ELSEWHERE provably unreachable by a bare mention. */
  pkg: String,
  enclosing: Option[EnclosingSort],
  /** Anthill leaf name → Scala type-parameter name. */
  typeParams: Map[String, String],
  /** Anthill leaf name → arity, for every type THIS FILE emits. */
  fileTypes: Map[String, Int],
  /** Anthill leaf name → the anthill package an `import` in scope brings it from. */
  importedFrom: Map[String, String],
  /** Names this file DECLARES and Bootstrap emits no Scala type for. */
  declaredNotEmitted: Set[String]
):

  def at(what: String, where: Span): TypeScope = copy(decl = what, declSpan = where)

  def withTypeParams(more: IterableOnce[(String, String)]): TypeScope =
    copy(typeParams = typeParams ++ more)

  /** The one lookup. Ordered most-local-first, which is also anthill's own order:
    * a type parameter shadows a sort of the same name, and the enclosing sort
    * answers before the file-wide table — where it also appears, with the same
    * arity but without the parameters to re-attach. */
  def place(anthillLeaf: String): Placement =
    typeParams.get(anthillLeaf) match
      case Some(p) => Placement.TypeParam(p)
      case None if enclosing.exists(_.anthillName == anthillLeaf) =>
        Placement.Enclosing(enclosing.get)
      case None =>
        fileTypes.get(anthillLeaf)
          .map(n => Placement.Known(Names.scalaTypeName(anthillLeaf), n))
          .orElse(TypeGen.preludeMapping(anthillLeaf))
          .getOrElse(unreachable(anthillLeaf))

  /** The name is not placed. Either Bootstrap can show a bare mention is wrong —
    * and then it refuses — or it cannot, and the name rides out unverified. */
  private def unreachable(anthillLeaf: String): Placement =
    if declaredNotEmitted.contains(anthillLeaf) then
      // The file DECLARES it and the emitted tree has no such type: a
      // namespace-level `sort Type = ?` is an opaque handle with no Scala
      // declaration here (`Type` in sort.anthill is exactly this), and a bare
      // `Type` in a member signature therefore names nothing at all.
      Placement.Unplaceable(
        s"this file declares `$anthillLeaf` in a position Bootstrap emits no Scala " +
        "type for (an abstract sort has no declaration in the output), so the name " +
        "is not in the emitted tree")
    else
      importedFrom.get(anthillLeaf) match
        case Some(from) if from != pkg =>
          // Provably wrong: the import says the name lives in ANOTHER package, and
          // Bootstrap emits no Scala `import`, so the bare mention cannot reach it.
          // `Term` / `NodeOccurrence` from `anthill.reflect` are this case, and
          // emitting the Scala import would only move the failure — the reflect
          // namespace is outside the generated closure.
          Placement.Unplaceable(
            s"`$anthillLeaf` is imported from `$from`, but this declaration is emitted " +
            s"into package `$pkg` and Bootstrap emits no Scala `import`, so a bare " +
            "mention cannot reach it")
        case _ =>
          val scalaName = Names.scalaTypeName(anthillLeaf)
          Placement.Ambient(if pkg.isEmpty then scalaName else s"$pkg.$scalaName")
