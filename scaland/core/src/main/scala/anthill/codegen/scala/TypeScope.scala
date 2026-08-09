package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.TypeExpr
import anthill.span.Span

/** What ONE declared type parameter is, in the only distinction `scala_std` has
  * to draw about it: does it survive into the emitted type (WI-1062).
  */
enum ParamKind:
  case Type
  /** Declared `effects E = ?`. `scala_std` erases effects (§2.8), so the
    * parameter is NOT emitted and an argument written into its slot goes with
    * it — there is no Scala type to put there and no slot left to want one. */
  case Effect

/** The parameters a declaration writes, in order, for a type whose declaration
  * Bootstrap can see (WI-1062).
  *
  * The pair `written` / `emitted` is the whole of what erasure costs the caller:
  * anthill writes `Stream[Element, E]` and Scala gets `Stream[Element]`, so the
  * count a use site is CHECKED against and the count it is EMITTED with are two
  * different numbers, and a single `arity` field could only be one of them.
  */
case class ParamKinds(kinds: IndexedSeq[ParamKind]):
  /** How many arguments a use site must write — anthill's own parameter count. */
  def written: Int = kinds.length
  /** How many the emitted Scala type takes. */
  def emitted: Int = kinds.count(_ == ParamKind.Type)
  /** The entries that stand in a non-erased slot, in order — the ONE reading of
    * "which slots survive", used both to build a declaration's binder list and to
    * drop a use site's arguments, so the two cannot go out of positional sync.
    *
    * Requires the count to match: the callers check it first, so a mismatch here
    * is a Bootstrap bug rather than a bad input.
    *
    * POSITIONAL, while anthill's bindings are NOMINAL (`Stream[T = X, E = {}]`).
    * `TypeGen.render` drops `SortBinding.param` before this point, so a REORDERED
    * named binding would erase the wrong slot; the arity guard already refuses a
    * PARTIAL one, and no corpus file writes either. Carrying the anthill name per
    * slot is what would close it, and it is the same column WI-1060's
    * profile-supplied table needs. */
  def keepTypeArgs[A](args: IndexedSeq[A]): IndexedSeq[A] =
    require(args.length == written,
      s"keepTypeArgs on ${args.length} argument(s) against $written parameter(s)")
    args.zip(kinds).collect { case (a, ParamKind.Type) => a }

object ParamKinds:
  val none: ParamKinds = ParamKinds(IndexedSeq.empty)
  /** A declaration with no effect parameters — every entity, and every sort that
    * writes only `sort X = ?`. */
  def allTypes(n: Int): ParamKinds = ParamKinds(IndexedSeq.fill(n)(ParamKind.Type))

/** How the declaration being rendered binds one of its OWN parameter names
  * (WI-1062).
  *
  * ONE map and not a map plus a set: a parameter is a Scala type parameter or an
  * erased effect row, never both and never neither. Held apart in two containers,
  * disjointness was a convention `place` had to honour by consulting them in the
  * right order — and the repo's rule is to make the illegal state unrepresentable
  * rather than to check for it.
  */
enum ParamBinding:
  /** A Scala type parameter. `memberArity` is 0 except for a HIGHER-KINDED
    * parameter (`sort DelayMonad[M[T, E]]` gives `M` an arity of 2), where it is
    * the one declaration a use site inside the sort can still see.
    *
    * An ARITY and not a [[ParamKinds]], which is the whole content of the claim
    * `Bootstrap.TypeParamDecl` makes: a member cannot be an effect parameter,
    * because the binder grammar has no `effects` spelling to mark one with. So a
    * matching application of `M` erases NOTHING — which is exactly what refuses
    * delay.anthill's `M[T = A, E = {}]` instead of collapsing it. */
  case Scala(scalaName: String, memberArity: Int)
  /** Declared `effects E = ?` on the enclosing sort, or an operation type
    * parameter its signature only ever uses in an effect position. Erased, so it
    * has no Scala name at all — the absent field is the point. */
  case Effect

/** The enclosing sort of the declaration being rendered, when there is one.
  *
  * `anthillName` and `scalaName` are kept apart because `Names.scalaTypeName` is
  * many-to-one — `foo_bar` and `fooBar` share an image — so two anthill names
  * that merely converge in Scala are not one symbol. `Bootstrap.shapeOf` keys
  * eponymy on the anthill name for the same reason (§6.3).
  *
  * `written` is every parameter the sort DECLARES and [[params]] the ones it
  * EMITS; under effect erasure those differ (WI-1062) and both are needed — the
  * second to re-attach to a bare mention, `kinds.written` to check an explicit
  * application. Stored as one list plus its kinds and derived, rather than as two
  * lists, so the two views cannot disagree.
  */
case class EnclosingSort(
  anthillName: String, scalaName: String,
  written: IndexedSeq[String], kinds: ParamKinds
):
  /** What a bare mention re-attaches: the parameters that survive erasure. */
  def params: IndexedSeq[String] = kinds.keepTypeArgs(written)

/** Where a written type NAME goes in Scala — decided from the parse IR alone.
  *
  * This is the whole of what Bootstrap knows about a name (proposal 034: no KB,
  * no typer), stated as a closed set so that each answer — including "I can prove
  * this cannot work" — is a CASE rather than a fallthrough.
  */
enum Placement:
  /** A type parameter in scope: the enclosing sort's, or the operation's own.
    * Written arguments pass through, because a higher-kinded parameter (`M[A]`,
    * where the sort declares `M[T]`) legitimately takes them.
    *
    * `memberArity` is how many members a HIGHER-KINDED parameter declares, which
    * is the one declaration a use site inside the sort can still see (WI-1062):
    * `sort DelayMonad[M[T, E]]` gives `M` a 2, none of whose slots can be an
    * effect, so a row written into one is refused rather than erased. A proper
    * parameter carries 0. The arity itself stays unchecked — see the note at
    * [[TypeGen]]'s `named`. */
  case TypeParam(scalaName: String, memberArity: Int)
  /** The enclosing sort's own name. A BARE occurrence gets the sort's parameters
    * re-attached (WI-1055 A3): in anthill they are already in scope, so
    * `operation get(c: Cell) -> V` inside `sort Cell[V]` means `Cell[V]`, and
    * Scala has no bare spelling for that. */
  case Enclosing(sort: EnclosingSort)
  /** A type whose PARAMETERS are known — one this file emits, or a `scala_std`
    * type-map entry. Knowing them is what makes an arity MISMATCH detectable
    * (Group B3) and, since WI-1062, what says which argument slots erase. */
  case Known(scalaName: String, kinds: ParamKinds)
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
  /** The name denotes an effect ROW, not a type: a sort parameter declared
    * `effects E = ?`, or an operation type parameter this declaration only ever
    * uses in an effect position (WI-1062).
    *
    * `scala_std` erases effects (§2.8), so the name has NO Scala form. It is
    * legal only in a slot that erases with it, and an erased slot is dropped
    * before its argument is ever rendered — so reaching [[TypeGen]] at all means
    * a row was written where a type is needed, and that is a refusal. */
  case ErasedEffect(anthillName: String)
  /** Bootstrap can PROVE a bare mention will not reach the intended type, and says
    * why. The refusal cases of WI-1055 B1. */
  case Unplaceable(reason: String)

/** The names one emitted declaration is rendered against, plus the site a
  * refusal points at.
  *
  * Built per emitted FILE (the name environment) and then narrowed per
  * declaration through [[at]] / [[withParams]], so a refusal can say which
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
  /** Anthill leaf name → how this declaration binds it: a Scala type parameter,
    * or an erased effect row (WI-1062). */
  params: Map[String, ParamBinding],
  /** Anthill leaf name → its declared parameters, for every type THIS FILE
    * emits. */
  fileTypes: Map[String, ParamKinds],
  /** Anthill leaf name → the anthill package an `import` in scope brings it from. */
  importedFrom: Map[String, String],
  /** Names this file DECLARES and Bootstrap emits no Scala type for. */
  declaredNotEmitted: Set[String]
):

  def at(what: String, where: Span): TypeScope = copy(decl = what, declSpan = where)

  def withParams(more: IterableOnce[(String, ParamBinding)]): TypeScope =
    copy(params = params ++ more)

  /** Is this written type ARGUMENT an effect row, judged from the argument alone?
    *
    * The fallback half of WI-1062's rule, used exactly where the other half
    * cannot run: a [[Placement.Ambient]] target's declaration is in a file
    * Bootstrap has not read, so nothing says which of ITS slots erase, and
    * `requires Iterable[C = C, Element = Element, E = E]` still has to emit
    * something. Both cases are locally PROVABLE facts about the argument —
    * a written row is a row, and a name this declaration binds as an effect
    * parameter denotes one — so neither is a guess about the callee.
    *
    * THE NAME HALF GOES THROUGH [[place]], so there is ONE reader of "this name
    * is an effect row" and not a second predicate over the same field.
    *
    * THE HAZARD IT CARRIES, and the reason the declaration answers first
    * wherever it can: a row is erasable only because the slot it fills is an
    * effect slot. A sort that holds a row in an ORDINARY parameter — delay.anthill's
    * graded monad, `M[T = A, E = {}]` where `E` is `sort E = ?` (proposal 047) —
    * is refused when Bootstrap can see that declaration, and would be silently
    * collapsed here. No prelude file reaches a graded monad through an ambient
    * name; a project that does gets `Delay[A]` for `Delay[A, {}]` with no
    * diagnostic. Giving Ambient a parameter table is the same job as WI-1060.
    */
  def isEffectArgument(sym: SymbolTable, te: TypeExpr): Boolean = te match
    case TypeExpr.EffectRow(_) | TypeExpr.EffectGuarded(_, _) => true
    case TypeExpr.Simple(n) => place(sym.name(n.last)).isInstanceOf[Placement.ErasedEffect]
    case _ => false

  /** The one lookup, as a precedence chain. Mostly most-local-first, which is also
    * anthill's own order: a type parameter shadows a sort of the same name, and the
    * enclosing sort answers before the file-wide table — where it also appears, with
    * the same arity but without the parameters to re-attach.
    *
    * THE ONE INVERSION IS THE SCALARS (WI-1021), and it is the rule rather than an
    * exception to it: a scalar has no anthill values, so its name denotes the host
    * carrier EVERYWHERE — including inside the file that declares it. Read
    * most-local-first, `int64.anthill`'s `operation compare(a: Int64, b: Int64)`
    * placed as [[Placement.Enclosing]] and emitted `def compare(a: Int64, b: Int64):
    * Int64` against the `trait Int64` that file emits: a trait no value inhabits,
    * over a name every consumer of the same file resolves to `Long`. That is the
    * one-name-two-types defect the whole decision removes, and it lived inside the
    * five files declaring a scalar. `Unit` reaches this by the same route — its
    * declaration is an opaque `sort Unit = ?`, which [[Placement.Unplaceable]] would
    * otherwise refuse. */
  def place(anthillLeaf: String): Placement =
    // WI-1062 adds no link: an erased effect parameter is a PARAMETER, so it
    // answers from the same first link every other one does. That it cannot be
    // shadowed by a scalar or a sort of the same name is the ordinary
    // most-local-first rule, not an exception carved out for it — which is what
    // one `Map[String, ParamBinding]` buys over a map plus a disjoint set.
    params.get(anthillLeaf).map[Placement] {
        case ParamBinding.Scala(name, memberArity) => Placement.TypeParam(name, memberArity)
        case ParamBinding.Effect => Placement.ErasedEffect(anthillLeaf)
      }
      .orElse(TypeGen.hostScalar(anthillLeaf))
      .orElse(enclosing.filter(_.anthillName == anthillLeaf).map(Placement.Enclosing(_)))
      .orElse(fileTypes.get(anthillLeaf)
        .map(ks => Placement.Known(Names.scalaTypeName(anthillLeaf), ks)))
      .orElse(TypeGen.preludeSort(anthillLeaf))
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
