package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.{Name, TypeExpr}
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
  * `binders` is every parameter the sort DECLARES, in order, under the ANTHILL name
  * it declares it by — and [[kinds]] and [[params]] are DERIVED from it rather than
  * carried beside it (WI-1081). Three readers need three different views of one list:
  * a bare mention re-attaches the EMITTED Scala names ([[params]]), an explicit
  * application is checked and erased against what the declaration WRITES ([[kinds]]),
  * and a path-dependent projection off a bare self receiver asks for ONE parameter BY
  * ITS ANTHILL NAME ([[binding]]). Held as one list, they cannot disagree; the scala
  * names alone could not answer the third, since `Names.scalaTypeName` is many-to-one.
  */
case class EnclosingSort(
  anthillName: String, scalaName: String,
  binders: IndexedSeq[(String, ParamBinding)]
):
  /** What a bare mention re-attaches: the parameters that survive erasure — which are
    * exactly the ones with a Scala name to re-attach. */
  def params: IndexedSeq[String] = binders.collect { case (_, ParamBinding.Scala(n, _)) => n }

  /** What an explicit application is checked and erased against. */
  def kinds: ParamKinds = ParamKinds(binders.map {
    case (_, ParamBinding.Scala(_, _)) => ParamKind.Type
    case (_, ParamBinding.Effect) => ParamKind.Effect
  })

  /** How the SORT binds one of its own parameter names — the question a projection off
    * a bare self receiver asks, and the reason this is not `TypeScope.params`: that map
    * has the OPERATION's type parameters merged in ([[TypeScope.withParams]]), and
    * `b.U` for an operation's own `U` is not a member of the sort at all (WI-1081). */
  def binding(anthillLeaf: String): Option[ParamBinding] =
    binders.collectFirst { case (n, b) if n == anthillLeaf => b }

/** How a VALUE in scope was declared, in the only distinction a path-dependent
  * projection off it needs (WI-1081).
  *
  * `s.T` in a type position is a projection off the VALUE `s` — the element of the
  * stream it holds — and not a package-qualified name, though the two share the
  * dotted spelling. What the projection denotes is read off the receiver's declared
  * type, and the two cases below are the two ways that type can answer:
  *
  *  - [[Applied]] — the receiver's occurrence WRITES the slot (`r1: Relation[T = L]`),
  *    so the projection IS what it wrote. relation.anthill's `join` exists to write
  *    them: its two operands carry INDEPENDENT schemas, and `r1.T` / `r2.T` are `L`
  *    and `R`, not one shared `T`.
  *  - [[Bare]] — the receiver's occurrence writes nothing. Then the projection is the
  *    ENCLOSING sort's parameter of that name, and only then: within a sort's own
  *    definition a bare self reference participates in the parametricity tie
  *    (`docs/design/type-parameter-scoping.md` §3), so `xs: List` inside `sort List[T]`
  *    makes `xs.T` this sort's `T`. A bare occurrence of any OTHER sort takes a fresh
  *    skolem (kernel §"How the slot is named", WI-1059), which has no Scala spelling.
  */
enum ReceiverType:
  /** Declared as an occurrence of the sort `head` NAMES, with NO written arguments.
    *
    * The whole written head and not its leaf: the tie is decided by asking whether the
    * head names the ENCLOSING sort, and that is the same question a type occurrence
    * asks — `app.model.Payload` and a sibling `app.Payload` are two sorts, and reading
    * the leaf alone is the defect this ticket exists to remove. */
  case Bare(head: IndexedSeq[String])
  /** Declared as an occurrence with arguments, indexed by the anthill parameter each
    * NAMES. Every reading of it is off the BINDING and never off the target's
    * declaration, which is why the head is not carried: `r1: Relation[T = L]` says
    * `r1.T` is `L` whatever `Relation` is and wherever it lives, and a qualified
    * spelling of the same receiver says exactly the same thing.
    *
    * A positional argument is absent from the map: which slot it fills is a fact about
    * the target's declaration, and no table here carries a per-slot parameter NAME
    * (see [[ParamKinds.keepTypeArgs]] — the same missing column).
    *
    * THE SAME MISSING COLUMN IS WHY A BINDING IS NOT VALIDATED: `r: Box[Q = L]` answers
    * `r.Q` with `L` though `Box` declares no `Q`. The receiver's OWN occurrence is not
    * name-checked either — [[Placement.Enclosing]] and [[Placement.Known]] compare
    * argument COUNTS — so this reads a malformed application rather than creating one,
    * and the reordered-binding hazard `keepTypeArgs` records is the other half of it. */
  case Applied(byName: Map[String, TypeExpr])
  /** Declared as something no projection can be read off, and what it is — for the
    * refusal. */
  case Other(what: String)

object ReceiverType:
  def of(sym: SymbolTable, te: TypeExpr): ReceiverType = te match
    case TypeExpr.Simple(n) => Bare(n.segments.map(sym.name))
    case TypeExpr.Parameterized(_, bindings) =>
      val named = bindings.collect {
        case b if b.param.isDefined => sym.name(b.param.get.last) -> b.bound
      }
      // A REPEATED binding is refused rather than last-wins (WI-1081): `Box[T = L,
      // T = R]` would silently answer `r.T` with `R`, and WI-1022 refuses the
      // structurally identical repeated sort binder at the repeat for the same reason.
      // The refusal is deferred to a projection off it — the receiver's own rendering
      // does not check repeats either, and widening that is a separate rule.
      val repeated = named.map(_._1).diff(named.map(_._1).distinct).distinct
      if repeated.nonEmpty then
        Other(s"an occurrence that writes ${repeated.map(n => s"`$n`").mkString(", ")} " +
          "more than once, so no one binding answers")
      else Applied(named.toMap)
    case TypeExpr.Arrow(_, _, _) => Other("an arrow type")
    case TypeExpr.TupleType(_) => Other("a tuple type")
    case TypeExpr.Variable(_, _) => Other("a type variable")
    case TypeExpr.Denoted(_) => Other("a value in a type position")
    case TypeExpr.EffectRow(_) | TypeExpr.EffectGuarded(_, _) => Other("an effect row")

/** What ONE written type name denotes (WI-1081) — the ONE answer both the renderer
  * and the effect-argument fallback read, so they cannot disagree about a spelling.
  *
  * Two cases and not one, because a path-dependent projection whose receiver WRITES
  * the slot is answered by a type EXPRESSION rather than by a placement: `r1.T`
  * against `r1: Relation[T = L]` is `L`, which still has to be rendered in scope.
  */
enum NamePlacement:
  case Direct(placement: Placement)
  /** Substitute this expression for the name. `receiver` is the value the projection
    * was taken off; rendering happens with THAT value dropped from scope, which is
    * what makes the substitution terminate — `p: Relation[T = p.T]` would otherwise
    * expand forever. */
  case Substituted(te: TypeExpr, receiver: String)

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
  /** A type whose PARAMETERS are known — one this file emits, one in the supplied
    * project/prelude closure, or a `scala_std` type-map entry. Knowing them is what
    * makes an arity MISMATCH detectable (Group B3) and, since WI-1062, what says which
    * argument slots erase. */
  case Known(scalaName: String, kinds: ParamKinds)
  /** Not placed by anything Bootstrap can see, and nothing Bootstrap CAN see says
    * it is wrong: the name is unqualified, unimported, and absent from the file plus
    * supplied project/prelude tables. Anthill resolved it in source context the caller
    * did not include in the emission closure.
    *
    * A BARE MENTION ONLY (WI-1081). A written `a.b.C` says where the type lives, so
    * there is no context to be missing and no guess to make: [[TypeScope.placeQualified]]
    * ends in [[Unplaceable]] instead.
    *
    * QUALIFIED WITH THE DECLARATION'S OWN PACKAGE, which is right whenever that
    * package is where the name lives. It is a GUESS when they differ: a file emitting into
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
  /** The Scala-converted anthill NAMESPACE this declaration's names are WRITTEN in —
    * which is what every lookup asks: the package chain a bare name walks, the scope a
    * written path's head resolves in, what an `import` of one's own namespace is
    * compared against, and what an [[Placement.Ambient]] guess qualifies with.
    *
    * NOT THE SAME QUESTION AS [[emittedPkg]], and a namespace's `<Ns>Ops` trait is where
    * they part (WI-1081): `namespace my.app`'s top-level operations emit into package
    * `my` as `AppOps`, while the names they write were written inside `my.app`. Held as
    * one field, lookups were anchored one package too high — a bare mention of a sort
    * `my.app` declares missed the package chain and fell to `Placement.Ambient` (`my.Foo`,
    * naming nothing), and a written path's head was read from `my`. The prelude never
    * showed it: `anthill.prelude`'s own sorts are reached through the AUTO-IMPORT rung,
    * which is package-blind. */
  writtenIn: String,
  /** The Scala package this declaration is EMITTED into — the file's own `package`
    * clause. Exactly one question needs it, and it is a Scala fact rather than an
    * anthill one: whether a selected declaration can be spelled BARE. Only a
    * declaration in this very package can. */
  emittedPkg: String,
  enclosing: Option[EnclosingSort],
  /** Anthill leaf name → how this declaration binds it: a Scala type parameter,
    * or an erased effect row (WI-1062). */
  params: Map[String, ParamBinding],
  /** The VALUE names in scope, with what a projection off each can read (WI-1081) —
    * an operation's own parameters, and nothing else, since only an operation
    * signature binds a value a type may project off. Empty for a sort's `requires`,
    * an entity's fields and a namespace's own scope.
    *
    * IT IS WHAT SEPARATES THE TWO READINGS OF ONE SPELLING: `s.T` and
    * `anthill.reflect.Term` are both dotted names, and which one a written path is
    * turns on whether its HEAD names a value or a package — the same question
    * anthill's own resolver asks of a dotted path's head segment (kernel §"A dotted
    * path ends the ladder on its head segment"). A value binding shadows a package
    * there too, which is why this is consulted first. */
  values: Map[String, ReceiverType],
  /** (Scala package, Anthill leaf) → the type THIS FILE promises to emit. Package is
    * load-bearing: one file may contain several namespaces (WI-1067). */
  fileTypes: Map[(String, String), Placement.Known],
  /** Anthill leaf name → the anthill package an `import` in scope brings it from. */
  importedFrom: Map[String, String],
  /** Package-qualified names this file DECLARES and Bootstrap emits no Scala type for. */
  declaredNotEmitted: Set[(String, String)],
  /** The project-wide prelude tables: the profile's scalars and the types the
    * auto-imported files emit (WI-1060). Resolved by the caller and passed into
    * `Bootstrap.generate` — the emitter reads no KB (proposal 034). */
  types: ScalaTypes
):

  def at(what: String, where: Span): TypeScope = copy(decl = what, declSpan = where)

  def withParams(more: IterableOnce[(String, ParamBinding)]): TypeScope =
    copy(params = params ++ more)

  def withValues(more: IterableOnce[(String, ReceiverType)]): TypeScope =
    copy(values = values ++ more)

  /** Drop one value binding — what a projection's substitution is rendered in
    * (WI-1081). The receiver cannot be projected off again, so `p: Relation[T = p.T]`
    * ends in a refusal rather than in an expansion that never terminates. */
  def withoutValue(name: String): TypeScope = copy(values = values - name)

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
    * THE NAME HALF GOES THROUGH [[placeName]], so there is ONE reader of "this name
    * is an effect row" and not a second predicate over the same field — and one
    * reader of what a DOTTED name is, so this cannot come to disagree with the
    * renderer about which spelling is a projection (WI-1081).
    *
    * THE HAZARD IT CARRIES, and the reason the declaration answers first
    * wherever it can: a row is erasable only because the slot it fills is an
    * effect slot. A sort that holds a row in an ORDINARY parameter — delay.anthill's
    * graded monad, `M[T = A, E = {}]` where `E` is `sort E = ?` (proposal 047) —
    * is refused when Bootstrap can see that declaration, and would be silently
    * collapsed here. No prelude file reaches a graded monad through an ambient
    * name; a project that does gets `Delay[A]` for `Delay[A, {}]` with no
    * diagnostic.
    *
    * WI-1060 SHRANK ITS REACH RATHER THAN CLOSING IT: every type the auto-imported
    * files emit is now in [[ScalaTypes]]`.preludeSorts` with its declared parameter
    * kinds, so a prelude name — delay.anthill's `Delay` included — is placed by its
    * DECLARATION and never gets here. What is left is a name from a file the caller
    * did not pass, which is the honest residue: nothing read it, so nothing knows
    * its slots. */
  def isEffectArgument(sym: SymbolTable, te: TypeExpr): Boolean = te match
    case TypeExpr.EffectRow(_) | TypeExpr.EffectGuarded(_, _) => true
    case TypeExpr.Simple(n) => placeName(sym, n) match
      case NamePlacement.Direct(_: Placement.ErasedEffect) => true
      // A projection whose receiver WRITES the slot is a row exactly when what it
      // wrote is one — `s: Stream[E = {}]` makes `s.E` the written row. Rendering
      // would refuse it here; asking the same question of the substitute is the
      // answer this predicate exists to give, and dropping the receiver is what
      // makes the recursion finite (WI-1081).
      case NamePlacement.Substituted(sub, receiver) =>
        withoutValue(receiver).isEffectArgument(sym, sub)
      case _ => false
    case _ => false

  /** Where ONE written type name goes, whatever its spelling — the entry point
    * [[TypeGen]] renders through (WI-1081).
    *
    * A SIMPLE name is [[place]]d. A DOTTED one is first split by what its HEAD names,
    * because anthill spells two different constructs the same way: a path-dependent
    * projection off a value (`s.T`) and a package-qualified type (`anthill.reflect.Term`).
    * Reading only the last segment — which is what this did before this ticket — makes
    * them one query and gets the second wrong every time: `anthill.reflect.Symbol` was
    * re-anchored to the DECLARING package and emitted as `anthill.prelude.Symbol`, a
    * type nothing declares, while the source had said exactly where it lives.
    */
  /* TWO READINGS AND NOT THREE, and the third is stated rather than silently folded in:
   * a head naming a SORT (`Box.T`, a sort-scoped member path) is a reading the kernel
   * has and this mapping does not implement — a sort's abstract members are emitted as
   * Scala TYPE PARAMETERS, which have no member syntax to project off. Such a name
   * reaches the qualified arm and is refused there for naming no package, which is true
   * but not the reason; `docs/scala-forward-mapping.md` §2.1b records both. No corpus
   * file writes one (measured across the prelude, WI-1081).
   *
   * `values` IS AN OPERATION'S PARAMETERS ONLY, so a projection written in an entity
   * field, a sort's `requires` or a namespace-level scope has no value in scope and is
   * read as a package path too. Same §, same reason to state it: the refusal names a
   * package, and its last clause is what tells a reader the head was read as one. */
  def placeName(sym: SymbolTable, n: Name): NamePlacement =
    val segments = n.segments.map(sym.name)
    if segments.length == 1 then NamePlacement.Direct(place(segments.head))
    else values.get(segments.head) match
      case Some(receiver) =>
        projection(segments.head, receiver, segments.tail, segments.mkString("."))
      case None => NamePlacement.Direct(
        placeQualified(segments.init.map(Names.scalaPackageSegment), segments.last))

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
    * otherwise refuse.
    *
    * THE AUTO-IMPORT TABLE SITS BELOW what this file and the mentioning declaration's
    * project package say, including their negative answers. [[shadowsThePrelude]] then
    * handles explicit imports, and its every answer is a refusal. That ordering is
    * anthill's own — a local/project declaration and an explicit `import` both shadow
    * the auto-import — and it stopped being a formality when WI-1060 derived the table:
    * six hand-picked names could rarely collide, every prelude sort collides often. */
  private def place(anthillLeaf: String): Placement =
    // WI-1062 adds no link: an erased effect parameter is a PARAMETER, so it
    // answers from the same first link every other one does. That it cannot be
    // shadowed by a scalar or a sort of the same name is the ordinary
    // most-local-first rule, not an exception carved out for it — which is what
    // one `Map[String, ParamBinding]` buys over a map plus a disjoint set.
    paramPlacement(anthillLeaf)
      .orElse(types.hostScalar(anthillLeaf))
      .orElse(enclosing.filter(_.anthillName == anthillLeaf).map(Placement.Enclosing(_)))
      .orElse(filePlacement(anthillLeaf))
      .orElse(types.packagePlacement(writtenIn, anthillLeaf))
      .orElse(shadowsThePrelude(anthillLeaf))
      .orElse(types.preludeSort(anthillLeaf))
      .orElse(types.preludeNotEmitted(anthillLeaf))
      .getOrElse(ambient(anthillLeaf))

  /** How this declaration binds a leaf name, as a [[Placement]]. */
  private def paramPlacement(anthillLeaf: String): Option[Placement] =
    params.get(anthillLeaf).map(placementOf(anthillLeaf, _))

  /** What a parameter BINDING is, as a [[Placement]]. ONE reader, because the bare
    * chain and the parametricity tie ask exactly this of two different binder maps, and
    * a second copy of the two-case mapping is a way for them to answer it differently. */
  private def placementOf(anthillLeaf: String, binding: ParamBinding): Placement =
    binding match
      case ParamBinding.Scala(name, memberArity) => Placement.TypeParam(name, memberArity)
      case ParamBinding.Effect => Placement.ErasedEffect(anthillLeaf)

  /** A path-dependent projection `receiver.member` (WI-1081) — see [[ReceiverType]]
    * for which of the two readings applies and why.
    *
    * EVERY ARM THAT IS NOT ONE OF THOSE TWO IS A REFUSAL, and that is the change of
    * standing this ticket makes: dropping the prefix and placing the member alone
    * answered `r1.T` against `r1: Relation[T = L]` with `T`, the ENCLOSING sort's
    * parameter — a different type from the `L` the source pinned, emitted silently.
    */
  private def projection(
    receiver: String, receiverType: ReceiverType, members: IndexedSeq[String], written: String
  ): NamePlacement =
    def refuse(why: String) = NamePlacement.Direct(Placement.Unplaceable(why))
    if members.length > 1 then
      // `s.T.U` — the tail is appended to whatever the head denotes and never looked
      // up on its own (kernel §"A dotted path ends the ladder on its head segment"),
      // and what `s.T` denotes is a type, which carries no further members here.
      refuse(s"`$written` projects off the projection `$receiver.${members.head}`, and " +
        "Bootstrap resolves one member off a value (proposal 034: no typer to give the " +
        "intermediate a sort)")
    else
      val member = members.head
      receiverType match
        case ReceiverType.Applied(byName) => byName.get(member) match
          case Some(bound) => NamePlacement.Substituted(bound, receiver)
          // AN UNWRITTEN SLOT IS THE RECEIVER'S OWN SKOLEM and not the enclosing sort's
          // parameter, which is why this does not fall back to the tie: kernel §"How the
          // slot is named" (WI-1059) says `r1: Relation[T = L]` is checked as
          // `Relation[T = L, E = r1.E]`, so `join`'s `{r1.E, r2.E}` are two DIFFERENT
          // rows. Tying them to one `E` is exactly the collapse the grading forbids, and
          // Scala has no term for the skolem itself.
          case None => refuse(
            s"`$written` projects `$member` off `$receiver`, whose declared type writes " +
            s"arguments and binds no `$member` among them. An unwritten slot of an " +
            "applied occurrence is that receiver's OWN skolem (kernel §\"How the slot is " +
            "named\"), not the enclosing sort's parameter, and Scala has no term for it; " +
            "a POSITIONAL argument names no slot at all")
        case ReceiverType.Bare(head) =>
          val self = headPlacement(head) match
            case Placement.Enclosing(sort) => Some(sort)
            case _ => None
          self match
            case None => refuse(
              s"`$written` projects `$member` off `$receiver`, whose declared type " +
              s"`${head.mkString(".")}` is not a bare occurrence of the enclosing sort. " +
              "Only that ties to the sort's own parameters " +
              "(`docs/design/type-parameter-scoping.md` §3); any other bare occurrence " +
              "takes a fresh skolem, which Scala has no term for")
            // THE SORT'S OWN BINDERS and not this declaration's `params`, which has the
            // OPERATION's type parameters merged in: `operation f[U](b: Box) -> b.U`
            // answered `U` off a name the sort never declared (WI-1081 review).
            case Some(sort) => sort.binding(member).map[NamePlacement](b =>
              NamePlacement.Direct(placementOf(member, b))).getOrElse(refuse(
                s"`$written` projects `$member` off a bare occurrence of the enclosing " +
                s"sort `${sort.anthillName}`, which declares no parameter `$member`"))
        case ReceiverType.Other(what) => refuse(
          s"`$written` projects `$member` off `$receiver`, which is declared as $what — " +
          "a projection is read off the receiver's declared SORT occurrence, and there " +
          "is none here")

  /** Where the head of a receiver's declared type goes — the ONE reader of "is this
    * written name the enclosing sort", shared with every other occurrence so a
    * qualified self-mention and a bare one answer alike (WI-1081). */
  private def headPlacement(head: IndexedSeq[String]): Placement =
    if head.length == 1 then place(head.head)
    else placeQualified(head.init.map(Names.scalaPackageSegment), head.last)

  /** Where a QUALIFIED written name goes (WI-1081): HEAD-QUALIFICATION, which is the
    * language's own reading of a written path — kernel §"`a.b.c` — **relative**, and
    * only relative": resolve the FIRST segment in scope, append the remaining segments
    * to what it denotes, and look THAT up.
    *
    * A MISS UNDER THE BOUND HEAD IS LOUD, and the same section says so in those words:
    * "the path is never re-anchored elsewhere". So the search is over the HEAD segment
    * alone — nearest enclosing package first, then the top level, which is where
    * `anthill.reflect.Symbol` written inside `anthill.prelude` binds its `anthill` —
    * and once a head binds, the leaf is looked up in exactly one package. Searching for
    * the LEAF instead would let a nearer package that merely lacks it hand the name to a
    * farther one, which is re-anchoring by another route.
    *
    * (The `..a.b.c` ABSOLUTE spelling is a separate reading the kernel defines and the
    * fastparse grammar does not yet accept, so no occurrence reaching here is one.)
    *
    * THE PREFIX IS WHAT IS RESOLVED, which is the whole content of the defect: the bare
    * chain ([[ScalaTypes.packagePlacement]]) looks for a LEAF up the mentioning
    * declaration's ancestors, and running it on a qualified name discards the prefix —
    * `anthill.reflect.Symbol` and a bare `Symbol` became one query, and the answer was
    * `anthill.prelude.Symbol`.
    *
    * NO [[Placement.Ambient]] AND NO IMPORT CHECK. A qualified name that nothing in the
    * emitted closure declares is a refusal: unlike a bare mention (which may be a sibling
    * in a file the caller did not supply — thirteen prelude files' worth, measured at
    * WI-1055), Bootstrap can PROVE the emitted spelling would name a different type than
    * the source wrote. And an `import` cannot shadow it, because the occurrence itself
    * says which package it means.
    *
    * THE SCALARS STILL WIN, but only in the package that declares them (WI-1021): a
    * profile's `type_map` names prelude sorts, so `anthill.prelude.Int64` is
    * `_root_.scala.Long` for the same reason the bare `Int64` is — no anthill value
    * inhabits the `trait Int64` that file emits. A project's OWN `my.app.Int64` is its
    * own type, which is one thing a written prefix can say and a bare name cannot.
    */
  private def placeQualified(prefix: IndexedSeq[String], anthillLeaf: String): Placement =
    val written = (prefix :+ anthillLeaf).mkString(".")
    val headReadings = (PackageNesting.from(writtenIn).map(owner =>
      if owner.isEmpty then prefix.head else s"$owner.${prefix.head}") :+ prefix.head).distinct
    headReadings.find(packageExists) match
      case None => Placement.Unplaceable(
        s"`$written` is a written path, so its head segment `${prefix.head}` must name a " +
        "package, and no supplied file declares anything in one (read as " +
        headReadings.map(p => s"`$p`").mkString(", ") +
        " — a head resolves in the enclosing namespace before the top level, as anthill " +
        s"resolves one). Add the declaring file to the closure passed to " +
        s"`ScalaTypes.resolve`; if `${prefix.head}` was meant as a VALUE, note that a " +
        "projection off one is read only in an operation signature, where the receiver " +
        "is a parameter")
      case Some(head) =>
        val owner = (head +: prefix.tail).mkString(".")
        // NO REMEDY IS SUGGESTED ON THIS ARM, deliberately, and the reason is measured
        // (WI-1081 review): for the corpus instance — `anthill.reflect.Symbol` — neither
        // obvious one works. Supplying reflect.anthill only changes the message, since
        // `Symbol` is an abstract sort there and so declared-and-not-emitted; and a
        // profile `type_map` entry is keyed by BARE leaf with no package column, so it
        // cannot say anything about a qualified occurrence at all. The head-miss arm
        // above does suggest one, because there it is the fix.
        inPackage(owner, anthillLeaf).getOrElse(Placement.Unplaceable(
          s"`$written` binds its head to package `$head`, and nothing Bootstrap can see " +
          s"declares `$anthillLeaf` in `$owner`. A miss under the package a path bound " +
          "is loud (kernel §\"a.b.c — relative, and only relative\"): the path is not " +
          "re-anchored elsewhere, because the source said where the type lives"))

  /** Does ANY declaration Bootstrap can see live in this package or below it? — which
    * is the most a parse-IR emitter can ask of "does this namespace exist" (proposal
    * 034: no KB). Prefix-closed, because `anthill` is a real package whenever
    * `anthill.prelude` holds a declaration, though nothing is declared in `anthill`
    * itself. */
  private def packageExists(owner: String): Boolean =
    def under(p: String) = p == owner || p.startsWith(s"$owner.")
    fileTypes.keysIterator.exists((p, _) => under(p)) ||
      declaredNotEmitted.iterator.exists((p, _) => under(p)) ||
      types.packageExists(owner)

  /** What ONE package says about a leaf — the answer that ENDS the reading walk,
    * including its negative answers: a package that declares the name and emits no type
    * for it has answered, and falling through to another reading would place the name
    * against a declaration the source did not name. */
  private def inPackage(owner: String, anthillLeaf: String): Option[Placement] =
    Option.when(owner == types.autoImportPackage)(types.hostScalar(anthillLeaf)).flatten
      .orElse(Option.when(owner == writtenIn)(
        enclosing.filter(_.anthillName == anthillLeaf).map(Placement.Enclosing(_))).flatten)
      .orElse(fileTypes.get(owner -> anthillLeaf))
      .orElse(Option.when(declaredNotEmitted.contains(owner -> anthillLeaf))(
        Placement.Unplaceable(
          s"this file declares `$anthillLeaf` in package `$owner` in a position " +
          "Bootstrap emits no Scala type for (an abstract sort has no declaration " +
          "in the output), so the name is not in the emitted tree")))
      .orElse(types.exactPlacement(owner, anthillLeaf))

  /** Place a type declared in THIS file (WI-1067).
    *
    * Only a declaration in the EXACT mentioning package is visible by a bare Scala
    * name. The generated source uses one top-level `package a.b` clause; Scala 3 does
    * not thereby bring `a.Foo` into bare scope. An Anthill ancestor-package declaration
    * is still the selected declaration, but keeps its `_root_`-qualified spelling. A
    * unique declaration elsewhere in the same file is treated the same way. Multiple
    * unreachable declarations with one leaf are ambiguous and refused. A
    * default-package declaration cannot be named from a named package even with
    * qualification in Scala 3, so that case is refused too.
    *
    * THE TWO PACKAGES ARE ASKED TWO DIFFERENT QUESTIONS (WI-1081). The WALK is over the
    * namespace the mention is written in — anthill's own lookup chain — while "may this
    * be spelled BARE" is about the package the FILE declares, which is a Scala fact.
    * They coincide for every sort and entity and part for a namespace's `<Ns>Ops` trait;
    * asking `emittedPkg == owner` rather than "distance 0" is what states that, and it
    * keeps a trait emitted one package up from spelling a name bare that its own
    * `package` clause does not reach.
    */
  private def filePlacement(anthillLeaf: String): Option[Placement] =
    PackageNesting.from(writtenIn).iterator.flatMap { owner =>
      fileTypes.get(owner -> anthillLeaf).map { known =>
        // Only the exact EMITTED package is bare. An ancestor selected by Anthill's
        // package chain deliberately retains its fully-qualified Scala spelling:
        // top-level Scala package clauses do not create a lexical enclosing scope.
        if owner == emittedPkg then
          Placement.Known(Names.scalaTypeName(anthillLeaf), known.kinds): Placement
        else known: Placement
      }.orElse {
        Option.when(declaredNotEmitted.contains(owner -> anthillLeaf)) {
          Placement.Unplaceable(
            s"this file declares `$anthillLeaf` in package `$owner` in a position " +
            "Bootstrap emits no Scala type for (an abstract sort has no declaration " +
            "in the output), so the name is not in the emitted tree")
        }
      }
    }.nextOption().orElse {
      val elsewhere = fileTypes.iterator.collect {
        case ((owner, leaf), known) if leaf == anthillLeaf => owner -> known
      }.toVector.sortBy(_._1)
      elsewhere match
        case Vector() => None
        case Vector((owner, _)) if owner.isEmpty && emittedPkg.nonEmpty =>
          Some(Placement.Unplaceable(
            s"this file declares `$anthillLeaf` in the empty package, but this " +
            s"declaration is emitted into named package `$emittedPkg`; Scala 3 does not make " +
            "default-package members reachable from a named package"))
        case Vector((_, known)) => Some(known)
        case many =>
          Some(Placement.Unplaceable(
            s"this file declares `$anthillLeaf` in several packages " +
            s"(${many.map(_._1).map(p => if p.isEmpty then "<empty>" else p).mkString(", ")}), " +
            s"none visible from `$writtenIn`; a bare mention cannot choose one"))
    }

  /** What THIS FILE says about the name, where that displaces the auto-imported
    * prelude — and every such answer is a refusal.
    *
    * BEFORE the prelude table and not after it, which is anthill's own scoping rule:
    * a local declaration and an explicit `import` both shadow the auto-import. Read
    * the other way round the emission is silently wrong rather than merely refused —
    * a project writing `import my.lib.{Numeric}` got `_root_.anthill.prelude.Numeric`,
    * a different library's type, compiled green. That mattered little while the
    * prelude table was six hand-picked names; WI-1060 derived it, so it is now every
    * sort the prelude emits and the collision surface is ten times wider.
    */
  private def shadowsThePrelude(anthillLeaf: String): Option[Placement] =
    importedFrom.get(anthillLeaf) match
      // AN IMPORT OF THE PRELUDE ITSELF IS NOT A SHADOW — it names the same
      // declaration the auto-import would have found, and half the prelude writes
      // one (`cell.anthill`'s `import anthill.prelude.{Unit, Modifiable, …}`). Only
      // an import from ELSEWHERE displaces the table, and then it is unreachable.
      case Some(from) if from != writtenIn && from != types.autoImportPackage =>
        // Provably wrong: the import says the name lives in ANOTHER package, and
        // Bootstrap emits no Scala `import`, so the bare mention cannot reach it.
        // `Term` / `NodeOccurrence` from `anthill.reflect` are this case, and
        // emitting the Scala import would only move the failure — the reflect
        // namespace is outside the generated closure.
        Some(Placement.Unplaceable(
          s"`$anthillLeaf` is imported from `$from`, but this declaration is emitted " +
          s"into package `$emittedPkg` and Bootstrap emits no Scala `import`, so a bare " +
          "mention cannot reach it"))
      case _ => None

  /** Nothing Bootstrap can see places the name, and nothing it can see says the name
    * is wrong: it rides out qualified with this declaration's own package. */
  private def ambient(anthillLeaf: String): Placement =
    val scalaName = Names.scalaTypeName(anthillLeaf)
    Placement.Ambient(if writtenIn.isEmpty then scalaName else s"$writtenIn.$scalaName")

  /** The host type for a scalar the RENDERER needs BY NAME — today only `Unit`, for
    * the empty tuple, which has no written occurrence to place.
    *
    * Absent is a refusal and not a bare `Unit` fallback: a profile whose `type_map`
    * drops the entry has broken a rendering path, and the fallback is how that would
    * ship looking emitted. LOCATED like every other refusal, and on [[TypeScope]]
    * rather than on [[ScalaTypes]] for that reason alone — the table has no
    * declaration and no span, and an unlocated throw would say only that the profile
    * is wrong, not which emission asked it for what.
    *
    * A [[ProfileError]] AND NOT A [[BootstrapError]] (WI-1080 review): a missing entry
    * is a fact about the PROFILE, so it is fatal rather than collected as this
    * declaration's refusal. `decl` is in the message because it says which rendering
    * path the broken entry defeated first, not because the declaration is at fault —
    * every other one that renders an empty tuple would fail the same way, and
    * reporting the same configuration fault once per declaration while returning a
    * tree built against it is exactly the "emit anyway" this backend refuses. */
  def requiredScalar(anthillLeaf: String, why: String): String =
    types.hostScalars.getOrElse(anthillLeaf, throw ProfileError(
      s"$decl: the profile's type_map declares no `$anthillLeaf` entry, and $why " +
      s"needs one; known scalars: ${types.hostScalars.keys.toVector.sorted.mkString(", ")}",
      declSpan))
