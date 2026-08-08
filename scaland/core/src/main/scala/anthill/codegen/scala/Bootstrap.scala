package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.*
import anthill.span.Span

import scala.collection.mutable.ArrayBuffer

/** A single Scala source file emitted by the bootstrap codegen. */
case class GeneratedFile(relPath: String, contents: String)

/** A declaration Bootstrap REFUSES, because no Scala spelling of it would mean
  * what the anthill declaration means (WI-940).
  *
  * `(message, span)` and `render = span.render(message)`, the shape
  * [[anthill.parse.ParseError]] and [[anthill.load.LoadError]] already have: the
  * ONE located renderer, so which STAGE found a fault cannot change how its
  * location reads (WI-947). `render` is also `getMessage`/`toString`, for the
  * reason it is on those two — nothing in this tree calls a renderer by name, so
  * one reachable only by name is a seam with no user.
  *
  * THROWN rather than collected, which is the one place it differs from them:
  * `generate` returns `IndexedSeq[GeneratedFile]` and has no production caller
  * yet (only tests), so a diagnostic channel would be a signature invented for
  * nobody. What matters is that the case is loud — emitting the nearest legal
  * Scala instead is exactly the silent-wrong-output this ticket removes.
  */
case class BootstrapError(message: String, span: Span) extends RuntimeException:
  def render: String = span.render(message)
  override def getMessage: String = render
  override def toString: String = render

/** Anthill → Scala bootstrap codegen (parse-IR-driven, no KB).
  *
  * v1 of the scala-gen pipeline per proposal 034. Walks a [[ParsedFile]]
  * and emits an sbt-shaped output tree:
  *
  *   src/main/scala/<package-path>/<Sort>.scala
  *   src/test/scala/<package-path>/<Sort>Laws.scala
  *
  * Mapping rules per `docs/scala-forward-mapping.md` §2; default
  * `scala_std` profile. Generated traits / enums / case classes
  * compile as-is with no method bodies (Scala traits accept abstract
  * members). Concrete companion objects with bodies are deferred to
  * the KB-driven `anthill-scala-gen` (proposal 034 §anthill-scala-gen).
  *
  * Out of scope for v1: KB-driven decisions, `Quoted` body inlining,
  * `scala_caps` / `scala_cats_effect` / `scala_zio` profiles,
  * `@anthillName` round-trip annotations, ScalaCheck arbitrary
  * derivation. Tests under `<Sort>Laws.scala` compile but invoke
  * `???` in their `Arbitrary` slot — opt out via `--skip-laws`.
  */
object Bootstrap:

  /** Generate Scala files from one parsed `.anthill` file. The package
    * path and per-file output is determined by the file's top-level
    * namespace (or sort/entity name when no namespace is present).
    */
  def generate(pf: ParsedFile): IndexedSeq[GeneratedFile] =
    val files = ArrayBuffer.empty[GeneratedFile]
    val env = fileEnv(pf.symbols, pf.items)
    pf.items.foreach {
      case Item.NamespaceItem(ns) => emitNamespace(pf.symbols, ns, "", env, Map.empty, files)
      case Item.SortWithBodyItem(s) => emitSort(pf.symbols, s, "", env, Map.empty, files)
      case Item.EntityItem(e) =>
        emitStandaloneEntity(pf.symbols, e, "", env, Map.empty, files)
      case _ =>
    }
    files.toIndexedSeq

  /** What Bootstrap knows about a whole parsed FILE, before any one declaration:
    * which types it EMITS (with their arity), and which names it declares and
    * emits nothing for. The second is not the complement of the first — it is the
    * set Bootstrap can point at and say "the emitted tree has no such type"
    * (WI-1055 B1).
    */
  private case class FileEnv(types: Map[String, Int], declaredNotEmitted: Set[String]):

    /** A [[TypeScope]] for one declaration, with the two file-wide fields filled
      * in. A factory rather than three call sites spelling `fileTypes = env.types,
      * declaredNotEmitted = env.declaredNotEmitted` — those two are the file's
      * answer and never the declaration's, so a call site that could vary them
      * would be a way for one emission to disagree with the rest of its file. */
    def scopeAt(
      decl: String, declSpan: Span, pkg: String, imports: Map[String, String],
      enclosing: Option[EnclosingSort] = None,
      typeParams: Map[String, String] = Map.empty
    ): TypeScope =
      TypeScope(decl, declSpan, pkg, enclosing, typeParams, types, imports,
        declaredNotEmitted)

  /** The name environment of one parsed file, in ONE walk.
    *
    * `types` is keyed on what is EMITTED and not on what is declared, which is the
    * whole point: `declaredNotEmitted` holds the names this file declares and
    * Bootstrap emits nothing for, so a member typed by one is refused rather than
    * shipped naming a type that is not in the tree.
    *
    * An `AbstractSortItem` at NAMESPACE level is that second case — `sort Type = ?`
    * in sort.anthill, an opaque handle whose Scala spelling would be an `opaque
    * type`, which needs an enclosing object rather than a package. (Inside a SORT
    * the same item is a type PARAMETER, which is why only the namespace walk
    * collects it.)
    *
    * THE DECLARATION IS STILL DROPPED SILENTLY, and only its USES are loud. That
    * asymmetry is deliberate but is a debt, not a design: refusing the whole file
    * on an un-emittable declaration would take sort.anthill and effects.anthill out
    * of the tree even when nothing refers to the name, and the measured trade for
    * the analogous choice ([[Placement.Ambient]]) was thirteen files. An abstract
    * sort nothing references therefore produces no output and no diagnostic.
    *
    * COUPLED TO THE EMIT WALK BY HAND: the three arms here are the same three
    * `generate`/`emitNamespace` dispatch on, and the `case _` means `-Wconf:id=E029`
    * cannot catch them drifting. An `Item` kind that gains an emission without
    * being taught here would fall through to `Placement.Ambient`, which performs no
    * arity check — quietly losing the guarantee WI-1055 exists for, on exactly the
    * type it should cover.
    */
  private def fileEnv(sym: SymbolTable, items: Iterable[Item]): FileEnv =
    items.foldLeft(FileEnv(Map.empty, Set.empty)) {
      case (acc, Item.NamespaceItem(ns)) =>
        val inner = fileEnv(sym, ns.items)
        FileEnv(acc.types ++ inner.types,
          acc.declaredNotEmitted ++ inner.declaredNotEmitted)
      case (acc, Item.SortWithBodyItem(s)) if !s.isTypeParam =>
        acc.copy(types = acc.types + (sym.name(s.name.last) -> sortTypeParams(sym, s).length))
      case (acc, Item.EntityItem(e)) =>
        acc.copy(types = acc.types + (sym.name(e.name.last) -> 0))
      case (acc, Item.AbstractSortItem(s)) =>
        acc.copy(declaredNotEmitted = acc.declaredNotEmitted + sym.name(s.name.last))
      case (acc, _) => acc
    }

  /** One refusal for a NAMED requirement slot, wherever it is written.
    *
    * WI-840 (proposal 058 §4.7): a named slot — `requires O: Ord[T]` on a sort,
    * `requires lo: Ord[T]` on an operation — is a type parameter whose value is a
    * chosen WITNESS. `docs/scala-forward-mapping.md` §2.7 states ONE rule for both
    * positions ("a `requires` can be either a type-class supertrait or a `using`
    * context parameter"), and a named slot is unambiguously the second; Bootstrap
    * emits no `using` clause, and WI-1022 owns that half.
    *
    * ONE site because it is one rule. Held apart, the sort and operation arms
    * immediately drifted in wording, which is how a reader comes to believe two
    * decisions were made.
    */
  private[codegen] def refuseNamedRequirementSlot(
    subject: String, slot: String, span: Span
  ): Nothing =
    throw BootstrapError(
      s"$subject declares the named requirement slot `$slot`; §2.7 maps that to a " +
      "`using` context parameter, which Bootstrap does not emit, and a plain type " +
      "parameter would be a phantom nothing binds",
      span)

  /** Anthill leaf name → the package an `import` brings it from, accumulated
    * down the nesting: a sort's imports add to its namespace's. */
  private def importedNames(
    sym: SymbolTable, imports: IndexedSeq[Import], outer: Map[String, String]
  ): Map[String, String] =
    imports.foldLeft(outer) { (acc, imp) =>
      val path = imp.path.segments.map(sym.name)
      imp.kind match
        case ImportKind.Selective(names) =>
          acc ++ names.map(n => sym.name(n.last) -> path.mkString("."))
        case ImportKind.Plain if path.length > 1 =>
          acc + (path.last -> path.dropRight(1).mkString("."))
        // A wildcard names nothing in particular, and a single-segment plain
        // import names a package rather than a member; neither places a name.
        case _ => acc
    }

  /** A sort's type parameters, in declaration order.
    *
    * BOTH desugarings of a head parameter, which is WI-1055 A2: the parser turns
    * a SIMPLE parameter `V` into an `AbstractSort` (`sort V = ?`) and a
    * HIGHER-KINDED one `M[T]` into a `SortWithBody` MARKED `isTypeParam`
    * (`AnthillParser.desugarSortTypeParam`, mirroring rustland). Only the first
    * was collected, so `sort anthill.prelude.Monad[M[T]]` emitted `trait Monad:`
    * with no parameters at all and every member mentioning `M` was unbound.
    *
    * A nested `sort F { … }` that is NOT marked stays a concrete nested sort and
    * is not a parameter — the same distinction the loader draws.
    */
  private def sortTypeParams(sym: SymbolTable, sort: SortWithBody): IndexedSeq[TypeParamDecl] =
    sort.items.collect {
      case Item.AbstractSortItem(s) =>
        TypeParamDecl(sym.name(s.name.last), IndexedSeq.empty)
      case Item.SortWithBodyItem(s) if s.isTypeParam =>
        TypeParamDecl(sym.name(s.name.last), sortTypeParams(sym, s))
    }

  /** One type parameter, as anthill wrote it and as Scala binds it.
    *
    * The BINDING form and the USE form differ for a higher-kinded parameter:
    * `M[T]` binds as `M[_]` and is used as `M`. Scala needs the kind at the
    * binder and forbids it at every mention.
    */
  private case class TypeParamDecl(anthillName: String, members: IndexedSeq[TypeParamDecl]):
    val scalaName: String = Names.scalaTypeName(anthillName)
    /** `T`, `M[_]`, `F[_[_]]` — what goes between the sort's brackets. */
    def decl: String = scalaName + kindSuffix
    /** The same kind with the name erased, for a nested binder position. */
    private def anonymousKind: String = "_" + kindSuffix
    private def kindSuffix: String =
      if members.isEmpty then ""
      else members.map(_.anonymousKind).mkString("[", ", ", "]")

  /** Project-level `build.sbt` for an output tree. Bootstrap is per-file, so
    * callers fold many `generate()` results into one tree and call this once
    * to write the project-global file — avoids the per-file last-write-wins
    * footgun.
    *
    * `scalaVersion` is a PARAMETER and has no default on purpose. Its source of truth is
    * the `scala_std` `LanguageMapping`'s `language_version`, read by
    * [[ScalaProfile.languageVersion]] — and a default here would be a second answer to a
    * question the profile already answers, silently winning whenever a caller forgot to
    * ask. This is not the same question as `build.sbt`'s `scala3Version`, which is what
    * scaland itself is COMPILED WITH; they agree today but are free not to.
    *
    * `Bootstrap` still reads no KB (proposal 034) — the caller resolves the profile and
    * passes the value in, which is what keeps this a pure function of its inputs.
    */
  def buildSbt(scalaVersion: String): GeneratedFile =
    GeneratedFile("build.sbt", s"scalaVersion := \"$scalaVersion\"\n")

  // ── Namespace ───────────────────────────────────────────────────

  private def emitNamespace(
    sym: SymbolTable, ns: Namespace, packagePath: String, env: FileEnv,
    outerImports: Map[String, String], out: ArrayBuffer[GeneratedFile]
  ): Unit =
    val (nsParentPkg, nsLeaf) =
      val segs = ns.name.segments.map(sym.name)
      if segs.length == 1 then (packagePath, segs.head)
      else
        val parent = segs.dropRight(1).mkString(".")
        val pkg = if packagePath.isEmpty then parent else s"$packagePath.$parent"
        (pkg, segs.last)
    val childPath = if nsParentPkg.isEmpty then nsLeaf else s"$nsParentPkg.$nsLeaf"
    val imports = importedNames(sym, ns.imports, outerImports)
    ns.items.foreach {
      case Item.NamespaceItem(child) =>
        emitNamespace(sym, child, childPath, env, imports, out)
      case Item.SortWithBodyItem(s) => emitSort(sym, s, childPath, env, imports, out)
      case Item.EntityItem(e) => emitStandaloneEntity(sym, e, childPath, env, imports, out)
      case _ => // facts/rules at namespace level — TODO in KB-driven gen
    }
    // Top-level operations inside a namespace land in a <NsName>Ops trait.
    val nsOps = ns.items.flatMap {
      case Item.OperationItem(op) => Seq(op)
      case Item.OperationBlockItem(b) => b.entries
      case _ => Seq.empty
    }
    if nsOps.nonEmpty then
      val typeName = Names.scalaTypeName(nsLeaf) + "Ops"
      val scope = env.scopeAt(
        s"namespace `$nsLeaf`", ns.name.span, nsParentPkg, imports)
      val sb = StringBuilder()
      if nsParentPkg.nonEmpty then sb ++= s"package $nsParentPkg\n\n"
      sb ++= s"trait $typeName:\n"
      nsOps.foreach(op => sb ++= s"  ${OpGen.renderAbstract(op, scope, sym)}\n")
      out += GeneratedFile(
        relPath = s"src/main/scala/${pathToDir(nsParentPkg)}$typeName.scala",
        contents = sb.toString)

  // ── Sort (trait or enum) ────────────────────────────────────────

  private def emitSort(
    sym: SymbolTable, sort: SortWithBody, packagePath: String, env: FileEnv,
    outerImports: Map[String, String], out: ArrayBuffer[GeneratedFile]
  ): Unit =
    // Multi-segment top-level decl like `enum anthill.prelude.Option`:
    // treat the prefix as the package path and the last segment as the type.
    val (effectivePkg, sortName) = splitPath(sym, sort.name, packagePath)
    val typeParams = sortTypeParams(sym, sort)
    val tpStr =
      if typeParams.isEmpty then "" else typeParams.map(_.decl).mkString("[", ", ", "]")
    val scope = env.scopeAt(
      s"sort `${sym.name(sort.name.last)}`", sort.name.span, effectivePkg,
      importedNames(sym, sort.imports, outerImports),
      enclosing = Some(EnclosingSort(
        sym.name(sort.name.last), sortName, typeParams.map(_.scalaName))),
      typeParams = typeParams.map(p => p.anthillName -> p.scalaName).toMap)
    val requires = sort.items.collect {
      case Item.RequiresDeclItem(r) =>
        // `sortedset.anthill` shipped the un-refused form: `SortedSet[T, O]` with
        // a phantom `O` that no member could ever bind, and every use of the type
        // inside it an arity error.
        r.binder.foreach(b =>
          refuseNamedRequirementSlot(
            s"sort `${sym.name(sort.name.last)}`", sym.name(b.last), b.span))
        TypeGen.render(sym, r.typeExpr, scope.at(s"$sortName's `requires`", r.span))
    }
    val ops = sort.items.flatMap {
      case Item.OperationItem(op) => Seq(op)
      case Item.OperationBlockItem(b) => b.entries
      case _ => Seq.empty
    }
    val shape = shapeOf(sym, sort.name, sort.items.collect { case Item.EntityItem(e) => e })

    // Rules + constraints are NOT emitted from bootstrap. Their bodies
    // are semantic (rule term → ScalaCheck Boolean expression); the
    // parse-IR-only path can't render them, and emitting a placeholder
    // (Prop.passed / ???) is either vacuously green or a spec violation
    // (see docs/scala-forward-mapping.md §1, §2.9). Laws emission is
    // owned by the KB-driven anthill-scala-gen.
    val mainSrc = renderMainSort(sortName, tpStr, typeParams, requires, ops, shape,
      effectivePkg, scope, sym)
    out += GeneratedFile(
      relPath = s"src/main/scala/${pathToDir(effectivePkg)}$sortName.scala",
      contents = mainSrc)

  // ── Standalone entity → case class ──────────────────────────────

  private def emitStandaloneEntity(
    sym: SymbolTable, e: Entity, packagePath: String, env: FileEnv,
    imports: Map[String, String], out: ArrayBuffer[GeneratedFile]
  ): Unit =
    val (effectivePkg, typeName) = splitPath(sym, e.name, packagePath)
    val pkg = if effectivePkg.isEmpty then "" else s"package $effectivePkg\n\n"
    val scope = env.scopeAt(
      s"entity `${sym.name(e.name.last)}`", e.name.span, effectivePkg, imports)
    val src = pkg +
      renderCaseClass(sym, typeName, tpStr = "", e.fields, extendsClause = "", scope)
    out += GeneratedFile(
      relPath = s"src/main/scala/${pathToDir(effectivePkg)}$typeName.scala",
      contents = src)

  // ── Sort shape (§6.3) ───────────────────────────────────────────

  /** Which ONE Scala declaration a sort body maps to.
    *
    * The three are DISJOINT by construction — a sort picks exactly one, and each
    * carries what its renderer needs — which is what keeps an eponymous sort
    * from reaching Scala as a data type AND a nested case of itself. cpp-gen
    * states the same contract over its three emission bands (WI-931,
    * `classify_namespace`); this is the same rule in the other backend.
    */
  private enum SortShape:
    /** `sort V { entity V(…) }` — the constructor IS the sort (§6.3 / WI-926),
      * so ONE `case class V(…)` and no `V.V`. */
    case Record(ctor: Entity)
    /** Constructors named differently from the sort → `enum S: case C1 …`. */
    case Sum(ctors: IndexedSeq[Entity])
    /** No constructors → `trait S` carrying the abstract operations. */
    case Algebra

  /** Classify a sort body per §6.3.
    *
    * Eponymy is keyed on the ANTHILL name, which is what §6.3 says ("keyed on
    * the name matching") and not on the emitted one: `Names.scalaTypeName` is
    * many-to-one — `foo_bar` and `fooBar` share an image — so two anthill names
    * that merely converge in Scala are not one symbol.
    */
  private def shapeOf(
    sym: SymbolTable, sortName: Name, ctors: IndexedSeq[Entity]
  ): SortShape =
    val sortLeaf = sym.name(sortName.last)
    val hasEponymous = ctors.exists(c => sym.name(c.name.last) == sortLeaf)
    if ctors.isEmpty then SortShape.Algebra
    else if !hasEponymous then SortShape.Sum(ctors)
    else if ctors.length == 1 then SortShape.Record(ctors.head)
    else
      // §6.3 admits an eponymous variant ALONGSIDE siblings ("an eponymous
      // variant is a sibling of the other variants of its sort", WI-946), and
      // Scala has no spelling for it: the sum and one of its cases would have to
      // be one name in one scope. `enum S: case S` does NOT say that — it
      // declares the nested `S.S` that §6.3 rules out, which is the very defect
      // this classification exists to remove. Refused loudly rather than emitted
      // wrong. The tree ships no sort of this shape (measured across stdlib).
      throw BootstrapError(
        s"sort '$sortLeaf' has a constructor of its own name alongside " +
        s"${ctors.length - 1} other constructor(s). §6.3 makes those ONE symbol, " +
        "which Scala cannot spell as both a sum and one of its cases",
        sortName.span)

  // ── Helpers ─────────────────────────────────────────────────────

  /** Split a multi-segment name into (packagePath, leafTypeName). For
    * `anthill.prelude.Option` returns ("anthill.prelude", "Option"); for
    * a single-segment name the enclosing `packagePath` is used instead.
    */
  private def splitPath(
    sym: SymbolTable, name: anthill.parse.Name, packagePath: String
  ): (String, String) =
    if name.segments.length > 1 then
      val prefix = name.segments.dropRight(1).map(sym.name).mkString(".")
      val leaf = Names.scalaTypeName(sym.name(name.last))
      val pkg = if packagePath.isEmpty then prefix else s"$packagePath.$prefix"
      (pkg, leaf)
    else
      (packagePath, Names.scalaTypeName(sym.name(name.last)))

  private def pathToDir(packagePath: String): String =
    if packagePath.isEmpty then "" else s"${packagePath.replace('.', '/')}/"

  // ── Render: main sort source ────────────────────────────────────

  private def renderMainSort(
    sortName: String, tpStr: String, typeParams: IndexedSeq[TypeParamDecl],
    requires: IndexedSeq[String], ops: IndexedSeq[Operation], shape: SortShape,
    packagePath: String, scope: TypeScope, sym: SymbolTable
  ): String =
    val sb = StringBuilder()
    if packagePath.nonEmpty then sb ++= s"package $packagePath\n\n"
    // `requires` lands on the sort's PRINCIPAL declaration — the same placement
    // the sum branch has always used, not a new decision for the record branch.
    val ext = if requires.isEmpty then "" else s" extends ${requires.mkString(", ")}"
    // The sort's parameters as ARGUMENTS (`[T]`), against `tpStr`'s BINDERS
    // (`[M[_]]`) — an enum case that has to name its parent needs both forms.
    val tpArgs =
      if typeParams.isEmpty then "" else typeParams.map(_.scalaName).mkString("[", ", ", "]")
    shape match
      case SortShape.Record(ctor) =>
        // case class Sort[T](fields) — ONE declaration (§6.3 / WI-926 / WI-940).
        sb ++= renderCaseClass(sym, sortName, tpStr, ctor.fields, ext, scope)
        sb ++= renderOpsTrait(sortName, tpStr, ops, scope, sym)
      case SortShape.Sum(ctors) =>
        // enum Sort[T] { case C1(...); case C2 }
        sb ++= s"enum $sortName$tpStr$ext:\n"
        ctors.foreach { c =>
          val cName = Names.scalaTypeName(sym.name(c.name.last))
          val fields = renderFieldList(sym, c.fields, scope)
          // An UNPARAMETERIZED enum's nullary case takes no parameter list at all —
          // `case Red`, not `case Red()`. The record branch has neither form: a
          // `case class` always needs its `()`.
          if c.fields.isEmpty && typeParams.isEmpty then sb ++= s"  case $cName\n"
          else
            val uncovered = uncoveredParams(sym, c, typeParams)
            if uncovered.isEmpty then sb ++= s"  case $cName($fields)\n"
            else sb ++= s"  case $cName$tpStr($fields) extends $sortName$tpArgs\n"
        }
        sb ++= renderOpsTrait(sortName, tpStr, ops, scope, sym)
      case SortShape.Algebra =>
        // trait Sort[T] { abstract ops }
        //
        // A sort declaring NO operations takes no body at all — not a `:` with a comment
        // under it. Scala's indentation syntax requires a block opened with `:` to
        // contain at least one definition, so `trait Eq[T] extends PartialEq[T]:` over a
        // lone comment is `indented definitions expected, eof found`. stdlib's `Eq` is
        // exactly that shape (it adds only a law), and it shipped uncompilable behind a
        // green substring test until WI-1020's harness compiled the output.
        if ops.isEmpty then sb ++= s"trait $sortName$tpStr$ext\n"
        else
          sb ++= s"trait $sortName$tpStr$ext:\n"
          ops.foreach(op => sb ++= s"  ${OpGen.renderAbstract(op, scope, sym)}\n")
    sb.toString

  /** The enum parameters a case's FIELD TYPES do not mention.
    *
    * Scala infers an enum case's parent arguments from its fields, so a case that
    * leaves a parameter unmentioned is `cannot determine type argument for enum
    * parent class List, type parameter type T is invariant`. `List.scala` and
    * `Option.scala` both shipped that way, through their nullary `nil` / `none`.
    *
    * THE RULE IS COVERAGE, NOT ARITY. Keying on "the case has no fields" would be a
    * proxy: `entity left(v: L)` in a two-parameter `sort Either[L, R]` has a field
    * and still leaves `R` uninferable. No prelude sort has that shape today, which
    * is exactly why the proxy would have looked right.
    *
    * A case that needs it is REPARAMETERIZED — `case Nil[T]() extends List[T]` —
    * rather than pinned to the covariant idiom `extends List[Nothing]`: anthill's
    * `nil` IS polymorphic (a `List[T]` for every `T`) and an anthill sort declares
    * no variance, so `List[Nothing]` would be a value no `List[Int]` context could
    * take. A higher-kinded parameter needs no special case — `case Nil[M[_]]()
    * extends Foo[M]` is the same shape, which is why the binder list is `tpStr`,
    * the sort's own.
    */
  private def uncoveredParams(
    sym: SymbolTable, ctor: Entity, typeParams: IndexedSeq[TypeParamDecl]
  ): Set[String] =
    val mentioned = ctor.fields.foldLeft(Set.empty[String])((acc, f) =>
      acc ++ namesIn(sym, f.ty))
    typeParams.map(_.anthillName).toSet -- mentioned

  /** Every type name written anywhere inside a type expression. Over-approximates
    * on purpose — a name that is not a parameter simply never matches. */
  private def namesIn(sym: SymbolTable, te: TypeExpr): Set[String] = te match
    case TypeExpr.Simple(n) => Set(sym.name(n.last))
    case TypeExpr.Parameterized(n, bindings) =>
      bindings.foldLeft(Set(sym.name(n.last)))((acc, b) => acc ++ namesIn(sym, b.bound))
    case TypeExpr.TupleType(fields) =>
      fields.foldLeft(Set.empty[String])((acc, f) => acc ++ namesIn(sym, f._2))
    case TypeExpr.Arrow(params, ret, effects) =>
      (params ++ effects :+ ret).foldLeft(Set.empty[String])((acc, t) => acc ++ namesIn(sym, t))
    case TypeExpr.EffectRow(effects) =>
      effects.foldLeft(Set.empty[String])((acc, t) => acc ++ namesIn(sym, t))
    case TypeExpr.EffectGuarded(label, _) => namesIn(sym, label)
    // A logical variable and a value-in-type name no type. Both are refused by
    // `TypeGen` before an emission gets this far, so neither can hide a mention.
    case TypeExpr.Variable(_, _) | TypeExpr.Denoted(_) => Set.empty

  /** The `case class` a SINGLE-CONSTRUCTOR sort maps to — the one declaration
    * BOTH of §6.3's spellings produce.
    *
    * Shared by the standalone-`entity` sugar and by the eponymous long form so
    * that equivalence ("the sugar and the long form denote the same thing")
    * holds BY CONSTRUCTION, rather than by two renderers happening to agree —
    * which they did not: the long form emitted `enum Vec3: case Vec3(…)`, the
    * nested `Vec3.Vec3` §6.3 rules out (WI-940).
    */
  private def renderCaseClass(
    sym: SymbolTable, typeName: String, tpStr: String,
    fields: IndexedSeq[FieldDecl], extendsClause: String, scope: TypeScope
  ): String =
    s"case class $typeName$tpStr(${renderFieldList(sym, fields, scope)})$extendsClause\n"

  /** A constructor's fields as a Scala parameter list, without the parentheses —
    * one rendering for the `case class` and the `enum case`, which declare the
    * same schema and must not drift on how a field name or type reaches Scala. */
  private def renderFieldList(
    sym: SymbolTable, fields: IndexedSeq[FieldDecl], scope: TypeScope
  ): String =
    fields.map { f =>
      s"${Names.scalaFieldName(sym.name(f.name))}: ${TypeGen.render(sym, f.ty, scope)}"
    }.mkString(", ")

  /** The abstract operation contract of a sort that has constructors, or "" when
    * it declares none.
    *
    * It stays a SEPARATE `trait <Sort>Ops` — not members of the `case class` /
    * `enum` — and that is a Scala limit, not a reading of §6.3: bootstrap emits
    * signatures only (bodies are the KB-driven gen's, proposal 034), and Scala
    * has no abstract member in an instantiable `case class`. cpp-gen puts an
    * eponymous sort's operations inside the same `struct` (WI-931) because a C++
    * member declaration needs no definition; that collapse has no analogue here.
    * What §6.3 buys in Scala is therefore that the TYPE is one declaration —
    * there is no `Vec3.Vec3` — while the contract an implementation satisfies
    * keeps the `<Sort>Ops` name it already has for a sum sort
    * (docs/scala-forward-mapping.md §2.3).
    */
  private def renderOpsTrait(
    sortName: String, tpStr: String,
    ops: IndexedSeq[Operation], scope: TypeScope, sym: SymbolTable
  ): String =
    if ops.isEmpty then ""
    else
      val sb = StringBuilder()
      sb ++= s"\ntrait ${sortName}Ops$tpStr:\n"
      ops.foreach(op => sb ++= s"  ${OpGen.renderAbstract(op, scope, sym)}\n")
      sb.toString

end Bootstrap
