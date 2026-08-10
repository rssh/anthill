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
    *
    * `types` is a PARAMETER and has no default (WI-1060), for the reason
    * [[buildSbt]]'s `scalaVersion` has none: the scalar half of it is a decision
    * `scala_std.anthill` makes and the emitter has no business making a second
    * time. A default here would be that second answer, silently winning wherever a
    * caller forgot to ask — which is exactly how the hardcoded table this replaced
    * came to disagree with the fact for two releases. [[ScalaTypes.resolve]] is the
    * one way to build it; Bootstrap still reads no KB (proposal 034).
    */
  def generate(pf: ParsedFile, types: ScalaTypes): IndexedSeq[GeneratedFile] =
    val files = ArrayBuffer.empty[GeneratedFile]
    val env = FileEnv(fileTypes(pf.symbols, pf.items, ""), types)
    pf.items.foreach {
      case Item.NamespaceItem(ns) => emitNamespace(pf.symbols, ns, "", env, Map.empty, files)
      case Item.SortWithBodyItem(s) => emitSort(pf.symbols, s, "", env, Map.empty, files)
      case Item.EntityItem(e) =>
        emitStandaloneEntity(pf.symbols, e, "", env, Map.empty, files)
      case _ =>
    }
    files.toIndexedSeq

  /** What a set of files makes reachable by a BARE name: the types they emit into the
    * auto-import package, and the names they declare there with no emission at all
    * (WI-1060). [[ScalaTypes]]'s prelude half.
    */
  case class AutoImported(
    types: Map[String, Placement.Known], declaredNotEmitted: Set[String]
  )

  /** Every type a set of files EMITS INTO `autoImportPackage`, by anthill leaf name,
    * named as an outsider must write it (WI-1060).
    *
    * This is where [[ScalaTypes]]'s prelude half comes from, and the point is that it is
    * the SAME walk `generate` places a file's own names with — so the parameters a
    * consumer is checked against are the ones the declaring file actually emits, not a
    * hand-copy of them. The table this replaced was that copy, with nothing
    * cross-checking it and only three of its six entries pinned by a compile.
    *
    * `_root_`-ANCHORED, which qualification alone does not achieve: `anthill.prelude.Option`
    * is a RELATIVE path, so a project emitting into `myco` alongside a `myco.anthill`
    * namespace captures it. See [[ScalaTypes]].
    *
    * FILTERED BY PACKAGE, and it is the auto-import rule and not an optimization: what a
    * bare mention reaches is `anthill.prelude`'s own members. `algebra.anthill` writes
    * `namespace anthill.prelude.algebra` and `meta.anthill` writes `namespace
    * anthill.prelude.Meta`, so an unfiltered walk enters `Ring`, `VectorSpace` and
    * `Meta` — names anthill itself would not resolve without an explicit import,
    * and a project declaring its own `Ring` in a sibling file would silently emit
    * `_root_.anthill.prelude.algebra.Ring`. A nested namespace is simply skipped rather
    * than refused: it is a legitimate declaration that this question does not reach.
    *
    * A LEAF DECLARED TWICE with two different emissions is a refusal rather than a
    * last-wins: the caller passes a file set it claims is reachable by bare name, and two
    * answers to one bare name means it is not.
    *
    * WHAT IT CANNOT SEE is whether `generate` would refuse the declaring FILE. Seven
    * prelude files are refused today (the refusal-set test names them), and their sorts
    * are in this table with an arity and a `_root_` name although the emitted tree will
    * contain neither. Answering would mean emitting every file to build the table — and
    * the closure compile catches it one step later, as a missing type rather than a
    * wrong one. The entry is a promise about a file that must be in the emission set,
    * not a claim that it already is — and WI-1067 owns making that either true or
    * stated where something enforces it.
    */
  def emittedTypes(
    files: Iterable[ParsedFile], autoImportPackage: String = "anthill.prelude"
  ): AutoImported =
    files.foldLeft(AutoImported(Map.empty, Set.empty)) { (acc, pf) =>
      val here = fileTypes(pf.symbols, pf.items, "")
      val types = here.types.foldLeft(acc.types) { case (m, (leaf, t)) =>
        if t.pkg != autoImportPackage then m
        else
          // Annotated: a Scala 3 enum-case constructor widens to the enum type without
          // an expected type, and the map's value type is the CASE.
          val known: Placement.Known = Placement.Known(t.qualified, t.kinds)
          m.get(leaf).filter(_ != known).foreach(prev =>
            // LOCATED, like every other refusal Bootstrap raises (WI-947): the caller's
            // file set is 45 files on the real corpus, and a message naming neither is
            // unactionable. The span is the SECOND declaration — the one that could not
            // be added — because the first is already named by its emitted spelling.
            throw BootstrapError(
              s"`$leaf` is emitted twice by the file set and the two disagree: " +
              s"${prev.scalaName} with ${prev.kinds.written} parameter(s), then " +
              s"${known.scalaName} with ${known.kinds.written} — a bare mention cannot " +
              "mean both",
              t.span))
          m + (leaf -> known)
      }
      AutoImported(types, acc.declaredNotEmitted ++ here.declaredNotEmitted.collect {
        case (leaf, pkg) if pkg == autoImportPackage => leaf
      })
    }

  /** One type a file EMITS: where it goes, what Scala calls it, how it is parameterized,
    * and where it was written (which is what a cross-file refusal points at). */
  private case class EmittedType(pkg: String, scalaName: String, kinds: ParamKinds,
                                 span: Span):
    /** The spelling an outsider must write. */
    def qualified: String = if pkg.isEmpty then s"_root_.$scalaName" else s"_root_.$pkg.$scalaName"

  /** What Bootstrap knows about a whole parsed FILE, before any one declaration:
    * which types it EMITS (with their arity), and which names it declares and
    * emits nothing for. The second is not the complement of the first — it is the
    * set Bootstrap can point at and say "the emitted tree has no such type"
    * (WI-1055 B1).
    */
  private case class FileTypes(
    types: Map[String, EmittedType], declaredNotEmitted: Map[String, String]
  ):
    /** What [[TypeScope]] checks a written occurrence against, and emits BARE.
      *
      * The PACKAGE is dropped, which is right exactly when the file emits into ONE
      * package — every corpus file does, and `place` is reached with the bare leaf
      * spelled into whatever package the mentioning declaration goes to. A file
      * writing two namespaces breaks it: `namespace a { sort Foo } namespace b { sort
      * Bar { operation f(x: Foo) } }` emits a bare `Foo` into `package b`, where it does
      * not resolve. `EmittedType.pkg` is what would close it — by filtering to the
      * mentioning declaration's package and the packages ENCLOSING it, since Scala
      * packages nest lexically — and that is a rule with its own case to make, not a
      * line to add here. WI-1067. */
    def kindsByLeaf: Map[String, ParamKinds] = types.view.mapValues(_.kinds).toMap

  /** One file's own names, plus the project-wide tables every file is rendered against. */
  private case class FileEnv(decls: FileTypes, scalaTypes: ScalaTypes):

    private val fileTypeKinds: Map[String, ParamKinds] = decls.kindsByLeaf

    /** A [[TypeScope]] for one declaration, with the file-wide and project-wide fields
      * filled in. A factory rather than three call sites spelling them out — those are
      * the file's answer and never the declaration's, so a call site that could vary
      * them would be a way for one emission to disagree with the rest of its file. */
    def scopeAt(
      decl: String, declSpan: Span, pkg: String, imports: Map[String, String],
      enclosing: Option[EnclosingSort] = None,
      params: Map[String, ParamBinding] = Map.empty
    ): TypeScope =
      TypeScope(decl, declSpan, pkg, enclosing, params, fileTypeKinds, imports,
        decls.declaredNotEmitted.keySet, scalaTypes)

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
    * IT TRACKS THE PACKAGE (WI-1060) because [[emittedTypes]] reads the same walk from
    * OUTSIDE the file, where the bare leaf is not a spelling that reaches anything. The
    * two package derivations — a nested namespace's, a dotted declaration's — are
    * [[namespacePath]] and [[splitPath]], the same two `emitNamespace` and `emitSort`
    * use, so the table names the package the emitter writes to and cannot drift from it.
    * Where that package is itself wrong the table is wrong with it, and [[splitPath]]
    * has one such shape: a dotted declaration whose prefix REPEATS its enclosing
    * namespace (`namespace anthill.prelude { sort anthill.prelude.Concat … }`) is
    * emitted into `anthill.prelude.anthill.prelude`. No corpus file writes it, and the
    * auto-import filter keeps such an entry out of the cross-file table — but it is a
    * fault in `splitPath`, not something this walk corrects. WI-1067.
    *
    * COUPLED TO THE EMIT WALK BY HAND: the three arms here are the same three
    * `generate`/`emitNamespace` dispatch on, and the `case _` means `-Wconf:id=E029`
    * cannot catch them drifting. An `Item` kind that gains an emission without
    * being taught here would fall through to `Placement.Ambient`, which performs no
    * arity check — quietly losing the guarantee WI-1055 exists for, on exactly the
    * type it should cover.
    */
  private def fileTypes(
    sym: SymbolTable, items: Iterable[Item], packagePath: String
  ): FileTypes =
    items.foldLeft(FileTypes(Map.empty, Map.empty)) {
      case (acc, Item.NamespaceItem(ns)) =>
        // `++` LAST-WINS, and the same leaf declared in two namespaces of one file is
        // therefore silently one of them. It is not the cross-file conflict
        // [[emittedTypes]] refuses — there both entries claim the same bare mention,
        // here they are two legitimately different packages — but the flat table
        // cannot hold both, so `place` gets an arbitrary winner and checks a use site
        // against the wrong arity. The fix is the same one `kindsByLeaf` names: key
        // the file table by package (WI-1067). No corpus file writes two namespaces.
        val inner = fileTypes(sym, ns.items, namespacePath(sym, ns, packagePath).childPath)
        FileTypes(acc.types ++ inner.types,
          acc.declaredNotEmitted ++ inner.declaredNotEmitted)
      case (acc, Item.SortWithBodyItem(s)) if !s.isTypeParam =>
        val (pkg, scalaName) = splitPath(sym, s.name, packagePath)
        acc.copy(types = acc.types + (sym.name(s.name.last) ->
          EmittedType(pkg, scalaName, paramKinds(sortTypeParams(sym, s)), s.name.span)))
      case (acc, Item.EntityItem(e)) =>
        val (pkg, scalaName) = splitPath(sym, e.name, packagePath)
        acc.copy(types = acc.types + (sym.name(e.name.last) ->
          EmittedType(pkg, scalaName, ParamKinds.none, e.name.span)))
      case (acc, Item.AbstractSortItem(s)) =>
        // The PACKAGE is tracked for the same reason the emitted types' is: read from
        // outside the file, "which names are unreachable" is a question about one
        // package, and a nested namespace's abstract sort is not in it.
        acc.copy(declaredNotEmitted = acc.declaredNotEmitted +
          (sym.name(s.name.last) -> splitPath(sym, s.name, packagePath)._1))
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

  /** A sort's type parameters, in declaration order — ALL of them, effect
    * parameters included.
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
    *
    * IT KEEPS THE ERASED ONES (WI-1062) rather than filtering them out here, and
    * that is load-bearing: an `effects E = ?` parameter is absent from the emitted
    * type but PRESENT in every written occurrence of the sort, so a use site is
    * checked and erased against this list while the emission is built from
    * `paramKinds(...).keepTypeArgs(...)`. Filtering at the source would leave
    * nothing able to say that `Stream[Element, E]` is a correct two-argument
    * application.
    */
  private def sortTypeParams(sym: SymbolTable, sort: SortWithBody): IndexedSeq[TypeParamDecl] =
    sort.items.collect {
      case Item.AbstractSortItem(s) =>
        TypeParamDecl(sym.name(s.name.last), IndexedSeq.empty, isEffect = s.isEffectRow)
      case Item.SortWithBodyItem(s) if s.isTypeParam =>
        TypeParamDecl(sym.name(s.name.last), sortTypeParams(sym, s))
    }

  private def paramKinds(params: IndexedSeq[TypeParamDecl]): ParamKinds =
    ParamKinds(params.map(p => if p.isEffect then ParamKind.Effect else ParamKind.Type))

  /** One type parameter, as anthill wrote it and as Scala binds it.
    *
    * The BINDING form and the USE form differ for a higher-kinded parameter:
    * `M[T]` binds as `M[_]` and is used as `M`. Scala needs the kind at the
    * binder and forbids it at every mention.
    *
    * `isEffect` is the parse-IR mark `effects E = ?` carries (WI-1062). A
    * higher-kinded parameter is never one: `sort S[M[T, E]]` writes its members
    * with the binder grammar, which has no `effects` spelling — so `E` there is an
    * ordinary `sort E = ?`, which is exactly what makes delay.anthill's graded
    * monad refusable rather than silently erased.
    */
  private case class TypeParamDecl(
    anthillName: String, members: IndexedSeq[TypeParamDecl], isEffect: Boolean = false
  ):
    val scalaName: String = Names.scalaTypeName(anthillName)
    /** `T`, `M[_]`, `F[_[_]]` — what goes between the sort's brackets. */
    def decl: String = scalaName + kindSuffix
    /** The same kind with the name erased, for a nested binder position. */
    private def anonymousKind: String = "_" + kindSuffix
    private def kindSuffix: String =
      // No `emitted` filter, and that is the claim above rather than an omission:
      // a member cannot be an effect parameter, because the binder grammar has no
      // `effects` spelling to mark one with.
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

  /** Where one `namespace` header puts things: the package its own OPS trait is
    * emitted into, its leaf name, and the package path its members inherit.
    *
    * Extracted (WI-1060) because [[fileTypes]] walks the same nesting to record where
    * each emitted type lands, and a second copy of this arithmetic is how a derived
    * table comes to name a package the emitter never writes to.
    */
  private case class NamespacePath(parentPkg: String, leaf: String):
    def childPath: String = if parentPkg.isEmpty then leaf else s"$parentPkg.$leaf"

  private def namespacePath(
    sym: SymbolTable, ns: Namespace, packagePath: String
  ): NamespacePath =
    val segs = ns.name.segments.map(sym.name)
    if segs.length == 1 then NamespacePath(packagePath, segs.head)
    else
      val parent = segs.dropRight(1).mkString(".")
      NamespacePath(
        if packagePath.isEmpty then parent else s"$packagePath.$parent", segs.last)

  private def emitNamespace(
    sym: SymbolTable, ns: Namespace, packagePath: String, env: FileEnv,
    outerImports: Map[String, String], out: ArrayBuffer[GeneratedFile]
  ): Unit =
    val here = namespacePath(sym, ns, packagePath)
    val nsParentPkg = here.parentPkg
    val nsLeaf = here.leaf
    val childPath = here.childPath
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
    val written = sortTypeParams(sym, sort)
    // WI-1062: the sort's own `effects E = ?` parameters are erased (§2.8a). They
    // are dropped from every EMITTED list — the binders and the `EnclosingSort`
    // arguments — and kept as `kinds`, which is what a written occurrence of this
    // sort is checked and erased against. ONE reading of "which slots survive"
    // (`keepTypeArgs`) serves both, so the binder list and a use site's argument
    // list cannot drift out of positional sync.
    val kinds = paramKinds(written)
    val typeParams = kinds.keepTypeArgs(written)
    val tpStr =
      if typeParams.isEmpty then "" else typeParams.map(_.decl).mkString("[", ", ", "]")
    val scope = env.scopeAt(
      s"sort `${sym.name(sort.name.last)}`", sort.name.span, effectivePkg,
      importedNames(sym, sort.imports, outerImports),
      enclosing = Some(EnclosingSort(
        sym.name(sort.name.last), sortName, written.map(_.scalaName), kinds)),
      params = written.map(p =>
        p.anthillName ->
          (if p.isEffect then ParamBinding.Effect
           else ParamBinding.Scala(p.scalaName, p.members.length))).toMap)
    val requires = sort.items.collect {
      case Item.RequiresDeclItem(r) =>
        // `sortedset.anthill` shipped the un-refused form: `SortedSet[T, O]` with
        // a phantom `O` that no member could ever bind, and every use of the type
        // inside it an arity error.
        r.binder.foreach(b =>
          refuseNamedRequirementSlot(
            s"sort `${sym.name(sort.name.last)}`", sym.name(b.last), b.span))
        SortRequirement(r,
          TypeGen.render(sym, r.typeExpr, scope.at(s"$sortName's `requires`", r.span)))
    }
    val ops = sort.items.flatMap {
      case Item.OperationItem(op) => Seq(op)
      case Item.OperationBlockItem(b) => b.entries
      case _ => Seq.empty
    }
    val shape = shapeOf(sym, sort.name, sort.items.collect { case Item.EntityItem(e) => e })
    // `typeParams` and not `written`: the carrier is chosen from the parameters that
    // SURVIVE erasure, through the one reading of which those are (`keepTypeArgs`).
    // Reading `written` and filtering it again here would be a second answer to that
    // question, and a parameter kind that erases for some new reason would make the
    // two disagree — the carrier would name a binder the emitted type does not have.
    val req = requiresMapping(
      sym, sym.name(sort.name.last), shape, typeParams, ops, requires, scope)

    // Rules + constraints are NOT emitted from bootstrap. Their bodies
    // are semantic (rule term → ScalaCheck Boolean expression); the
    // parse-IR-only path can't render them, and emitting a placeholder
    // (Prop.passed / ???) is either vacuously green or a spec violation
    // (see docs/scala-forward-mapping.md §1, §2.9). Laws emission is
    // owned by the KB-driven anthill-scala-gen.
    val mainSrc = renderMainSort(sortName, tpStr, typeParams, req, ops, shape,
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

  /** One `requires` declaration of a sort, as written and as rendered. Both halves
    * are needed and neither derives the other: the rendered string is what an
    * `extends` clause or a field-type comparison uses, and the written `TypeExpr` is
    * what the carrier question below is asked of — a Scala string has lost which of
    * its arguments the anthill declaration bound where. */
  private case class SortRequirement(decl: RequiresDecl, rendered: String):
    def span: Span = decl.span

  /** What a sort's `requires` declarations become in the emitted declaration: the
    * `extends` clause, and the note recording every requirement that is NOT one. */
  private case class RequiresMapping(ext: String, note: String)

  /** Map a sort's `requires` declarations onto its emitted declaration (§2.7a).
    *
    * A SORT-LEVEL `requires` IS NOT AN IS-A CLAIM. Kernel spec §8.7: it "conditions
    * every provision, and supplies every body's evidence" — it is the requirement
    * DICTIONARY. The is-a claim is `provides`. So `requires` → `extends` is right
    * only where the two coincide, namely where the required spec's carrier slot is
    * bound to the declaring sort's OWN carrier (`sort Ord { sort T = ?; requires
    * Eq[T] }` — ops take `a: T`, so `T` is Ord's carrier, and `trait Ord[T] extends
    * Eq[T]` says what the declaration says).
    *
    * ON A SORT WITH CONSTRUCTORS IT NEVER COINCIDES (WI-1064): the sort IS the
    * carrier, so a requirement can only be over some other parameter.
    * `finite_combinators.anthill` writes `requires FiniteCollection[C = SrcC, …]`
    * over its SOURCE parameter, while its claim about itself is the `provides
    * FiniteCollection[C = FiniteMappedStream, …]` three lines below. The `extends`
    * was built from the first, because `emitSort` reads `RequiresDeclItem` and
    * NOTHING reads `ProvidesClauseItem` — the is-a claim falls through a `case _`.
    * Measured symptom: `class Fmapped needs to be abstract, since it has 9
    * unimplemented members`. The two data shapes therefore answer the carrier
    * question from the SHAPE and never consult [[carrierOf]]; that is exact, not an
    * approximation, and this ticket does not reopen it.
    *
    * WITHOUT CONSTRUCTORS THE CARRIER MUST BE READ (WI-1066), and until it was, the
    * shape stood in for it: every algebra sort got the supertrait unconditionally.
    * That is right wherever the requirement is over the carrier (`trait Ord[T]
    * extends Eq[T]`) and wrong wherever it is over an ELEMENT, a KEY or a SCALAR —
    * three measured emissions, `trait Set[T] extends Eq[T]` (set.anthill:13, whose
    * real claim is the `provides Eq[T = Set]` eleven lines below), `trait Map[K, V]
    * extends Eq[K]` (map.anthill:16) and `trait VectorSpace[V, F] extends Ring[F]`
    * (algebra.anthill:65). All three COMPILE — a trait tolerates unimplemented
    * members — so neither `ScalaCompile` nor the refusal-set test could see them;
    * what ships is an obligation on every implementor that `sort Set` never
    * declared, sitting beside Set's own `eq(a: Set, b: Set)` as an overload.
    *
    * NOT A SILENT DROP, in both directions: a data sort's undischarged requirement
    * is refused ([[checkDischarged]]), and an algebra sort's is RECORDED in the
    * emitted source ([[evidenceNote]]).
    */
  private def requiresMapping(
    sym: SymbolTable, sortLeaf: String, shape: SortShape,
    typeParams: IndexedSeq[TypeParamDecl], ops: IndexedSeq[Operation],
    requires: IndexedSeq[SortRequirement], scope: TypeScope
  ): RequiresMapping =
    if requires.isEmpty then RequiresMapping("", "")
    else
      shape match
        case SortShape.Algebra =>
          val carrier = carrierOf(sym, sortLeaf, typeParams, ops)
          val (supertraits, evidence) =
            requires.partition(r => isOverCarrier(sym, r, carrier))
          RequiresMapping(
            if supertraits.isEmpty then ""
            else s" extends ${supertraits.map(_.rendered).mkString(", ")}",
            evidence.map(r => evidenceNote(r.rendered, carrier)).mkString)
        case SortShape.Record(ctor) =>
          checkDischarged(sym, sortLeaf, IndexedSeq(ctor), requires, scope)
          RequiresMapping("", "")
        case SortShape.Sum(ctors) =>
          checkDischarged(sym, sortLeaf, ctors, requires, scope)
          RequiresMapping("", "")

  /** What an algebra sort's operations are an algebra OVER. */
  private enum Carrier:
    /** Self-representing (`Set`, `Map`): the operations take the SORT, and its type
      * parameters are content — element, key, value. */
    case TheSort(leaf: String)
    /** The sort's own carrier parameter (`FiniteCollection`'s `C`, `Ord`'s `T`). */
    case Param(param: String)

    /** The anthill name a requirement's argument must mention to be over it. */
    def mentionName: String = this match
      case TheSort(leaf) => leaf
      case Param(name) => name

    def describe: String = this match
      case TheSort(leaf) => s"`$leaf` itself (self-representing)"
      case Param(name) => s"its parameter `$name`"

  /** The carrier of a sort that declares no constructors.
    *
    * THIS IS RUSTLAND'S RULE, not a second one invented here:
    * `requires_edge_is_carrier_preserving` / `spec_is_self_representing`
    * (`kb/typing.rs`, WI-614) decide the identical question for member lending, and
    * the two halves below are theirs — "does ANY declared operation take the sort
    * ITSELF as a self-receiver parameter … a self-representing spec's carrier is the
    * spec, not a type-param", otherwise the carrier is "its first type-param — the
    * `provision_carrier_sort` convention, shared with the provides resolver".
    *
    * ANY operation, not the first: `set.anthill` declares `empty() -> Set` before
    * `insert(s: Set, x: T)`, and a RETURN of the sort is not a receiver. Reading only
    * the first operation would classify `Set` as carried by `T`.
    *
    * THE FIRST TYPE PARAMETER, not the one the operations happen to receive, and the
    * difference is what makes the no-operation sorts answerable rather than a special
    * case: `sort Eq` (eq.anthill:35) declares NO operations at all — it adds only the
    * reflexivity law — so it has no receiver to read, and `sort NonEq` /
    * `BoundedLattice` declare only nullary ones (`nonEqRefl() -> T`, `top() -> T`).
    * All three are carried by their sole parameter under this rule with nothing
    * special said about them, and all three keep the supertrait they had.
    *
    * THE PARAMETERS ARE THE EMITTED ONES, which is how an `effects E = ?` is skipped:
    * a carrier is a sort and an effect row is not one, and it does not survive to the
    * emitted type anyway (§2.8a). The caller passes the list `keepTypeArgs` already
    * built rather than the written one — see the note at the call site. No corpus sort
    * declares an effect parameter first, so this is a statement rather than a fix.
    *
    * IDENTITY IS BY LEAF NAME, as `shapeOf`'s eponymy test and `namesIn` also are, and
    * that is the anthill question rather than the Scala one: inside a sort body a bare
    * mention of the sort's own name means the sort (WI-1055 A3). It would misread a
    * parameter typed by a DIFFERENT sort of the same leaf name — which needs that other
    * sort to share the enclosing sort's own name, a shape no corpus file writes and one
    * anthill's own scoping resolves the other way. `TypeScope.place` is what draws the
    * distinction for rendering, and it cannot be borrowed here: it answers about the
    * EMISSION, so `sort String`'s `s: String` places as a host scalar although the
    * operation plainly receives the sort.
    *
    * NO TYPE PARAMETERS AT ALL ⇒ the sort itself, because there is nothing else it
    * could be. `sort Hello { requires anthill.cli.Main; operation main(…) }`
    * (rustland's CLI fixtures) is that shape. Rustland's function answers `false`
    * here — but it is asking whether the required spec lends its MEMBERS to this
    * receiver, and a marker spec has none to lend; the question here is whether the
    * emitted Scala type is a subtype, which for a marker is exactly what is meant.
    * See [[isOverCarrier]].
    */
  private def carrierOf(
    sym: SymbolTable, sortLeaf: String,
    typeParams: IndexedSeq[TypeParamDecl], ops: IndexedSeq[Operation]
  ): Carrier =
    val selfReceiver = ops.exists(_.params.exists(p => headName(sym, p.ty).contains(sortLeaf)))
    if selfReceiver then Carrier.TheSort(sortLeaf)
    else
      typeParams.headOption match
        case Some(p) => Carrier.Param(p.anthillName)
        case None => Carrier.TheSort(sortLeaf)

  /** The sort a written type APPLIES, or `None` where it names no sort at all (an
    * arrow, a tuple). Deliberately blind to the arguments — `s: Set` and a
    * hypothetical `s: Set[T = X]` are both a receiver of `Set`. */
  private def headName(sym: SymbolTable, te: TypeExpr): Option[String] = te match
    case TypeExpr.Simple(n) => Some(sym.name(n.last))
    case TypeExpr.Parameterized(n, _) => Some(sym.name(n.last))
    case _ => None

  /** Is this requirement over the declaring sort's own carrier — i.e. do the
    * requirement and the is-a claim coincide, so `extends` says what the declaration
    * says?
    *
    * A WEAKER TEST THAN THE REAL QUESTION, stated rather than hidden. The real
    * question is whether the required spec's CARRIER SLOT is bound to `carrier`, and
    * answering it means knowing which of `Ring[…]`'s parameters is its carrier — its
    * first, by the convention [[carrierOf]] quotes — which lives in the file that
    * declares `Ring`. Proposal 034 gives Bootstrap one `ParsedFile` and no KB; the
    * resolved type table (WI-1060) carries each prelude sort's parameter COUNT and
    * kinds, not their names, so it cannot say which named binding is the carrier
    * one. What is asked instead is whether the carrier is mentioned among the
    * requirement's arguments AT ALL.
    *
    * WHERE THE TWO DIFFER: a requirement naming the carrier in a NON-carrier slot
    * (`sort Foo { sort C = ?; sort E = ?; requires Bar[X = E, Y = C] }` where `Bar`'s
    * carrier is `X`) qualifies here and should not. No corpus file writes one, and
    * the weaker test is exact on every file that does: `Iterable[C = C, …]` mentions
    * `C`; `Ring[F]` does not mention `V`; `Eq[T]` inside `Set` does not mention
    * `Set`; `Eq[T = K]` inside `Map` does not mention `Map`.
    *
    * A REQUIREMENT WITH NO ARGUMENTS is over the carrier: it has no slot to be over
    * anything else. `requires anthill.cli.Main` is that shape — a marker with no
    * parameters and no members, whose whole content is the tag, and `trait Hello
    * extends Main` carries exactly the tag and nothing else. This is sound only
    * because a spec that DOES declare parameters cannot reach here written bare:
    * `TypeGen` refuses a partial application ("declares N type parameter(s), but 0
    * were written") before this runs. The one gap is a [[Placement.Ambient]] name,
    * whose declaration Bootstrap has not read and whose arity therefore goes
    * unchecked — the same blind spot every ambient name has.
    */
  private def isOverCarrier(
    sym: SymbolTable, req: SortRequirement, carrier: Carrier
  ): Boolean =
    val args = writtenArguments(req)
    args.isEmpty ||
      args.foldLeft(Set.empty[String])((acc, a) => acc ++ namesIn(sym, a))
        .contains(carrier.mentionName)

  /** The arguments a `requires` writes, or none where it writes a bare name.
    *
    * The two argument-less spellings answer as ONE — a `Simple` name is what the
    * parser mints for `requires Main`, and an empty binding list is what a
    * `Parameterized` would carry for the same thing — so the marker rule above cannot
    * depend on which node the grammar happened to build. (`parameterizedType` is a
    * `rep(1, …)`, so only the first occurs today; a guard admitting the other and then
    * refusing it would advertise a case it handles wrong.)
    */
  private def writtenArguments(req: SortRequirement): IndexedSeq[TypeExpr] =
    req.decl.typeExpr match
      case TypeExpr.Simple(_) => IndexedSeq.empty
      case TypeExpr.Parameterized(_, bindings) => bindings.map(_.bound)
      case _ =>
        // The grammar takes a full `typeExpr` after `requires`, so an arrow or a
        // tuple parses. Neither names a sort, so neither has a carrier slot and the
        // question above has no answer for it. Treating one as a marker emits `trait
        // Weird[T] extends (T) => T:`, which MEASURED does not even parse ("end of
        // toplevel definition expected but '=>' found") — so what the refusal buys is
        // not a rescued compile but a diagnostic AT the `requires` instead of a syntax
        // error in generated text, the same trade WI-1055 made everywhere else.
        throw BootstrapError(
          s"a `requires` must name a sort, and `${req.rendered}` does not, so it has " +
          "no carrier slot to compare against the declaring sort's carrier (§2.7a)",
          req.span)

  /** The comment an algebra sort's non-supertrait `requires` becomes.
    *
    * WHY A RECORD AND NOT A REFUSAL, which is the other thing it could be and is what
    * the DATA shape does. The two cases are not alike. A data sort's requirement has
    * exactly one place to ride in a signature-only emission — the type of a
    * constructor field — so one that rides nowhere is a loss with no remedy short of
    * §2.7's `using` half, and [[checkDischarged]] refuses it. An algebra sort's
    * requirement HAS a Scala home: `using` context parameters on the operations
    * (§2.7), which WI-1022 owns and Bootstrap does not emit yet. Refusing would take
    * set/map/algebra out of the emitted tree to punish a gap that is already
    * ticketed, and would delete the three emissions this rule exists to correct
    * rather than correct them.
    *
    * SO IT IS RECORDED, not dropped: the requirement is named in the emitted source
    * with what it is over and what would carry it. That keeps the reader of the
    * generated trait told about an obligation the type no longer states, and gives
    * WI-1022 a greppable list of every site it must fill. It is a comment and not a
    * type — it says so — and the emitted trait is genuinely weaker than the anthill
    * declaration until that ticket lands.
    *
    * ABOVE the declaration and not inside it: Scala's indentation syntax requires a
    * block opened with `:` to contain a definition, so a comment inside the body of
    * an operation-less sort is `indented definitions expected, eof found` — the same
    * trap [[renderMainSort]]'s `ops.isEmpty` arm exists for.
    */
  private def evidenceNote(rendered: String, carrier: Carrier): String =
    // The requirement gets its own line: it is the only part of this whose length
    // varies, so wrapping the rest by hand stays honest as the name grows.
    s"// `requires $rendered`\n" +
    "//   is EVIDENCE, not a supertype claim (§2.7a, kernel §8.7). This sort's carrier is\n" +
    s"//   ${carrier.describe}, and the requirement is not over it. What carries\n" +
    "//   it is §2.7's `using` context parameter, which Bootstrap does not emit (WI-1022).\n"

  /** Refuse a data sort's `requires` that the emitted tree would not carry.
    *
    * The question is asked of the EMISSION and not of the source, which is what
    * makes it the right question: the requirement survives when a constructor field
    * is TYPED BY it, so the evidence reaches Scala as that field's type. Both
    * corpus instances are exactly that — `requires FiniteCollection[C = SrcC,
    * Element = Src, E = ES]` beside `entity fmapped(source: FiniteCollection[C =
    * SrcC, Element = Src, E = ES], …)` — and there the omitted `extends` costs the
    * emitted tree nothing. Rendering through the SAME `scope` the field list uses
    * (`at` varies only the diagnostic label) is what makes the two comparable.
    *
    * PER CONSTRUCTOR, not per sort. Over the flattened field list of a sum, one
    * constructor carrying the requirement would discharge it for its siblings, and
    * a sibling that carries it nowhere is the silent drop this exists to prevent.
    *
    * CONTAINMENT, not equality, and bounded on the left so `MyWalk[T]` cannot
    * discharge `Walk[T]`. A field is often the requirement NESTED — `sources:
    * List[T = Walk[…]]` renders `_root_.anthill.prelude.List[Walk[SrcC, Src]]` —
    * and whole-string equality refused those, which aborts `generate` and takes
    * every other sort in the file with it.
    *
    * TWO LIMITS, both real and neither reached by the corpus. Effect arguments
    * erase before rendering (§2.8a), so a field carrying a DIFFERENT row compares
    * equal to the requirement — the check is blind in exactly that slot.
    * `Names.scalaTypeName` is many-to-one, so `requires foo_bar[T]` is discharged
    * by a field `x: fooBar[T]`. Both are the price of asking the question of the
    * rendered output; asking it of the parse IR instead would be asking about a
    * type the emission may not carry.
    */
  private def checkDischarged(
    sym: SymbolTable, sortLeaf: String, ctors: IndexedSeq[Entity],
    requires: IndexedSeq[SortRequirement], scope: TypeScope
  ): Unit =
    requires.foreach { req =>
      val rendered = req.rendered
      val occurrence = java.util.regex.Pattern.compile(
        s"(?<![\\w.])${java.util.regex.Pattern.quote(rendered)}")
      ctors.foreach { ctor =>
        val carried = ctor.fields.exists(f =>
          occurrence.matcher(TypeGen.render(sym, f.ty, scope)).find())
        if !carried then
          throw BootstrapError(
            s"sort `$sortLeaf` has constructors, so its `requires $rendered` is " +
            "evidence supplied to bodies (kernel §8.7) and not a claim about the " +
            s"type — and constructor `${sym.name(ctor.name.last)}` has no field " +
            "typed by it, so the emitted declaration would carry the requirement " +
            "nowhere. §2.7's other half maps it to a `using` context parameter, " +
            "which Bootstrap does not emit (WI-1022)",
            req.span)
      }
    }

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
    req: RequiresMapping, ops: IndexedSeq[Operation], shape: SortShape,
    packagePath: String, scope: TypeScope, sym: SymbolTable
  ): String =
    val sb = StringBuilder()
    if packagePath.nonEmpty then sb ++= s"package $packagePath\n\n"
    // The `requires` mapping arrives ALREADY DECIDED ([[requiresMapping]]), rather
    // than being derived from `requires` here: the three branches below share one
    // answer, and while they shared one DERIVATION the algebra sort's reading was
    // applied to the two data shapes as well (WI-1064).
    val ext = req.ext
    sb ++= req.note
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
