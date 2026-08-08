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
    pf.items.foreach {
      case Item.NamespaceItem(ns) => emitNamespace(pf.symbols, ns, packagePath = "", files)
      case Item.SortWithBodyItem(s) => emitSort(pf.symbols, s, packagePath = "", files)
      case Item.EntityItem(e) => emitStandaloneEntity(pf.symbols, e, packagePath = "", files)
      case _ =>
    }
    files.toIndexedSeq

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
    sym: SymbolTable, ns: Namespace, packagePath: String,
    out: ArrayBuffer[GeneratedFile]
  ): Unit =
    val (nsParentPkg, nsLeaf) =
      val segs = ns.name.segments.map(sym.name)
      if segs.length == 1 then (packagePath, segs.head)
      else
        val parent = segs.dropRight(1).mkString(".")
        val pkg = if packagePath.isEmpty then parent else s"$packagePath.$parent"
        (pkg, segs.last)
    val childPath = if nsParentPkg.isEmpty then nsLeaf else s"$nsParentPkg.$nsLeaf"
    ns.items.foreach {
      case Item.NamespaceItem(child) => emitNamespace(sym, child, childPath, out)
      case Item.SortWithBodyItem(s) => emitSort(sym, s, childPath, out)
      case Item.EntityItem(e) => emitStandaloneEntity(sym, e, childPath, out)
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
      val sb = StringBuilder()
      if nsParentPkg.nonEmpty then sb ++= s"package $nsParentPkg\n\n"
      sb ++= s"trait $typeName:\n"
      nsOps.foreach(op => sb ++= s"  ${OpGen.renderAbstract(op, IndexedSeq.empty, sym)}\n")
      out += GeneratedFile(
        relPath = s"src/main/scala/${pathToDir(nsParentPkg)}$typeName.scala",
        contents = sb.toString)

  // ── Sort (trait or enum) ────────────────────────────────────────

  private def emitSort(
    sym: SymbolTable, sort: SortWithBody, packagePath: String,
    out: ArrayBuffer[GeneratedFile]
  ): Unit =
    // Multi-segment top-level decl like `enum anthill.prelude.Option`:
    // treat the prefix as the package path and the last segment as the type.
    val (effectivePkg, sortName) = splitPath(sym, sort.name, packagePath)
    val typeParams = sort.items.collect {
      case Item.AbstractSortItem(s) => sym.name(s.name.last)
    }
    val tpStr = if typeParams.isEmpty then "" else typeParams.mkString("[", ", ", "]")
    val requires = sort.items.collect {
      case Item.RequiresDeclItem(r) => TypeGen.render(sym, r.typeExpr)
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
      effectivePkg, sym)
    out += GeneratedFile(
      relPath = s"src/main/scala/${pathToDir(effectivePkg)}$sortName.scala",
      contents = mainSrc)

  // ── Standalone entity → case class ──────────────────────────────

  private def emitStandaloneEntity(
    sym: SymbolTable, e: Entity, packagePath: String,
    out: ArrayBuffer[GeneratedFile]
  ): Unit =
    val (effectivePkg, typeName) = splitPath(sym, e.name, packagePath)
    val pkg = if effectivePkg.isEmpty then "" else s"package $effectivePkg\n\n"
    val src = pkg + renderCaseClass(sym, typeName, tpStr = "", e.fields, extendsClause = "")
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
    sortName: String, tpStr: String, typeParams: IndexedSeq[String],
    requires: IndexedSeq[String], ops: IndexedSeq[Operation], shape: SortShape,
    packagePath: String, sym: SymbolTable
  ): String =
    val sb = StringBuilder()
    if packagePath.nonEmpty then sb ++= s"package $packagePath\n\n"
    // `requires` lands on the sort's PRINCIPAL declaration — the same placement
    // the sum branch has always used, not a new decision for the record branch.
    val ext = if requires.isEmpty then "" else s" extends ${requires.mkString(", ")}"
    shape match
      case SortShape.Record(ctor) =>
        // case class Sort[T](fields) — ONE declaration (§6.3 / WI-926 / WI-940).
        sb ++= renderCaseClass(sym, sortName, tpStr, ctor.fields, ext)
        sb ++= renderOpsTrait(sortName, tpStr, typeParams, ops, sym)
      case SortShape.Sum(ctors) =>
        // enum Sort[T] { case C1(...); case C2 }
        sb ++= s"enum $sortName$tpStr$ext:\n"
        ctors.foreach { c =>
          val cName = Names.scalaTypeName(sym.name(c.name.last))
          // A nullary case takes no parameter list — `case None`, not `case None()`.
          // The record branch has no such form: a `case class` needs its `()`.
          if c.fields.isEmpty then sb ++= s"  case $cName\n"
          else sb ++= s"  case $cName(${renderFieldList(sym, c.fields)})\n"
        }
        sb ++= renderOpsTrait(sortName, tpStr, typeParams, ops, sym)
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
          ops.foreach(op => sb ++= s"  ${OpGen.renderAbstract(op, typeParams, sym)}\n")
    sb.toString

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
    fields: IndexedSeq[FieldDecl], extendsClause: String
  ): String =
    s"case class $typeName$tpStr(${renderFieldList(sym, fields)})$extendsClause\n"

  /** A constructor's fields as a Scala parameter list, without the parentheses —
    * one rendering for the `case class` and the `enum case`, which declare the
    * same schema and must not drift on how a field name or type reaches Scala. */
  private def renderFieldList(sym: SymbolTable, fields: IndexedSeq[FieldDecl]): String =
    fields.map { f =>
      s"${Names.scalaFieldName(sym.name(f.name))}: ${TypeGen.render(sym, f.ty)}"
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
    sortName: String, tpStr: String, typeParams: IndexedSeq[String],
    ops: IndexedSeq[Operation], sym: SymbolTable
  ): String =
    if ops.isEmpty then ""
    else
      val sb = StringBuilder()
      sb ++= s"\ntrait ${sortName}Ops$tpStr:\n"
      ops.foreach(op => sb ++= s"  ${OpGen.renderAbstract(op, typeParams, sym)}\n")
      sb.toString

end Bootstrap
