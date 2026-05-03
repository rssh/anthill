package anthill.codegen.scala

import anthill.intern.{SymbolTable, TermSymbol}
import anthill.parse.*

import scala.collection.mutable.ArrayBuffer

/** A single Scala source file emitted by the bootstrap codegen. */
case class GeneratedFile(relPath: String, contents: String)

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
    val hasTests = files.exists(_.relPath.startsWith("src/test/"))
    if files.nonEmpty then files += GeneratedFile("build.sbt", buildSbtContents(hasTests))
    files.toIndexedSeq

  private def buildSbtContents(hasTests: Boolean): String =
    val sb = StringBuilder()
    sb ++= "scalaVersion := \"3.6.3\"\n"
    if hasTests then
      sb ++= "libraryDependencies += \"org.scalacheck\" %% \"scalacheck\" % \"1.18.0\" % Test\n"
    sb.toString

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
    val ctors = sort.items.collect { case Item.EntityItem(e) => e }
    val rules = sort.items.flatMap {
      case Item.RuleItem(r) => Seq(r)
      case Item.RuleBlockItem(b) => b.entries
      case _ => Seq.empty
    }
    val constraints = sort.items.collect { case Item.ConstraintItem(c) => c }

    val mainSrc = renderMainSort(sortName, tpStr, typeParams, requires, ops, ctors,
      sort.kind, effectivePkg, sym)
    out += GeneratedFile(
      relPath = s"src/main/scala/${pathToDir(effectivePkg)}$sortName.scala",
      contents = mainSrc)

    if rules.nonEmpty || constraints.nonEmpty then
      val testSrc = LawsGen.render(sortName, typeParams, rules, constraints, effectivePkg, sym)
      out += GeneratedFile(
        relPath = s"src/test/scala/${pathToDir(effectivePkg)}${sortName}Laws.scala",
        contents = testSrc)

  // ── Standalone entity → case class ──────────────────────────────

  private def emitStandaloneEntity(
    sym: SymbolTable, e: Entity, packagePath: String,
    out: ArrayBuffer[GeneratedFile]
  ): Unit =
    val (effectivePkg, typeName) = splitPath(sym, e.name, packagePath)
    val pkg = if effectivePkg.isEmpty then "" else s"package $effectivePkg\n\n"
    val fields = e.fields.map { f =>
      s"${Names.scalaFieldName(sym.name(f.name))}: ${TypeGen.render(sym, f.ty)}"
    }.mkString(", ")
    val src = s"${pkg}case class $typeName($fields)\n"
    out += GeneratedFile(
      relPath = s"src/main/scala/${pathToDir(effectivePkg)}$typeName.scala",
      contents = src)

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
    requires: IndexedSeq[String], ops: IndexedSeq[Operation], ctors: IndexedSeq[Entity],
    kind: SortDeclKind, packagePath: String, sym: SymbolTable
  ): String =
    val sb = StringBuilder()
    if packagePath.nonEmpty then sb ++= s"package $packagePath\n\n"
    if ctors.nonEmpty then
      // enum Sort[T] { case C1(...); case C2 }
      sb ++= s"enum $sortName$tpStr"
      if requires.nonEmpty then sb ++= s" extends ${requires.mkString(", ")}"
      sb ++= ":\n"
      ctors.foreach { c =>
        val cName = Names.scalaTypeName(sym.name(c.name.last))
        if c.fields.isEmpty then sb ++= s"  case $cName\n"
        else
          val fs = c.fields.map(f =>
            s"${Names.scalaFieldName(sym.name(f.name))}: ${TypeGen.render(sym, f.ty)}"
          ).mkString(", ")
          sb ++= s"  case $cName($fs)\n"
      }
      // Companion trait carrying the abstract op signatures, if any.
      if ops.nonEmpty then
        sb ++= s"\ntrait ${sortName}Ops$tpStr:\n"
        ops.foreach(op => sb ++= s"  ${OpGen.renderAbstract(op, typeParams, sym)}\n")
    else
      // trait Sort[T] { abstract ops }
      sb ++= s"trait $sortName$tpStr"
      if requires.nonEmpty then sb ++= s" extends ${requires.mkString(", ")}"
      sb ++= ":\n"
      if ops.isEmpty then sb ++= "  // (no operations)\n"
      else ops.foreach(op => sb ++= s"  ${OpGen.renderAbstract(op, typeParams, sym)}\n")
    sb.toString

end Bootstrap
