package anthill.codegen.scala

import dotty.tools.dotc.Driver
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.interfaces
import dotty.tools.dotc.reporting.{Diagnostic, Reporter}

import java.nio.file.{Files, Path}
import scala.collection.mutable.ArrayBuffer
import scala.io.Source

/** Compiles Bootstrap's emitted Scala with a real Scala compiler (WI-1020).
  *
  * WHY THIS EXISTS. Every other assertion about codegen output in this suite is a
  * substring match on the emitted text, and a substring match tests the test author's
  * expectations, not the emitter: `docs/scala-forward-mapping.md` §2.3 promises "the
  * generated file compiles as-is" and nothing checked it. A codegen backend's capability
  * is emitting COMPILABLE SOURCE, so its driving test compiles the source and reports the
  * compiler's own diagnostics.
  *
  * That this was not theoretical: the `eq` closure did not compile, and the string-match
  * test covering it was green.
  *
  * IN-PROCESS, through `dotc.Driver`, rather than shelling out to `scala-cli`. The driver
  * needs no network at test time and cannot be missing, so there is no skip-when-
  * unavailable branch for a defect to hide behind; it is pinned to the build's
  * `scala3Version`; and it yields structured `Diagnostic`s instead of colour-coded stderr
  * that would have to be parsed.
  *
  * WHAT IT DOES NOT CATCH: output that compiles and means the wrong thing. `enum Pair:
  * case Pair(...)` — the nested `Pair.Pair` §6.3 rules out — compiles perfectly well
  * (measured). Those need their own assertions; this harness is a floor, not a ceiling.
  */
object ScalaCompile:

  /** One compiler diagnostic, flattened to what a failure message needs. */
  case class Diag(file: String, line: Int, message: String):
    def render: String = s"$file:$line: $message"

  /** Compile `files` as ONE compilation unit set and return the ERRORS, in the order the
    * compiler emitted them. Empty means it compiled.
    *
    * The whole set goes to one invocation because the emitted tree is cross-referential —
    * `Eq.scala` names `PartialEq`, declared by a sibling file — so compiling files
    * individually would report missing-symbol errors that say nothing about the emitter.
    */
  def errors(files: Seq[GeneratedFile]): Seq[Diag] =
    val root = Files.createTempDirectory("anthill-scala-gen")
    val sources = files.filter(_.relPath.endsWith(".scala")).map { f =>
      val target = root.resolve(f.relPath)
      Files.createDirectories(target.getParent)
      Files.writeString(target, f.contents)
      target.toString
    }
    require(sources.nonEmpty, s"nothing to compile in: ${files.map(_.relPath)}")
    val out = Files.createDirectory(root.resolve("classes"))
    val reporter = CollectingReporter()
    Driver().process(
      Array("-classpath", classpath, "-d", out.toString) ++ sources, reporter)
    reporter.errors.toSeq

  /** Compile and fail the calling test with the compiler's own diagnostics.
    * `label` names what was compiled, since the temp paths in a diagnostic are opaque. */
  def assertCompiles(label: String, files: Seq[GeneratedFile]): Unit =
    val errs = errors(files)
    if errs.nonEmpty then
      val rendered = errs.map(e => s"  ${e.render}").mkString("\n")
      throw AssertionError(
        s"$label does not compile (${errs.length} error(s)):\n$rendered\n\n" +
        files.map(f => s"── ${f.relPath}\n${f.contents}").mkString("\n"))

  /** The classpath the emitted code compiles AGAINST, written by a `resourceGenerator`
    * (see `build.sbt`). Read from a resource rather than `java.class.path` because sbt
    * runs tests unforked: that property holds the launcher's classpath, which carries no
    * `scala3-library`, and every compile would fail on `Any` instead of on the code under
    * test. A missing resource is a BUILD fault and says so — degrading to a guess here
    * would turn a wiring mistake into mysterious compile errors.
    */
  private lazy val classpath: String =
    val name = "/scala-compile-classpath.txt"
    val stream = Option(getClass.getResourceAsStream(name)).getOrElse(
      throw IllegalStateException(
        s"$name is not on the test classpath — the `Test / resourceGenerators` entry in " +
        "build.sbt that writes it is missing or failed"))
    val src = Source.fromInputStream(stream)
    val entries = try src.getLines().filter(_.nonEmpty).toVector finally src.close()
    require(entries.nonEmpty, s"$name is empty")
    entries.mkString(java.io.File.pathSeparator)

  /** Accumulates errors. `Reporter` is abstract over `doReport`; the alternative,
    * `StoreReporter`, needs a `Context` to read its buffer back, which this never has. */
  private final class CollectingReporter extends Reporter:
    val errors: ArrayBuffer[Diag] = ArrayBuffer.empty

    def doReport(dia: Diagnostic)(using Context): Unit =
      // ERRORS only. Warnings are not this harness's business, and the compiler also
      // emits a positionless "N errors found" summary at WARNING level that would
      // otherwise show up as a phantom extra finding.
      if dia.level >= interfaces.Diagnostic.ERROR then
        val pos = dia.pos
        val file = if pos.exists then pos.source.file.name else "<no position>"
        val line = if pos.exists then pos.line + 1 else 0
        errors += Diag(file, line, dia.msg.message)

end ScalaCompile
