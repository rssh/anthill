package anthill.smtgen

import java.nio.file.Paths

import anthill.kb.KnowledgeBase
import anthill.load.{EmbeddedStdlib, Loader, Prelude}
import anthill.parse.{ParsedFile, Parser}

/** Shared fixture for smt-gen tests: resolves the stdlib path
  * (matching scaland/core's pattern), caches its parse, and offers a
  * one-call `loadKbWith(source)` that returns a KB with stdlib +
  * user source loaded.
  */
object Common:

  private val stdlibDir: String = sys.env.getOrElse("ANTHILL_STDLIB",
    System.getProperty("user.dir") + "/../stdlib")

  private lazy val stdlibParsed: IndexedSeq[ParsedFile] =
    val (parsed, errs) = EmbeddedStdlib.parseFromDir(Paths.get(stdlibDir))
    if errs.nonEmpty then
      throw new AssertionError(s"stdlib parse errors: $errs")
    parsed

  /** Load the stdlib chain plus a user-supplied anthill source string
    * into a fresh KB. Mirrors the rustland test helper of the same
    * name. The loader's verdict is READ: a KB that did not finish loading
    * would let a row pass over a half-built index, and did — `CommDelayTest`
    * imported a prelude name that no longer exists, unnoticed.
    */
  def loadKbWith(source: String): KnowledgeBase =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val userPf = Parser.parse(source, "<test>") match
      case Right(pf) => pf
      case Left(errs) => throw new AssertionError(
        s"parse failed: ${errs.map(_.message).mkString(", ")}")
    val loadErrs = Loader.loadAll(kb, stdlibParsed :+ userPf)
    if loadErrs.nonEmpty then throw new AssertionError(s"load errors: $loadErrs")
    kb
