package anthill.smtgen

import java.nio.file.{Files, Path, StandardOpenOption}
import scala.sys.process.*

/** Tiny wrapper around `z3 -smt2 -in` for round-trip tests. Mirrors
  * `rustland/anthill-smt-gen/tests/common/mod.rs::run_z3` and
  * `z3_available`.
  */
object Z3Runner:

  /** True when a `z3` binary is on `$PATH`. Tests that need Z3 should
    * `assume(Z3Runner.available)` to skip cleanly when absent.
    */
  lazy val available: Boolean =
    try Process(Seq("z3", "--version")).!(ProcessLogger(_ => (), _ => ())) == 0
    catch case _: Throwable => false

  /** Write `smt` to a temp `.smt2` file and ask Z3 to solve it.
    * Returns the trimmed stdout — typically `unsat`, `sat`, or
    * `unknown` followed by optional model / unsat-core blocks.
    */
  def run(label: String, smt: String): String =
    val tmp: Path = Files.createTempFile(s"anthill-smt-${label}-", ".smt2")
    try
      Files.writeString(tmp, smt, StandardOpenOption.WRITE, StandardOpenOption.TRUNCATE_EXISTING)
      val out = StringBuilder()
      val logger = ProcessLogger(line => { out.append(line); out.append('\n') }, _ => ())
      Process(Seq("z3", tmp.toAbsolutePath.toString)).!(logger)
      out.toString.trim
    finally
      Files.deleteIfExists(tmp)
