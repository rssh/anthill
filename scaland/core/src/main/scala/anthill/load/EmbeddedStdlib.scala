package anthill.load

import anthill.parse.{Parser, ParsedFile}

import java.nio.file.Path

/** Loads standard-library `.anthill` files via a [[SourceResolver]].
  *
  * Mirrors `rustland/anthill-cli/src/stdlib_embedded.rs`: the canonical list
  * of stdlib modules that should be available to every KB. Unlike rustland,
  * we don't bundle the source into the JAR — we read it from disk through a
  * [[SourceResolver]] so that the same machinery serves user-supplied files.
  *
  * The list is intentionally a subset of rustland's: only files the scaland
  * parser/loader is known to handle today (post-WI-152 / WI-153). Add to it as
  * scaland gains support for more proposals.
  */
object EmbeddedStdlib:

  /** Canonical paths (in dotted notation) of stdlib files scaland can load.
    * Order matters: dependencies first.
    */
  val stdlibPaths: IndexedSeq[String] = IndexedSeq(
    // WI-138: parametric algebra spec — Ring, VectorSpace
    "anthill.prelude.algebra",
    // WI-153: Float operations layered on Numeric + algebra.Ring
    "anthill.prelude.float",
    // WI-137: Vec3 + EulerAngles + per-component vec_* rules + algebraic laws
    "anthill.geometry",
    // Proposal 030 phase α / WI-155: ProofWitness + SmtVerdict + SortBinding
    "anthill.realization.witness",
    // WI-155: ProofRecord + ProofStrategyOpen + ProofBodyNone + Pending + ParametricBinding
    "anthill.realization.realization",
  )

  /** Parse all stdlib files via `resolver`. Returns parsed files in dependency
    * order plus any errors encountered.
    */
  def parseAll(resolver: SourceResolver): (IndexedSeq[ParsedFile], IndexedSeq[String]) =
    val parsed = IndexedSeq.newBuilder[ParsedFile]
    val errors = IndexedSeq.newBuilder[String]
    for path <- stdlibPaths do
      resolver.resolve(path) match
        case Left(msg) => errors += s"stdlib $path: $msg"
        case Right(source) =>
          Parser.parse(source, s"$path.anthill") match
            case Right(pf) => parsed += pf
            case Left(errs) =>
              for e <- errs do errors += s"stdlib $path: ${e.message}"
    (parsed.result(), errors.result())

  /** Convenience: build a [[FileSourceResolver]] rooted at `stdlibBaseDir`
    * and parse every stdlib file. `stdlibBaseDir` should be the directory
    * containing the top-level `anthill/` tree (e.g. the repo's `stdlib/`).
    */
  def parseFromDir(stdlibBaseDir: Path): (IndexedSeq[ParsedFile], IndexedSeq[String]) =
    parseAll(FileSourceResolver(IndexedSeq(stdlibBaseDir)))

end EmbeddedStdlib
