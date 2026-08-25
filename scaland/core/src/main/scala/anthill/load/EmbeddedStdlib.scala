package anthill.load

import anthill.parse.{Parser, ParsedFile}

import java.nio.file.Path

/** Loads standard-library `.anthill` files via a [[SourceResolver]].
  *
  * Mirrors `rustland/anthill-stl/src/stdlib.rs`: the canonical list
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
    // ── primitive / kernel layer
    "anthill.prelude.primitives",
    "anthill.prelude.nothing",
    "anthill.prelude.unit",
    "anthill.prelude.bool",
    "anthill.prelude.int64",
    "anthill.prelude.bigint",
    "anthill.prelude.float",
    "anthill.prelude.string",
    // ── typeclass chain (WI-163: structural-op disambiguation removed the
    //    AmbiguousSymbol cascade; WI-162: bool/int/iteration/collection/
    //    list/reflect now parse)
    "anthill.prelude.eq",
    "anthill.prelude.ordered",
    "anthill.prelude.numeric",
    // monad.anthill defines `sort Monad[M[T]]` — imported by option (Option is a
    // Monad instance). Self-contained (no imports); the 2-phase scan tolerates
    // its position, but it precedes option for readability.
    "anthill.prelude.monad",
    "anthill.prelude.option",
    "anthill.prelude.pair",
    "anthill.prelude.function",
    // WI-20260824-VT8CF: `Divisible` / `EuclideanDomain` — the `/` and `%` tower.
    // BEFORE `field`, which reaches `div` through it (`provides Divisible[T = T]`)
    // instead of declaring a second one; scaland reads the same `stdlib/` files from
    // disk, so field.anthill's import of `Divisible` is unresolved without this line.
    "anthill.prelude.division",
    "anthill.prelude.field",
    "anthill.prelude.lattice",
    // ── effects + I/O
    "anthill.prelude.effects",
    "anthill.prelude.effects-runtime",
    "anthill.prelude.console",
    // ── collections
    "anthill.prelude.iteration",
    "anthill.prelude.collection",
    "anthill.prelude.iterable",
    "anthill.prelude.finite_collection",
    "anthill.prelude.indexed_seq",
    "anthill.prelude.list",
    "anthill.prelude.set",
    "anthill.prelude.map",
    "anthill.prelude.stream",
    // combinators defines MappedStream/FilteredStream — imported by iterable.
    // (Loader is 2-phase scan-then-resolve, so the forward ref is fine.)
    "anthill.prelude.combinators",
    // finiteness Phase B (WI-588): FiniteStream + finite map/filter carriers.
    // Reference FiniteCollection (loaded above) and Stream/combinators.
    "anthill.prelude.finite_stream",
    "anthill.prelude.finite_combinators",
    "anthill.prelude.logical_stream",
    // ── meta + reflect
    "anthill.prelude.sort",
    "anthill.prelude.meta",
    "anthill.reflect.reflect",
    "anthill.reflect.typing",
    // ── kernel meta-spec
    "anthill.kernel.kernel",
    // ── parametric algebra (WI-138)
    "anthill.prelude.algebra",
    // ── geometry (WI-935: sort Vec3 + its VectorSpace members; EulerAngles)
    "anthill.geometry",
    // ── logic specs
    "anthill.logic.minimal",
    "anthill.logic.constructive",
    "anthill.logic.classical",
    // ── realization layer (WI-155: ProofWitness / ProofRecord)
    "anthill.realization.witness",
    "anthill.realization.realization",
    "anthill.realization.policy",
    "anthill.realization.platform",
    "anthill.realization.rust_std",
    "anthill.realization.cpp_std",
    "anthill.realization.rust_anthill",
    "anthill.realization.scala_std",
    "anthill.realization.scala_caps",
    // ── persistence (no `anthill.persistence.sql`: it moved to
    //    `examples/sql-store/` — WI-934)
    "anthill.persistence.store",
    "anthill.persistence.filesystem",
    // ── CLI argparse (WI-159 / WI-164)
    "anthill.cli.spec",
    "anthill.cli.parse",
    "anthill.cli.help",
    "anthill.cli.main",
  )

  /** Parse all stdlib files via `resolver`. Returns parsed files in dependency
    * order plus any errors encountered.
    */
  def parseAll(resolver: SourceResolver): (IndexedSeq[ParsedFile], IndexedSeq[String]) =
    val parsed = IndexedSeq.newBuilder[ParsedFile]
    val errors = IndexedSeq.newBuilder[String]
    for path <- stdlibPaths do
      resolver.resolve(path) match
        // No file was read, so there is no path to name — the MODULE ID is the whole
        // identity this branch has, and it is spelled as one.
        case Left(msg) => errors += s"stdlib $path: $msg"
        case Right(source) =>
          // WI-947: the RELATIVE PATH, not `s"$path.anthill"`. `path` is a dotted module
          // id (`anthill.realization.witness`), and `Span.render` puts whatever it is
          // given into `file:line:col:` — the shape editors and terminals make
          // openable. Spelled the module way, that named a file which does not exist,
          // in a syntax that invited someone to click it. This is the SAME mapping
          // `FileSourceResolver.resolve` just used to find the text.
          val relPath = path.replace('.', '/') + ".anthill"
          Parser.parse(source, relPath) match
            case Right(pf) => parsed += pf
            case Left(errs) =>
              // `render`, not `message`: the rendering names the file AND the position
              // inside it. Hand-prefixing `$path` is what a caller reaches for when a
              // diagnostic cannot locate itself, and it still could not say WHERE.
              for e <- errs do errors += s"stdlib ${e.render}"
    (parsed.result(), errors.result())

  /** Convenience: build a [[FileSourceResolver]] rooted at `stdlibBaseDir`
    * and parse every stdlib file. `stdlibBaseDir` should be the directory
    * containing the top-level `anthill/` tree (e.g. the repo's `stdlib/`).
    */
  def parseFromDir(stdlibBaseDir: Path): (IndexedSeq[ParsedFile], IndexedSeq[String]) =
    parseAll(FileSourceResolver(IndexedSeq(stdlibBaseDir)))

end EmbeddedStdlib
