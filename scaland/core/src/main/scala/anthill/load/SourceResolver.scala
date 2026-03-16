package anthill.load

import java.nio.file.{Files, Path, Paths}

/** Abstraction over the filesystem for resolving import paths to source text. */
trait SourceResolver:
  def resolve(path: String): Either[String, String]

/** Resolves import paths by searching filesystem base directories. */
class FileSourceResolver(baseDirs: IndexedSeq[Path]) extends SourceResolver:
  def resolve(path: String): Either[String, String] =
    val relPath = path.replace('.', '/') + ".anthill"
    for base <- baseDirs do
      val full = base.resolve(relPath)
      if Files.exists(full) then
        return Right(Files.readString(full))
    Left(s"cannot resolve '$path' in base dirs: $baseDirs")

/** A resolver that always fails — for tests that don't use imports. */
object NullResolver extends SourceResolver:
  def resolve(path: String): Either[String, String] =
    Left(s"NullResolver: cannot resolve '$path'")
