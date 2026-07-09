package anthill.codegen.scala

import anthill.parse.Parser

class BootstrapTest extends munit.FunSuite:

  private val stdlibDir = sys.env.getOrElse("ANTHILL_STDLIB",
    System.getProperty("user.dir") + "/../stdlib")

  private def parseStdlib(rel: String) =
    val src = scala.io.Source.fromFile(s"$stdlibDir/$rel")
    val text = try src.mkString finally src.close()
    Parser.parse(text, rel) match
      case Right(pf) => pf
      case Left(es) => fail(s"$rel parse failed: ${es.head.message}")

  test("WI-170: Bootstrap.generate on option.anthill emits Option enum") {
    val pf = parseStdlib("anthill/prelude/option.anthill")
    val files = Bootstrap.generate(pf)
    val mainFiles = files.filter(_.relPath.startsWith("src/main/scala/"))
    assert(mainFiles.nonEmpty, s"expected at least one main-source file, got: ${files.map(_.relPath)}")
    val optionFile = mainFiles.find(_.relPath.endsWith("/Option.scala"))
      .getOrElse(fail(s"expected Option.scala in: ${mainFiles.map(_.relPath)}"))
    val src = optionFile.contents
    assert(src.contains("package anthill.prelude"),
      s"missing package declaration in:\n$src")
    assert(src.contains("enum Option"),
      s"expected `enum Option` in:\n$src")
    // option.anthill defines `entity none` and `entity some(value: T)` —
    // both should appear as Scala enum cases.
    assert(src.contains("case None"), s"expected `case None` in:\n$src")
    assert(src.contains("case Some(value: T)"),
      s"expected `case Some(value: T)` in:\n$src")
  }

  test("WI-170: Bootstrap.generate on pair.anthill emits Pair enum") {
    val pf = parseStdlib("anthill/prelude/pair.anthill")
    val files = Bootstrap.generate(pf)
    val pairFile = files.find(_.relPath.endsWith("/Pair.scala"))
      .getOrElse(fail(s"expected Pair.scala in: ${files.map(_.relPath)}"))
    val src = pairFile.contents
    assert(src.contains("package anthill.prelude"))
    assert(src.contains("enum Pair"))
    assert(src.contains("case Pair(fst: A, snd: B)"),
      s"expected `case Pair(fst: A, snd: B)` in:\n$src")
    // Pair has two type parameters A and B — both should appear in
    // the enum's type parameter list.
    assert(src.contains("[A, B]"), s"expected `[A, B]` type params in:\n$src")
    // Pair has companion ops (fst, snd) — should land in PairOps trait.
    assert(src.contains("trait PairOps"),
      s"expected `trait PairOps` companion in:\n$src")
    assert(src.contains("def fst"), s"expected `def fst` in:\n$src")
    assert(src.contains("def snd"), s"expected `def snd` in:\n$src")
  }

  test("WI-170/WI-644: eq.anthill emits PartialEq with the abstract ops; Eq extends it (no new ops)") {
    val pf = parseStdlib("anthill/prelude/eq.anthill")
    val files = Bootstrap.generate(pf)
    // WI-644: the `eq`/`neq` OPERATIONS live in `PartialEq`; `Eq` just
    // `requires PartialEq[T]` (→ `extends PartialEq[T]`) and adds only the
    // reflexivity law — no new operation. So the abstract ops are emitted on
    // `PartialEq`, and `Eq` inherits them.
    val partialEq = files.find(_.relPath.endsWith("/PartialEq.scala"))
      .getOrElse(fail(s"expected PartialEq.scala in: ${files.map(_.relPath)}"))
    val peSrc = partialEq.contents
    assert(peSrc.contains("package anthill.prelude"))
    assert(peSrc.contains("trait PartialEq[T]"), s"expected `trait PartialEq[T]` in:\n$peSrc")
    assert(peSrc.contains("def eq(a: T, b: T): Boolean"),
      s"expected `def eq(a: T, b: T): Boolean` in:\n$peSrc")
    assert(peSrc.contains("def neq(a: T, b: T): Boolean"),
      s"expected `def neq(a: T, b: T): Boolean` in:\n$peSrc")

    val eqFile = files.find(_.relPath.endsWith("/Eq.scala"))
      .getOrElse(fail(s"expected Eq.scala in: ${files.map(_.relPath)}"))
    val eqSrc = eqFile.contents
    assert(eqSrc.contains("trait Eq[T] extends PartialEq[T]"),
      s"expected `trait Eq[T] extends PartialEq[T]` in:\n$eqSrc")
    // Eq inherits eq/neq from PartialEq — it must NOT redeclare them.
    assert(!eqSrc.contains("def eq("),
      s"Eq should inherit `eq` from PartialEq, not redeclare it:\n$eqSrc")
  }

  test("WI-170: snake_case operation names convert to camelCase") {
    // bigint.anthill exposes `to_bigint`, `to_int`, `to_float` ops —
    // verify they convert to camelCase per docs/scala-forward-mapping.md §5.
    val pf = parseStdlib("anthill/prelude/bigint.anthill")
    val files = Bootstrap.generate(pf)
    // proposal 038: BigInt is now a top-level `sort` (was `namespace`), so its
    // operations land in `BigInt.scala` (a trait with an inner BigIntOps), not
    // a standalone `BigIntOps.scala`.
    val bigIntFile = files.find(_.relPath.endsWith("/BigInt.scala"))
      .getOrElse(fail(s"expected BigInt.scala in: ${files.map(_.relPath)}"))
    val src = bigIntFile.contents
    assert(src.contains("def toBigint"), s"expected `def toBigint` (from to_bigint) in:\n$src")
    assert(src.contains("def toInt"), s"expected `def toInt` (from to_int) in:\n$src")
    assert(src.contains("def toFloat"), s"expected `def toFloat` (from to_float) in:\n$src")
    // The original snake_case name should NOT appear.
    assert(!src.contains("to_bigint"), s"snake_case `to_bigint` leaked into output:\n$src")
  }

  test("WI-170: standalone entity → case class") {
    // geometry.anthill has standalone `entity Vec3(x: Float, y: Float, z: Float)`
    // and `entity EulerAngles(roll, pitch, yaw)`.
    val pf = parseStdlib("anthill/geometry.anthill")
    val files = Bootstrap.generate(pf)
    val vec3File = files.find(_.relPath.endsWith("/Vec3.scala"))
      .getOrElse(fail(s"expected Vec3.scala in: ${files.map(_.relPath)}"))
    val src = vec3File.contents
    assert(src.contains("package anthill.geometry"))
    assert(src.contains("case class Vec3(x: Double, y: Double, z: Double)"),
      s"expected `case class Vec3(...)` with Float→Double mapping in:\n$src")
  }

  test("scala-forward-mapping §1: ??? must never appear in generated output") {
    // Multi-file scan across stdlib files known to contain rules — locks
    // in that no Bootstrap path emits `???`. Per spec §1, `???` is a
    // codegen bug.
    val files = Seq(
      "anthill/prelude/option.anthill",
      "anthill/prelude/eq.anthill",
      "anthill/geometry.anthill",
    ).flatMap(rel => Bootstrap.generate(parseStdlib(rel)))
    files.foreach { f =>
      assert(!f.contents.contains("???"),
        s"`???` leaked into ${f.relPath}:\n${f.contents}")
    }
  }

  test("Bootstrap.generate does not emit Laws.scala (KB-driven gen owns laws)") {
    // eq.anthill has a rule inside the Eq sort. Bootstrap must NOT emit
    // EqLaws.scala — rule term bodies are semantic and out of scope per
    // proposal 034 §Bootstrap. Vacuous Prop.passed placeholders mask
    // broken implementations, so bootstrap drops Laws emission entirely.
    val pf = parseStdlib("anthill/prelude/eq.anthill")
    val files = Bootstrap.generate(pf)
    val laws = files.filter(_.relPath.endsWith("Laws.scala"))
    assert(laws.isEmpty, s"bootstrap should not emit Laws files; got: ${laws.map(_.relPath)}")
  }

  test("Bootstrap.buildSbt is project-global (single source of truth)") {
    // build.sbt is project-level, not per-file. The previous per-file
    // emission was a footgun: a no-laws file emitted after a laws-file
    // would silently overwrite the build.sbt with a missing scalacheck
    // dep. The fix: build.sbt is exposed as a separate API the caller
    // invokes once after merging all per-file outputs.
    val a = Bootstrap.generate(parseStdlib("anthill/prelude/option.anthill"))
    val b = Bootstrap.generate(parseStdlib("anthill/prelude/eq.anthill"))
    val merged = a ++ b :+ Bootstrap.buildSbt
    val buildSbts = merged.filter(_.relPath == "build.sbt")
    assertEquals(buildSbts.size, 1, s"expected exactly one build.sbt in merged tree; got ${buildSbts.size}")
    assert(buildSbts.head.contents.contains("scalaVersion"),
      s"build.sbt missing scalaVersion:\n${buildSbts.head.contents}")
    // generate() itself never emits build.sbt
    assert(!a.exists(_.relPath == "build.sbt"),
      "generate() should not emit build.sbt; that's a separate API")
    assert(!b.exists(_.relPath == "build.sbt"),
      "generate() should not emit build.sbt; that's a separate API")
  }
