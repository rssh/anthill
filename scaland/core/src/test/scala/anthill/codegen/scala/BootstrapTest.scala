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

  test("WI-170: Bootstrap.generate on eq.anthill emits Eq trait with abstract ops") {
    val pf = parseStdlib("anthill/prelude/eq.anthill")
    val files = Bootstrap.generate(pf)
    val eqFile = files.find(_.relPath.endsWith("/Eq.scala"))
      .getOrElse(fail(s"expected Eq.scala in: ${files.map(_.relPath)}"))
    val src = eqFile.contents
    assert(src.contains("package anthill.prelude"))
    assert(src.contains("trait Eq[T]"), s"expected `trait Eq[T]` in:\n$src")
    assert(src.contains("def eq(a: T, b: T): Boolean"),
      s"expected `def eq(a: T, b: T): Boolean` in:\n$src")
    assert(src.contains("def neq(a: T, b: T): Boolean"),
      s"expected `def neq(a: T, b: T): Boolean` in:\n$src")
  }

  test("WI-170: snake_case operation names convert to camelCase") {
    // bigint.anthill exposes `to_bigint`, `to_int`, `to_float` ops —
    // verify they convert to camelCase per docs/scala-forward-mapping.md §5.
    val pf = parseStdlib("anthill/prelude/bigint.anthill")
    val files = Bootstrap.generate(pf)
    val bigIntFile = files.find(_.relPath.endsWith("/BigIntOps.scala"))
      .getOrElse(fail(s"expected BigIntOps.scala in: ${files.map(_.relPath)}"))
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
