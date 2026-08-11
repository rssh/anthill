package anthill.codegen.scala

import anthill.kb.KnowledgeBase
import anthill.load.{EmbeddedStdlib, Loader, Prelude}
import anthill.parse.{ParsedFile, Parser}

import java.nio.file.Paths

/** The advertised stdlib, parsed ONCE per JVM.
  *
  * An OBJECT and not a suite member: sbt runs every suite in one JVM (no `fork`), so a
  * per-instance `lazy val` caches within its own class only, and each suite that wants
  * the stdlib pays the ~0.5s parse again. That is most of a suite's wall clock here —
  * measured at roughly a fifth of scaland's total before this was hoisted. Loading is
  * cheap by comparison (~0.07s) and stays per-KB, so tests keep their isolation.
  */
object StdlibFixture:

  val dir: String = sys.env.getOrElse("ANTHILL_STDLIB",
    System.getProperty("user.dir") + "/../stdlib")

  lazy val parsed: IndexedSeq[ParsedFile] =
    val (files, parseErrs) = EmbeddedStdlib.parseFromDir(Paths.get(dir))
    assert(parseErrs.isEmpty, s"stdlib parse errors: $parseErrs")
    files

  /** Every `.anthill` file under `anthill/prelude`, in path order, with its file name.
    *
    * THE DIRECTORY AND NOT `EmbeddedStdlib.stdlibPaths`, which is a smaller set — nine
    * prelude files (cell, delay, relation, sortedset, time, …) are not in scaland's
    * loadable list yet. This is the set a bare name reaches through anthill's
    * auto-import, so it is the set [[ScalaTypes]] must place prelude names against: a
    * consumer writing `Cell` still needs the type cell.anthill declares, whether or not
    * the KB can load that file today.
    *
    * ONE LISTING AND ONE PARSE for the whole suite. The refusal-set test walks the same
    * files, and while it listed and parsed them itself the two could disagree about
    * which files are in the set — the table would be built from one and the emission
    * asserted over the other. The directory stream is CLOSED: `Files.list` holds an open
    * directory handle until it is.
    */
  lazy val preludeByName: IndexedSeq[(String, ParsedFile)] =
    val stream = java.nio.file.Files.list(Paths.get(s"$dir/anthill/prelude"))
    val paths =
      try
        stream.toArray.map(_.asInstanceOf[java.nio.file.Path]).toIndexedSeq
          .filter(_.toString.endsWith(".anthill")).sortBy(_.toString)
      finally stream.close()
    paths.map { p =>
      val name = p.getFileName.toString
      val src = scala.io.Source.fromFile(p.toFile)
      val text = try src.mkString finally src.close()
      Parser.parse(text, s"anthill/prelude/$name") match
        case Right(pf) => name -> pf
        case Left(es)  => throw AssertionError(s"$p: ${es.head.render}")
    }

  lazy val preludeFiles: IndexedSeq[ParsedFile] = preludeByName.map(_._2)

  /** The stdlib plus any extra parsed files, loaded into one KB. The loader's verdict is
    * READ and not discarded — a KB that never finished loading would let every assertion
    * over it pass against a half-built index. */
  def kbWith(extra: ParsedFile*): KnowledgeBase =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val loadErrs = Loader.loadAll(kb, parsed ++ extra)
    assert(loadErrs.isEmpty, s"load errors: $loadErrs")
    kb

class BootstrapTest extends munit.FunSuite:

  /** munit's default is 30s, and the refusal-set test crosses it (WI-1062).
    *
    * NOT A HANG, and worth saying so at the one place that would otherwise look
    * like one: that test invokes `dotc` in process once per prelude file to see
    * which ones compile standalone, so it costs 40-odd real compiler runs. It grew
    * by six when WI-1062 moved six files out of the refusal set, and under a full
    * `sbt test` the three subprojects compete for cores — measured at 32.6s there
    * against 7s under `testOnly`, which is why it passed in isolation first.
    * Raised rather than trimmed because the probe is the thing being asserted; a
    * timeout large enough to be an outright hang detector still is one. */
  override def munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(180, "s")

  private val stdlibDir = StdlibFixture.dir

  /** The plain stdlib KB, loaded once for the suite. */
  private lazy val stdlibKb: KnowledgeBase = StdlibFixture.kbWith()

  /** The tables every emission below is rendered against (WI-1060): `scala_std`'s
    * scalars read out of the KB, and the prelude's own parsed files for every other
    * name. Resolved ONCE — it is the project's answer, not a per-test knob — and the
    * suite emits through [[gen]] so no test can quietly render against a different one.
    * The tests that DO vary it (the mutation tests below) call `Bootstrap.generate`
    * directly, which is how they read as the exception they are. */
  private lazy val scalaTypes: ScalaTypes =
    ScalaTypes.resolve(stdlibKb, StdlibFixture.preludeFiles)

  private def gen(pf: ParsedFile): IndexedSeq[GeneratedFile] =
    Bootstrap.generate(pf, scalaTypes)

  private def parseStdlib(rel: String) =
    val src = scala.io.Source.fromFile(s"$stdlibDir/$rel")
    val text = try src.mkString finally src.close()
    parseSource(text, rel)

  private def parseSource(text: String, name: String) =
    Parser.parse(text, name) match
      case Right(pf) => pf
      case Left(es) => fail(s"$name parse failed: ${es.head.message}")

  /** The emission of several prelude files as ONE compilation set. Bootstrap is
    * per-file and its output is cross-referential, so almost every compile
    * assertion here names the file under test plus the siblings it mentions. */
  private def preludeClosure(names: String*) =
    names.toIndexedSeq.flatMap(n => gen(parseStdlib(s"anthill/prelude/$n.anthill")))

  test("WI-170: Bootstrap.generate on option.anthill emits Option enum") {
    val pf = parseStdlib("anthill/prelude/option.anthill")
    val files = gen(pf)
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
    val files = gen(pf)
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
    val files = gen(pf)
    // WI-644: the `eq`/`neq` OPERATIONS live in `PartialEq`; `Eq` just
    // `requires PartialEq[T]` (→ `extends PartialEq[T]`) and adds only the
    // reflexivity law — no new operation. So the abstract ops are emitted on
    // `PartialEq`, and `Eq` inherits them.
    val partialEq = files.find(_.relPath.endsWith("/PartialEq.scala"))
      .getOrElse(fail(s"expected PartialEq.scala in: ${files.map(_.relPath)}"))
    val peSrc = partialEq.contents
    assert(peSrc.contains("package anthill.prelude"))
    assert(peSrc.contains("trait PartialEq[T]"), s"expected `trait PartialEq[T]` in:\n$peSrc")
    assert(peSrc.contains("def eq(a: T, b: T): _root_.scala.Boolean"),
      s"expected `def eq(a: T, b: T): _root_.scala.Boolean` in:\n$peSrc")
    assert(peSrc.contains("def neq(a: T, b: T): _root_.scala.Boolean"),
      s"expected `def neq(a: T, b: T): _root_.scala.Boolean` in:\n$peSrc")

    val eqFile = files.find(_.relPath.endsWith("/Eq.scala"))
      .getOrElse(fail(s"expected Eq.scala in: ${files.map(_.relPath)}"))
    val eqSrc = eqFile.contents
    assert(eqSrc.contains("trait Eq[T] extends PartialEq[T]"),
      s"expected `trait Eq[T] extends PartialEq[T]` in:\n$eqSrc")
    // Eq inherits eq/neq from PartialEq — it must NOT redeclare them.
    assert(!eqSrc.contains("def eq("),
      s"Eq should inherit `eq` from PartialEq, not redeclare it:\n$eqSrc")
  }

  test("WI-1020: the emitted eq closure COMPILES") {
    // The first test in this suite to DRIVE the capability rather than describe it.
    // `docs/scala-forward-mapping.md` §2.3 promises "the generated file compiles as-is";
    // this is what checks it.
    //
    // SUBSUMES NOTHING ABOVE, and that is not a hedge — the two ask different questions.
    // The string matches pin WHICH construct each declaration maps to (`trait Eq[T]
    // extends PartialEq[T]`, ops on `PartialEq` and not on `Eq`); a compile cannot tell
    // you the mapping is right, only that whatever was emitted is valid Scala. Neither
    // implies the other, so both stay.
    //
    // WHAT IT CAUGHT ON ARRIVAL, and the reason this file was chosen first: `Eq` declares
    // no operations, and the Algebra branch emitted `trait Eq[T] extends PartialEq[T]:`
    // over a lone `// (no operations)` comment — `indented definitions expected, eof
    // found`. Every assertion in the test above passed against that file.
    //
    // FAILS WHEN BACKED OUT: restore the `:`-plus-comment form in `renderMainSort` and
    // this reports the compiler's own error; the test above stays green either way.
    //
    // The whole closure goes to one invocation because `Eq` and `NonEq` name `PartialEq`,
    // which a sibling file declares. eq.anthill is self-contained — the three sorts
    // reference only each other — so no other stdlib file is needed here.
    val files = gen(parseStdlib("anthill/prelude/eq.anthill"))
    assertEquals(files.map(_.relPath).sorted, IndexedSeq(
      "src/main/scala/anthill/prelude/Eq.scala",
      "src/main/scala/anthill/prelude/NonEq.scala",
      "src/main/scala/anthill/prelude/PartialEq.scala",
    ), "the closure being compiled must be the whole file, not a subset that happens to work")
    ScalaCompile.assertCompiles("the eq.anthill closure", files)
  }

  test("WI-1020: the harness compiles with the version scala_std declares") {
    // What makes the compile above MEAN anything. The harness runs whatever
    // `scala3-compiler % Test` resolved to; the emitted project declares whatever
    // `scala_std` says. If those drift, "the closure compiles" is an answer to a
    // question nobody asked — the output would be verified against a compiler no
    // consumer of it uses.
    //
    // This is the coupling that a hardcoded default in the emitter used to hide: bump
    // build.sbt alone and this fails naming both numbers, rather than the harness
    // quietly checking the wrong dialect.
    //
    // KNOWN LIMIT, stated rather than left to be discovered: the harness can only ever
    // exercise ONE compiler — the one on its test classpath. A caller configuring some
    // other target is unverified, and this assertion is what confines the gap to that
    // case.
    val declared = ScalaProfile.languageVersion(stdlibKb) match
      case LanguageVersion.Declared(v) => v
      case other => fail(s"scala_std must declare a language_version; got $other")
    assertEquals(dotty.tools.dotc.config.Properties.versionNumberString, declared,
      "the compiler this harness runs and the version scala_std targets have diverged; " +
      "move `scala3Version` in build.sbt and `language_version` in scala_std.anthill together")
  }

  test("WI-170: snake_case operation names convert to camelCase") {
    // bigint.anthill exposes `to_bigint`, `to_int`, `to_float` ops —
    // verify they convert to camelCase per docs/scala-forward-mapping.md §5.
    val pf = parseStdlib("anthill/prelude/bigint.anthill")
    val files = gen(pf)
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
    // `EulerAngles(roll, pitch, yaw)` is geometry's standalone entity.
    //
    // This used to read `Vec3`, which WI-935 turned into a SORT with an
    // eponymous constructor and four members — so it is no longer an example of
    // what this test is named for. It is re-pointed rather than deleted: the
    // claim ("a standalone entity becomes a case class, Float→Double") is still
    // worth pinning, and `EulerAngles` still is one. Vec3's own emission is now
    // asserted by the WI-940 tests below.
    //
    // CONTROL for WI-940: this passes either way BY DESIGN. Its job is to say
    // the record collapse did not reach the sugar path it was already correct
    // on — the shared `renderCaseClass` must not have moved this output.
    val pf = parseStdlib("anthill/geometry.anthill")
    val files = gen(pf)
    val eulerFile = files.find(_.relPath.endsWith("/EulerAngles.scala"))
      .getOrElse(fail(s"expected EulerAngles.scala in: ${files.map(_.relPath)}"))
    val src = eulerFile.contents
    assert(src.contains("package anthill.geometry"))
    assert(src.contains("case class EulerAngles(roll: _root_.scala.Double, pitch: _root_.scala.Double, yaw: _root_.scala.Double)"),
      s"expected `case class EulerAngles(...)` with Float→Double mapping in:\n$src")
  }

  // ── WI-940: an eponymous constructor IS its sort (§6.3) ───────────────────

  test("WI-940/§6.3: eponymous sort Vec3 is ONE case class — no `enum Vec3: case Vec3`") {
    // `sort Vec3 { entity Vec3(x, y, z); operation vec_add(…) = … }` writes
    // `Vec3` once and defines ONE symbol (§6.3, WI-926) — there is no
    // `Vec3.Vec3`. Bootstrap emitted `enum Vec3:` + `case Vec3(…)` for it, which
    // is exactly that nested name; the same defect WI-931 fixed in the other
    // backend, where cpp-gen emitted `struct Vec3` twice for this shape.
    //
    // CONTROL, MEASURED not asserted: with `shapeOf` returning `Sum` for the
    // eponymous single-constructor case (i.e. the old behaviour), exactly FOUR
    // tests fail — this one, `TotalFloat`, `the entity sugar and the eponymous
    // long form emit the SAME declaration`, and `an eponymous PARAMETRIC sort`.
    // The two named CONTROL / REFUSED tests and every WI-170 test pass either
    // way BY DESIGN; the refusal has its own probe, recorded at its site.
    val pf = parseStdlib("anthill/geometry.anthill")
    val files = gen(pf)
    val vec3 = files.find(_.relPath.endsWith("/Vec3.scala"))
      .getOrElse(fail(s"expected Vec3.scala in: ${files.map(_.relPath)}"))
    val src = vec3.contents
    assert(src.contains("package anthill.geometry"), s"missing package in:\n$src")
    assert(!src.contains("enum Vec3"),
      s"an eponymous sort must not reach Scala as an enum:\n$src")
    assert(!src.linesIterator.exists(_.trim.startsWith("case Vec3")),
      s"`case Vec3` is the nested Vec3.Vec3 §6.3 rules out:\n$src")
    assert(src.contains("case class Vec3(x: _root_.scala.Double, y: _root_.scala.Double, z: _root_.scala.Double)"),
      s"expected the one `case class Vec3(…)` declaration in:\n$src")
    // The four members stay reachable — as the abstract contract, since
    // bootstrap emits signatures only and a `case class` has no abstract member.
    assert(src.contains("trait Vec3Ops:"), s"expected `trait Vec3Ops` in:\n$src")
    assert(src.contains("def vecAdd(a: Vec3, b: Vec3): Vec3"),
      s"expected `def vecAdd(a: Vec3, b: Vec3): Vec3` in:\n$src")
    assert(src.contains("def vecScale(c: _root_.scala.Double, v: Vec3): Vec3"),
      s"expected `def vecScale(c: _root_.scala.Double, v: Vec3): Vec3` in:\n$src")
    assert(src.contains("def vecZero(): Vec3"), s"expected `def vecZero(): Vec3` in:\n$src")
  }

  test("WI-940: TotalFloat — stdlib's other eponymous sort — collapses the same way") {
    // Vec3 is not a special case of geometry: `sort TotalFloat { entity
    // TotalFloat(raw: Float); operation eq(…) }` is the same shape in the
    // prelude, and gets the same one declaration. Two real fixtures, so the rule
    // is not fitted to one file.
    val pf = parseStdlib("anthill/prelude/totalfloat.anthill")
    val files = gen(pf)
    val tf = files.find(_.relPath.endsWith("/TotalFloat.scala"))
      .getOrElse(fail(s"expected TotalFloat.scala in: ${files.map(_.relPath)}"))
    val src = tf.contents
    assert(!src.contains("enum TotalFloat"), s"eponymous sort emitted as an enum:\n$src")
    assert(src.contains("case class TotalFloat(raw: _root_.scala.Double)"),
      s"expected `case class TotalFloat(raw: _root_.scala.Double)` in:\n$src")
    assert(src.contains("def eq(a: TotalFloat, b: TotalFloat): _root_.scala.Boolean"),
      s"expected the `eq` member on the TotalFloatOps contract in:\n$src")
  }

  test("WI-940/§6.3: the `entity` sugar and the eponymous long form emit the SAME declaration") {
    // §6.3 calls the desugaring an EQUIVALENCE — "the sugar and the long form
    // denote the same thing", so "a codegen backend naming `Acct` gets the same
    // answer either way". That is what failed: the sugar emitted a case class
    // and the long form an `enum Acct: case Acct(…)`. Asserted as byte equality
    // of the whole file rather than as two independent expectations, so the two
    // paths cannot drift apart again while both still "look right".
    val sugar = gen(parseSource(
      """namespace anthill.wi940
        |  entity Acct(id: Int64, balance: Float)
        |end
        |""".stripMargin, "sugar.anthill"))
    val longForm = gen(parseSource(
      """namespace anthill.wi940
        |  sort Acct
        |    entity Acct(id: Int64, balance: Float)
        |  end
        |end
        |""".stripMargin, "long.anthill"))
    // Both sides emit exactly one file — asserted, not assumed: `assertEquals`
    // on two EMPTY sequences would pass, and this is what stops that from being
    // a way for the test to be vacuously green.
    assertEquals(sugar.size, 1, s"expected one file from the sugar: ${sugar.map(_.relPath)}")
    assertEquals(longForm.size, 1, s"expected one file from the long form: ${longForm.map(_.relPath)}")
    assertEquals(longForm.map(f => (f.relPath, f.contents)),
      sugar.map(f => (f.relPath, f.contents)))
    assert(sugar.head.contents.contains("case class Acct(id: _root_.scala.Long, balance: _root_.scala.Double)"),
      s"expected the record declaration in:\n${sugar.head.contents}")
  }

  test("WI-940: an eponymous PARAMETRIC sort keeps its type parameters on the case class") {
    // `case class Box[T](value: T)`, not `case class Box(value: T)[T]` — the
    // record branch is the first one to place `tpStr` on a `case class`.
    val files = gen(parseSource(
      """namespace anthill.wi940
        |  sort Box
        |    sort T = ?
        |    entity Box(value: T)
        |    operation unbox(b: Box) -> T
        |  end
        |end
        |""".stripMargin, "box.anthill"))
    val src = files.find(_.relPath.endsWith("/Box.scala"))
      .getOrElse(fail(s"expected Box.scala in: ${files.map(_.relPath)}")).contents
    assert(src.contains("case class Box[T](value: T)"),
      s"expected `case class Box[T](value: T)` in:\n$src")
    assert(src.contains("trait BoxOps[T]:"), s"expected `trait BoxOps[T]` in:\n$src")
  }

  test("WI-940 CONTROL: a non-eponymous multi-constructor sort still emits an enum") {
    // The collapse is keyed on the constructor's name matching its sort's
    // (§6.3), not on being a sole variant — so a sum sort is untouched. This
    // passes both with and without the change BY DESIGN: its job is to say the
    // record branch did not widen into the sum branch. (The stdlib `Option` and
    // `Pair` tests above are the same control on real files.)
    val files = gen(parseSource(
      """namespace anthill.wi940
        |  sort Shape
        |    entity Circle(r: Float)
        |    entity Square(side: Float)
        |  end
        |end
        |""".stripMargin, "shape.anthill"))
    val src = files.find(_.relPath.endsWith("/Shape.scala"))
      .getOrElse(fail(s"expected Shape.scala in: ${files.map(_.relPath)}")).contents
    assert(src.contains("enum Shape:"), s"expected `enum Shape:` in:\n$src")
    assert(src.contains("case Circle(r: _root_.scala.Double)"), s"expected `case Circle(r: _root_.scala.Double)` in:\n$src")
    assert(src.contains("case Square(side: _root_.scala.Double)"), s"expected `case Square(side: _root_.scala.Double)` in:\n$src")
    assert(!src.contains("case class"), s"a sum sort is not a record:\n$src")
  }

  test("WI-940: an eponymous variant ALONGSIDE siblings is REFUSED, not emitted wrong") {
    // §6.3 admits this shape ("an eponymous variant is a sibling of the other
    // variants of its sort", WI-946) and Scala has no spelling for it: the sum
    // and one of its cases would have to be one name in one scope. Emitting
    // `enum Node: case Node` would declare the nested `Node.Node` this whole
    // classification exists to remove, so it is refused loudly. No stdlib file
    // has this shape (measured), which is exactly why the case needs a fixture.
    //
    // CONTROL, MEASURED: replacing the refusal with `SortShape.Sum(ctors)` fails
    // THIS test and nothing else — the record collapse's own probe leaves it
    // green, so the two claims are pinned separately.
    val pf = parseSource(
      """namespace anthill.wi940
        |  sort Node
        |    entity Node(v: Int64)
        |    entity Leaf
        |  end
        |end
        |""".stripMargin, "node.anthill")
    val err = intercept[BootstrapError](gen(pf))
    assert(err.getMessage.contains("Node"), s"refusal must name the sort: ${err.getMessage}")
    assert(err.getMessage.contains("node.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  // ── WI-1055 Group A: information the parse IR already had, and dropped ────
  //
  // Each of these DRIVES the fix by compiling the emission. A string match alone
  // could not: every one of these files emitted, and looked emitted, while not
  // being Scala.

  test("WI-1055 A1/A2: monad.anthill COMPILES — operation type params and a higher-kinded sort param") {
    // TWO defects on one file, which is why it is the fixture for both arms.
    //   A2: `sort anthill.prelude.Monad[M[T]]` desugars its head parameter to a
    //       `SortWithBody` MARKED `isTypeParam`, and `emitSort` collected only the
    //       `AbstractSortItem` form — so this emitted `trait Monad:`, with no
    //       parameters at all and `M` unbound at every mention.
    //   A1: `operation pure[A](a: A) -> M[A]` emitted `def pure(a: A): M[A]`.
    //       `Operation.typeParams` has been in the IR since WI-269 and nothing in
    //       this backend ever read it.
    //
    // FAILS WHEN BACKED OUT, separately and MEASURED: drop the `isTypeParam` arm
    // from `sortTypeParams` and THIS test alone fails (A2); drop `op.typeParams`
    // from `OpGen.renderAbstract` and this test plus the nullary-enum test below
    // fail, since `Option`'s `optionPure[A]` loses its parameter too (A1). The two
    // string assertions name which arm each is, so a failure says WHICH half
    // regressed rather than only that the file stopped compiling.
    val files = gen(parseStdlib("anthill/prelude/monad.anthill"))
    val src = files.find(_.relPath.endsWith("/Monad.scala"))
      .getOrElse(fail(s"expected Monad.scala in: ${files.map(_.relPath)}")).contents
    assert(src.contains("trait Monad[M[_]]"),
      s"A2: the higher-kinded head parameter must reach the trait's binder:\n$src")
    assert(src.contains("def pure[A](a: A): M[A]"),
      s"A1: the operation's own type parameters must be bound:\n$src")
    ScalaCompile.assertCompiles("monad.anthill's emission", files)
  }

  test("WI-1055 A3: cell.anthill COMPILES — the enclosing sort's own name keeps its parameters") {
    // `sort Cell[V]` writes `operation get(c: Cell) -> V`: in anthill the sort's
    // parameters are already in scope at a bare mention of its own name, and Scala
    // has no bare spelling for that. `def get(c: Cell): V` is `Missing type
    // parameter for anthill.prelude.Cell`, six times over this one file.
    //
    // FAILS WHEN BACKED OUT, MEASURED: make `Placement.Enclosing` render
    // `self.scalaName` without re-attaching `self.params` and three tests fail —
    // this one, the `Pair` one below, and the enum-case coverage CONTROL, whose
    // `case Cons(head: T, tail: List[T])` names its own sort too. The string
    // assertion pins WHICH parameters are re-attached, which the compile cannot:
    // `Cell[Any]` would also compile.
    val files = gen(parseStdlib("anthill/prelude/cell.anthill"))
    val src = files.find(_.relPath.endsWith("/Cell.scala"))
      .getOrElse(fail(s"expected Cell.scala in: ${files.map(_.relPath)}")).contents
    assert(src.contains("def get(c: Cell[V]): V"),
      s"the sort's own parameters must be re-attached at a bare mention:\n$src")
    ScalaCompile.assertCompiles("cell.anthill's emission", files)
  }

  test("WI-1055 A3: a sort's own name is not rewritten through the prelude type map") {
    // WI-1021's headline, fixed by the same mechanism and therefore pinned here.
    // `mapPrelude` rewrote `Pair` to `Tuple2` unconditionally, INCLUDING inside
    // pair.anthill, so `operation fst(p: Pair) -> A` emitted `def fst(p: Tuple2): A`
    // — a different type from the declaration three lines above it, and one Scala
    // rejects bare (`Missing type parameter for [T1, T2] =>> (T1, T2)`).
    //
    // The enclosing sort answers BEFORE the type map (`TypeScope.place`), so the
    // name a file declares can no longer be captured by an entry meant for its
    // consumers. WI-1021 has since removed the `Pair -> Tuple2` entry outright —
    // the nominal-vs-host answer — so this now pins the ORDERING alone; the
    // consumer half has its own test below.
    //
    // FAILS WHEN BACKED OUT: reorder `place` to consult `types.preludeSort` before
    // `enclosing`, and a bare `Pair` no longer has parameters to re-attach — it is
    // a 0-argument write against a 2-parameter entry, so `generate` throws.
    val files = gen(parseStdlib("anthill/prelude/pair.anthill"))
    val src = files.find(_.relPath.endsWith("/Pair.scala"))
      .getOrElse(fail(s"expected Pair.scala in: ${files.map(_.relPath)}")).contents
    assert(!src.contains("Tuple2"),
      s"pair.anthill's own `Pair` must not be rewritten to the host type:\n$src")
    assert(src.contains("def fst(p: Pair[A, B]): A"),
      s"expected `def fst(p: Pair[A, B]): A` in:\n$src")
    ScalaCompile.assertCompiles("pair.anthill's emission", files)
  }

  // ── WI-1021: which prelude names have a HOST counterpart, and which are the
  //    prelude's own emitted type ────────────────────────────────────────────

  test("WI-1021: a prelude sort at a CONSUMER site is the emitted anthill type") {
    // THE DECISION. `Pair -> Tuple2` was not merely wrong inside pair.anthill
    // (WI-1055 A3 fixed that); it was wrong for the consumers it was written FOR.
    // pair.anthill emits `enum Pair[A, B]` into `anthill.prelude` and list.anthill,
    // four lines of output away, emitted `Option[Tuple2[T, List[T]]]` — one anthill
    // name denoting two unrelated Scala types in one tree, the host one structural
    // where anthill's has named fields, its own `eq`, and four conditioned
    // `provides` clauses no `Tuple2` can carry.
    //
    // DRIVEN BY COMPILING THE THREE FILES TOGETHER, not by the substring alone: the
    // point is that `List.splitFirst`'s result type is the SAME type pair.anthill
    // declares, and only a compile of both can say so.
    //
    // FAILS WHEN BACKED OUT, and note what backing out now COSTS: the two-table
    // split cannot express the old entry — `hostScalars` has no arity column and
    // `preludeSorts` has no name column — so it takes restoring a single
    // `(name, arity)` table and writing `case "Pair" => known("Tuple2", 2)`. Do
    // that and the `Tuple2` assertion fails. The COMPILE does not: `Tuple2` is a
    // real Scala type and the emission stays well-formed, which is exactly why
    // this needed a decision and not a compiler.
    val files = preludeClosure("pair", "option", "list")
    val list = files.find(_.relPath.endsWith("/List.scala"))
      .getOrElse(fail(s"expected List.scala in: ${files.map(_.relPath)}")).contents
    assert(list.contains("def splitFirst(xs: List[T]): " +
      "_root_.anthill.prelude.Option[_root_.anthill.prelude.Pair[T, List[T]]]"),
      s"a consumer must reach the prelude's OWN Pair/Option:\n$list")
    assert(!files.exists(_.contents.contains("Tuple2")),
      "no emission may name the host tuple: " +
      files.filter(_.contents.contains("Tuple2")).map(_.relPath).mkString(", "))
    ScalaCompile.assertCompiles("the pair/option/list closure", files)
  }

  test("WI-1021: a prelude sort is emitted QUALIFIED, so an absent sibling cannot capture") {
    // THE SECOND HALF OF THE DECISION, and the reason the entries were RE-POINTED
    // rather than deleted. `List -> List`, `Option -> Option`, `Set -> Set` and
    // `Map -> Map` emitted a BARE name that is also root-imported, so what the
    // emission meant depended on what else was in the compilation: with the sibling
    // present `anthill.prelude.Option`, without it `scala.Option`. That is the
    // `Numeric` / `scala.math.Numeric` capture `Placement.Ambient` exists to close
    // (see the B1 CONTROL above), reintroduced by a table entry.
    //
    // Deleting the entries would have closed the capture too, by dropping the name
    // to `Ambient` — but Ambient qualifies with the DECLARATION's package, which is
    // right only inside the prelude and would emit `my.app.Option` for a project
    // consumer, and it performs no arity check on exactly the names WI-1055 B3
    // added one for. Re-pointing keeps both.
    //
    // FAILS WHEN BACKED OUT, in one edit: drop the `_root_.` anchor and the package
    // from `Bootstrap.EmittedType.qualified` — the one place a derived entry's spelling
    // is built — and this assertion finds no such error. MEASURED (before WI-1060 the
    // same edit was to `TypeGen.preludeSort`'s hardcoded strings, and the outcome was
    // identical):
    // the bare emission reports `Not found: type Pair` instead (Scala 3 root-imports
    // no `Pair`, only `Tuple2`), so the file still fails to compile alone but for a
    // reason that says nothing about capture. `Option` is the one that silently
    // rebinds, and it is why the assertion names `Option` specifically.
    val list = gen(parseStdlib("anthill/prelude/list.anthill"))
    val errs = ScalaCompile.errors(list)
    assert(errs.exists(_.message.contains("Option is not a member of anthill.prelude")),
      "compiling List.scala ALONE must fail on the missing sibling rather than " +
      s"silently binding scala.Option; got: ${errs.map(_.render)}")
    // THE CONTROL for the same emission: with the sibling present it is not a
    // missing name, it is the right one. Without this arm "does not compile alone"
    // could be satisfied by any breakage at all.
    ScalaCompile.assertCompiles("list + its siblings",
      list ++ preludeClosure("option", "pair"))
  }

  test("WI-1021: an effect-carrying collection places against the prelude's own arity") {
    // `Stream -> LazyList` was the entry whose wrongness showed as ARITY: anthill's
    // `Stream` has two parameters (`sort T` and `effects E`) and `LazyList` has one,
    // so every written occurrence was a refusal — `iterable.anthill` and
    // `combinators.anthill` were out of the emitted tree entirely. There is no
    // same-arity Scala counterpart to find, because the effect row is a parameter
    // Scala's collection does not have; the answer is that `Stream` was never a host
    // type. It now places against the `trait Stream` that stream.anthill itself
    // emits.
    //
    // THE ARITY THE ENTRY CLAIMS IS ANTHILL'S — two, `sort T = ?` and
    // `effects E = ?` — and since WI-1062 that is no longer the emitted one: §2.8a
    // erases the effect parameter, so a use site writes two arguments and gets
    // `Stream[T]`. Both numbers are in the entry (`ParamKinds`), and per POSITION
    // rather than as a pair of counts, because dropping an argument list needs to
    // know WHICH slot went.
    //
    // A FIXTURE and not iterable.anthill, which was refused when this was written
    // and now emits — see the WI-1062 tests below, where iterable.anthill itself
    // drives the same claim. A fixture keeps THIS assertion about the table entry:
    // `Reader` declares two ORDINARY parameters and hands the second to `Stream`'s
    // effect slot, so what erases the argument is unambiguously the callee's
    // declaration and nothing about the argument.
    //
    // FAILS WHEN BACKED OUT, in one edit — and since WI-1060 the entry is DERIVED, so
    // the edit is to what it is derived from: delete `effects E = ?` from
    // stream.anthill and `Stream` has the one parameter the `LazyList` entry claimed,
    // so `generate` throws `declares 1 type parameter(s), but 2 were written` — the
    // same refusal, now against the right type. Make `Bootstrap.paramKinds` return
    // `ParamKind.Type` for every declaration and the two parameters become ORDINARY,
    // so the emission is `Stream[T, E]` — the WI-1062 half.
    val files = gen(parseSource(
      """namespace anthill.wi1021
        |  sort Reader
        |    sort T = ?
        |    sort E = ?
        |    operation source(r: Reader) -> Stream[T = T, E = E]
        |  end
        |end
        |""".stripMargin, "reader.anthill"))
    val src = files.head.contents
    assert(src.contains("def source(r: Reader[T, E]): _root_.anthill.prelude.Stream[T]"),
      s"a written Stream occurrence must reach the prelude's own Stream, with its " +
      s"effect argument erased:\n$src")
    ScalaCompile.assertCompiles("reader.anthill + stream.anthill",
      files ++ preludeClosure("stream", "option", "pair", "list"))
  }

  // ── WI-1062: an effect PARAMETER is erased, and its argument with it ────────
  //
  // THE DECISION, `docs/scala-forward-mapping.md` §2.8a. §2.8 already erased
  // effects from a method's SHAPE and said nothing about a sort's effect
  // PARAMETERS, which left `Stream[Element, E]` with an argument that had to
  // become a Scala type and nothing to become. The answer is that the parameter
  // goes too: `sort anthill.prelude.Stream` emits `trait Stream[T]`, and a written
  // occurrence's second argument is dropped with the slot it filled.
  //
  // WHICH END DECIDES is the part that needed a ticket, and it is split: the
  // DECLARATION where Bootstrap can see one, the ARGUMENT where it cannot. The two
  // tests below drive one arm each, and the delay.anthill refusal (WI-1055 B2
  // above) is what the split buys — a row in an ORDINARY parameter is a graded
  // monad's index, not an erasable annotation.

  test("WI-1062: an effect parameter is erased from the emitted sort, and so is its argument") {
    // BOTH HALVES OF §2.8a IN ONE FILE, because they are one decision read from
    // two sides: `stream.anthill` declares `sort T = ?` + `effects E = ?` and emits
    // `trait Stream[T]`; `iterable.anthill` WRITES `Stream[Element, E]` and gets
    // `Stream[Element]`. A test asserting only the declaration side would pass with
    // every use site refused, which is the state this ticket found.
    //
    // THE ARGUMENT ERASED HERE IS A PLAIN NAME. `Stream[Element, E]` says nothing
    // syntactic about `E` — it is an identifier in a type-argument slot, exactly
    // like `Element` beside it — so nothing but `Stream`'s own declaration can say
    // it goes. That is the whole reason the rule is declaration-driven and not
    // "drop anything that looks like a row".
    //
    // FAILS WHEN BACKED OUT: make `Bootstrap.paramKinds` return `ParamKind.Type` for
    // every declaration — which gives the derived `Stream` entry two ORDINARY
    // parameters — and the emitted `Iterable.iterator` becomes `Stream[Element, E]`
    // with `E` unbound — the first assertion fails and the compile below fails
    // again on `Not found: type E`. Drop `isEffectRow` at
    // `AnthillParser.effectsSortItem` and `trait Stream[T, E]` comes back, failing
    // the arity assertion.
    val stream = gen(parseStdlib("anthill/prelude/stream.anthill"))
    assert(stream.head.contents.contains("trait Stream[T]:"),
      s"an effect parameter must not reach the emitted type:\n${stream.head.contents}")
    val iterable = gen(parseStdlib("anthill/prelude/iterable.anthill"))
    val src = iterable.head.contents
    assert(src.contains("trait Iterable[C, Element]:"),
      s"Iterable's own `effects E = ?` must be erased too:\n$src")
    assert(src.contains("def iterator(c: C): _root_.anthill.prelude.Stream[Element]"),
      s"the argument in the erased slot must go with it:\n$src")
    // The row LITERAL form of the same slot, and the operation type parameter that
    // only ever stands in a row: `map[Dst, EffP](…) -> Stream[Dst, {E, EffP}]`
    // emits neither `EffP` nor the row.
    assert(src.contains("def map[Dst](c: C, f: (Element) => Dst): " +
      "_root_.anthill.prelude.Stream[Dst]"),
      s"a row literal and a row-only operation parameter must both be erased:\n$src")
    // DRIVES IT: the two files plus what they name must actually compile. This is
    // the acceptance the ticket names — iterable.anthill and combinators.anthill
    // were out of the tree entirely, and through `Iterable` so were their
    // dependents.
    ScalaCompile.assertCompiles("the iterable/combinators closure",
      iterable ++ preludeClosure("stream", "combinators", "option", "pair", "list"))
  }

  test("WI-1062: where no declaration is in reach, the ARGUMENT says it is an effect") {
    // The other arm. `Placement.Ambient` is a name whose declaration lives in a
    // file Bootstrap has not read (per-file by design, proposal 034), so nothing
    // says which of ITS slots erase — and a `requires Foo[C = C, Element = Element,
    // E = E]` still has to emit something. The argument decides there: `E` is a name
    // THIS file declares `effects E = ?`, which is a locally provable fact about the
    // argument and not a guess about the callee.
    //
    // THE FIXTURE NAMES A SORT NOTHING DECLARES, and that is a WI-1060 edit worth
    // stating rather than a fixture written obscurely. It used to name `Iterable`,
    // whose declaration was out of reach only because Bootstrap is per-file; the
    // prelude table is now derived from the prelude's own files, so `Iterable` is
    // placed by iterable.anthill and its `effects E = ?` slot erases on the
    // DECLARATION side — the arm above, not this one. Keeping `Iterable` here would
    // have left this test passing while measuring the other rule, which is exactly
    // the failure mode "assert the CONTROL too" names. `Ambient`'s honest residue is
    // a file the caller never passed, so the fixture names one.
    //
    // COMPILED AGAINST A HAND-WRITTEN SIBLING, since by construction no emitted file
    // declares `Extern` — that stub is what a file Bootstrap has not read looks like
    // from here, and compiling against it is what makes the two-argument emission an
    // assertion about a real supertype rather than about a string.
    //
    // FAILS WHEN BACKED OUT: make `named` pass an Ambient name's arguments through
    // unerased and the emission becomes `extends anthill.prelude.Extern[C, Element, E]`
    // — the assertion fails and the compile reports `Too many type arguments for
    // trait Extern`.
    val fixture = gen(parseSource(
      """namespace anthill.prelude
        |  sort Walkable
        |    sort C = ?
        |    sort Element = ?
        |    effects E = ?
        |    requires Extern[C = C, Element = Element, E = E]
        |    operation walked(c: C) -> Element effects E
        |  end
        |end
        |""".stripMargin, "walkable.anthill"))
    val fsrc = fixture.head.contents
    assert(fsrc.contains("trait Walkable[C, Element] extends " +
      "anthill.prelude.Extern[C, Element]:"),
      s"an ambient name's effect argument must be erased from the argument side:\n$fsrc")
    ScalaCompile.assertCompiles("walkable.anthill against an unread sibling",
      fixture :+ GeneratedFile("src/main/scala/anthill/prelude/Extern.scala",
        "package anthill.prelude\n\ntrait Extern[C, Element]\n"))

    // THE DECLARATION SIDE ON THE SAME SHAPE, so the two rules are seen to agree
    // where both can run (WI-1062's rule is that the declaration answers first).
    // Identical but for the name, and `Iterable` really does declare
    // `sort C`, `sort Element`, `effects E` — so the erasure below is iterable.anthill's
    // answer and the one above is the argument's.
    val declared = gen(parseSource(
      """namespace anthill.prelude
        |  sort Walkable2
        |    sort C = ?
        |    sort Element = ?
        |    effects E = ?
        |    requires Iterable[C = C, Element = Element, E = E]
        |    operation walked(c: C) -> Element effects E
        |  end
        |end
        |""".stripMargin, "walkable2.anthill")).head.contents
    assert(declared.contains("trait Walkable2[C, Element] extends " +
      "_root_.anthill.prelude.Iterable[C, Element]:"),
      s"a placed name's effect slot must erase on the declaration side:\n$declared")

    // THE CORPUS INSTANCE, asserted on its emitted TEXT here; the closure COMPILE
    // is WI-1065's test below. When these files entered the tree, `requires` ->
    // `extends` (§2.7) turned out to be unsound in two shapes neither of which is
    // about effects: `FiniteMappedStream` is a DATA sort that `requires` an
    // algebra, so its enum case inherited nine abstract members (WI-1064), and
    // `FiniteCollection.map` SHADOWS `Iterable.map` with a different return type —
    // distinct operations per kernel §8.7, which Scala's one override group cannot
    // hold (WI-1065). Both are since fixed, which is why the corpus header below
    // carries NO supertrait where the non-shadowing fixture above keeps one.
    //
    // What IS this ticket's, and is asserted: the arities. The nested
    // `FiniteMappedStream[SrcC = C, Src = Element, T = Dst, ES = E, EF = EffP]` is
    // written with five arguments, of which `ES = E` is a sort effect parameter and
    // `EF = EffP` is an operation type parameter this signature only ever uses
    // inside a row — three survive, matching the three the emission declares.
    val src = gen(parseStdlib("anthill/prelude/finite_collection.anthill"))
      .head.contents
    assert(src.contains("trait FiniteCollection[C, Element]:"),
      s"the corpus instance must erase the same way as the fixture:\n$src")
    assert(src.contains("def map[Dst](c: C, f: (Element) => Dst): " +
      "FiniteCollection[_root_.anthill.prelude.FiniteMappedStream[C, Element, Dst], Dst]"),
      s"an operation's row-only type parameter must erase like a sort's:\n$src")
    val fmapped = gen(parseStdlib("anthill/prelude/finite_combinators.anthill"))
      .head.contents
    assert(fmapped.contains("enum FiniteMappedStream[SrcC, Src, T]"),
      s"the three surviving arguments must be the three the declaration emits:\n$fmapped")
  }

  test("WI-1062: an effect parameter written where a TYPE belongs is refused") {
    // The third arm, and the only one that is a refusal rather than an erasure:
    // an effect parameter's NAME reaching a slot that is not erased with it.
    // `Placement.ErasedEffect` is what says so, and it is the answer `place`
    // returns for the name — the same answer `isEffectArgument` reads to drop an
    // argument, so this arm and the erasure are two consumers of one fact rather
    // than two predicates that must agree.
    //
    // A FIXTURE, because no stdlib file writes the shape — every prelude
    // occurrence of an effect parameter is inside a slot that erases. Without it
    // the arm is unreachable in the suite and could be deleted with nothing
    // failing, which is the standard the sibling B2 arms are held to.
    //
    // FAILS WHEN BACKED OUT: make `place` return `Placement.TypeParam("E", 0)`
    // for an effect parameter and this emits `def leak(c: C): E` with `E` bound to
    // nothing — the `intercept` finds no throw.
    val err = intercept[BootstrapError](gen(parseSource(
      """namespace anthill.wi1062
        |  sort Leaky
        |    sort C = ?
        |    effects E = ?
        |    operation leak(c: C) -> E
        |  end
        |end
        |""".stripMargin, "leaky.anthill")))
    assert(err.getMessage.contains("`E` is an effect row, not a type"),
      s"refusal must say what defeated it: ${err.getMessage}")
    assert(err.getMessage.contains("`leak`"),
      s"refusal must name the declaration: ${err.getMessage}")
    assert(err.getMessage.contains("leaky.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1062 CONTROL: a sort with no effect parameter is emitted and applied unchanged") {
    // The boundary. Erasure keys on the `effects E = ?` SPELLING, so a sort whose
    // parameters are all `sort X = ?` must keep every one of them — including a
    // parameter NAMED `E`, and including one holding an effect row as a value.
    //
    // Passes both with and without §2.8a BY DESIGN — that is what makes it the
    // control. What it would catch is an erasure keyed on anything looser than the
    // declaration: on the name (`E` here would vanish), or on the argument's shape
    // (delay.anthill's `Delay[T = A, E = {}]`, which is refused rather than
    // collapsed — see the WI-1055 B2 arm).
    val files = gen(parseSource(
      """namespace anthill.wi1062
        |  sort Graded
        |    sort T = ?
        |    sort E = ?
        |    operation of(g: Graded) -> Graded[T = T, E = E]
        |  end
        |end
        |""".stripMargin, "graded.anthill"))
    val src = files.head.contents
    assert(src.contains("trait Graded[T, E]:"),
      s"an ordinary parameter named `E` is not an effect parameter:\n$src")
    assert(src.contains("def of(g: Graded[T, E]): Graded[T, E]"),
      s"nothing may be erased from a sort that declares no effect parameter:\n$src")
    ScalaCompile.assertCompiles("graded.anthill", files)
  }

  test("WI-1021: a SCALAR maps to its host type, and to a 64-bit one") {
    // The boundary of the decision, and the reason it is not "no anthill sort maps
    // to a host type". A scalar cannot be BUILT in anthill — `int64.anthill`
    // declares no `entity` and nothing but a literal makes one — so the host type
    // is the carrier and there is no rival anthill value for it to disagree with.
    // Every re-pointed name fails that test: `List`/`Option`/`Pair` have anthill
    // constructors, `Set`/`Map`/`Stream` have a provider-chosen carrier.
    //
    // `Int64` IS `Long`. The table said `Int` — 32-bit, so every anthill value above
    // 2^31-1 truncated silently. `rust_std` maps the same sort to `i64` and
    // `cpp_std` to `int64_t`; this was the outlier, and it predates WI-1021.
    //
    // FAILS WHEN BACKED OUT: restore `"Int64" -> "_root_.scala.Int"` and this fails
    // twice over — the spelling assertion, and the `Probe` compile, which is the arm
    // that would still catch it if someone "fixed" the expected string. MEASURED:
    // three other expectations move with it (the `Acct`, `Slot` and own-file
    // signatures), so the width is pinned in four places and the spelling in one.
    val files = gen(parseSource(
      """namespace anthill.wi1021
        |  entity Tick(n: Int64, on: Bool, tag: String, ratio: Float)
        |end
        |""".stripMargin, "tick.anthill"))
    assert(files.head.contents.contains(
      "case class Tick(n: _root_.scala.Long, on: _root_.scala.Boolean, " +
      "tag: _root_.java.lang.String, ratio: _root_.scala.Double)"),
      s"the scalar half of the type map must still fire:\n${files.head.contents}")
    // DRIVES the width rather than pinning a spelling: a value no `Int` can hold
    // must type-check against the emitted field.
    ScalaCompile.assertCompiles("tick.anthill's emission", files :+ GeneratedFile(
      "src/main/scala/anthill/wi1021/Probe.scala",
      "package anthill.wi1021\nobject Probe:\n  val t = Tick(9223372036854775807L, true, \"x\", 1.0)\n"))
  }

  test("WI-1021: a scalar means the HOST type inside its own file too") {
    // The one inversion in `TypeScope.place`'s precedence, and it is the same rule
    // rather than an exception: a scalar has no anthill values, so `Int64` denotes
    // the carrier everywhere — including in int64.anthill, which declares it.
    //
    // Read most-local-first, the enclosing sort answered first and `int64.anthill`
    // emitted `def compare(a: Int64, b: Int64): Int64` on the `trait Int64` it was
    // emitting — a trait no value inhabits, over a name every CONSUMER of the same
    // file resolves to `Long`. That is one anthill name denoting two unrelated Scala
    // types in one tree, which is the defect this whole ticket removes, surviving
    // inside the five files that declare a scalar.
    //
    // FAILS WHEN BACKED OUT: move `types.hostScalar` back below `enclosing` in
    // `place` and every assertion here fails, naming `Int64` where `Long` belongs.
    val files = gen(parseStdlib("anthill/prelude/int64.anthill"))
    val src = files.head.contents
    assert(src.contains("trait Int64:"),
      s"the algebra trait is still emitted under its anthill name:\n$src")
    assert(src.contains(
      "def compare(a: _root_.scala.Long, b: _root_.scala.Long): _root_.scala.Long"),
      s"a scalar's own members are typed by the CARRIER, not by its algebra:\n$src")
    assert(!src.contains(": Int64"),
      s"no member may be typed by the algebra trait:\n$src")
    ScalaCompile.assertCompiles("int64.anthill's emission", files)
  }

  test("WI-1055: a nullary case of a PARAMETERIZED enum is reparameterized") {
    // `enum Option[T]: case None` is `cannot determine type argument for enum
    // parent class Option, type parameter type T is invariant` — a case
    // mentioning none of the enum's parameters gives Scala nothing to infer them
    // from. option.anthill and list.anthill both shipped that way.
    //
    // `case None[T]() extends Option[T]` and NOT the covariant idiom `extends
    // Option[Nothing]`: anthill's `none` is polymorphic and an anthill sort
    // declares no variance, so `Option[Nothing]` would be a value that no
    // `Option[Int]` context could accept. Asserted, because both spellings
    // compile and only one means what the declaration says.
    //
    // FAILS WHEN BACKED OUT: emit a bare `case None` and the compile reports the
    // enum-parent error. The UNPARAMETERIZED control is the `Shape` fixture in the
    // WI-940 CONTROL test above, which keeps its bare `case Circle(...)`.
    val files = gen(parseStdlib("anthill/prelude/option.anthill"))
    val src = files.find(_.relPath.endsWith("/Option.scala"))
      .getOrElse(fail(s"expected Option.scala in: ${files.map(_.relPath)}")).contents
    assert(src.contains("case None[T]() extends Option[T]"),
      s"expected the reparameterized nullary case in:\n$src")
    ScalaCompile.assertCompiles("option.anthill's emission", files)
  }

  test("WI-1055: an enum case that leaves a parameter UNMENTIONED names its parent") {
    // The rule is parameter COVERAGE, not arity. `case Left(v: L)` in a
    // two-parameter enum has a field and still leaves `R` uninferable, so it is the
    // same `cannot determine type argument` failure the nullary case gives — and
    // keying the fix on "the case has no fields" would have missed it.
    //
    // A FIXTURE, because no prelude sort has this shape. That is exactly why the
    // proxy would have looked correct indefinitely: it is right on every file in
    // the tree today and wrong on the first one that is not.
    //
    // FAILS WHEN BACKED OUT: key `renderMainSort`'s branch on `c.fields.isEmpty`
    // instead of `uncoveredParams` and the compile reports the enum-parent error
    // for both cases. The CONTROL below is the other direction — a case that DOES
    // cover its parameters is left alone.
    val files = gen(parseSource(
      """namespace anthill.wi1055
        |  sort Either
        |    sort L = ?
        |    sort R = ?
        |    entity left(v: L)
        |    entity right(v: R)
        |  end
        |end
        |""".stripMargin, "either.anthill"))
    val src = files.head.contents
    assert(src.contains("case Left[L, R](v: L) extends Either[L, R]"),
      s"a case not covering every parameter must name its parent:\n$src")
    assert(src.contains("case Right[L, R](v: R) extends Either[L, R]"),
      s"a case not covering every parameter must name its parent:\n$src")
    ScalaCompile.assertCompiles("a partially-covering enum", files)
  }

  test("WI-1055 CONTROL: an enum case COVERING every parameter is left alone") {
    // The other direction of the coverage rule, and the reason it is not "always
    // reparameterize": `case Cons(head: T, tail: List[T])` mentions `T`, so Scala
    // infers the parent and the plain spelling is both shorter and what
    // `docs/scala-forward-mapping.md` §2.3 shows. Passes with and without the
    // coverage check BY DESIGN — its job is to say the fix did not widen into every
    // case.
    val files = gen(parseStdlib("anthill/prelude/list.anthill"))
    val src = files.find(_.relPath.endsWith("/List.scala"))
      .getOrElse(fail(s"expected List.scala in: ${files.map(_.relPath)}")).contents
    assert(src.contains("  case Cons(head: T, tail: List[T])\n"),
      s"a fully-covering case must keep the inferred form:\n$src")
    assert(src.contains("case Nil[T]() extends List[T]"),
      s"and its nullary sibling must still name the parent:\n$src")
  }

  test("WI-1055 CONTROL: an unparameterized enum's nullary case stays bare") {
    // The reparameterization is keyed on the enum HAVING parameters, not on the
    // case being nullary. `case Red[]() extends Colour[]` is not Scala, so this
    // passes both with and without the change BY DESIGN — its job is to say the
    // fix did not widen past the shape that needs it.
    val files = gen(parseSource(
      """namespace anthill.wi1055
        |  sort Colour
        |    entity Red
        |    entity Green
        |  end
        |end
        |""".stripMargin, "colour.anthill"))
    val src = files.head.contents
    assert(src.contains("  case Red\n"), s"expected a bare `case Red` in:\n$src")
    ScalaCompile.assertCompiles("an unparameterized enum", files)
  }

  // ── WI-1055 Group B: refusals ─────────────────────────────────────────────
  //
  // Each arm has its own test because each is a separate claim about what
  // Bootstrap can and cannot know from the parse IR, and a single "these files
  // are refused" assertion would stay green if two arms swapped which case they
  // caught. Every one asserts the message NAMES the declaration and is LOCATED —
  // a refusal that says only "cannot emit" recreates the blindness it replaced.

  test("WI-1055 B1: a name imported from ANOTHER package is refused, not emitted bare") {
    // `effects.anthill` writes `import anthill.reflect.{NodeOccurrence, Term}` and
    // its sorts emit into `anthill.prelude`. A bare `NodeOccurrence` there reaches
    // nothing, and Bootstrap can PROVE it: the import says which package the name
    // lives in, and Bootstrap emits no Scala `import`.
    //
    // This is the half of B1 that is decidable. The other half — a bare name a
    // sibling file declares in the same package — is NOT refused, and has its own
    // control below.
    //
    // FAILS WHEN BACKED OUT: drop the `importedFrom` arm of `TypeScope.unreachable`
    // and this file emits `case class MatchFailed(occurrence: NodeOccurrence, ...)`
    // with no refusal at all.
    val err = intercept[BootstrapError](
      gen(parseStdlib("anthill/prelude/effects.anthill")))
    assert(err.getMessage.contains("NodeOccurrence"),
      s"refusal must name the type it could not place: ${err.getMessage}")
    assert(err.getMessage.contains("anthill.reflect"),
      s"refusal must say where the name was imported from: ${err.getMessage}")
    assert(err.getMessage.contains("MatchFailed"),
      s"refusal must name the declaration: ${err.getMessage}")
    assert(err.getMessage.contains("effects.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1055 B1: a name this file DECLARES and Bootstrap emits no type for is refused") {
    // `sort.anthill` declares `sort Type = ?` at NAMESPACE level — an opaque handle
    // whose Scala spelling would be an `opaque type`, which needs an enclosing
    // object rather than a package. Bootstrap emits nothing for it, and
    // `EffectExpression`'s members are typed by it, so a bare `Type` in the output
    // names nothing in the tree.
    //
    // Distinct from the import arm: nothing is imported here, and the proof is that
    // the file itself declares the name in a position with no emission.
    //
    // FAILS WHEN BACKED OUT: drop the `declaredNotEmitted` arm and `present(label:
    // Type)` emits, naming a type nowhere in the closure.
    val err = intercept[BootstrapError](
      gen(parseStdlib("anthill/prelude/sort.anthill")))
    assert(err.getMessage.contains("`Type`"),
      s"refusal must name the type: ${err.getMessage}")
    assert(err.getMessage.contains("EffectExpression"),
      s"refusal must name the declaration: ${err.getMessage}")
    assert(err.getMessage.contains("sort.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1055 B1 CONTROL: an unplaced SAME-PACKAGE name is emitted QUALIFIED, not refused") {
    // The boundary of B1, and the reason it is not "refuse every name I cannot
    // resolve". A `requires Eq[T]` may name a sort a SIBLING FILE declares in the
    // same namespace — anthill's enclosing-namespace and auto-prelude lookups both
    // land there, and so does Scala's package scope. Refusing these took thirteen
    // prelude files out of the tree (measured) to catch nothing the closure compile
    // does not already catch.
    //
    // It is emitted QUALIFIED rather than bare, which is the part that is not a
    // hope: a bare mention also resolves against Scala's root imports, so an
    // ABSENT sibling does not fail, it CAPTURES. Measured — `field.anthill` emitted
    // a bare `Numeric`, compiled green, and meant `scala.math.Numeric`.
    //
    // A FIXTURE SINCE WI-1060, and `field.anthill` is why the change was needed
    // rather than cosmetic: `Numeric` is a PRELUDE sort, so the derived table now
    // places it and the corpus file no longer takes this path at all (it emits
    // `_root_.anthill.prelude.Numeric[T]`, checked against numeric.anthill's own
    // parameter count — strictly better, and a different rule). What is left of
    // Ambient is a name from a file the CALLER never passed: a project's own sibling.
    // The fixture is that, in a package with no prelude standing behind it.
    //
    // THE REQUIREMENT IS NOT SPELLED `Numeric`, and the reason is the shadowing gap
    // TypeGen states: `my.app`'s OWN `Numeric`, declared in a SIBLING FILE with no
    // import, is still emitted `_root_.anthill.prelude.Numeric` (measured — it is what
    // the first draft of this fixture did). `fileTypes` is per-file and the caller's
    // auto-import set is the prelude, so nothing here knows the project declares one.
    // The IMPORTED half of that gap is closed and has its own test below; this half
    // needs a resolved project closure, not a `place` link.
    //
    // FAILS WHEN BACKED OUT, in both directions: make `Ambient` a refusal and the
    // `generate` call throws; make it emit bare and the `contains` below fails
    // while the file still "compiles" — against `scala.math.Numeric`'s neighbours.
    val files = gen(parseSource(
      """namespace my.app
        |  sort Field2
        |    sort T = ?
        |    requires AppNumeric[T]
        |    operation div(a: T, b: T) -> T
        |  end
        |end
        |""".stripMargin, "field2.anthill"))
    val src = files.find(_.relPath.endsWith("/Field2.scala"))
      .getOrElse(fail(s"expected Field2.scala in: ${files.map(_.relPath)}")).contents
    assert(src.contains("extends my.app.AppNumeric[T]"),
      s"a sibling-file name must be emitted qualified, so it cannot capture:\n$src")
    val errs = ScalaCompile.errors(files)
    assert(errs.exists(_.message.contains("AppNumeric is not a member of my.app")),
      "compiling Field2.scala ALONE must fail on the missing sibling rather than " +
      s"binding whatever a bare mention would reach; got: ${errs.map(_.render)}")
  }

  test("WI-1055 B2: a type VARIABLE in a type position is refused") {
    // `TypeGen` rendered `TypeExpr.Variable` as the literal `?`, which is not a
    // Scala type — so the emitted file did not even parse. What the variable
    // stands for is a typer question and scaland has no typer.
    //
    // A FIXTURE, and it was logical_stream.anthill until WI-1062. That file writes
    // `LogicalStream[?A]` — one argument against a sort declaring two — so it is
    // BOTH a bare variable and a partial application, and erasure made the arity
    // check run first (arguments are placed before they are rendered, so an
    // argument in an erased slot is never rendered at all). The stdlib instance
    // therefore no longer reaches this arm FIRST, and a test that depends on which
    // of two true diagnoses wins is measuring the wrong thing. Same reason the
    // other two B2 arms are fixtures.
    //
    // ARITY-CORRECT ON PURPOSE: one argument against the one-parameter `Option`, so
    // nothing but the variable can defeat it.
    //
    // FAILS WHEN BACKED OUT: restore `case TypeExpr.Variable(_, _) => "?"` and this
    // `intercept` finds no throw.
    val err = intercept[BootstrapError](gen(parseSource(
      """namespace anthill.wi1055
        |  sort Holder
        |    operation get() -> Option[?A]
        |  end
        |end
        |""".stripMargin, "holder.anthill")))
    assert(err.getMessage.contains("type VARIABLE"),
      s"refusal must say what defeated it: ${err.getMessage}")
    assert(err.getMessage.contains("`get`"),
      s"refusal must name the declaration: ${err.getMessage}")
    assert(err.getMessage.contains("holder.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1055 B2 / WI-1062: an effect row in an ORDINARY parameter slot is refused") {
    // WHAT IS LEFT OF THE B2 EFFECT-ROW REFUSAL once §2.8a erases effect
    // PARAMETERS. It used to fire on any written row and took eight prelude files
    // with it; it now fires only where the DECLARATION says the slot holds a type,
    // which is one file and one construct.
    //
    // delay.anthill is that construct and is why the arm is not dead code. Its
    // graded monad (proposal 047) declares `sort E = ?` — an ORDINARY parameter —
    // and stores the captured effect set in it, so `pure`'s `M[T = A, E = {}]` and
    // `delay`'s `M[T = A, E = EffP]` are DIFFERENT types. Erasing `E` would make
    // them one, which is the entire content of the grading; `Any` (what this
    // emitted before WI-1055) collapses them the same way while compiling.
    //
    // FAILS WHEN BACKED OUT, two ways: restore `case TypeExpr.EffectRow(_) => "Any"`
    // and the `intercept` finds no throw; alternatively erase a written row
    // wherever it stands instead of asking the declaration, and delay.anthill emits
    // `M[A]` against a two-member `M[T, E]` — MEASURED, the refusal disappears from
    // the named list above.
    val err = intercept[BootstrapError](
      gen(parseStdlib("anthill/prelude/delay.anthill")))
    assert(err.getMessage.contains("ORDINARY type-parameter slot"),
      s"refusal must say what defeated it: ${err.getMessage}")
    assert(err.getMessage.contains("proposal 047"),
      s"refusal must name the construct it is protecting: ${err.getMessage}")
    assert(err.getMessage.contains("`pure`"),
      s"refusal must name the declaration: ${err.getMessage}")
    assert(err.getMessage.contains("delay.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1055 B2: a VALUE in a type-argument slot is refused") {
    // Value-in-type (WI-302): Scala has no dependent type slot to put the literal
    // in, and `Any` was emitted. No stdlib file writes one, which is exactly why
    // this arm needs a fixture — without it the case is unreachable in the suite
    // and could be deleted with nothing failing.
    //
    // `Vector`, which nothing declares, and not `List`: WI-302's own example is
    // `Vector[Int64, 3]`, and an unplaced name reaches `Placement.Ambient`, whose
    // arguments pass through unchecked. Written against `List` the occurrence is
    // two arguments to a one-parameter sort, so since WI-1062 the ARITY refusal
    // fires first and this arm is never reached — the literal has to be the only
    // thing wrong with the type for the test to be about the literal.
    //
    // FAILS WHEN BACKED OUT: restore `case TypeExpr.Denoted(_) => "Any"`.
    val err = intercept[BootstrapError](gen(parseSource(
      """namespace anthill.wi1055
        |  sort Buf
        |    entity Buf(cells: Vector[Int64, 3])
        |  end
        |end
        |""".stripMargin, "buf.anthill")))
    assert(err.getMessage.contains("value in a type-argument slot"),
      s"refusal must say what defeated it: ${err.getMessage}")
    assert(err.getMessage.contains("buf.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1055 B3: a PARTIAL application of a mapped type is refused") {
    // The arity guard's surviving half. It had two: an arity-incompatible map ENTRY
    // (`Stream[Element, E]` against a one-parameter `LazyList`) and a partial
    // APPLICATION. WI-1021 removed the first shape from the table — every entry now
    // names a type of the arity it claims — so what is left to drive is a written
    // occurrence with too few arguments.
    //
    // A FIXTURE, and it is WI-1021's own headline shape read from OUTSIDE: inside
    // pair.anthill `p: Pair` is the enclosing sort and gets `[A, B]` re-attached,
    // but a consumer writing the same bare `Pair` has nothing to re-attach from.
    // Scala has no bare type constructor here, so this is a refusal and not a
    // rendering choice. No stdlib file writes one, which is why the arm needs a
    // fixture: without it the guard is unreachable in the suite and could be
    // deleted with nothing failing.
    //
    // FAILS WHEN BACKED OUT: drop the `args.length != kinds.written` guard in
    // `Placement.Known` and this emits `def swap(p: anthill.prelude.Pair): ...`,
    // which is `Missing type parameter`.
    val err = intercept[BootstrapError](gen(parseSource(
      """namespace anthill.wi1021
        |  sort Flip
        |    operation swap(p: Pair) -> Pair
        |  end
        |end
        |""".stripMargin, "flip.anthill")))
    assert(err.getMessage.contains("`Pair` maps to Scala `_root_.anthill.prelude.Pair`"),
      s"refusal must name both sides of the mapping: ${err.getMessage}")
    // The count is what ANTHILL declares, which since WI-1062 is not always what
    // Scala takes. `Pair` erases nothing, so the two agree here and the message
    // carries no erasure clause — the arm that says so is the `Stream` test below.
    assert(err.getMessage.contains("declares 2 type parameter(s), but 0 were written"),
      s"refusal must state the arity conflict: ${err.getMessage}")
    assert(!err.getMessage.contains("erased"),
      s"a sort with no effect parameter must not mention erasure: ${err.getMessage}")
    assert(err.getMessage.contains("flip.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1055 B3 CONTROL: an arity-COMPATIBLE map entry still maps") {
    // The arity check must not have turned the type map off. `Option[T = Int64]`
    // is one written argument against the one-parameter `Option`, and still maps.
    // Passes with and without the B3 guard BY DESIGN.
    //
    // ALSO WI-1021's project-consumer case, which no prelude file can show: this
    // namespace is not `anthill.prelude`, so the two halves of the map are visibly
    // different answers — `Int64` reaches the HOST `Int`, `Option` reaches the
    // prelude's OWN emitted type, qualified. Deleting the `Option` entry (the
    // alternative WI-1021 refused) would emit `anthill.wi1055.Option` here, since
    // `Placement.Ambient` qualifies with the declaration's package.
    val files = gen(parseSource(
      """namespace anthill.wi1055
        |  entity Slot(v: Option[T = Int64])
        |end
        |""".stripMargin, "slot.anthill"))
    assert(files.head.contents.contains("case class Slot(v: _root_.anthill.prelude.Option[_root_.scala.Long])"),
      s"the type map must still fire for a compatible arity:\n${files.head.contents}")
  }

  test("WI-1055: a NAMED requirement slot is refused, at sort level and at operation level") {
    // WI-840 (proposal 058 §4.7): a named slot — `requires O: Ord[T]` — is a type
    // parameter of the sort whose value is a chosen WITNESS, and §2.7 maps a
    // requires to "either a type-class supertrait or a `using` context parameter".
    // A named slot is unambiguously the second, and Bootstrap emits no `using`
    // clause. `sortedset.anthill` shipped `SortedSet[T, O]` with a phantom `O` that
    // no member could bind, and every use of the type inside it was
    // `Too many type arguments for SortedSet[T]`.
    //
    // BOTH LEVELS in one test because it is one decision. The operation-level arm
    // has no stdlib instance and would otherwise be unreachable code.
    //
    // FAILS WHEN BACKED OUT: delete the sort-level throw and sortedset.anthill
    // emits again; delete the operation-level throw and the second `intercept`
    // finds no throw (the slot silently becomes a lowercase type parameter).
    val sortLevel = intercept[BootstrapError](
      gen(parseStdlib("anthill/prelude/sortedset.anthill")))
    assert(sortLevel.getMessage.contains("`SortedSet`") &&
           sortLevel.getMessage.contains("`O`"),
      s"refusal must name the sort and the slot: ${sortLevel.getMessage}")
    assert(sortLevel.getMessage.contains("sortedset.anthill:"),
      s"refusal must be located: ${sortLevel.getMessage}")

    val opLevel = intercept[BootstrapError](gen(parseSource(
      """namespace anthill.wi1055
        |  sort Bag
        |    sort T = ?
        |    operation biFold(x: T) -> T
        |      requires lo: Ord[T]
        |  end
        |end
        |""".stripMargin, "bag.anthill")))
    assert(opLevel.getMessage.contains("`biFold`") && opLevel.getMessage.contains("`lo`"),
      s"refusal must name the operation and the slot: ${opLevel.getMessage}")
    assert(opLevel.getMessage.contains("bag.anthill:"),
      s"refusal must be located: ${opLevel.getMessage}")
  }

  test("WI-1055: the enclosing sort written with the WRONG number of arguments is refused") {
    // The parameters Bootstrap emits and the ones a declaration writes can diverge
    // — that is how `SortedSet[T = T, O = O]` reached the output against a
    // `SortedSet[T]`. Refused rather than passed through, because passing written
    // arguments through unchecked is what made the self-reference path able to
    // emit an arity Scala rejects.
    //
    // A FIXTURE and not sortedset.anthill: the named-slot refusal above fires
    // first there, so the stdlib instance cannot reach this arm.
    //
    // FAILS WHEN BACKED OUT: drop the `args.length != self.params.length` guard in
    // `Placement.Enclosing` and `Box[Int, Int]` is emitted against `Box[T]`.
    val err = intercept[BootstrapError](gen(parseSource(
      """namespace anthill.wi1055
        |  sort Box
        |    sort T = ?
        |    operation dup(b: Box[T = T, U = T]) -> T
        |  end
        |end
        |""".stripMargin, "box2.anthill")))
    assert(err.getMessage.contains("enclosing sort"),
      s"refusal must say what defeated it: ${err.getMessage}")
    assert(err.getMessage.contains("1 type parameter(s), but 2 argument(s) were written"),
      s"refusal must state both counts: ${err.getMessage}")
  }

  // ── WI-1064: `requires` → `extends` is an ALGEBRA sort's reading ───────────
  //
  // §2.7 offers two mappings for a `requires` and did not say when each applies,
  // which is how one of them came to be applied unconditionally. The rule is read
  // off the requirement's CARRIER SLOT: on an algebra sort it is over the same
  // carrier the sort is an algebra over, and a supertrait is exactly what that
  // says; on a sort with CONSTRUCTORS the sort IS the carrier, so a requirement
  // over a PARAMETER constrains an INPUT and is not an is-a claim about anything.

  test("WI-1064: a data sort's `requires` constrains an input, so it emits no `extends`") {
    // A FIXTURE and not finite_combinators.anthill, for a reason worth stating: when
    // this ticket landed, the corpus instance could not be COMPILED in a closure of
    // its own — the `FiniteCollection` its field names was itself rejected by
    // RefChecks for an unrelated defect (a shadowing redeclaration, since fixed;
    // WI-1065's test now compiles that closure). A fixture lets this arm be driven
    // by the compiler rather than by a substring either way. The corpus instance is
    // asserted on its emitted text below.
    //
    // BOTH READINGS IN ONE FIXTURE, because they are one decision: `Counted` is an
    // algebra whose `requires Walk[C = C, …]` is over its OWN carrier and must keep
    // its supertrait, and `Wrapper` is a data sort whose `requires Walk[C = SrcC,
    // …]` is over a parameter and must not become one.
    //
    // FAILS WHEN BACKED OUT, run: make `requiresMapping` unconditional (its
    // pre-WI-1064 form) and the emission is `enum Wrapper[SrcC, Src] extends
    // Walk[SrcC, Src]:`, so the exact-line assertion fails — before the compile,
    // which is therefore not what the control demonstrates. The compile symptom of
    // that same emission is on record from the corpus instead: `class Fmapped needs
    // to be abstract, since it has 9 unimplemented members`. The `Counted`
    // assertion passes either way BY DESIGN; it is the control that the arm did not
    // overreach, and the same reading is pinned on stdlib by the WI-170/WI-644 test
    // above (`trait Eq[T] extends PartialEq[T]`), which also stays green.
    val files = gen(parseSource(
      """namespace anthill.wi1064
        |  sort Walk
        |    sort C = ?
        |    sort Element = ?
        |    operation head(c: C) -> Element
        |  end
        |
        |  sort Counted
        |    sort C = ?
        |    sort Element = ?
        |    requires Walk[C = C, Element = Element]
        |    operation count(c: C) -> Element
        |  end
        |
        |  sort Wrapper
        |    sort SrcC = ?
        |    sort Src = ?
        |    requires Walk[C = SrcC, Element = Src]
        |    entity wrapped(source: Walk[C = SrcC, Element = Src])
        |  end
        |end
        |""".stripMargin, "wi1064.anthill"))

    val wrapper = files.find(_.relPath.endsWith("/Wrapper.scala"))
      .getOrElse(fail(s"expected Wrapper.scala in: ${files.map(_.relPath)}")).contents
    assert(wrapper.contains("enum Wrapper[SrcC, Src]:"),
      s"a data sort's `requires` must leave the declaration alone:\n$wrapper")
    // NOT DROPPED, which is the other half of the rule: the requirement still
    // reaches Scala, as the type of the field that carries it.
    // PASSES EITHER WAY BY DESIGN, like the `Counted` assertion below: the arm
    // never touched field rendering. It is here because the doc's load-bearing
    // claim — the requirement is not discarded, it reaches Scala as the field's
    // type — would otherwise be asserted nowhere at all.
    assert(wrapper.contains("case Wrapped(source: Walk[SrcC, Src])"),
      s"the field must still carry the requirement:\n$wrapper")

    val counted = files.find(_.relPath.endsWith("/Counted.scala"))
      .getOrElse(fail(s"expected Counted.scala in: ${files.map(_.relPath)}")).contents
    assert(counted.contains("trait Counted[C, Element] extends Walk[C, Element]:"),
      s"an ALGEBRA sort's `requires` is still a supertrait:\n$counted")

    ScalaCompile.assertCompiles("the WI-1064 fixture", files)
  }

  test("WI-1064: the RECORD shape takes the same arm as the sum — eponymy is not a loophole") {
    // THE ARM NO OTHER TEST REACHES. `shapeOf` keys eponymy on the ANTHILL name, so
    // every other fixture here (`Wrapper`/`wrapped`, `Boxed`/`boxed`) and BOTH corpus
    // sorts (`FiniteMappedStream`/`fmapped`) classify as `Sum` — the lowercase-entity
    // form is stdlib's convention. The `Record` branch of `requiresMapping` was
    // therefore dead to the suite, and every pre-existing Record test (Vec3,
    // TotalFloat, Box, Acct) declares no `requires`, so it short-circuits at
    // `if requires.isEmpty`. Only an EXACT-case eponymous constructor gets here.
    //
    // FAILS WHEN BACKED OUT: restore the `extends` on the Record arm alone — the
    // one edit the whole 404-test suite used to tolerate — and `case class
    // Holder[SrcC, Src](source: Walk[SrcC, Src])` gains ` extends Walk[SrcC, Src]`,
    // failing this assertion and then the compile (a `case class` is instantiable,
    // so an inherited `head` it does not define is `class Holder needs to be
    // abstract`).
    val files = gen(parseSource(
      """namespace anthill.wi1064
        |  sort Walk
        |    sort C = ?
        |    sort Element = ?
        |    operation head(c: C) -> Element
        |  end
        |
        |  sort Holder
        |    sort SrcC = ?
        |    sort Src = ?
        |    requires Walk[C = SrcC, Element = Src]
        |    entity Holder(source: Walk[C = SrcC, Element = Src])
        |  end
        |end
        |""".stripMargin, "holder.anthill"))
    val holder = files.find(_.relPath.endsWith("/Holder.scala"))
      .getOrElse(fail(s"expected Holder.scala in: ${files.map(_.relPath)}")).contents
    assert(holder.contains("case class Holder[SrcC, Src](source: Walk[SrcC, Src])\n"),
      s"the Record shape must take the same arm as the Sum shape:\n$holder")
    ScalaCompile.assertCompiles("the WI-1064 Record fixture", files)
  }

  test("WI-1064: discharge is PER CONSTRUCTOR — a sibling that carries it nowhere is refused") {
    // Over a sum's flattened field list, one constructor carrying the requirement
    // would discharge it for every other case, which is precisely the silent drop
    // `checkDischarged` exists to prevent. Both corpus instances are
    // single-constructor, so the hole was invisible there.
    //
    // FAILS WHEN BACKED OUT: restore `ctors.flatMap(_.fields)` and this emits
    // `enum Wrap[SrcC, Src]: case Carried(...); case Bare[SrcC, Src](n: Long)` with
    // no refusal — `Bare` carries the requirement nowhere.
    val err = intercept[BootstrapError](gen(parseSource(
      """namespace anthill.wi1064
        |  import anthill.prelude.{Int64}
        |  sort Walk
        |    sort C = ?
        |    sort Element = ?
        |    operation head(c: C) -> Element
        |  end
        |
        |  sort Wrap
        |    sort SrcC = ?
        |    sort Src = ?
        |    requires Walk[C = SrcC, Element = Src]
        |    entity carried(source: Walk[C = SrcC, Element = Src])
        |    entity bare(n: Int64)
        |  end
        |end
        |""".stripMargin, "wrap.anthill")))
    assert(err.getMessage.contains("constructor `bare`"),
      s"refusal must name the constructor that carries it nowhere: ${err.getMessage}")
  }

  test("WI-1064 CONTROL: a requirement carried NESTED in a field type still discharges") {
    // Containment, not equality. `sources: List[T = Walk[…]]` renders
    // `_root_.anthill.prelude.List[Walk[SrcC, Src]]`, which is not the requirement
    // string — and a whole-string test refused it, aborting `generate` for the whole
    // FILE over a requirement every list element satisfies.
    //
    // FAILS WHEN BACKED OUT: restore `fieldTypes.contains(rendered)` (exact
    // equality) and this throws instead of emitting.
    val files = gen(parseSource(
      """namespace anthill.wi1064
        |  import anthill.prelude.{List}
        |  sort Walk
        |    sort C = ?
        |    sort Element = ?
        |    operation head(c: C) -> Element
        |  end
        |
        |  sort Many
        |    sort SrcC = ?
        |    sort Src = ?
        |    requires Walk[C = SrcC, Element = Src]
        |    entity many(sources: List[T = Walk[C = SrcC, Element = Src]])
        |  end
        |end
        |""".stripMargin, "many.anthill"))
    val many = files.find(_.relPath.endsWith("/Many.scala"))
      .getOrElse(fail(s"expected Many.scala in: ${files.map(_.relPath)}")).contents
    assert(many.contains("enum Many[SrcC, Src]:"), s"no `extends` on a data sort:\n$many")
    assert(many.contains("List[Walk[SrcC, Src]]"),
      s"the nested requirement must reach the emitted field:\n$many")
  }

  test("WI-1064: a data sort's `requires` that NO field carries is REFUSED, not dropped") {
    // The omission above is admissible only because the emitted tree still carries
    // the requirement through a field's declared type. Where it would not, omitting
    // it is a real loss — the emitted `Boxed` says nothing of `Ordering[T]` — and
    // that is §2.7's other half, the `using` context parameter WI-1022 owns and
    // Bootstrap does not emit. No prelude file has this shape, which is exactly why
    // emitting `""` for every data sort unconditionally would have looked right.
    //
    // FAILS WHEN BACKED OUT: delete the `checkDischarged` call and this `intercept`
    // finds no throw — the bound is silently gone from the emitted declaration.
    val err = intercept[BootstrapError](gen(parseSource(
      """namespace anthill.wi1064
        |  sort Ordering
        |    sort T = ?
        |    operation cmp(a: T, b: T) -> T
        |  end
        |
        |  sort Boxed
        |    sort T = ?
        |    requires Ordering[T]
        |    entity boxed(x: T)
        |  end
        |end
        |""".stripMargin, "boxed.anthill")))
    assert(err.getMessage.contains("`Boxed`"),
      s"refusal must name the sort: ${err.getMessage}")
    // "evidence supplied to bodies" and not "constrains an input": the latter is
    // false of a NULLARY marker requirement, which has no input slot at all, and
    // `examples/classic-mini/*` write `sort Program { requires anthill.cli.Main }`
    // — today an algebra, but one `entity` away from reaching this message.
    assert(err.getMessage.contains("evidence supplied to bodies"),
      s"refusal must say what a sort-level `requires` IS: ${err.getMessage}")
    assert(err.getMessage.contains("has no field typed by it"),
      s"refusal must say why it cannot be carried: ${err.getMessage}")
    assert(err.getMessage.contains("boxed.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1064 CORPUS: finite_combinators.anthill emits no `extends`, and still names it") {
    // THE MEASURED INSTANCE, on emitted TEXT rather than compiled, for the reason
    // the fixture test states. Both sorts, because both carried the defect.
    //
    // The `requires FiniteCollection[C = SrcC, …]` these two write sits two lines
    // above a `provides FiniteCollection[C = FiniteMappedStream, …]` — the sort's
    // actual claim about itself, which Bootstrap reads nothing of (`emitSort` has
    // no `ProvidesClauseItem` arm). The `extends` was built from the wrong line.
    //
    // `_root_`-ANCHORED SINCE WI-1060, and only the spelling changed: `FiniteCollection`
    // used to reach [[Placement.Ambient]], which qualifies with the DECLARING file's
    // package and so happened to be right here; it is now placed by
    // finite_collection.anthill's own declaration, which is also what checks the two
    // arguments against the two that declaration emits.
    //
    // FAILS WHEN BACKED OUT: the pre-WI-1064 emission is `enum
    // FiniteMappedStream[SrcC, Src, T] extends anthill.prelude.FiniteCollection[
    // SrcC, Src]:`, whose measured consequence was `class Fmapped needs to be
    // abstract, since it has 9 unimplemented members`.
    val files = preludeClosure("finite_combinators")
    Seq(
      ("FiniteMappedStream", "enum FiniteMappedStream[SrcC, Src, T]:",
        "case Fmapped(source: _root_.anthill.prelude.FiniteCollection[SrcC, Src],"),
      ("FiniteFilteredStream", "enum FiniteFilteredStream[SrcC, T]:",
        "case Ffiltered(source: _root_.anthill.prelude.FiniteCollection[SrcC, T],"),
    ).foreach { case (sort, decl, field) =>
      val src = files.find(_.relPath.endsWith(s"/$sort.scala"))
        .getOrElse(fail(s"expected $sort.scala in: ${files.map(_.relPath)}")).contents
      assert(src.contains(decl), s"$sort must carry no `extends`:\n$src")
      assert(src.contains(field), s"$sort must still name what it requires:\n$src")
    }
  }

  // ── WI-1066: an ALGEBRA sort's carrier is READ, not assumed ────────────────
  //
  // WI-1064 answered the carrier question from the SORT SHAPE, which is exact with
  // constructors and a proxy without them. These read it: the carrier is the sort
  // ITSELF when some operation takes the sort as a parameter (self-representing —
  // `Set`, `Map`), and otherwise the sort's FIRST type parameter. That is rustland's
  // rule and not a second one — `spec_is_self_representing` /
  // `requires_edge_is_carrier_preserving` (kb/typing.rs, WI-614) decide the identical
  // question for member lending, down to "its first type-param".
  //
  // NOTHING HERE CAN BE DRIVEN BY A COMPILE, and that is the ticket's own finding: a
  // Scala trait tolerates unimplemented members, so `trait Set[T] extends Eq[T]`
  // compiles exactly as well as `trait Set[T]` does. The fixtures below are compiled
  // anyway — the emission must stay legal Scala — but every arm is carried by an
  // assertion on the emitted TEXT.

  /** The four algebra shapes the carrier rule has to separate, in one file so the
    * arm and its controls are compiled together and cannot drift apart. */
  private val wi1066Fixture =
    """namespace anthill.wi1066
      |  sort Cmp
      |    sort T = ?
      |    operation cmp(a: T, b: T) -> T
      |  end
      |
      |  sort Bag
      |    sort T = ?
      |    requires Cmp[T]
      |    operation empty() -> Bag
      |    operation insert(s: Bag, x: T) -> Bag
      |  end
      |
      |  sort Space
      |    sort V = ?
      |    sort F = ?
      |    requires Cmp[F]
      |    operation vadd(a: V, b: V) -> V
      |    operation vscale(c: F, v: V) -> V
      |  end
      |
      |  sort Graded
      |    sort V = ?
      |    sort F = ?
      |    requires Cmp[V]
      |    operation gadd(a: V, b: V) -> V
      |  end
      |
      |  sort Marked
      |    sort T = ?
      |    requires Cmp[T]
      |  end
      |end
      |""".stripMargin

  private def wi1066Emission(sort: String, files: IndexedSeq[GeneratedFile]): String =
    files.find(_.relPath.endsWith(s"/$sort.scala"))
      .getOrElse(fail(s"expected $sort.scala in: ${files.map(_.relPath)}")).contents

  test("WI-1066: a SELF-REPRESENTING algebra's `requires` is over its ELEMENT") {
    // `Bag`'s operations take `s: Bag`, so the carrier is `Bag` and `T` is content —
    // `requires Cmp[T]` constrains the element and claims nothing about `Bag`. This is
    // set.anthill's shape (WI-596 made `Set` self-representing) and map.anthill's.
    //
    // ANY operation and not the first: `empty() -> Bag` is declared ahead of `insert`
    // and RETURNS the sort rather than receiving it. Reading only the first operation
    // classifies `Bag` as carried by `T` and this test goes green for the wrong reason
    // — which is why the fixture declares them in that order.
    //
    // FAILS WHEN BACKED OUT, run: make the Algebra arm of `requiresMapping`
    // unconditional (its WI-1064 form) and the emission is `trait Bag[T] extends
    // Cmp[T]:`, so both assertions below fail. The compile passes either way, by
    // design — see the block comment above.
    val files = gen(parseSource(wi1066Fixture, "wi1066.anthill"))
    val bag = wi1066Emission("Bag", files)
    assert(bag.contains("trait Bag[T]:"),
      s"a self-representing algebra's `requires` is not a supertrait:\n$bag")
    assert(!bag.contains("extends"), s"and no other clause smuggles it back:\n$bag")

    // CONTROL, and the one that stops the arm reading as "algebra sorts lost their
    // supertraits": `Graded`'s requirement IS over its carrier `V`, and it keeps the
    // clause. Passes either way BY DESIGN — it is what the arm must not break.
    val graded = wi1066Emission("Graded", files)
    assert(graded.contains("trait Graded[V, F] extends Cmp[V]:"),
      s"a requirement over the carrier is still a supertrait:\n$graded")

    ScalaCompile.assertCompiles("the WI-1066 fixture", files)
  }

  test("WI-1066: the carrier is the sort's FIRST type parameter, not any it names") {
    // `Space` is algebra.anthill's `VectorSpace` shape: carried by `V`, requiring a
    // spec over the SCALAR `F`. It is not self-representing at all, so a rule keyed on
    // self-representation alone would miss it — which is why the fixture carries this
    // sort beside `Bag`.
    //
    // THE FIRST TYPE PARAMETER is rustland's convention (`provision_carrier_sort`),
    // and reading it here rather than reading the operations is what makes `Marked`
    // below answerable. Note `vscale(c: F, v: V)` receives `F` too: "some operation
    // receives it" does not separate `V` from `F`, and declaration order does.
    //
    // FAILS WHEN BACKED OUT: with the Algebra arm unconditional the emission is `trait
    // Space[V, F] extends Cmp[F]:`. It also fails if the carrier is taken from the
    // requirement's own argument rather than the declaration.
    val files = gen(parseSource(wi1066Fixture, "wi1066.anthill"))
    val space = wi1066Emission("Space", files)
    assert(space.contains("trait Space[V, F]:"),
      s"a requirement over a non-carrier parameter is not a supertrait:\n$space")
  }

  test("WI-1066: a sort declaring NO operations takes its first parameter as carrier") {
    // THE TRAP THE TICKET NAMES. `sort Eq` (eq.anthill:35) declares no operations at
    // all — it adds only the reflexivity law — so it has no receiver to read, and it
    // is one of the two emissions pinned green since WI-170/WI-644. `Marked` is that
    // shape as a fixture. Answering "the first type parameter" costs it nothing: with
    // no operation to take the sort, it is not self-representing, and its sole
    // parameter is its first.
    //
    // FAILS WHEN BACKED OUT: default the carrier to the SORT when no operation names a
    // parameter — the other plausible reading — and `Marked` loses its supertrait
    // here, and `trait Eq[T] extends PartialEq[T]` fails in the WI-170/WI-644 test
    // above. Refusing the case instead (there being no receiver to read) fails here
    // with a `BootstrapError` rather than an assertion.
    val files = gen(parseSource(wi1066Fixture, "wi1066.anthill"))
    val marked = wi1066Emission("Marked", files)
    assert(marked.contains("trait Marked[T] extends Cmp[T]"),
      s"a sort with no operations is carried by its sole parameter:\n$marked")
  }

  test("WI-1066: a requirement with NO arguments is a marker, and stays a supertrait") {
    // `sort anthill.cli.Main` is empty — no parameters, no operations, no laws — and
    // rustland's CLI fixtures write `sort Hello { requires anthill.cli.Main; operation
    // main(…) }`. A requirement with no arguments has no slot to be over anything but
    // the declaring sort, so the tag is its whole content and `extends` carries
    // exactly the tag.
    //
    // SOUND ONLY BECAUSE A PARAMETERIZED SPEC CANNOT REACH HERE WRITTEN BARE: `TypeGen`
    // refuses a partial application first (WI-1055 B3, pinned in its own test). What is
    // left is a genuinely nullary spec.
    //
    // DIVERGES FROM RUSTLAND DELIBERATELY: `requires_edge_is_carrier_preserving`
    // answers `false` for a sort with no type parameters, because it asks whether the
    // required spec lends its MEMBERS to this receiver and a marker has none to lend.
    // The question here is whether the emitted Scala type is a subtype.
    //
    // FAILS WHEN BACKED OUT, run: delete the `args.isEmpty ||` disjunct in
    // `isOverCarrier`, so an argument-less requirement is judged by a mention it has no
    // slot to make. `Tagged` then loses `extends Tag` and gains an evidence note.
    val files = gen(parseSource(
      """namespace anthill.wi1066
        |  import anthill.prelude.{Int64}
        |  sort Tag
        |  end
        |
        |  sort Tagged
        |    requires Tag
        |    operation run() -> Int64
        |  end
        |end
        |""".stripMargin, "tagged.anthill"))
    val tagged = wi1066Emission("Tagged", files)
    assert(tagged.contains("trait Tagged extends Tag:"),
      s"a marker requirement is a supertrait:\n$tagged")
    ScalaCompile.assertCompiles("the WI-1066 marker fixture", files)
  }

  test("WI-1066: a `requires` that names no sort at all is REFUSED") {
    // The grammar takes a full `typeExpr` after `requires`, so an arrow parses. It
    // names no sort, hence has no carrier slot, and the rule above has no answer for
    // it. No corpus file writes one.
    //
    // WHAT THE REFUSAL BUYS, measured rather than assumed: the alternative emission
    // `trait Weird[T] extends (T) => T:` does not compile — `end of toplevel definition
    // expected but '=>' found` — so this is not a silent-wrong-output case but a
    // located diagnostic instead of a syntax error inside generated text, which is the
    // trade WI-1055 made for every other unrenderable construct.
    //
    // FAILS WHEN BACKED OUT, run: return `IndexedSeq.empty` from the fallback arm of
    // `writtenArguments` — reading an arrow as a marker — and this `intercept` finds no
    // throw.
    val err = intercept[BootstrapError](gen(parseSource(
      """namespace anthill.wi1066
        |  sort Weird
        |    sort T = ?
        |    requires (T) -> T
        |    operation f(a: T) -> T
        |  end
        |end
        |""".stripMargin, "weird.anthill")))
    assert(err.getMessage.contains("must name a sort"),
      s"refusal must say what is wrong with it: ${err.getMessage}")
    assert(err.getMessage.contains("weird.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1066 CORPUS: Set / Map / VectorSpace stop claiming a spec over their element") {
    // THE THREE MEASURED EMISSIONS, on emitted TEXT because a compile cannot see them:
    // all three compiled before this ticket and all three compile after it. What
    // shipped was an obligation on every implementor that the anthill sort never
    // declared — an implementor of `trait Set[T] extends Eq[T]` must supply `eq(a: T,
    // b: T)` over ELEMENTS, beside Set's own `eq(a: Set, b: Set)` as an overload.
    //
    // Each sort's real claim about itself is a `provides` (set.anthill's `provides
    // Eq[T = Set]`, eleven lines below the `requires`), which Bootstrap reads nothing
    // of — `emitSort` has no `ProvidesClauseItem` arm — so the `extends` was built
    // from the only line it did read.
    //
    // WHAT THE OMITTED CLAUSE BECOMES is asserted here too, and it is a RECORD rather
    // than a refusal: the requirement is named in the emitted source with what it is
    // over and what would carry it (§2.7's `using`, WI-1022). A data sort's
    // undischarged requirement is refused instead (WI-1064) because its only possible
    // home — a constructor field's type — is genuinely absent; an algebra sort's has a
    // Scala home that Bootstrap has not implemented, and refusing would delete three
    // prelude files from the tree to punish that.
    //
    // FAILS WHEN BACKED OUT: with the Algebra arm unconditional the three emissions are
    // `trait Set[T] extends _root_.anthill.prelude.Eq[T]:`, `trait Map[K, V] extends
    // _root_.anthill.prelude.Eq[K]:` and `trait VectorSpace[V, F] extends Ring[F]:`,
    // and every assertion below fails. MEASURED with the peeled-closure harness: the
    // three are the ONLY emissions in the 44-file prelude that change.
    Seq(
      ("set", "Set", "trait Set[T]:", "`requires _root_.anthill.prelude.Eq[T]`",
        "carrier is\n//   `Set` itself (self-representing)"),
      ("map", "Map", "trait Map[K, V]:", "`requires _root_.anthill.prelude.Eq[K]`",
        "carrier is\n//   `Map` itself (self-representing)"),
      ("algebra", "VectorSpace", "trait VectorSpace[V, F]:", "`requires Ring[F]`",
        "carrier is\n//   its parameter `V`"),
    ).foreach { case (file, sort, decl, named, carrier) =>
      val src = wi1066Emission(sort, preludeClosure(file))
      assert(src.contains(decl), s"$sort must carry no supertrait:\n$src")
      assert(src.contains(named), s"$sort must still NAME what it requires:\n$src")
      assert(src.contains(carrier), s"$sort must say what its carrier is:\n$src")
      assert(src.contains("WI-1022"), s"$sort must say what would carry it:\n$src")
    }
  }

  test("WI-1066 CORPUS CONTROL: every other prelude supertrait is unchanged") {
    // THE OTHER SIDE OF THE SAME MEASUREMENT, and the complete one: fourteen prelude
    // algebra sorts carry a `requires` (sortedset.anthill's fifteenth is refused
    // earlier, for its named requirement slot). Three lose the clause to WI-1066's
    // carrier rule, and a fourth — `FiniteCollection`, WI-1066's own named control —
    // lost it later to WI-1065's shadow rule (its `requires Iterable[C = C, …]` IS
    // over its own carrier, but the sort redeclares `map`/`filter`; pinned in the
    // WI-1065 tests below). These are the other TEN, all of them, so a rule that
    // simply stopped emitting `extends` for algebra sorts fails here rather than
    // looking like a fix.
    //
    // `Ord` carries TWO requirements and keeps both. `Eq` is the no-operations
    // shape, also pinned by the WI-170/WI-644 test above.
    //
    // PASSES EITHER WAY BY DESIGN — that is what a control is. It fails if the carrier
    // reading overreaches: taking the carrier from the requirement's argument, or
    // treating a nullary-operation sort (`NonEq`, `BoundedLattice`) as having no
    // readable carrier, breaks lines here. It equally fails if the WI-1065 shadow
    // reading overreaches: every row below names a spec whose members its requirer
    // does NOT redeclare (measured — the corpus intersections are all empty), so a
    // demotion keyed on anything looser than a member-name collision lands here.
    Seq(
      ("ordered", "Ord", "trait Ord[T] extends _root_.anthill.prelude.Eq[T], PartialOrd[T]:"),
      ("ordered", "PartialOrd", "trait PartialOrd[T] extends _root_.anthill.prelude.PartialEq[T]:"),
      ("collection", "PersistentCollection",
        "trait PersistentCollection[C, Element] extends _root_.anthill.prelude.Iterable[C, Element]:"),
      // A requirement whose named slot DIFFERS from the parameter written into it
      // (`requires Modifiable[T = C]`) — the shape `Map`'s `Eq[T = K]` has, and here it
      // is over the carrier, so the two are separated by the argument and not the name.
      ("mutable_collection", "MutableCollection",
        "trait MutableCollection[C, Element] extends _root_.anthill.prelude.Iterable[C, Element], " +
        "_root_.anthill.prelude.Modifiable[C]:"),
      ("eq", "Eq", "trait Eq[T] extends PartialEq[T]"),
      ("eq", "NonEq", "trait NonEq[T] extends PartialEq[T]:"),
      ("lattice", "Lattice", "trait Lattice[T] extends _root_.anthill.prelude.Eq[T]:"),
      ("lattice", "BoundedLattice", "trait BoundedLattice[T] extends Lattice[T]:"),
      ("numeric", "Numeric", "trait Numeric[T] extends _root_.anthill.prelude.PartialOrd[T]:"),
      ("field", "Field", "trait Field[T] extends _root_.anthill.prelude.Numeric[T]:"),
    ).foreach { case (file, sort, decl) =>
      val src = wi1066Emission(sort, preludeClosure(file))
      assert(src.contains(decl), s"$sort's supertrait must be unchanged:\n$src")
      assert(!src.contains("is EVIDENCE"), s"$sort must carry no evidence note:\n$src")
    }
  }

  // ── WI-1065: a redeclared required member is a SHADOW, not an override ─────
  //
  // Kernel §8.7: a sort that merely `requires` a spec and redeclares an operation
  // of the same name is NOT overriding it — the two are DISTINCT operations, and
  // a shadow that provably refines the signature is "a distinct operation by
  // construction". The spec's own worked example is this corpus pair:
  // `FiniteCollection.map` returns a `FiniteCollection` where `Iterable.map`
  // returns a `Stream`. Scala reads the same two declarations the other way —
  // matching members (same name and parameter types; the return type is not part
  // of matching) form ONE override group, checked at the declaration — so the
  // emitted `extends` asserted a relation the kernel denies, and RefChecks
  // refused it (E164, `error overriding method map in trait Iterable`, twice).
  // The fix is not a Scala spelling for the refinement; it is not emitting the
  // relation: a shadowed requirement is demoted to evidence.
  //
  // The collision is CROSS-FILE knowledge — Iterable's members live in
  // iterable.anthill, and proposal 034 gives Bootstrap one ParsedFile — so it
  // arrives like every other resolved table (WI-1060's channel): the caller
  // derives `ScalaTypes.specMembers` from the same parsed closure.

  test("WI-1065: a redeclared required member demotes the supertrait to evidence") {
    // FAILS WHEN BACKED OUT, run: drop the shadow partition from `requiresMapping`
    // (emit every over-carrier requirement as a supertrait, its pre-WI-1065 form)
    // and `Shadower`'s no-extends assertion fails here, the corpus test fails at
    // its pin (before its compile — which would then report this ticket's two
    // E164s, on record in the peel ladder and reproduced from the emitted
    // signatures), and the transitive test fails too. `Keeper` and the WI-1066
    // corpus controls pass either way BY DESIGN — the control that a non-shadowing
    // requirer keeps its clause (as does WI-1062's Walkable2 fixture above).
    //
    // `Shadower.map` takes DIFFERENT parameters than `Iterable.map` on purpose: in
    // Scala that pair would be a legal overload, and the demotion fires anyway,
    // which is the stated name-keyed over-approximation (`specMemberNames`) driven
    // rather than described — demotion-safe, because evidence never breaks a
    // compile and a kept clause can.
    val src = gen(parseSource(
      """namespace anthill.wi1065
        |  sort Shadower
        |    import anthill.prelude.{Iterable, Bool}
        |    sort C = ?
        |    sort Element = ?
        |    effects E = ?
        |    requires Iterable[C = C, Element = Element, E = E]
        |    operation map(c: C) -> Element effects E
        |    operation walked(c: C) -> Bool effects E
        |  end
        |  sort Keeper
        |    import anthill.prelude.{Iterable, Bool}
        |    sort C = ?
        |    sort Element = ?
        |    effects E = ?
        |    requires Iterable[C = C, Element = Element, E = E]
        |    operation walked(c: C) -> Bool effects E
        |  end
        |end
        |""".stripMargin, "wi1065.anthill"))
    val shadower = src.find(_.relPath.endsWith("Shadower.scala"))
      .getOrElse(fail(s"expected Shadower.scala in: ${src.map(_.relPath)}")).contents
    assert(shadower.contains("trait Shadower[C, Element]:"),
      s"a shadowed requirement must not become a supertrait:\n$shadower")
    assert(!shadower.contains("extends"),
      s"no extends clause may survive the demotion:\n$shadower")
    assert(shadower.contains("`map`") && shadower.contains("WI-1065"),
      s"the note must name the shadowing member and the rule:\n$shadower")
    assert(!shadower.contains("`walked`"),
      s"a member the spec does not declare is no shadow:\n$shadower")
    val keeper = src.find(_.relPath.endsWith("Keeper.scala"))
      .getOrElse(fail(s"expected Keeper.scala in: ${src.map(_.relPath)}")).contents
    assert(keeper.contains(
      "trait Keeper[C, Element] extends _root_.anthill.prelude.Iterable[C, Element]:"),
      s"a non-shadowing requirer keeps its supertrait:\n$keeper")
  }

  test("WI-1065: the shadow is read through the required spec's own `requires` chain") {
    // `eq` is not PartialOrd's member — it is PartialEq's, one `requires` edge
    // below — and Scala inherits through the whole extends chain, so the demotion
    // must too. FAILS WHEN BACKED OUT, run: replace `specMemberNames`' fixpoint
    // with the direct member sets (drop the closure loop) and this assertion fails
    // while the direct-shadow fixture above still passes.
    val src = gen(parseSource(
      """namespace anthill.wi1065
        |  sort Chained
        |    import anthill.prelude.{PartialOrd, Bool}
        |    sort T = ?
        |    requires PartialOrd[T]
        |    operation eq(a: T, b: T) -> Bool
        |  end
        |end
        |""".stripMargin, "wi1065b.anthill")).head.contents
    assert(src.contains("trait Chained[T]:") && !src.contains("extends"),
      s"a member of a transitively required spec still shadows:\n$src")
    assert(src.contains("`eq`"),
      s"the note must name the transitively shadowed member:\n$src")
  }

  test("WI-1065: a spec declared in the SAME file still feeds the shadow check") {
    // The suite's `scalaTypes` is resolved over the prelude only, so nothing in
    // THIS fixture is in `ScalaTypes.specMembers` — the closure table alone would
    // keep `SameFile`'s supertrait and emit the E164 shape §2.7a promises not to.
    // What this drives is `generate`'s per-file complement
    // (`specMemberNames(Seq(pf), base = types.specMembers)`): `Walk` is seen from
    // the file itself, and `ChainedLocal` additionally needs the file-local entry
    // CLOSED against the prelude table (`lt` reaches it only through Walk's
    // `requires PartialOrd`, whose members live in `base`).
    //
    // FAILS WHEN BACKED OUT, run: pass `env.scalaTypes.specMembers` to
    // `requiresMapping` instead of `env.specMembers` and both demotions here fail
    // (supertraits kept) while every prelude-spec fixture above still passes —
    // which is exactly why this test exists. `Walk` itself keeps its OWN
    // supertrait either way by design: it requires PartialOrd and redeclares
    // nothing, the control that the merge does not over-demote same-file sorts.
    val src = gen(parseSource(
      """namespace anthill.wi1065
        |  sort Walk
        |    import anthill.prelude.{PartialOrd}
        |    sort C = ?
        |    requires PartialOrd[T = C]
        |    operation step(c: C) -> C
        |  end
        |  sort SameFile
        |    sort C = ?
        |    requires Walk[C = C]
        |    operation step(c: C) -> C
        |  end
        |  sort ChainedLocal
        |    import anthill.prelude.{Bool}
        |    sort C = ?
        |    requires Walk[C = C]
        |    operation lt(a: C, b: C) -> Bool
        |  end
        |end
        |""".stripMargin, "wi1065c.anthill"))
    def emitted(leaf: String): String =
      src.find(_.relPath.endsWith(s"$leaf.scala"))
        .getOrElse(fail(s"expected $leaf.scala in: ${src.map(_.relPath)}")).contents
    val same = emitted("SameFile")
    assert(same.contains("trait SameFile[C]:") && !same.contains("extends"),
      s"a same-file required spec's member must shadow:\n$same")
    assert(same.contains("`step`"),
      s"the note must name the same-file shadowed member:\n$same")
    val chained = emitted("ChainedLocal")
    assert(chained.contains("trait ChainedLocal[C]:") && !chained.contains("extends"),
      s"the file-local entry must close against the resolved table:\n$chained")
    assert(chained.contains("`lt`"),
      s"the note must name the member reached through the base table:\n$chained")
    assert(emitted("Walk").contains(
      "trait Walk[C] extends _root_.anthill.prelude.PartialOrd[C]:"),
      s"a same-file sort that shadows nothing keeps its supertrait:\n${emitted("Walk")}")
  }

  test("WI-1065 CORPUS: FiniteCollection is demoted, and its closure COMPILES") {
    // The pair the kernel spec names, pinned on the emission and then DRIVEN
    // through dotc — the two E164s this ticket was filed on are gone, so the two
    // files WI-1062 brought into the tree and WI-1064 half-fixed finally compile
    // together. Before this ticket the peel ladder ended `… -> 2 -> 4 -> clean at
    // 32 files`: the 2 were these overrides, and the trailing 4 was
    // finite_combinators losing `FiniteCollection` once its file was peeled.
    val fc = gen(parseStdlib("anthill/prelude/finite_collection.anthill"))
      .head.contents
    assert(fc.contains("trait FiniteCollection[C, Element]:"),
      s"the corpus shadow must be demoted:\n$fc")
    assert(!fc.contains("FiniteCollection[C, Element] extends"),
      s"no supertrait may survive on the corpus shadow:\n$fc")
    assert(fc.contains("`map`, `filter`"),
      s"the note must name both shadowing members, in declaration order:\n$fc")
    ScalaCompile.assertCompiles("the finite_collection/finite_combinators closure",
      preludeClosure("finite_collection", "finite_combinators", "iterable",
        "stream", "combinators", "option", "pair", "list"))
  }

  // ── WI-1054: the hyphen is the one character anthill admits and Scala does not ──
  //
  // Not a style question. An anthill identifier is `[a-zA-Z_][a-zA-Z0-9_-]*`
  // (`Tokens.identToken`), and `def zero-val(): T` is a PARSE error — dotc reads
  // `zero` applied to an operator — so the emitter produced text that is not the
  // language. `docs/scala-forward-mapping.md` §5 states the rule: `-` normalises to
  // `_` FIRST, then the per-kind convention runs, so `zero-val` and `zero_val` reach
  // Scala as one name.

  test("WI-1054 CORPUS: numeric.anthill's `zero-val` emits `zeroVal`, and the file compiles") {
    // The corpus instance the ticket was measured on (WI-1020's harness, commit
    // 0ebec357): `Numeric.scala:8: '=' expected, but identifier found`.
    //
    // FAILS WHEN BACKED OUT: drop `normalize` from `Names.scalaMethodName` and the
    // `def zeroVal` assertion fails; `assertCompiles` then fails too, with that same
    // parse error. The siblings are in the set because Numeric `requires
    // PartialOrd[T]`, which `requires PartialEq[T]` — neither carries a hyphen, so
    // both pass either way and are here only to close the compile.
    val files = preludeClosure("numeric", "ordered", "eq")
    val src = files.find(_.relPath == "src/main/scala/anthill/prelude/Numeric.scala")
      .getOrElse(fail(s"expected Numeric.scala in: ${files.map(_.relPath)}")).contents
    assert(src.contains("def zeroVal(): T"),
      s"a hyphenated operation must emit as camelCase:\n$src")
    assert(!src.contains("zero-val"),
      s"no hyphen may survive into the emitted source:\n$src")
    ScalaCompile.assertCompiles("numeric.anthill's emission", files)
  }

  test("WI-1054: a hyphen in EVERY identifier position emits a legal Scala name") {
    // Five positions over THREE normalisation sites — `scalaFieldName` delegates to
    // `scalaMethodName`, so a field and a method are one site, not two — and each
    // converts by its own §5 rule after the shared normalisation. A test asserting
    // only "no hyphen" would pass on `zero_val`, `my_sort` and `myLib` alike, so
    // every assertion names the CHOSEN spelling.
    //
    // FAILS WHEN BACKED OUT, measured one site at a time:
    //   - `Names.scalaMethodName`     → `def zeroVal(myArg: T)` and `myField`
    //   - `Names.scalaTypeName`       → `trait MyAlgebra` / `enum MyData` / `case MyEntity`
    //   - `Names.scalaPackageSegment` → `package my_lib` and the `my_lib/` relPath
    // Each back-out leaves the other two assertions green, which is why they are
    // separate assertions and not one compile. `Bootstrap.splitPath`'s multi-segment
    // prefix is the FOURTH site and no fixture here reaches it — the dotted-declaration
    // test below owns it.
    val files = gen(parseSource(
      """namespace my-lib
        |  sort my-algebra
        |    sort T = ?
        |    operation zero-val(my-arg: T) -> T
        |  end
        |
        |  sort my-data
        |    entity my-entity(my-field: Int64)
        |    entity plain-one
        |  end
        |end
        |""".stripMargin, "my-lib.anthill"))

    // The NAMESPACE segment: package clause and the directory derived from it. §5
    // leaves a segment otherwise as-written — `my_lib`, not `myLib` — because a
    // lowercase segment is already idiomatic for a Scala package.
    assertEquals(files.map(_.relPath).sorted, IndexedSeq(
      "src/main/scala/my_lib/MyAlgebra.scala", "src/main/scala/my_lib/MyData.scala"))
    files.foreach(f => assert(f.contents.startsWith("package my_lib\n"),
      s"a hyphenated namespace segment must emit as `package my_lib`:\n${f.contents}"))

    val algebra = files.find(_.relPath.endsWith("/MyAlgebra.scala")).get.contents
    assert(algebra.contains("trait MyAlgebra[T]:"),
      s"a hyphenated sort must PascalCase:\n$algebra")
    assert(algebra.contains("def zeroVal(myArg: T): T"),
      s"a hyphenated operation and parameter must camelCase:\n$algebra")

    val data = files.find(_.relPath.endsWith("/MyData.scala")).get.contents
    assert(data.contains("enum MyData:"), s"a hyphenated sort must PascalCase:\n$data")
    assert(data.contains("case MyEntity(myField: _root_.scala.Long)"),
      s"a hyphenated entity and field must convert by their own rule:\n$data")
    assert(data.contains("case PlainOne"), s"a nullary hyphenated entity too:\n$data")

    // CODE LINES ONLY, and the exclusion is not a convenience: `Bootstrap.evidenceNote`
    // legitimately writes anthill names into `//` comments (`This sort's carrier is its
    // parameter \`my-carrier\``), so a whole-file scan would assert an invariant the
    // emitter does not hold and fail on correct output. What IS an invariant is that
    // every identifier the emitter puts in code position went through `Names`.
    files.foreach { f =>
      val code = f.contents.linesIterator.filterNot(_.trim.startsWith("//"))
      code.foreach(line => assert(!line.contains("-"),
        s"no hyphen may survive into code in ${f.relPath}:\n${f.contents}"))
    }
    ScalaCompile.assertCompiles("a hyphen in every identifier position", files)
  }

  test("WI-1054: a DOTTED declaration's package prefix is converted too") {
    // The fourth conversion site, and the one the three tests above all miss:
    // `Bootstrap.splitPath`'s multi-segment branch. A top-level `sort my-co.Thing`
    // takes its package from the declaration's own prefix rather than from an
    // enclosing `namespace`, so it reaches neither `namespacePath` nor the
    // single-segment `else` branch the other fixtures use.
    //
    // FAILS WHEN BACKED OUT: revert the `prefix` line in `splitPath` to
    // `.map(sym.name).mkString(".")` and this emits `package my-co` at
    // `src/main/scala/my-co/Thing.scala` — both assertions below, and the compile.
    // Measured: with that one line reverted the other three WI-1054 tests stay green.
    val files = gen(parseSource(
      """sort my-co.deep-ns.Thing
        |  entity Thing(v: Int64)
        |end
        |""".stripMargin, "thing.anthill"))
    assertEquals(files.map(_.relPath),
      IndexedSeq("src/main/scala/my_co/deep_ns/Thing.scala"))
    assert(files.head.contents.startsWith("package my_co.deep_ns\n"),
      s"every prefix segment is converted, not only the first:\n${files.head.contents}")
    ScalaCompile.assertCompiles("a dotted declaration with a hyphenated prefix", files)
  }

  test("WI-1054: two anthill names converging on one Scala name is REFUSED, not last-wins") {
    // What normalising `-` to `_` costs, and the reason it is paid at the emitter and
    // not left to whoever writes the tree to disk. `Names.scalaTypeName` was already
    // many-to-one (`foo_bar` and `fooBar` share an image); §5 adds `foo-bar` to that
    // class. Two sorts in it emit two `FooBar.scala`, and NOTHING downstream could see
    // it — `emittedTypes`' duplicate check is keyed on the ANTHILL leaf, so two
    // different leaves never meet there, and a last-writer-wins tree compiles green
    // with one declaration silently absent.
    //
    // FAILS WHEN BACKED OUT: drop the `refuseColliding(files)` call in
    // `Bootstrap.generate` and this returns two `GeneratedFile`s at one relPath with
    // no error at all.
    val err = intercept[BootstrapError](gen(parseSource(
      """namespace my-lib
        |  sort foo-bar
        |    entity foo-bar(v: Int64)
        |  end
        |
        |  sort foo_bar
        |    entity foo_bar(v: Int64)
        |  end
        |end
        |""".stripMargin, "collide.anthill")))
    assert(err.getMessage.contains("src/main/scala/my_lib/FooBar.scala"),
      s"the refusal must name the path that collides: ${err.getMessage}")

    // THE CONTROL, and it is the point of the whole ticket: the SAME two spellings in
    // ONE declaration are one name, not a collision. Passes with and without
    // `refuseColliding` BY DESIGN — its job is to say the refusal did not widen into
    // "a hyphen anywhere is suspicious".
    val ok = gen(parseSource(
      """namespace my-lib
        |  sort foo-bar
        |    entity foo-bar(v: Int64)
        |  end
        |end
        |""".stripMargin, "single.anthill"))
    assertEquals(ok.map(_.relPath), IndexedSeq("src/main/scala/my_lib/FooBar.scala"))
  }

  test("WI-1054: `-` and `_` are ONE name, so a hyphenated import is not a foreign package") {
    // The consequence of normalising rather than giving `-` its own spelling, and the
    // one place it is observable beyond the emitted text: `TypeScope` compares an
    // import's package against the package the declaration is EMITTED into
    // (`shadowsThePrelude`), and an import of one's own namespace must not read as an
    // import from elsewhere. Convert the emitted side alone and every name this file
    // imports becomes `Unplaceable` — "imported from `my-lib`, but this declaration is
    // emitted into package `my_lib`".
    //
    // FAILS WHEN BACKED OUT: drop the conversion in `Bootstrap.importedNames` and this
    // is a BootstrapError, not a wrong string.
    //
    // TWO FILES, and that is what makes it drive the comparison at all: `place`
    // consults the file's OWN types before `shadowsThePrelude`, so an import of a
    // sibling declared in the same file never reaches the package check. (Measured —
    // written as one file, this test passed with the conversion backed out.)
    val payload = gen(parseSource(
      """namespace my-lib
        |  sort Payload
        |    entity Payload(v: Int64)
        |  end
        |end
        |""".stripMargin, "payload.anthill"))
    val holder = gen(parseSource(
      """namespace my-lib
        |  sort Holder
        |    import my-lib.{Payload}
        |    operation held() -> Payload
        |  end
        |end
        |""".stripMargin, "holder.anthill"))
    val src = holder.find(_.relPath == "src/main/scala/my_lib/Holder.scala")
      .getOrElse(fail(s"expected Holder.scala in: ${holder.map(_.relPath)}")).contents
    assert(src.contains("def held(): my_lib.Payload"),
      s"a self-import through a hyphenated package must still place the name:\n$src")
    ScalaCompile.assertCompiles("a hyphenated namespace importing itself", payload ++ holder)
  }

  test("WI-1055: the prelude refusal set is a NAMED list, and the compiling count is a floor") {
    // The ticket's two numeric guards, together because they are one trade-off:
    // every refusal added takes a file out of the tree, so the refusal list and
    // the compiling count have to be read against each other.
    //
    // THE NAMED LIST. A refusal is an EXCLUSION, and an exclusion nobody named is
    // a silent skip wearing a diagnostic. Each entry below pairs the file with the
    // construct that defeated the emitter, so adding a refusal is an edit here and
    // not a quiet shrinking of the backend. WI-1020's closure test consumes this
    // set: what it compiles is the complement.
    //
    // THE FLOOR. 16 of 44 prelude files compiled standalone when WI-1020 measured
    // (commit 0ebec357); the ticket makes that a floor so that "refuse everything"
    // cannot pass for a fix. Asserted as `>=` and not `==` on purpose — the number
    // moves in BOTH directions for good reasons, so pinning it exactly would fail
    // on being improved and would also have to be re-pinned by every honest loss.
    //
    // WHAT A STANDALONE COMPILE MEANS HERE, stated because the number is easy to
    // over-read: a file whose emission references a SIBLING file cannot compile
    // alone, so this counts self-contained files, not correct ones. It went 24 ->
    // 17 under WI-1021, and every one of the seven is a file that stopped
    // CAPTURING: `list`/`stream`/`string`/`bigint`/`indexed_seq`/`iteration`/
    // `finite_stream` each named a prelude sibling that the type map used to
    // rewrite to a same-spelled Scala type (`Option`, `List`, `Tuple2`), so they
    // compiled alone against `scala.Option` and friends. Now they name
    // `anthill.prelude.Option` and honestly need the sibling.
    //
    // RE-MEASURED AT WI-1062: still 17, and that is the metric being useless
    // rather than the fix doing nothing. Six files left the refusal set and every
    // one of them names a sibling (`Stream`, `Iterable`, `FiniteCollection`), so
    // none of them can compile ALONE — they went from "refused" to "emitted and
    // needs its siblings", which this counter cannot see. The closure is the number
    // that moved: 11 errors -> 4.
    //
    // RE-MEASURED AT WI-1066: 18, and the one that moved is set.anthill. Its only
    // reference to a sibling WAS the `extends _root_.anthill.prelude.Eq[T]` that ticket
    // removed; every remaining name in `Set.scala` is `Set` itself or a scalar, so it
    // now compiles alone. The counter going UP for a removed `extends` is a fair
    // reading of what it measures (self-containedness, §"WHAT A STANDALONE COMPILE
    // MEANS HERE") and not evidence that the emission got better — `Map` and
    // `VectorSpace` changed the same way and still name siblings.
    //
    // Compiling the whole closure is WI-1020's. What is left of it, MEASURED at
    // WI-1062: FOUR errors, down from eleven. One was WI-1054 (`zero-val` is not a
    // Scala identifier, `Numeric.scala`); the other three are `Modifiable`, which
    // effects.anthill declares and is refused for an unrelated `anthill.reflect`
    // import, cascading into `MutableCollection.scala`. The eight that went were
    // all `Iterable is not a member of anthill.prelude` — the cascade WI-1062 was
    // filed to remove — and `PersistentCollection.scala` is now clean.
    //
    // RE-MEASURED AT WI-1054: THREE, and they are the `Modifiable` three. The parse
    // error is gone — that ticket normalizes `-` to `_` before the §5 conversion, so
    // `Numeric.scala` emits `def zeroVal(): T`. Nothing else in the closure carried a
    // hyphen (measured across the prelude: `zero-val` was the only one), which is why
    // this is a one-error move and not a cascade.
    //
    // BOTH COUNTS UNDER-REPORT, and by construction: `dotc` ends the run at the
    // phase that first reported an error, so nothing a LATER phase would say is in
    // them. Peeling the failing files off and recompiling until it is clean gives
    // the real shape, measured both ways:
    //   before WI-1062  11 -> 3 (Field, the Numeric cascade) -> clean
    //   after  WI-1062   4 -> 3 (the same) -> 4 -> clean
    //   after  WI-1064   4 -> 3 (the same) -> 2 -> 4 -> clean
    //   after  WI-1066   4 -> 3 (the same) -> 2 -> 4 -> clean   (unchanged)
    //   after  WI-1054        3 (Modifiable) -> 2 -> 4 -> clean
    //   after  WI-1065        3 (Modifiable, mutable_collection.anthill) -> clean at 36 files
    // WI-1054 removed the FIRST rung outright rather than shortening one: the round
    // of 4 was 3 Modifiable errors plus the `zero-val` parse error, and with the
    // parse error gone that round IS the old second rung. The remaining ladder is
    // unchanged, which is the check that it fixed one thing.
    //
    // WI-1065 removed the LAST TWO rungs together, which is one fix and not two:
    // the 2 was its overrides (`error overriding method map in trait Iterable`,
    // map and filter), and the trailing 4 was only ever those errors seen one
    // round later — finite_combinators reporting `FiniteCollection` missing once
    // its file was peeled. With the shadowed `requires` demoted to evidence,
    // finite_collection.anthill and finite_combinators.anthill BOTH stay in the
    // compiled set, which is why the clean count grew. The one rung left is the
    // `Modifiable` cascade: effects.anthill is refused (see the set above), so
    // `MutableCollection`'s second supertrait names a type no file emits.
    // Six more files compile at WI-1062, and the round it added is the one it
    // UNCOVERED rather than caused: `requires` -> `extends` (§2.7) is unsound for a
    // refining override and for a data sort that requires an algebra, which only
    // became observable once FiniteCollection / FiniteMappedStream /
    // FiniteFilteredStream were in the tree at all. Nothing about effects.
    //
    // WI-1064 TOOK THE DATA-SORT HALF: that round of 4 became 2, and the two that
    // went are `class Fmapped needs to be abstract` / the `Ffiltered` twin. The two
    // that were left were the shadowing redeclaration (`error overriding method map
    // in trait Iterable`), WI-1065's — taken since, see its ladder row above.
    //
    // WI-1066 MOVED NOTHING HERE, and that is the expected result rather than a fix
    // that failed. The three emissions it corrects (`Set` / `Map` / `VectorSpace`) all
    // COMPILED before and after — a trait tolerates unimplemented members — so none of
    // them was ever among these errors. What it removes is a claim nothing in the
    // closure depended on, which is exactly why no compile could have caught it and
    // why its own tests assert on emitted text.
    //
    // THAT ERA'S FINAL ROUND OF 4 WAS PEELING, NOT A DEFECT, and reading it as one
    // would have been easy: once finite_collection.anthill was peeled off for the
    // override above, `FiniteCollection` left the compilation set, so the two
    // combinator files that name it as a FIELD TYPE reported `type FiniteCollection
    // is not a member of anthill.prelude` — WI-1065's error seen one round later.
    // That is also why WI-1064 alone could not grow the closure (the files it fixed
    // depend on the file WI-1065 owned), and why WI-1065's row grows it by four.
    //
    // (DECLARATION, construct) and not the construct alone: WI-1021's measured
    // finding was precisely that iterable.anthill's refusal MOVED within its file,
    // from `operation iterator` (an arity conflict) to `operation map` (the row).
    // Pinning the declaration is what holds that; the message already carries it,
    // so a refusal that relocated within a file fails here rather than passing as
    // the same entry.
    //
    // SIX FILES LEFT (WI-1062), from thirteen. `scala_std` erases an effect
    // PARAMETER along with the argument written into it (§2.8a), so combinators /
    // finite_collection / finite_combinators / iterable / map / mutable_stack now
    // emit. TWO entries MOVED rather than left, and both are worth reading as
    // findings:
    //   * relation.anthill — its effect row is erased, and the file is still
    //     refused one operation later on `NodeOccurrence`, an `anthill.reflect`
    //     import. The row was never its only problem.
    //   * logical_stream.anthill — the refusal moves from the type VARIABLE `?A`
    //     to the ARITY of the occurrence carrying it. `LogicalStream[?A]` writes
    //     one argument where the sort declares two, and erasure is what made that
    //     check run first: arguments are now placed before they are rendered, so
    //     the application's shape is judged before its parts. Both diagnoses are
    //     true of the same line; the `?A` arm is driven by a fixture instead
    //     (WI-1055 B2 above), for exactly the reason the other B2 arms are.
    val expectedRefusals = Map(
      "delay.anthill" -> ("operation `pure`", "ORDINARY type-parameter slot"),
      "effects.anthill" -> ("sort `MatchFailed`", "imported from `anthill.reflect`"),
      "logical_stream.anthill" -> ("operation `empty`", "declares 2 type parameter(s)"),
      "meta.anthill" -> ("entity `Meta`", "imported from `anthill.reflect`"),
      "relation.anthill" -> ("operation `guarded_of`", "imported from `anthill.reflect`"),
      "sort.anthill" -> ("sort `EffectExpression`", "emits no Scala type for"),
      "sortedset.anthill" -> ("sort `SortedSet`", "named requirement slot"),
    )
    // THE SAME SET `scalaTypes` WAS BUILT FROM (WI-1060), and not a second listing of
    // the same directory: the table places every name these files emit, so a walk that
    // could differ from it would assert the emission of one set against the table of
    // another.
    val sources = StdlibFixture.preludeByName
    assert(sources.length >= 44, s"expected the measured prelude, got ${sources.length} files")

    val refused = scala.collection.mutable.Map.empty[String, String]
    var compiled = 0
    sources.foreach { case (name, pf) =>
      try
        val files = gen(pf)
        // unit.anthill declares no sort/entity, so it emits nothing and is neither
        // refused nor compiled — counted as neither rather than as a pass.
        if files.nonEmpty && ScalaCompile.errors(files).isEmpty then compiled += 1
      catch case e: BootstrapError => refused(name) = e.getMessage
    }

    assertEquals(refused.keySet.toVector.sorted, expectedRefusals.keySet.toVector.sorted,
      "the refusal set changed; an exclusion must be named here with its reason, " +
      "not left for a reader to discover from a shrinking output tree")
    expectedRefusals.foreach { case (file, (decl, construct)) =>
      assert(refused(file).contains(construct),
        s"$file is refused for a different reason than recorded: ${refused(file)}")
      assert(refused(file).contains(decl),
        s"$file is refused at a different DECLARATION than recorded: ${refused(file)}")
    }
    assert(compiled >= 16,
      s"only $compiled prelude files compile standalone; 16 did before WI-1055, and " +
      "refusing more than is fixed would show up here")
  }

  test("scala-forward-mapping §1: ??? must never appear in generated output") {
    // Multi-file scan across stdlib files known to contain rules — locks
    // in that no Bootstrap path emits `???`. Per spec §1, `???` is a
    // codegen bug.
    val files = Seq(
      "anthill/prelude/option.anthill",
      "anthill/prelude/eq.anthill",
      "anthill/geometry.anthill",
    ).flatMap(rel => gen(parseStdlib(rel)))
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
    val files = gen(pf)
    val laws = files.filter(_.relPath.endsWith("Laws.scala"))
    assert(laws.isEmpty, s"bootstrap should not emit Laws files; got: ${laws.map(_.relPath)}")
  }

  test("Bootstrap.buildSbt is project-global (single source of truth)") {
    // build.sbt is project-level, not per-file. The previous per-file
    // emission was a footgun: a no-laws file emitted after a laws-file
    // would silently overwrite the build.sbt with a missing scalacheck
    // dep. The fix: build.sbt is exposed as a separate API the caller
    // invokes once after merging all per-file outputs.
    val a = gen(parseStdlib("anthill/prelude/option.anthill"))
    val b = gen(parseStdlib("anthill/prelude/eq.anthill"))
    // A version no profile would ever declare, so the assertion below can only pass by
    // `buildSbt` USING its parameter. Reintroducing a hardcoded default — the thing this
    // seam exists to prevent — fails here rather than emitting a plausible wrong number.
    val merged = a ++ b :+ Bootstrap.buildSbt("9.9.9-test")
    val buildSbts = merged.filter(_.relPath == "build.sbt")
    assertEquals(buildSbts.size, 1, s"expected exactly one build.sbt in merged tree; got ${buildSbts.size}")
    assert(buildSbts.head.contents.contains("scalaVersion := \"9.9.9-test\""),
      s"build.sbt must emit the version it was given:\n${buildSbts.head.contents}")
    // generate() itself never emits build.sbt
    assert(!a.exists(_.relPath == "build.sbt"),
      "generate() should not emit build.sbt; that's a separate API")
    assert(!b.exists(_.relPath == "build.sbt"),
      "generate() should not emit build.sbt; that's a separate API")
  }

  test("the emitted scalaVersion comes from scala_std's LanguageMapping, not the emitter") {
    // DRIVES the chain end to end: load the stdlib KB, resolve the `scala_std` profile,
    // read `language_version` off it, and emit a build.sbt from what came back. Every
    // link is exercised — a test that only asserted `ScalaProfile` returns a string
    // would keep passing if `buildSbt` ignored it.
    //
    // FAILS WHEN BACKED OUT, specifically: delete `language_version` from
    // `scala_std.anthill` and this reports `FieldOmitted`; drop it from the
    // `LanguageMapping` entity in `realization.anthill` and the stdlib stops loading, so
    // `stdlibKb` fails first; give `buildSbt` a hardcoded version again and the emitted
    // text stops tracking the fact. It cannot pass with the seam removed.
    // No literal version is pinned here on purpose. `3.8.4` already lives in
    // `scala_std.anthill` and `scaland/build.sbt`, and those two are documented as free
    // to diverge; a third copy in a test would make every profile retarget an edit here
    // for no added coverage. What is asserted is the PROPERTY — the emitted manifest is
    // whatever the profile said — which is the thing that can actually regress.
    val version = ScalaProfile.languageVersion(stdlibKb) match
      case LanguageVersion.Declared(v) => v
      case other => fail(
        s"scala_std must declare a language_version; got $other")

    assertEquals(Bootstrap.buildSbt(version).contents, s"scalaVersion := \"$version\"\n",
      "the emitted manifest must be exactly the profile's version")
  }

  test("an omitted language_version and an explicit `none` are different answers") {
    // The two absence cases side by side in ONE test, because they are one distinction
    // and asserting them apart made each half depend on the other for its meaning.
    // Collapsing `DeclaredAbsent` and `FieldOmitted` in `ScalaProfile` cannot keep both
    // assertions below green — that is the whole control, and it is now local.
    //
    // Scaland can tell these apart because an omitted named argument is genuinely absent
    // from the loaded fact: `Loader.reallocTerm` copies `namedArgs` verbatim and pads
    // nothing. (Rustland's loader pads with an unbound var — a different mechanism, and
    // not the one this runs against.)
    val kb = StdlibFixture.kbWith(parseSource(
      """
      namespace test.langver
        import anthill.realization.{LanguageMapping, ImplTrait}
        import anthill.prelude.Option.{some, none}

        fact LanguageMapping(
          language: "manifestless",
          profile: some("std"),
          language_version: none,
          effect_map: [],
          receiver_map: [],
          type_map: [],
          trait_return: ImplTrait
        )
      end
      """, "langver.anthill"))
    // `rust_std` ships a mapping and never writes the field — it emits no sbt-like
    // manifest. MEASURED: deleting `language_version` from scala_std.anthill made the
    // chain test above report `FieldOmitted` by this same absent-field route.
    assertEquals(
      ScalaProfile.languageVersion(kb, language = "rust", profile = "std"),
      LanguageVersion.FieldOmitted,
      "rust_std omits language_version, so it must report the field absent, not a value")
    assertEquals(
      ScalaProfile.languageVersion(kb, language = "manifestless", profile = "std"),
      LanguageVersion.DeclaredAbsent,
      "an explicitly-declared `none` is a decision, not a missing field")
  }

  test("a malformed language_version is refused loudly, not read as absent") {
    // Both throw paths. They exist so that `DeclaredAbsent` means "the fact said none"
    // and nothing else — without them a junk value falls through to the same answer as a
    // deliberate `none`, which is how the arms this replaced managed to be dead code.
    def mapping(lang: String, version: String) = parseSource(
      s"""
      namespace test.malformed_$lang
        import anthill.realization.{LanguageMapping, ImplTrait}
        import anthill.prelude.Option.{some, none}

        fact LanguageMapping(
          language: "$lang",
          profile: some("std"),
          language_version: $version,
          effect_map: [],
          receiver_map: [],
          type_map: [],
          trait_return: ImplTrait
        )
      end
      """, s"malformed_$lang.anthill")

    val kb = StdlibFixture.kbWith(mapping("notanoption", "42"), mapping("notastring", "some(42)"))
    val bare = intercept[IllegalStateException](
      ScalaProfile.languageVersion(kb, language = "notanoption", profile = "std"))
    assert(bare.getMessage.contains("not an Option term"),
      s"refusal must say what was wrong: ${bare.getMessage}")
    val wrapped = intercept[IllegalStateException](
      ScalaProfile.languageVersion(kb, language = "notastring", profile = "std"))
    assert(wrapped.getMessage.contains("not a string literal"),
      s"refusal must say what was wrong: ${wrapped.getMessage}")
  }

  test("ScalaProfile reports no mapping for an unknown language or profile") {
    assertEquals(
      ScalaProfile.languageVersion(stdlibKb, language = "cobol", profile = "std"),
      LanguageVersion.NoSuchMapping,
      "a language with no LanguageMapping fact must not report a version")
    assertEquals(
      ScalaProfile.languageVersion(stdlibKb, language = "scala", profile = "no-such"),
      LanguageVersion.NoSuchMapping,
      "a real language at an unknown profile is still no mapping")
    assertEquals(
      ScalaProfile.typeMap(stdlibKb, language = "cobol", profile = "std"),
      HostTypeMap.NoSuchMapping,
      "the type map answers the same question the same way")
  }

  // ── WI-1060: the emitter's type tables come from outside the emitter ──────

  /** A sort whose every member is typed by the scalar under test, so a changed
    * `type_map` entry has somewhere to show. Parameterized by profile-independent
    * text so the mutation tests below emit the SAME anthill twice. */
  private def scalarFixture = parseSource(
    """namespace my.app
      |  sort Adder
      |    operation add(a: Int64, b: Int64) -> Int64
      |  end
      |end
      |""".stripMargin, "adder.anthill")

  test("WI-1060: the emitted host type is the PROFILE's, and an edit to the fact moves it") {
    // THE TICKET'S ACCEPTANCE, and it is a mutation rather than an agreement check:
    // "the table is read" is not observable — a table read and then ignored passes
    // every assertion a stock emission can make. So the same anthill file is emitted
    // twice against two profiles that differ in ONE entry, and the two outputs must
    // differ in exactly that entry.
    //
    // FAILS WHEN BACKED OUT: reinstate a hardcoded `hostScalars` in the emitter and
    // both emissions say `_root_.scala.Long`, so the first assertion fails; drop the
    // `types` parameter from `generate` and it does not compile.
    val kb = StdlibFixture.kbWith(parseSource(
      """
      namespace test.mutant_scalars
        import anthill.realization.{LanguageMapping, TypeMapping, ImplTrait}
        import anthill.prelude.Option.{some, none}

        fact LanguageMapping(
          language: "scala",
          profile: some("mutant"),
          language_version: some("3.8.4"),
          effect_map: [],
          receiver_map: [],
          type_map: [
            TypeMapping(anthill_type: "Int64", host_type: "_root_.my.own.Fixnum")
          ],
          trait_return: ImplTrait
        )
      end
      """, "mutant_scalars.anthill"))
    val mutant = ScalaTypes.resolve(
      kb, StdlibFixture.preludeFiles, language = "scala", profile = "mutant")

    val moved = Bootstrap.generate(scalarFixture, mutant).head.contents
    assert(moved.contains("def add(a: _root_.my.own.Fixnum, b: _root_.my.own.Fixnum): " +
      "_root_.my.own.Fixnum"),
      s"the emission must carry the profile's host type verbatim:\n$moved")

    // THE CONTROL, and it is what makes the assertion above about the FACT rather
    // than about the fixture: the same source under `scala_std` says `Long`.
    val stock = gen(scalarFixture).head.contents
    assert(stock.contains("def add(a: _root_.scala.Long, b: _root_.scala.Long): " +
      "_root_.scala.Long"),
      s"the stock profile must still say what scala_std declares:\n$stock")
  }

  test("WI-1060: a scalar the profile drops stops being a scalar") {
    // The other half of "the fact decides", and the sharper one: `Int64` is a host
    // carrier only because an entry says so. A profile with an EMPTY type_map leaves
    // `int64.anthill`'s own `sort Int64` as the answer — the trait no value inhabits —
    // which is a bad emission and exactly the point. Nothing in the emitter special-
    // cases the name, so nothing in the emitter can keep the entry alive.
    val kb = StdlibFixture.kbWith(parseSource(
      """
      namespace test.no_scalars
        import anthill.realization.{LanguageMapping, ImplTrait}
        import anthill.prelude.Option.{some, none}

        fact LanguageMapping(
          language: "scala", profile: some("scalarless"),
          language_version: none,
          effect_map: [], receiver_map: [], type_map: [],
          trait_return: ImplTrait
        )
      end
      """, "no_scalars.anthill"))
    val scalarless = ScalaTypes.resolve(
      kb, StdlibFixture.preludeFiles, language = "scala", profile = "scalarless")
    val src = Bootstrap.generate(scalarFixture, scalarless).head.contents
    assert(src.contains("def add(a: _root_.anthill.prelude.Int64"),
      s"with no entry, `Int64` must fall to the sort the prelude declares:\n$src")
  }

  test("WI-1060: both `language: \"scala\"` profiles declare the same scalars") {
    // `scala_caps.anthill` says of its own table that it is not a caps-specific
    // choice — capture-checking changes the ARROW and the effect shape, not what an
    // anthill sort's values ARE — and until now nothing held it to that. A profile
    // switch that restored `Pair -> Tuple2` in one of them reintroduces WI-1021's
    // measured defect in one step, and only in that profile.
    assertEquals(
      ScalaProfile.typeMap(stdlibKb, profile = "caps"),
      ScalaProfile.typeMap(stdlibKb, profile = "std"),
      "the two scala profiles must agree on what an anthill scalar's values are")
  }

  test("WI-1060: a prelude sort's arity is the DECLARING file's, not a list in the emitter") {
    // The design question the ticket left open — where the arity comes from, since
    // `TypeMapping` has no column for it — answered by DERIVING it. What that buys
    // over the hand-written table it replaced is asserted here in the only way it
    // can be: the same consumer, placed against two file sets.
    //
    // The declaring file is a FIXTURE and not a prelude file, because the point is
    // the derivation and not any particular sort. `Boxy` writes two parameters, so:
    //   * with the declaration in the set, a two-argument use is placed and qualified
    //     and a one-argument use is REFUSED naming the count;
    //   * with it out of the set, neither happens — the name is Ambient, which
    //     performs no arity check at all. That second half is the control: it is what
    //     fails if the table is populated from something other than the file.
    val declaring = parseSource(
      """namespace anthill.prelude
        |  sort Boxy
        |    sort A = ?
        |    sort B = ?
        |    operation unbox(b: Boxy) -> A
        |  end
        |end
        |""".stripMargin, "boxy.anthill")
    def consumer(args: String) = parseSource(
      s"""namespace my.app
         |  sort User
         |    sort X = ?
         |    sort Y = ?
         |    operation use(b: Boxy$args) -> X
         |  end
         |end
         |""".stripMargin, "user.anthill")

    val withDecl = ScalaTypes.resolve(stdlibKb, StdlibFixture.preludeFiles :+ declaring)
    val src = Bootstrap.generate(consumer("[A = X, B = Y]"), withDecl).head.contents
    assert(src.contains("def use(b: _root_.anthill.prelude.Boxy[X, Y]): X"),
      s"a derived entry must name the type the declaring file emits:\n$src")
    val err = intercept[BootstrapError](Bootstrap.generate(consumer("[A = X]"), withDecl))
    assert(err.getMessage.contains("declares 2 type parameter(s)"),
      s"the arity checked must be the declaration's: ${err.getMessage}")

    // CONTROL. Same consumer, same profile, declaration NOT in the set: no entry, so
    // `Placement.Ambient` — a package-qualified guess with no arity check, and the
    // one-argument form that was refused above now emits.
    val ambient = Bootstrap.generate(consumer("[A = X]"), scalaTypes).head.contents
    assert(ambient.contains("def use(b: my.app.Boxy[X]): X"),
      s"without the declaration nothing checks the arity:\n$ambient")
  }

  test("WI-1060/WI-1067: two declarations in one package are refused, not last-wins") {
    // The derived table is keyed on PACKAGE + LEAF, because that pair is one Scala
    // declaration address. Two files answering the same address means the caller's
    // closure has two declarations for one name, and a fold that just overwrote would
    // pick by file ORDER and emit the loser's arity everywhere.
    //
    // No corpus set has the shape (the 45 prelude files do not), so this arm is
    // driven by a fixture or not at all.
    def dup(file: String, params: String) = parseSource(
      s"""namespace anthill.prelude
         |  sort Twin
         |$params
         |  end
         |end
         |""".stripMargin, file)
    val err = intercept[BootstrapError](Bootstrap.emittedTypes(IndexedSeq(
      dup("one.anthill", "    sort A = ?"),
      dup("two.anthill", "    sort A = ?\n    sort B = ?"))))
    assert(err.getMessage.contains("`Twin` is declared twice in Scala package `anthill.prelude`"),
      s"the refusal must name the leaf: ${err.getMessage}")
    // LOCATED, and that is not decoration: the real call passes 45 files, so a message
    // naming the leaf alone leaves a reader grepping for it. The span is the SECOND
    // declaration — the one that could not be added.
    assert(err.getMessage.contains("two.anthill:"),
      s"the refusal must name the file it could not add: ${err.getMessage}")
    assert(err.getMessage.contains("first declaration is at one.anthill:"),
      s"the refusal must name the first declaration too: ${err.getMessage}")
    // CONTROL: the SAME PARSED FILE twice is not a conflict — a repeated input has the
    // same source span and is one declaration listed twice, not two declarations.
    val once = dup("one.anthill", "    sort A = ?")
    assertEquals(
      Bootstrap.emittedTypes(IndexedSeq(once, once)).in("anthill.prelude").types.keySet,
      Set("Twin"))
  }

  test("WI-1060: a malformed type_map is refused loudly, not read as a partial table") {
    // The same discipline `language_version` has, for the same reason: an entry this
    // reader cannot honour must not become an entry that is quietly absent, because
    // an absent scalar is not an error downstream — it silently becomes the prelude's
    // own `trait Int64` (the test two above measures exactly that fall-through).
    def mapping(lang: String, entries: String) = parseSource(
      s"""
      namespace test.badmap_$lang
        import anthill.realization.{LanguageMapping, TypeMapping, ImplTrait}
        import anthill.prelude.Option.{some, none}

        fact LanguageMapping(
          language: "$lang", profile: some("std"),
          language_version: none,
          effect_map: [], receiver_map: [],
          type_map: $entries,
          trait_return: ImplTrait
        )
      end
      """, s"badmap_$lang.anthill")

    val kb = StdlibFixture.kbWith(
      mapping("dup", """[TypeMapping(anthill_type: "Int64", host_type: "A"),
                        TypeMapping(anthill_type: "Int64", host_type: "B")]"""),
      // WI-088's marshalled form: the host holds the value DIFFERENTLY and converts at
      // the boundary. Read as a plain rename it emits code that type-checks and moves
      // the wrong bytes, so it is refused rather than half-honoured.
      mapping("marshalled", """[TypeMapping(anthill_type: "Vec3", host_type: "Array[Double]",
                                lift: some("Vec3.fromArray"))]"""),
      // A junk `lift` must not read as "no adapter": that is the one way a marshalled
      // entry could still pass as a plain rename.
      mapping("badlift", """[TypeMapping(anthill_type: "Int64", host_type: "Long", lift: 42)]"""),
      // WI-089's FLAT keyed form, written where the nested one belongs. `key` selects a
      // profile or a foreign-binding OVERLAY and `lang` selects a host language, and
      // `realization.anthill` documents `none` for both as "legacy/nested entry" — so a
      // written key can only DISAGREE with the LanguageMapping enclosing it. Read as a
      // plain rename, `key: some("webots")` emits the webots-only host type everywhere.
      mapping("overlay", """[TypeMapping(anthill_type: "Vec3", host_type: "const double *",
                             key: some("webots"))]"""),
      mapping("otherlang", """[TypeMapping(anthill_type: "Int64", host_type: "int64_t",
                               lang: some("cpp"))]"""),
      mapping("notalist", """TypeMapping(anthill_type: "Int64", host_type: "Long")"""),
      mapping("notastring", """[TypeMapping(anthill_type: "Int64", host_type: 42)]"""))

    def refusal(lang: String) = intercept[IllegalStateException](
      ScalaProfile.typeMap(kb, language = lang, profile = "std")).getMessage
    assert(refusal("dup").contains("two entries for `Int64`"), refusal("dup"))
    assert(refusal("marshalled").contains("MARSHALLED"), refusal("marshalled"))
    assert(refusal("badlift").contains("`lift` that is not an Option term"),
      refusal("badlift"))
    assert(refusal("overlay").contains("`key`-QUALIFIED entry (webots)"), refusal("overlay"))
    assert(refusal("otherlang").contains("`lang`-QUALIFIED entry (cpp)"), refusal("otherlang"))
    assert(refusal("notalist").contains("not a list literal"), refusal("notalist"))
    assert(refusal("notastring").contains("no `host_type` string literal"),
      refusal("notastring"))
  }

  test("WI-1060: a mapping with no type_map field at all is a distinct answer") {
    // `FieldOmitted` and not an empty table, for the reason `language_version` keeps
    // the same case: a profile that declares `type_map: []` has DECIDED to map no
    // scalar (the scalarless test above emits from exactly that), and a fact that
    // predates the field has decided nothing. Collapsing them would let schema drift
    // read as a deliberate choice, and `ScalaTypes.resolve` throws on one and not the
    // other.
    val kb = StdlibFixture.kbWith(parseSource(
      """
      namespace test.nofield
        import anthill.realization.{LanguageMapping, ImplTrait}
        import anthill.prelude.Option.{some, none}

        fact LanguageMapping(
          language: "fieldless", profile: some("std"),
          language_version: none,
          effect_map: [], receiver_map: [],
          trait_return: ImplTrait
        )
      end
      """, "nofield.anthill"))
    assertEquals(
      ScalaProfile.typeMap(kb, language = "fieldless", profile = "std"),
      HostTypeMap.FieldOmitted,
      "a fact that never writes type_map must not read as one that maps nothing")
    assertEquals(
      ScalaProfile.typeMap(kb, language = "scala", profile = "scalarless-check") match
        case HostTypeMap.NoSuchMapping => "absent"
        case other                     => other.toString,
      "absent",
      "and an unknown profile is still no mapping")
  }

  // ── WI-1060 review: what the DERIVED table made newly wrong ───────────────
  //
  // Deriving the prelude half answered the membership question — every sort the
  // prelude emits is in the table now, not the six that happened to have a host
  // entry — and that same widening turned three previously-narrow gaps into live
  // ones. Each is driven below, with the CONTROL that says it is the derivation
  // being measured and not the fixture.

  test("WI-1060: an explicit import of ANOTHER package shadows the prelude table") {
    // `place` consulted the prelude table before the import table, so a project
    // writing `import my.lib.{Option}` was emitted `_root_.anthill.prelude.Option` —
    // a different library's type, compiled green. Anthill's own scoping says the
    // opposite: an explicit import shadows the auto-import, and Bootstrap emits no
    // Scala `import`, so the name it names cannot be reached at all.
    //
    // WHY IT MATTERS MORE SINCE WI-1060: while the table was six hand-picked names,
    // an import had to collide with one of `Int64`/`Pair`/`Option`/`List`/`Set`/`Map`
    // to be captured. Derived, it is every prelude sort — `Eq`, `Numeric`, `Cell`,
    // `Field`, `Ord`, `Time` — so the collision surface is ten times wider.
    //
    // FAILS WHEN BACKED OUT: move `shadowsThePrelude` back below `types.preludeSort`
    // in `place` and this emits `_root_.anthill.prelude.Option[X]` with no refusal.
    // MEASURED: this test alone fails — the corpus is unmoved, because no prelude file
    // imports a prelude name from anywhere but `anthill.prelude`.
    def holder(imports: String) = parseSource(
      s"""namespace my.app
         |$imports
         |  sort Holder
         |    sort X = ?
         |    operation get(o: Option[T = X]) -> X
         |  end
         |end
         |""".stripMargin, "holder.anthill")

    val err = intercept[BootstrapError](gen(holder("  import my.lib.{Option}")))
    assert(err.getMessage.contains("`Option` is imported from `my.lib`"),
      s"the refusal must say which package the import names: ${err.getMessage}")
    assert(err.getMessage.contains("holder.anthill:"),
      s"the refusal must be located: ${err.getMessage}")

    // CONTROL 1: no import, and the same occurrence reaches the prelude's own type.
    // Without this the test above would pass against a `place` that refused every
    // prelude name outright.
    val ambient = gen(holder("")).head.contents
    assert(ambient.contains("def get(o: _root_.anthill.prelude.Option[X]): X"),
      s"an unimported prelude name must still reach the prelude's type:\n$ambient")

    // CONTROL 2, and it is the arm that keeps the corpus emitting: an import OF THE
    // PRELUDE is not a shadow. It names the same declaration the auto-import finds,
    // and half the prelude writes one (`cell.anthill`'s `import anthill.prelude.{Unit,
    // Modifiable, …}`). Refusing on `importedFrom` alone takes those files out of the
    // tree — measured, the refusal set grows past its recorded seven.
    val imported = gen(holder("  import anthill.prelude.{Option}")).head.contents
    assert(imported.contains("def get(o: _root_.anthill.prelude.Option[X]): X"),
      s"an import of the auto-imported package must not shadow it:\n$imported")
  }

  test("WI-1060: a NESTED namespace's sorts are not reachable by a bare name") {
    // The derived table is what a bare mention reaches, and that is the auto-imported
    // package's own members. `algebra.anthill` writes `namespace anthill.prelude.algebra`
    // and `meta.anthill` writes `namespace anthill.prelude.Meta`, so an unfiltered walk
    // enters `Ring`, `Trust` and `ProofResult` — names anthill itself will not resolve
    // without an explicit import. A project declaring its own `Ring` would then emit
    // `_root_.anthill.prelude.algebra.Ring`.
    //
    // ONE FIXTURE, TWO NAMESPACES, so the only thing that varies is the package the
    // declaration is emitted into — and the consumer is written with the RIGHT arity,
    // so what differs between the two runs is the NAME and not a refusal.
    //
    // FAILS WHEN BACKED OUT: drop the `t.pkg != autoImportPackage` filter in
    // `emittedTypes` and the first assertion emits `_root_.anthill.prelude.algebra.Ringy[X]`.
    // MEASURED: that is the ONLY test that changes — no corpus emission and no member of
    // the refusal set moves, so this fixture is the whole of what holds the rule.
    def declaring(ns: String) = parseSource(
      s"""namespace $ns
         |  sort Ringy
         |    sort T = ?
         |  end
         |end
         |""".stripMargin, "ringy.anthill")
    val consumer = parseSource(
      """namespace my.app
        |  sort User
        |    sort X = ?
        |    operation use(r: Ringy[T = X]) -> X
        |  end
        |end
        |""".stripMargin, "user.anthill")

    val nested = ScalaTypes.resolve(
      stdlibKb, StdlibFixture.preludeFiles :+ declaring("anthill.prelude.algebra"))
    val src = Bootstrap.generate(consumer, nested).head.contents
    assert(src.contains("def use(r: my.app.Ringy[X]): X"),
      s"a nested namespace's sort must not be placed by a bare mention:\n$src")

    // CONTROL: the SAME declaration in the auto-imported package itself IS in the
    // table, and the same occurrence then names it. Without this arm the assertion
    // above would pass against an `emittedTypes` that saw nothing in the file at all.
    val direct = ScalaTypes.resolve(
      stdlibKb, StdlibFixture.preludeFiles :+ declaring("anthill.prelude"))
    val placed = Bootstrap.generate(consumer, direct).head.contents
    assert(placed.contains("def use(r: _root_.anthill.prelude.Ringy[X]): X"),
      s"the same sort in `anthill.prelude` must be placed by the table:\n$placed")
  }

  test("WI-1060: a name the prelude declares but emits NOTHING for is refused everywhere") {
    // WI-1055 B1's cross-file half, which had no carrier until the derived table
    // existed. `sort.anthill` writes `sort Type = ?` at namespace level — an opaque
    // handle whose Scala spelling would be an `opaque type`, needing an enclosing
    // object rather than a package — so Bootstrap emits nothing for it. INSIDE
    // sort.anthill a bare `Type` was already refused (the file's own
    // `declaredNotEmitted`); from any other file the same name fell to
    // `Placement.Ambient` and emitted `my.app.Type`, a bare identifier naming nothing
    // in the tree. That is the defect B1 was filed for, surviving one file over.
    //
    // WI-1067 CLOSES THE OLD TRADE: a caller that supplies a sibling project `Type`
    // gets that exact-package declaration before this prelude negative. This fixture
    // deliberately supplies no such project declaration, so the prelude refusal is the
    // only honest answer; omitting a real sibling from `projectFiles` violates the
    // caller's complete-closure promise.
    //
    // FAILS WHEN BACKED OUT: drop `PackageTypes.declaredNotEmitted` (retain only the
    // positive types) and this emits `def label(t: my.app.Type): X` with no refusal.
    val consumer = parseSource(
      """namespace my.app
        |  sort Labeller
        |    sort X = ?
        |    operation label(t: Type) -> X
        |  end
        |end
        |""".stripMargin, "labeller.anthill")
    val err = intercept[BootstrapError](gen(consumer))
    assert(err.getMessage.contains("`Type`"),
      s"the refusal must name the type: ${err.getMessage}")
    assert(err.getMessage.contains("anthill.prelude"),
      s"the refusal must say which auto-imported package declares it: ${err.getMessage}")
    assert(err.getMessage.contains("operation `label`") &&
           err.getMessage.contains("labeller.anthill:"),
      s"the refusal must name the declaration and be located: ${err.getMessage}")

    // CONTROL: a name NOTHING declares is still Ambient, not a refusal. Without this
    // the assertion above would pass against a `place` that refused every unplaced
    // name — which is the thirteen-file outcome B1's CONTROL exists to prevent.
    val open = gen(parseSource(
      """namespace my.app
        |  sort Labeller2
        |    sort X = ?
        |    operation label(t: Typo) -> X
        |  end
        |end
        |""".stripMargin, "labeller2.anthill")).head.contents
    assert(open.contains("def label(t: my.app.Typo): X"),
      s"an undeclared name must still ride out qualified:\n$open")
  }

  test("WI-1060: a type_map entry for a PARAMETERIZED sort is refused") {
    // The check that replaced `TypeGen.preludeSorts`' deleted `require`, and it guards
    // the mistake WI-1021 measured and reverted: `List -> scala.List`. `preludeSorts`
    // is `autoImportPackage.types -- hostScalars.keySet`, so such an entry DELETES list
    // .anthill's declared arity and re-adds `List` as a 0-parameter host type — and
    // every `List[T = X]` in the corpus is then refused with "`List` maps to Scala
    // `_root_.scala.List` and declares 0 type parameter(s), but 1 were written", a
    // message blaming the use site for a bad fact entry. rust_std.anthill carries
    // exactly this entry today, so it is not a hypothetical shape.
    //
    // FAILS WHEN BACKED OUT: delete the `parameterizedScalars` check and `resolve`
    // returns a table in which `List` is a 0-parameter host type, so the `intercept`
    // finds nothing thrown. What the check buys is WHERE the fault is reported — at
    // the fact that is wrong, rather than at every use site that is right.
    val kb = StdlibFixture.kbWith(parseSource(
      """
      namespace test.list_scalar
        import anthill.realization.{LanguageMapping, TypeMapping, ImplTrait}
        import anthill.prelude.Option.{some, none}

        fact LanguageMapping(
          language: "scala", profile: some("listy"),
          language_version: none,
          effect_map: [], receiver_map: [],
          type_map: [TypeMapping(anthill_type: "List", host_type: "_root_.scala.List")],
          trait_return: ImplTrait
        )
      end
      """, "list_scalar.anthill"))
    val err = intercept[IllegalArgumentException](ScalaTypes.resolve(
      kb, StdlibFixture.preludeFiles, language = "scala", profile = "listy"))
    assert(err.getMessage.contains("`List` -> `_root_.scala.List`"),
      s"the refusal must name the entry: ${err.getMessage}")
    assert(err.getMessage.contains("1 type parameter(s)"),
      s"the refusal must say what the declaration writes: ${err.getMessage}")

    // CONTROL: an entry for a sort that really has no parameters is accepted — the
    // check is about ARITY and not about a scalar also being a declared sort, which
    // every one of them is.
    assert(ScalaTypes.resolve(stdlibKb, StdlibFixture.preludeFiles)
      .hostScalar("Int64").nonEmpty,
      "a 0-parameter sort must still be mappable as a host scalar")
  }

  test("WI-1060: a profile with no `Unit` entry refuses the empty tuple, located") {
    // `TypeScope.requiredScalar` is the one path that reads a scalar BY NAME rather
    // than by placing a written occurrence, and nothing drove it: the scalarless
    // fixture below has no `()` in it, so deleting the throw and returning a bare
    // "Unit" — the exact fallback its doc says it exists to prevent — left the suite
    // green.
    //
    // FAILS WHEN BACKED OUT, in both directions: return `"Unit"` instead of throwing
    // and the `intercept` fails; throw an unlocated `IllegalStateException` (where it
    // lived before this review) and the located assertion fails — and the refusal-set
    // test would stop recording it as a refusal at all, since it catches
    // `BootstrapError` alone.
    val unitFixture = parseSource(
      """namespace my.app
        |  sort Sink
        |    operation drop(a: Int64) -> ()
        |  end
        |end
        |""".stripMargin, "sink.anthill")
    // The positive half first: with the entry present the empty tuple IS the profile's
    // host type, spelled as the fact spells it.
    val stock = gen(unitFixture).head.contents
    assert(stock.contains("def drop(a: _root_.scala.Long): _root_.scala.Unit"),
      s"the empty tuple must render through the profile's `Unit` entry:\n$stock")

    val kb = StdlibFixture.kbWith(parseSource(
      """
      namespace test.unitless
        import anthill.realization.{LanguageMapping, ImplTrait}
        import anthill.prelude.Option.{some, none}

        fact LanguageMapping(
          language: "scala", profile: some("unitless"),
          language_version: none,
          effect_map: [], receiver_map: [], type_map: [],
          trait_return: ImplTrait
        )
      end
      """, "unitless.anthill"))
    val unitless = ScalaTypes.resolve(
      kb, StdlibFixture.preludeFiles, language = "scala", profile = "unitless")
    val err = intercept[BootstrapError](Bootstrap.generate(unitFixture, unitless))
    assert(err.getMessage.contains("declares no `Unit` entry"),
      s"the refusal must name the missing entry: ${err.getMessage}")
    assert(err.getMessage.contains("drop") && err.getMessage.contains("sink.anthill:"),
      s"the refusal must name the declaration and be located: ${err.getMessage}")
  }

  // ── WI-1067: package-keyed local/project type lookup ─────────────────────

  test("WI-1067: one file resolves exact packages and qualifies cross-package uses") {
    // A generated top-level `package a.b` does NOT make `a.Foo` bare-visible in Scala
    // 3. The package chain still selects a.Foo for Anthill's nested namespace, but both
    // that reference and the sibling-package reference must be qualified. The old flat
    // table emitted bare `Foo` in both places; only a real compile exposed the defect.
    //
    // FAILS WHEN BACKED OUT: flatten `FileTypes` by leaf and `Sibling.use` emits bare
    // `Foo`; the real compiler rejects it. CONTROL: `Same.use` is in Foo's exact package,
    // stays bare, and compiles, proving the fix does not qualify everything.
    val fixture = parseSource(
      """namespace a
        |  sort Foo
        |    operation id(x: Int64) -> Int64
        |  end
        |  sort Same
        |    operation use(x: Foo) -> Foo
        |  end
        |  namespace b
        |    sort Nested
        |      operation use(x: Foo) -> Foo
        |    end
        |  end
        |end
        |namespace c
        |  sort Sibling
        |    operation use(x: Foo) -> Foo
        |  end
        |end
        |""".stripMargin, "two_packages.anthill")
    val files = gen(fixture)
    val same = files.find(_.relPath.endsWith("/a/Same.scala")).get.contents
    val nested = files.find(_.relPath.endsWith("/a/b/Nested.scala")).get.contents
    val sibling = files.find(_.relPath.endsWith("/c/Sibling.scala")).get.contents
    assert(same.contains("def use(x: Foo): Foo"),
      s"a type in the exact package must remain bare:\n$same")
    assert(nested.contains("def use(x: _root_.a.Foo): _root_.a.Foo"),
      s"an ancestor-package type must be selected but qualified:\n$nested")
    assert(sibling.contains("def use(x: _root_.a.Foo): _root_.a.Foo"),
      s"a unique sibling-package type must be qualified:\n$sibling")
    ScalaCompile.assertCompiles("one file spanning exact, nested, and sibling packages", files)
  }

  test("WI-1067: the empty package is not an ancestor candidate of a named package") {
    // Scala 3 does not make a default-package member reachable from a named package;
    // even `_root_.RootType` cannot name it there. The correct outcome is therefore a
    // located refusal rather than generated source that fails later.
    val fixture = parseSource(
      """sort RootType
        |  operation id(x: Int64) -> Int64
        |end
        |namespace named
        |  sort User
        |    operation use(x: RootType) -> RootType
        |  end
        |end
        |""".stripMargin, "default_package.anthill")
    val err = intercept[BootstrapError](gen(fixture))
    assert(err.getMessage.contains("default-package members") &&
           err.getMessage.contains("named package `named`"), err.getMessage)
    assert(err.getMessage.contains("default_package.anthill:"),
      s"the refusal must point at the use: ${err.getMessage}")
  }

  test("WI-1067: a nearer negative declaration shadows an emitted ancestor") {
    // Positive and negative tables must be searched in ONE nearest-package walk. Two
    // separate walks let `a.Shadow` jump over the abstract `a.b.Shadow`, turning an
    // unrepresentable source declaration into a different, compilable Scala type.
    val ancestor = parseSource(
      """namespace a
        |  sort Shadow
        |    operation id(x: Int64) -> Int64
        |  end
        |end
        |""".stripMargin, "ancestor_shadow.anthill")
    val nearer = parseSource(
      """namespace a.b
        |  sort Shadow = ?
        |end
        |""".stripMargin, "nearer_shadow.anthill")
    val consumer = parseSource(
      """namespace a.b.c
        |  sort User
        |    operation use(x: Shadow) -> Shadow
        |  end
        |end
        |""".stripMargin, "shadow_user.anthill")

    val shadowed = ScalaTypes.resolve(stdlibKb, StdlibFixture.preludeFiles,
      projectFiles = IndexedSeq(ancestor, nearer, consumer))
    val err = intercept[BootstrapError](Bootstrap.generate(consumer, shadowed))
    assert(err.getMessage.contains("`Shadow` is declared in package `a.b`") &&
           err.getMessage.contains("emits no Scala type"), err.getMessage)
    assert(err.getMessage.contains("shadow_user.anthill:"),
      s"the refusal must locate the use: ${err.getMessage}")

    // CONTROL: remove only the nearer negative declaration. The ancestor becomes the
    // selected type, stays qualified in package a.b.c, and the real closure compiles.
    val reachable = ScalaTypes.resolve(stdlibKb, StdlibFixture.preludeFiles,
      projectFiles = IndexedSeq(ancestor, consumer))
    val files = Bootstrap.generate(ancestor, reachable) ++
      Bootstrap.generate(consumer, reachable)
    val user = files.find(_.relPath.endsWith("/a/b/c/User.scala")).get.contents
    assert(user.contains("def use(x: _root_.a.Shadow): _root_.a.Shadow"), user)
    ScalaCompile.assertCompiles("ancestor package after removing a nearer negative", files)
  }

  test("WI-1067: duplicate leaves conflict within one package and coexist across packages") {
    // The within-file namespace merge used `++`, so the second declaration silently
    // replaced the first before either placement or the project-wide duplicate guard
    // could see it. The message must identify BOTH declarations; pointing only at the
    // second leaves a reader searching a multi-namespace file for the first.
    val samePackage = parseSource(
      """namespace dup
        |  sort Twin
        |    operation one(x: Int64) -> Int64
        |  end
        |  sort Twin
        |    operation two(x: Int64) -> Int64
        |  end
        |end
        |""".stripMargin, "same_package.anthill")
    val err = intercept[BootstrapError](gen(samePackage))
    assert(err.getMessage.contains("`Twin` is declared twice in Scala package `dup`"),
      err.getMessage)
    assert(err.getMessage.contains("first declaration is at same_package.anthill:"),
      s"the first declaration must be named: ${err.getMessage}")
    assert(err.getMessage.startsWith("same_package.anthill:"),
      s"the second declaration must locate the refusal: ${err.getMessage}")

    // CONTROL: package is part of identity. These two declarations are legal, both
    // survive the table, and the resulting source set compiles together.
    val differentPackages = parseSource(
      """namespace left
        |  sort Twin
        |    operation one(x: Int64) -> Int64
        |  end
        |end
        |namespace right
        |  sort Twin
        |    operation two(x: Int64) -> Int64
        |  end
        |end
        |""".stripMargin, "different_packages.anthill")
    val files = gen(differentPackages)
    assertEquals(files.map(_.relPath).sorted, IndexedSeq(
      "src/main/scala/left/Twin.scala", "src/main/scala/right/Twin.scala"))
    ScalaCompile.assertCompiles("same leaf in two packages", files)
  }

  test("WI-1067: a project sibling type beats the prelude and absence falls back") {
    def ownPair = parseSource(
      """namespace my.app
        |  sort Pair
        |    sort A = ?
        |    sort B = ?
        |    operation fst(p: Pair) -> A
        |  end
        |end
        |""".stripMargin, "project_pair.anthill")
    def consumer = parseSource(
      """namespace my.app
        |  sort User
        |    sort X = ?
        |    sort Y = ?
        |    operation use(p: Pair[A = X, B = Y]) -> X
        |  end
        |end
        |""".stripMargin, "project_user.anthill")

    // The caller supplies its COMPLETE project parse set once when resolving the
    // tables; every per-file generation reads the same answer. With the sibling
    // present, `_root_.my.app.Pair` must win over the auto-imported prelude Pair, and
    // compiling both files proves the selected name exists.
    val project = IndexedSeq(ownPair, consumer)
    val projectTypes = ScalaTypes.resolve(
      stdlibKb, StdlibFixture.preludeFiles, projectFiles = project)
    val projectOut = project.flatMap(Bootstrap.generate(_, projectTypes))
    val user = projectOut.find(_.relPath.endsWith("/User.scala")).get.contents
    assert(user.contains("def use(p: _root_.my.app.Pair[X, Y]): X"),
      s"the same-package sibling must beat the prelude:\n$user")
    ScalaCompile.assertCompiles("project Pair plus its consumer", projectOut)

    // CONTROL: remove only the sibling declaration. The same consumer still reaches
    // `_root_.anthill.prelude.Pair`; compiling it with pair.anthill proves the fallback
    // names a real declaration rather than merely producing the expected substring.
    val fallbackTypes = ScalaTypes.resolve(
      stdlibKb, StdlibFixture.preludeFiles, projectFiles = IndexedSeq(consumer))
    val fallback = Bootstrap.generate(consumer, fallbackTypes)
    val fallbackUser = fallback.head.contents
    assert(fallbackUser.contains("def use(p: _root_.anthill.prelude.Pair[X, Y]): X"),
      s"without the sibling the prelude must remain the fallback:\n$fallbackUser")
    val preludePair = Bootstrap.generate(
      parseStdlib("anthill/prelude/pair.anthill"), fallbackTypes)
    ScalaCompile.assertCompiles("prelude Pair fallback plus its consumer",
      preludePair ++ fallback)
  }

  test("WI-1067: a repeated fully-qualified dotted declaration does not double its package") {
    // `splitPath` used to append the dotted prefix to the enclosing package even when
    // the prefix already WAS that package, producing
    // `anthill.prelude.anthill.prelude.Concat`. Both the relPath and a real compile
    // drive the fix; a source-only assertion would not catch a mismatched path/table.
    val fixture = parseSource(
      """namespace anthill.prelude
        |  sort anthill.prelude.Concat
        |    operation apply(x: Int64) -> Int64
        |  end
        |end
        |""".stripMargin, "qualified_concat.anthill")
    val files = gen(fixture)
    assertEquals(files.map(_.relPath),
      IndexedSeq("src/main/scala/anthill/prelude/Concat.scala"))
    assert(files.head.contents.startsWith("package anthill.prelude\n"),
      files.head.contents)
    ScalaCompile.assertCompiles("a repeated fully-qualified declaration prefix", files)
  }
