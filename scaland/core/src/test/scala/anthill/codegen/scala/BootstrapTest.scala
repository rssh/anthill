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

  private val stdlibDir = StdlibFixture.dir

  /** The plain stdlib KB, loaded once for the suite. */
  private lazy val stdlibKb: KnowledgeBase = StdlibFixture.kbWith()

  private def parseStdlib(rel: String) =
    val src = scala.io.Source.fromFile(s"$stdlibDir/$rel")
    val text = try src.mkString finally src.close()
    parseSource(text, rel)

  private def parseSource(text: String, name: String) =
    Parser.parse(text, name) match
      case Right(pf) => pf
      case Left(es) => fail(s"$name parse failed: ${es.head.message}")

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
    val files = Bootstrap.generate(parseStdlib("anthill/prelude/eq.anthill"))
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
    val files = Bootstrap.generate(pf)
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
    val files = Bootstrap.generate(pf)
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
    val files = Bootstrap.generate(pf)
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
    val sugar = Bootstrap.generate(parseSource(
      """namespace anthill.wi940
        |  entity Acct(id: Int64, balance: Float)
        |end
        |""".stripMargin, "sugar.anthill"))
    val longForm = Bootstrap.generate(parseSource(
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
    val files = Bootstrap.generate(parseSource(
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
    val files = Bootstrap.generate(parseSource(
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
    val err = intercept[BootstrapError](Bootstrap.generate(pf))
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
    val files = Bootstrap.generate(parseStdlib("anthill/prelude/monad.anthill"))
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
    val files = Bootstrap.generate(parseStdlib("anthill/prelude/cell.anthill"))
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
    // FAILS WHEN BACKED OUT: reorder `place` to consult `TypeGen.preludeSort` before
    // `enclosing`, and a bare `Pair` no longer has parameters to re-attach — it is
    // a 0-argument write against a 2-parameter entry, so `generate` throws.
    val files = Bootstrap.generate(parseStdlib("anthill/prelude/pair.anthill"))
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
    val files = Seq("pair", "option", "list")
      .flatMap(n => Bootstrap.generate(parseStdlib(s"anthill/prelude/$n.anthill")))
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
    // FAILS WHEN BACKED OUT, in one edit: drop the `_root_.anthill.prelude.` prefix
    // in `TypeGen.preludeSort` and this assertion finds no such error — MEASURED,
    // the bare emission reports `Not found: type Pair` instead (Scala 3 root-imports
    // no `Pair`, only `Tuple2`), so the file still fails to compile alone but for a
    // reason that says nothing about capture. `Option` is the one that silently
    // rebinds, and it is why the assertion names `Option` specifically.
    val list = Bootstrap.generate(parseStdlib("anthill/prelude/list.anthill"))
    val errs = ScalaCompile.errors(list)
    assert(errs.exists(_.message.contains("Option is not a member of anthill.prelude")),
      "compiling List.scala ALONE must fail on the missing sibling rather than " +
      s"silently binding scala.Option; got: ${errs.map(_.render)}")
    // THE CONTROL for the same emission: with the sibling present it is not a
    // missing name, it is the right one. Without this arm "does not compile alone"
    // could be satisfied by any breakage at all.
    ScalaCompile.assertCompiles("list + its siblings",
      list ++ Seq("option", "pair").flatMap(n =>
        Bootstrap.generate(parseStdlib(s"anthill/prelude/$n.anthill"))))
  }

  test("WI-1021: an effect-carrying collection places against the prelude's own arity") {
    // `Stream -> LazyList` was the entry whose wrongness showed as ARITY: anthill's
    // `Stream` has two parameters (`sort T` and `effects E`) and `LazyList` has one,
    // so every written occurrence was a refusal — `iterable.anthill` and
    // `combinators.anthill` were out of the emitted tree entirely. There is no
    // same-arity Scala counterpart to find, because the effect row is a parameter
    // Scala's collection does not have; the answer is that `Stream` was never a host
    // type. It now places against the two-parameter `trait Stream[T, E]` that
    // stream.anthill itself emits.
    //
    // A FIXTURE and not iterable.anthill: that file is still refused, for the
    // DIFFERENT reason recorded in the refusal set (a written effect ROW in a
    // type-argument slot, `Stream[Dst, {E, EffP}]`, which is the open question
    // WI-1062 owns). A fixture keeps this assertion about the entry.
    //
    // FAILS WHEN BACKED OUT, in one edit: set `preludeSorts`' `"Stream"` back to
    // the arity the `LazyList` entry claimed (1) and `generate` throws `takes 1
    // type argument(s), but 2 were written` — the same refusal, now against the
    // right type. Restoring the host NAME as well takes the shape change described
    // on the consumer-site test above.
    val files = Bootstrap.generate(parseSource(
      """namespace anthill.wi1021
        |  sort Reader
        |    sort T = ?
        |    sort E = ?
        |    operation source(r: Reader) -> Stream[T = T, E = E]
        |  end
        |end
        |""".stripMargin, "reader.anthill"))
    val src = files.head.contents
    assert(src.contains("def source(r: Reader[T, E]): _root_.anthill.prelude.Stream[T, E]"),
      s"a written Stream occurrence must reach the prelude's own two-parameter Stream:\n$src")
    ScalaCompile.assertCompiles("reader.anthill + stream.anthill",
      files ++ Seq("stream", "option", "pair", "list").flatMap(n =>
        Bootstrap.generate(parseStdlib(s"anthill/prelude/$n.anthill"))))
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
    val files = Bootstrap.generate(parseSource(
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
    // FAILS WHEN BACKED OUT: move `TypeGen.hostScalar` back below `enclosing` in
    // `place` and every assertion here fails, naming `Int64` where `Long` belongs.
    val files = Bootstrap.generate(parseStdlib("anthill/prelude/int64.anthill"))
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
    val files = Bootstrap.generate(parseStdlib("anthill/prelude/option.anthill"))
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
    val files = Bootstrap.generate(parseSource(
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
    val files = Bootstrap.generate(parseStdlib("anthill/prelude/list.anthill"))
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
    val files = Bootstrap.generate(parseSource(
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
      Bootstrap.generate(parseStdlib("anthill/prelude/effects.anthill")))
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
      Bootstrap.generate(parseStdlib("anthill/prelude/sort.anthill")))
    assert(err.getMessage.contains("`Type`"),
      s"refusal must name the type: ${err.getMessage}")
    assert(err.getMessage.contains("EffectExpression"),
      s"refusal must name the declaration: ${err.getMessage}")
    assert(err.getMessage.contains("sort.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1055 B1 CONTROL: an unplaced SAME-PACKAGE name is emitted QUALIFIED, not refused") {
    // The boundary of B1, and the reason it is not "refuse every name I cannot
    // resolve". `sort Lattice { requires Eq[T] }` names a sort a SIBLING FILE
    // declares in the same namespace — anthill's enclosing-namespace and
    // auto-prelude lookups both land there, and so does Scala's package scope.
    // Refusing these took thirteen prelude files out of the tree (measured) to
    // catch nothing the closure compile does not already catch.
    //
    // It is emitted QUALIFIED rather than bare, which is the part that is not a
    // hope: a bare mention also resolves against Scala's root imports, so an
    // ABSENT sibling does not fail, it CAPTURES. Measured — `field.anthill` emitted
    // a bare `Numeric`, compiled green, and meant `scala.math.Numeric`.
    //
    // FAILS WHEN BACKED OUT, in both directions: make `Ambient` a refusal and the
    // `generate` call throws; make it emit bare and the `contains` below fails
    // while the file still "compiles" — against the wrong type.
    val files = Bootstrap.generate(parseStdlib("anthill/prelude/field.anthill"))
    val src = files.find(_.relPath.endsWith("/Field.scala"))
      .getOrElse(fail(s"expected Field.scala in: ${files.map(_.relPath)}")).contents
    assert(src.contains("extends anthill.prelude.Numeric[T]"),
      s"a sibling-file name must be emitted qualified, so it cannot capture:\n$src")
    val errs = ScalaCompile.errors(files)
    assert(errs.exists(_.message.contains("Numeric is not a member of anthill.prelude")),
      "compiling Field.scala ALONE must now fail on the missing sibling rather than " +
      s"silently binding scala.math.Numeric; got: ${errs.map(_.render)}")
  }

  test("WI-1055 B2: a type VARIABLE in a type position is refused") {
    // `TypeGen` rendered `TypeExpr.Variable` as the literal `?`, which is not a
    // Scala type — so the emitted file did not even parse. What the variable
    // stands for is a typer question and scaland has no typer.
    //
    // logical_stream.anthill is the stdlib instance; `operation empty` is the
    // first declaration to reach one.
    //
    // FAILS WHEN BACKED OUT: restore `case TypeExpr.Variable(_, _) => "?"` and this
    // `intercept` finds no throw.
    val err = intercept[BootstrapError](
      Bootstrap.generate(parseStdlib("anthill/prelude/logical_stream.anthill")))
    assert(err.getMessage.contains("type VARIABLE"),
      s"refusal must say what defeated it: ${err.getMessage}")
    assert(err.getMessage.contains("`empty`"),
      s"refusal must name the declaration: ${err.getMessage}")
    assert(err.getMessage.contains("logical_stream.anthill:"),
      s"refusal must be located: ${err.getMessage}")
  }

  test("WI-1055 B2: a written EFFECT ROW in a type-argument slot is refused") {
    // scala_std ERASES effects (§2.8), so a written row in a type-ARGUMENT slot has
    // nothing to erase to — the slot still needs a type. `Any` was emitted, which
    // compiles and is a silent widening of whatever the row constrained.
    //
    // FAILS WHEN BACKED OUT: restore `case TypeExpr.EffectRow(_) => "Any"` and
    // delay.anthill emits again, with `Any` where the row was.
    val err = intercept[BootstrapError](
      Bootstrap.generate(parseStdlib("anthill/prelude/delay.anthill")))
    assert(err.getMessage.contains("effect row"),
      s"refusal must say what defeated it: ${err.getMessage}")
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
    // FAILS WHEN BACKED OUT: restore `case TypeExpr.Denoted(_) => "Any"`.
    val err = intercept[BootstrapError](Bootstrap.generate(parseSource(
      """namespace anthill.wi1055
        |  sort Buf
        |    entity Buf(cells: List[Int64, 3])
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
    // FAILS WHEN BACKED OUT: drop the `args.length != arity` guard in
    // `Placement.Known` and this emits `def swap(p: anthill.prelude.Pair): ...`,
    // which is `Missing type parameter`.
    val err = intercept[BootstrapError](Bootstrap.generate(parseSource(
      """namespace anthill.wi1021
        |  sort Flip
        |    operation swap(p: Pair) -> Pair
        |  end
        |end
        |""".stripMargin, "flip.anthill")))
    assert(err.getMessage.contains("`Pair` maps to Scala `_root_.anthill.prelude.Pair`"),
      s"refusal must name both sides of the mapping: ${err.getMessage}")
    assert(err.getMessage.contains("takes 2 type argument(s), but 0 were written"),
      s"refusal must state the arity conflict: ${err.getMessage}")
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
    val files = Bootstrap.generate(parseSource(
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
      Bootstrap.generate(parseStdlib("anthill/prelude/sortedset.anthill")))
    assert(sortLevel.getMessage.contains("`SortedSet`") &&
           sortLevel.getMessage.contains("`O`"),
      s"refusal must name the sort and the slot: ${sortLevel.getMessage}")
    assert(sortLevel.getMessage.contains("sortedset.anthill:"),
      s"refusal must be located: ${sortLevel.getMessage}")

    val opLevel = intercept[BootstrapError](Bootstrap.generate(parseSource(
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
    val err = intercept[BootstrapError](Bootstrap.generate(parseSource(
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
    // `anthill.prelude.Option` and honestly need the sibling. Measured on the
    // closure, which is the number that means something: unchanged at 11 errors.
    //
    // Compiling the whole closure is WI-1020's. It needs WI-1054 (`zero-val` is
    // not a Scala identifier) and the effect-row question (WI-1062): `Iterable`
    // and `Modifiable` are still refused, so their dependents cascade.
    // (DECLARATION, construct) and not the construct alone: eight of the thirteen
    // are now "effect row", so that half of the list stopped distinguishing them —
    // and WI-1021's measured finding is precisely that iterable.anthill's refusal
    // MOVED, from `operation iterator` (an arity conflict) to `operation map` (the
    // row). Pinning the declaration is what holds that; the message already carries
    // it, so a refusal that relocated within a file fails here rather than passing
    // as the same entry.
    val expectedRefusals = Map(
      "combinators.anthill" -> ("operation `map`", "effect row"),
      "delay.anthill" -> ("operation `pure`", "effect row"),
      "effects.anthill" -> ("sort `MatchFailed`", "imported from `anthill.reflect`"),
      "finite_collection.anthill" -> ("operation `map`", "effect row"),
      "finite_combinators.anthill" -> ("operation `iterator`", "effect row"),
      "iterable.anthill" -> ("operation `map`", "effect row"),
      "logical_stream.anthill" -> ("operation `empty`", "type VARIABLE"),
      "map.anthill" -> ("operation `iterator`", "effect row"),
      "meta.anthill" -> ("entity `Meta`", "imported from `anthill.reflect`"),
      "mutable_stack.anthill" -> ("operation `iterator`", "effect row"),
      "relation.anthill" -> ("operation `union`", "effect row"),
      "sort.anthill" -> ("sort `EffectExpression`", "emits no Scala type for"),
      "sortedset.anthill" -> ("sort `SortedSet`", "named requirement slot"),
    )
    val preludeDir = java.nio.file.Paths.get(s"$stdlibDir/anthill/prelude")
    val sources = java.nio.file.Files.list(preludeDir).toArray
      .map(_.asInstanceOf[java.nio.file.Path]).toVector
      .filter(_.toString.endsWith(".anthill")).sortBy(_.toString)
    assert(sources.length >= 44, s"expected the measured prelude, got ${sources.length} files")

    val refused = scala.collection.mutable.Map.empty[String, String]
    var compiled = 0
    sources.foreach { p =>
      val name = p.getFileName.toString
      val pf = parseStdlib(s"anthill/prelude/$name")
      try
        val files = Bootstrap.generate(pf)
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
  }
