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
    assert(src.contains("case class EulerAngles(roll: Double, pitch: Double, yaw: Double)"),
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
    assert(src.contains("case class Vec3(x: Double, y: Double, z: Double)"),
      s"expected the one `case class Vec3(…)` declaration in:\n$src")
    // The four members stay reachable — as the abstract contract, since
    // bootstrap emits signatures only and a `case class` has no abstract member.
    assert(src.contains("trait Vec3Ops:"), s"expected `trait Vec3Ops` in:\n$src")
    assert(src.contains("def vecAdd(a: Vec3, b: Vec3): Vec3"),
      s"expected `def vecAdd(a: Vec3, b: Vec3): Vec3` in:\n$src")
    assert(src.contains("def vecScale(c: Double, v: Vec3): Vec3"),
      s"expected `def vecScale(c: Double, v: Vec3): Vec3` in:\n$src")
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
    assert(src.contains("case class TotalFloat(raw: Double)"),
      s"expected `case class TotalFloat(raw: Double)` in:\n$src")
    assert(src.contains("def eq(a: TotalFloat, b: TotalFloat): Boolean"),
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
    assert(sugar.head.contents.contains("case class Acct(id: Int, balance: Double)"),
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
    assert(src.contains("case Circle(r: Double)"), s"expected `case Circle(r: Double)` in:\n$src")
    assert(src.contains("case Square(side: Double)"), s"expected `case Square(side: Double)` in:\n$src")
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
