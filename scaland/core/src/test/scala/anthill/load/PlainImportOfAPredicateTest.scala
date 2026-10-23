package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, Literal, Var}
import anthill.resolve.SearchStream

/** WI-20261022-JBHQC (rustland's `wi_jbhqc_plain_import_of_a_predicate_test`, whose doc
  * has the whole account) — an import of a predicate a rule head of the same load
  * introduces is WIRED before the heads are decided, and reads as an import of an
  * existing name. The plain form `import a.b.p` was refused in pass 2, so two namespaces
  * of one load could not import each other's predicates that way while the `{p}`
  * spelling loaded; and a deferred import was retried in pass 4, after the mint, with
  * the mint guard alone told of it, for the head's own scope alone — so a clause in a
  * sort nested in the importing namespace minted a predicate of its own. Now pass 3's
  * head census wires each deferred import to the symbol reserved for its target, and the
  * ladder answers every head: the import's DEFINER is not taken by it, an import no head
  * mints is refused before any head reads it, and a local minted in a scope that ENCLOSES
  * a head denoting through an import captures it as one at its own address does.
  *
  * A fourth round (rustland's `/code-review`): a capture is told by the frozen answer
  * against the answer after the mint, not by an overlay walk that refused programs that
  * load; reservations are withdrawn only once nothing they read is withdrawn too; a
  * deferred import keeps its place among the writes of its name; and a name one scope
  * below is wired by which heads introduce it, after phase 2.
  *
  * WHICH TESTS FAIL WHEN THE FIX IS BACKED OUT, each part on its own, measured — the
  * table is in the MEASURED comment at the end of this file.
  */
class PlainImportOfAPredicateTest extends munit.FunSuite:

  private val lib = """namespace jq.lib
                      |  fact s(1)
                      |  rule r(?x) :- s(?x)
                      |end""".stripMargin

  /** `lib` with `r` DECLARED (proposal 061), so an import of it resolves in pass 2. */
  private val declaredLib = """namespace jq.lib
                              |  fact s(1)
                              |  rule r(?x)
                              |  rule r(?x) :- s(?x)
                              |end""".stripMargin

  private def app(imp: String) = s"""namespace jq.app
                                    |  import $imp
                                    |  rule q(?x) :- r(?x)
                                    |end""".stripMargin

  private def loaded(files: (String, String)*)(using munit.Location): KnowledgeBase =
    LoadFixture.loaded(files.map(LoadFixture.parsed).toIndexedSeq)

  private def loadErrors(files: (String, String)*)(using munit.Location): Seq[LoadError] =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    LoadFixture.registerKernel(kb)
    Loader.loadAll(kb, files.map(LoadFixture.parsed).toIndexedSeq).toSeq

  /** All Int solutions of `qualifiedRule(?x)`, sorted. */
  private def values(kb: KnowledgeBase, qualifiedRule: String)(using munit.Location): List[Long] =
    val sym = kb.tryResolveSymbol(qualifiedRule)
      .getOrElse(fail(s"`$qualifiedRule` must be registered — fixture drift"))
    val vid = kb.freshVar(kb.intern("x"))
    val query = kb.alloc(Term.Fn(sym, IArray(kb.alloc(Term.Var(Var.Global(vid)))), IArray.empty))
    SearchStream.resolve(kb, query).allSolutions(kb).map { sol =>
      sol.subst.resolve(vid).map(kb.getTerm) match
        case Some(Term.Const(Literal.IntLit(v))) => v
        case other => fail(s"expected an Int binding for $qualifiedRule, got $other")
    }.toList.sorted

  private def assertUnresolvedImport(errs: Seq[LoadError], path: String)(using munit.Location): Unit =
    errs match
      case Seq(LoadError.UnresolvedImport(got, _)) => assertEquals(got, path)
      case other => fail(s"expected exactly `UnresolvedImport` at $path, got $other")

  private def isCapture(e: LoadError): Boolean = e.toString.contains("would capture the same head")

  // ── the plain form, in one load ─────────────────────────────────────────

  test("JBHQC: a plain import of a predicate of the same load resolves") {
    val kb = loaded(s"$lib\n${app("jq.lib.r")}" -> "main.anthill")
    assertEquals(values(kb, "jq.app.q"), List(1L))
  }

  test("JBHQC: across two files of one load") {
    val kb = loaded(lib -> "lib.anthill", app("jq.lib.r") -> "app.anthill")
    assertEquals(values(kb, "jq.app.q"), List(1L))
  }

  test("JBHQC: a clause at the imported name joins the imported predicate") {
    val joining = """namespace jq.app
                    |  import jq.lib.r
                    |  fact r(3)
                    |end""".stripMargin
    val kb = loaded(s"$lib\n$joining" -> "main.anthill")
    assertEquals(values(kb, "jq.lib.r"), List(1L, 3L))
    assertEquals(kb.symbols.byQualifiedName.get("jq.app.r"), None)
  }

  test("JBHQC: a one-segment plain import of a top-level predicate resolves") {
    val top = "rule p(1) :- true"
    val importer = """namespace jq.app
                     |  import p
                     |  rule q(?x) :- p(?x)
                     |end""".stripMargin
    val kb = loaded(top -> "top.anthill", importer -> "app.anthill")
    assertEquals(values(kb, "jq.app.q"), List(1L))
  }

  test("JBHQC control: the selective form of the same program loads") {
    val kb = loaded(s"$lib\n${app("jq.lib.{r}")}" -> "main.anthill")
    assertEquals(values(kb, "jq.app.q"), List(1L))
  }

  test("JBHQC: a selective import reaches a name one scope below") {
    val src = """namespace nsq
                |  sort Rec
                |    entity rec
                |    rule p(1) :- true
                |  end
                |end
                |namespace otherq
                |  import nsq.{p}
                |  rule q(?x) :- p(?x)
                |end""".stripMargin
    assertEquals(values(loaded(src -> "main.anthill"), "otherq.q"), List(1L))
  }

  // ── an import that names nothing ────────────────────────────────────────

  test("JBHQC control: a leaf that names nothing is still unresolved") {
    assertUnresolvedImport(
      loadErrors(s"$lib\nnamespace jq.app\n  import jq.lib.nope\nend" -> "main.anthill"),
      "jq.lib.nope")
  }

  test("JBHQC control: a base that names nothing is still unresolved") {
    assertUnresolvedImport(
      loadErrors("namespace jq.app\n  import jq.nowhere.r\n  fact r(1)\nend" -> "main.anthill"),
      "jq.nowhere.r")
  }

  test("JBHQC control: an import naming nothing beside a head of its name is one error") {
    assertUnresolvedImport(
      loadErrors(s"$lib\nnamespace jq.app\n  import jq.lib.nope\n  fact nope(1)\nend" -> "main.anthill"),
      "jq.lib.nope")
  }

  /** An import naming nothing, beside a head of its name in another file at the same
    * scope: the two heads introducing `rr` in two files is 061's own refusal; what must
    * NOT be here is the sibling's head refused as capturing the import. */
  private def namingNothingBesideASiblingFile(imp: String)(using munit.Location): Unit =
    val errs = loadErrors(
      lib -> "lib.anthill",
      s"namespace jq.app\n  import $imp\n  fact rr(1)\nend" -> "a.anthill",
      "namespace jq.app\n  fact rr(2)\nend" -> "b.anthill")
    assert(!errs.exists(isCapture), s"no head captured by an import that names nothing: $errs")
    assert(errs.exists { case LoadError.UnresolvedImport(p, _) => p == imp; case _ => false }, s"$errs")

  test("JBHQC control: a leaf that names nothing takes no sibling file's head") {
    namingNothingBesideASiblingFile("jq.lib.rr")
  }

  test("JBHQC control: a base that names nothing takes no sibling file's head") {
    namingNothingBesideASiblingFile("jq.nowhere.rr")
  }

  /** `Lib`'s `r` reads `other.r` through the nearer `import other.r`, so it mints no
    * `app.Lib.r`, and the import of it in `user` names nothing — one error, the import's. */
  test("JBHQC: a reservation no head mints is withdrawn") {
    val src = """namespace other
                |  fact r(9)
                |end
                |namespace app
                |  import other.r
                |  sort Lib
                |    entity l
                |    fact s(1)
                |    rule r(?x) :- s(?x)
                |  end
                |end
                |namespace user
                |  import app.Lib.r
                |end""".stripMargin
    assertUnresolvedImport(loadErrors(src -> "main.anthill"), "app.Lib.r")
  }

  // ── a head under a deferred import reads as under a wired one ───────────

  /** `fact r(5)` in `sort S` of the importing namespace lands on `jq.lib.r`, and `S`
    * declares no `r`. */
  private def nestedClauseJoins(library: String, imp: String)(using munit.Location): Unit =
    val app = s"""namespace jq.app
                 |  import $imp
                 |  sort S
                 |    entity s0
                 |    fact r(5)
                 |  end
                 |end""".stripMargin
    val kb = loaded(s"$library\n$app" -> "main.anthill")
    assertEquals(values(kb, "jq.lib.r"), List(1L, 5L))
    assertEquals(kb.symbols.byQualifiedName.get("jq.app.S.r"), None)

  test("JBHQC: a clause in a sort nested in the importing namespace joins — plain") {
    nestedClauseJoins(lib, "jq.lib.r")
  }

  test("JBHQC: a clause in a sort nested in the importing namespace joins — selective") {
    nestedClauseJoins(lib, "jq.lib.{r}")
  }

  test("JBHQC control: a clause in a sort nested in the importing namespace joins — declared") {
    nestedClauseJoins(declaredLib, "jq.lib.r")
  }

  // ── the definer of what an import waits for ─────────────────────────────

  /** The import's DEFINER under the importing scope is not taken by it: `Lib`'s rule mints
    * `app.Lib.r`, which is what the import waits for. */
  private def definerUnderTheImport(imp: String)(using munit.Location): Unit =
    val src = s"""namespace app
                 |  import $imp
                 |  sort Lib
                 |    entity l
                 |    fact s(1)
                 |    rule r(?x) :- s(?x)
                 |  end
                 |  rule q(?x) :- r(?x)
                 |end""".stripMargin
    assertEquals(values(loaded(src -> "main.anthill"), "app.q"), List(1L))

  test("JBHQC: the definer under an enclosing import is not taken by it — plain") {
    definerUnderTheImport("app.Lib.r")
  }

  test("JBHQC: the definer under an enclosing import is not taken by it — selective") {
    definerUnderTheImport("app.Lib.{r}")
  }

  test("JBHQC: the definer under a file-level import is not taken by it") {
    val src = s"""import jq.lib.r
                 |$lib
                 |${app("jq.lib.r").replace("  import jq.lib.r\n", "")}""".stripMargin
    assertEquals(values(loaded(src -> "main.anthill"), "jq.app.q"), List(1L))
  }

  /** Two deferred imports of one short name reach the definer; the nearer is the one of
    * the predicate it defines, so it defines it — `q` reads `Lib`'s row, not `a`'s. */
  test("JBHQC: the definer under two imports of its name defines it") {
    val src = """namespace a
                |  fact s(1)
                |  rule r(?x) :- s(?x)
                |end
                |import a.{r}
                |namespace app
                |  import app.Lib.{r}
                |  sort Lib
                |    entity l
                |    fact t(2)
                |    rule r(?x) :- t(?x)
                |  end
                |  rule q(?x) :- r(?x)
                |end""".stripMargin
    assertEquals(values(loaded(src -> "main.anthill"), "app.q"), List(2L))
  }

  // ── a local that captures a head denoting through an import ─────────────

  /** `fact r(5)` in `jq.app.S` denotes `jq.lib.r` through `jq.app`'s import; another file
    * writes `fact r(7)` at `jq.app`, whose local the first head's ladder meets first.
    * Refused, not loaded clean with the first fact moved under `jq.app.r`. */
  private def enclosingLocalCaptures(library: String)(using munit.Location): Unit =
    val importer = s"""$library
                      |namespace jq.app
                      |  import jq.lib.r
                      |  sort S
                      |    entity s0
                      |    fact r(5)
                      |  end
                      |end""".stripMargin
    val errs = loadErrors(importer -> "a.anthill", "namespace jq.app\n  fact r(7)\nend" -> "b.anthill")
    errs match
      case Seq(e) if isCapture(e) => assert(e.toString.contains("'jq.app'"), s"$e")
      case other => fail(s"expected the capture refusal alone, got $other")

  test("JBHQC: a local in an enclosing scope captures a head denoting through an import") {
    enclosingLocalCaptures(lib)
  }

  test("JBHQC control: a local in an enclosing scope captures a head denoting through an import — declared") {
    enclosingLocalCaptures(declaredLib)
  }

  // ── the fourth round ─────────────────────────────────────────────────────

  test("JBHQC control: a head denoting its own scope's declaration is not captured") {
    val src = """namespace e
                |  rule p(1) :- true
                |  namespace s
                |    rule p(?x)
                |    rule p(2) :- true
                |  end
                |end""".stripMargin
    val kb = loaded(src -> "main.anthill")
    assertEquals(values(kb, "e.s.p"), List(2L))
    assertEquals(values(kb, "e.p"), List(1L))
  }

  test("JBHQC control: a head denoting the reservation its enclosing scope mints is not captured") {
    val src = """namespace app
                |  import app.Lib.r
                |  namespace Lib
                |    fact s(1)
                |    rule r(?x) :- s(?x)
                |    namespace Inner
                |      fact r(5)
                |    end
                |  end
                |end""".stripMargin
    assertEquals(values(loaded(src -> "main.anthill"), "app.Lib.r"), List(1L, 5L))
  }

  test("JBHQC: a reservation whose definer reads a withdrawn one is kept") {
    val src = """namespace z
                |  fact p(0)
                |end
                |namespace y
                |  import z.p
                |  fact p(9)
                |end
                |namespace x
                |  import y.p
                |  sort Rec
                |    entity e
                |    fact p(1)
                |  end
                |end
                |namespace user
                |  import x.Rec.p
                |end""".stripMargin
    assertUnresolvedImport(loadErrors(src -> "main.anthill"), "y.p")
  }

  test("JBHQC: a deferred import keeps its place among the writes of its name") {
    def src(imports: String) = s"""namespace lib
                                  |  fact s(1)
                                  |  rule r(?x) :- s(?x)
                                  |end
                                  |namespace other
                                  |  rule r(?x)
                                  |  fact r(2)
                                  |end
                                  |namespace app
                                  |$imports
                                  |  rule q(?x) :- r(?x)
                                  |end""".stripMargin
    assertEquals(values(loaded(src("  import lib.r\n  import other.r") -> "main.anthill"), "app.q"), List(2L))
    assertEquals(values(loaded(src("  import other.r\n  import lib.r") -> "main.anthill"), "app.q"), List(1L))
  }

  test("JBHQC: a selective import reaches the one name one scope below that a head introduces") {
    val src = """namespace other
                |  fact p(7)
                |end
                |namespace base
                |  sort A
                |    entity a
                |    import other.p
                |    fact p(1)
                |  end
                |  sort B
                |    entity b
                |    fact p(2)
                |  end
                |end
                |namespace user
                |  import base.{p}
                |  rule q(?x) :- p(?x)
                |end""".stripMargin
    assertEquals(values(loaded(src -> "main.anthill"), "user.q"), List(2L))
  }

  // ── the fifth round: a deferred import keeps the place the text gave it ─

  test("JBHQC: a late import keeps its place before a later direct one") {
    def src(imports: String) = s"""namespace other
                                  |  fact p(7)
                                  |end
                                  |namespace base
                                  |  sort B
                                  |    entity b
                                  |    fact p(2)
                                  |  end
                                  |end
                                  |namespace user
                                  |$imports
                                  |  rule q(?x) :- p(?x)
                                  |end""".stripMargin
    assertEquals(values(loaded(src("  import base.{p}\n  import other.p") -> "main.anthill"), "user.q"), List(7L))
    assertEquals(values(loaded(src("  import other.p\n  import base.{p}") -> "main.anthill"), "user.q"), List(2L))
  }

  test("JBHQC: deferred and resolved imports of one name keep the text's order") {
    val src = """namespace lib
                |  fact p(1)
                |end
                |namespace lib2
                |  fact p(3)
                |end
                |namespace other
                |  rule p(?x)
                |  fact p(2)
                |end
                |namespace last
                |  rule p(?x)
                |  fact p(4)
                |end
                |namespace user
                |  import lib.p
                |  import lib.p
                |  import other.p
                |  import lib2.p
                |  import last.p
                |  rule q(?x) :- p(?x)
                |end""".stripMargin
    assertEquals(values(loaded(src -> "main.anthill"), "user.q"), List(4L))
  }

  test("JBHQC: a selective import whose target is withdrawn lands one scope below") {
    val first = """namespace other
                  |  fact p(0)
                  |end
                  |namespace base
                  |  import other.p
                  |  fact p(1)
                  |end""".stripMargin
    val second = """namespace base
                   |  sort B
                   |    entity b
                   |    fact p(2)
                   |  end
                   |end
                   |namespace user
                   |  import base.{p}
                   |  rule q(?x) :- p(?x)
                   |end""".stripMargin
    val kb = loaded(first -> "first.anthill", second -> "second.anthill")
    assertEquals(values(kb, "user.q"), List(2L))
    assertEquals(values(kb, "other.p"), List(0L, 1L))
  }

  // MEASURED — which rows fail when each part is backed out on its own:
  //   the `case None if imp.kind == ImportKind.Plain` arm removed (the plain form refused in pass 2):
  //     every row with a plain import of a predicate of the load — same-load, two-file, join,
  //     one-segment, withdrawn-reservation, nested-plain, definer-plain, file-level-definer,
  //     capture (not its declared control), reservation-control, chain, write-order,
  //     one-introduces, late-before-direct, interleaved and withdrawn-lands-below.
  //   the wiring done after the mint instead: join, withdrawn-reservation, the two nested,
  //     capture, reservation-control, chain, write-order, one-introduces, late-before-direct,
  //     interleaved, withdrawn-lands-below, and ImportFileLocalityTest's two-writer row.
  //   `isOwnReservation` answering false: the four definer rows and the reservation-control row.
  //   `settleWiring` doing nothing: withdrawn-reservation (on the unminted report's invariant
  //     error), chain, withdrawn-lands-below.
  //   `settleWiring` withdrawing every idle reservation at once: the chain row.
  //   `reportPostMintCaptures` dropped: the two capture rows.
  //   no selective import left for `wireLate` (the one-scope-below rung): both one-scope-below
  //     rows and late-before-direct.
  //   `oneScopeBelow` counting every head one scope below: the one-introduces row.
  //   `wireImport` appending instead of taking the import's place: write-order,
  //     late-before-direct, interleaved.
  //   `takeBack` refusing a selective import instead of re-pointing it: withdrawn-lands-below.
  // Pass either way BY DESIGN: the two `not captured` controls against the capture check (the
  // programs an overlay walk refused — the reservation one needs the plain form and the definer
  // exclusion, as its failures above say), the other `declared` rows, the selective row and the
  // `names nothing` controls.
