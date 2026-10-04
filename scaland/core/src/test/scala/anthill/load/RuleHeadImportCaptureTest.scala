package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}

/** WI-20260821-JR7BB — a file-local import cannot be silently captured by a local
  * rule-head declaration minted from a sibling file at the same address.
  *
  * BACK-OUT MEASUREMENT: remove `reportRuleHeadImportCaptures`. The first test fails
  * because the program loads and silently captures the imported head; both controls
  * pass either way by design. */
class RuleHeadImportCaptureTest extends munit.FunSuite:

  private val lib = """namespace jr7.lib
                      |  fact seed(1)
                      |  rule p(?x) :- seed(?x)
                      |end""".stripMargin

  private def importer(importForm: String) =
    s"""namespace jr7.demo
       |  import jr7.lib.$importForm
       |  fact imported_seed(2)
       |  rule p(?x) :- imported_seed(?x)
       |end""".stripMargin

  private val sibling = """namespace jr7.demo
                           |  fact local_seed(3)
                           |  rule p(?x) :- local_seed(?x)
                           |end""".stripMargin

  private def tryLoad(files: (String, String)*): Either[IndexedSeq[String], KnowledgeBase] =
    val parsed = files.map((source, label) => LoadFixture.parsed(source, label)).toIndexedSeq
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errors = Loader.loadAll(kb, parsed)
    if errors.isEmpty then Right(kb) else Left(errors.map(_.render).toIndexedSeq)

  test("a deferred selective import and a sibling local head are refused as a capture") {
    tryLoad(
      lib -> "lib.anthill",
      importer("{p}") -> "importer.anthill",
      sibling -> "local.anthill") match
      case Right(_) => fail("the sibling local must not silently capture the imported head")
      case Left(errors) =>
        val capture = errors.find(e => e.contains("would capture") && e.contains("`p`"))
          .getOrElse(fail(s"expected the capture diagnostic, got:\n${errors.mkString("\n")}"))
        assert(capture.contains("importer.anthill"), capture)
        assert(capture.contains("local.anthill"), capture)
        assert(capture.contains("jr7.demo"), capture)
  }

  test("a selectively imported head with no competing local mint still contributes") {
    val kb = tryLoad(lib -> "lib.anthill", importer("{p}") -> "importer.anthill") match
      case Right(kb) => kb
      case Left(errors) => fail(s"the one-file contribution must load:\n${errors.mkString("\n")}")
    val imported = kb.tryResolveSymbol("jr7.lib.p").getOrElse(fail("jr7.lib.p must exist"))
    assertEquals(kb.byFunctor(imported).length, 2)
    assertEquals(kb.tryResolveSymbol("jr7.demo.p"), None)
  }

  test("Bool.{ite} remains a valid selective import without a competing head") {
    val boolFixture = """namespace anthill.prelude.Bool
                        |  fact jr7_seed(1)
                        |  rule ite(?x) :- jr7_seed(?x)
                        |end""".stripMargin
    val source = """namespace jr7.ite_control
                   |  import anthill.prelude.Bool.{ite}
                   |end""".stripMargin
    val kb = tryLoad(
      boolFixture -> "bool-fixture.anthill",
      source -> "ite-control.anthill") match
      case Right(kb) => kb
      case Left(errors) => fail(s"the Bool.{ite} control must load:\n${errors.mkString("\n")}")
    val scope = kb.symbols.scopeOf(kb.resolveSymbol("jr7.ite_control"))
    assert(kb.symbols.resolveInScope("ite", scope).denotes)
  }
