package anthill.span

import anthill.kb.KnowledgeBase
import anthill.load.{LoadError, Loader, Prelude}
import anthill.parse.{ParseError, ParsedFile, Parser}

/** WI-947 — what a user actually sees: a scaland diagnostic names `file:line:col`.
  *
  * Every assertion here is on a SPECIFIC row and column, not on "a position was
  * produced". That is the point: before this WI every span in the tree was built
  * with row and col hard-coded to 0, so a test that only checked "an error came
  * back" passed just as well with no location at all — which is how the gap
  * survived.
  *
  * CONTROL, measured, not asserted from the armchair: make `Span.at` hand back a
  * zero START and 16 of the 21 tests in this package fail — the survivors being the
  * `LineIndex` units (which never build a span) and the locationless-`Span.empty`
  * case. Revert the `Index` capture in ONE production (`param`) and exactly 3 fail:
  * the two WI-727 ones and the rendering-parity one, which uses a WI-727 error as
  * its load-side sample. The pre-existing tests that assert message TEXT
  * (`ParseTest`'s WI-950 scoping tests, `ParserIntegrationTest`'s WI-727 refusals)
  * pass either way BY DESIGN — they never look at a position, which is exactly why
  * they could not have caught this.
  *
  * Declaration spans that no diagnostic cites are pinned in `DeclarationSpanTest`,
  * one case per shape — testing them only through diagnostics left most of the
  * family unpinned.
  */
class DiagnosticLocationTest extends munit.FunSuite:

  private def parseErrors(src: String, file: String = "demo.anthill"): IndexedSeq[ParseError] =
    Parser.parse(src, file) match
      case Right(_) => fail("expected the parse to report an error")
      case Left(errs) => errs

  private def loadErrors(src: String, file: String = "demo.anthill"): IndexedSeq[LoadError] =
    val pf: ParsedFile = Parser.parse(src, file) match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.render).mkString("; ")}")
    val kb = KnowledgeBase()
    Prelude.register(kb)
    Loader.loadAll(kb, IndexedSeq(pf)).toIndexedSeq

  private def at(span: Span): (Int, Int) = (span.startRow, span.startCol)

  // ── The parse family ─────────────────────────────────────────

  test("a syntax error is reported at its own line and column") {
    // Line 4 is `  fact p(` — an argument list that is never closed. What the user
    // used to get for this was `Parse error at 39: Position 4:9, found "("`: a raw
    // offset from us, and a position only because fastparse spelled one inside its
    // own message text. Now the position is ours, on the span, rendered by the one
    // renderer both families share.
    val src =
      """namespace demo
        |  sort S
        |  end
        |  fact p(
        |end""".stripMargin
    val errs = parseErrors(src)
    assertEquals(errs.length, 1, s"got: ${errs.map(_.render).mkString("; ")}")
    assertEquals(at(errs.head.span), (4, 9))
    assertEquals(src.split("\n")(3).charAt(8), '(')   // the column really is the `(`
    assertEquals(errs.head.render, s"demo.anthill:4:9: ${errs.head.message}")
    assert(errs.head.message.startsWith("parse error: "), errs.head.message)
  }

  test("a refusal about a well-formed declaration points at the offending token") {
    // WI-850: the type-param default. Line 3, and the column is the `T` — not the
    // `[`, not the whitespace before it.
    val src =
      """namespace demo
        |  sort S
        |    operation g[T = S](x: S) -> S
        |  end
        |end""".stripMargin
    val errs = parseErrors(src)
    val refusal = errs.find(_.message.contains("carries a default"))
      .getOrElse(fail(s"expected the WI-850 refusal, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(refusal.span), (3, 17))
    assertEquals(src.split("\n")(2).charAt(16), 'T')  // the column really is the `T`
    assert(refusal.render.startsWith("demo.anthill:3:17: "), refusal.render)
  }

  test("WI-952: an unterminated block comment is located at its OPENER") {
    // The opener is on line 2; the scan gives up at end of input on line 4. The
    // reported position must be the opener — that is what the author has to fix.
    val src =
      """namespace demo
        |  {- opened here
        |  sort S
        |  end""".stripMargin
    val errs = parseErrors(src)
    val unterminated = errs.find(_.message.contains("Unterminated block comment"))
      .getOrElse(fail(s"expected the WI-952 refusal, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(unterminated.span), (2, 3))
  }

  // ── The load family ──────────────────────────────────────────

  test("WI-727: a misplaced variadic capture is located at the capture") {
    // Line 4, column 19: the `...` of `...args`. The refusal is about the marker's
    // POSITION, so the marker is what it points at.
    val src =
      """namespace v
        |  sort Rel
        |    sort R = ?
        |    operation fix(...args: R, p: Rel) -> Rel
        |  end
        |end""".stripMargin
    val errs = loadErrors(src)
    val (refusal, span) = errs.collectFirst {
      case e @ LoadError.Other(m, s) if m.contains("LAST parameter") => (e, s)
    }.getOrElse(fail(s"expected the WI-727 refusal, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(span), (4, 19))
    assertEquals(src.split("\n")(3).substring(18, 21), "...")
    assert(refusal.render.startsWith("demo.anthill:4:19: "), refusal.render)
  }

  test("WI-727: with TWO captures the refusal points at the SECOND") {
    val src =
      """namespace v
        |  sort Rel
        |    sort R = ?
        |    operation fix(...a: R, ...b: R) -> Rel
        |  end
        |end""".stripMargin
    val errs = loadErrors(src)
    val span = errs.collectFirst { case LoadError.Other(m, s) if m.contains("at most one") => s }
      .getOrElse(fail(s"expected the WI-727 refusal, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(span), (4, 28))
    assertEquals(src.split("\n")(3).substring(27, 30), "...")
  }

  test("an unlabelled multi-head rule is located at the rule") {
    val src =
      """namespace demo
        |  rule p(?x), q(?x) :- r(?x)
        |end""".stripMargin
    val errs = loadErrors(src)
    val span = errs.collectFirst { case LoadError.Other(m, s) if m.contains("multi-head rule requires a label") => s }
      .getOrElse(fail(s"expected the multi-head refusal, got: ${errs.map(_.render).mkString("; ")}"))
    // Column 3 is the `rule` keyword: a declaration spans its own first token, and
    // `ruleDecl` re-stamps the entry it dispatched to so the keyword is included.
    // (A rule written inside a braced `rule { … }` block has no keyword of its own
    // and spans from its label-or-first-head — that difference is the two surface
    // forms differing, not the span rule differing.)
    assertEquals(at(span), (2, 3))
    assertEquals(src.split("\n")(1).substring(2, 6), "rule")
  }

  test("WI-949's missing-scope report is located at the declaration whose body was dropped") {
    // The one way to reach `lookupScope`'s miss: run `Loader.load` WITHOUT
    // `scanDefinitions`, so pass 1 never defined the scope. The span is the
    // declaration's NAME — the missing name has nothing to point at on the symbol-table
    // side, and what the reader needs is the declaration whose contents were dropped.
    val src =
      """namespace demo
        |  sort S
        |  end
        |end""".stripMargin
    val pf = Parser.parse(src, "demo.anthill") match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.render).mkString("; ")}")
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.load(kb, pf).toIndexedSeq
    val span = errs.collectFirst { case LoadError.Other(m, s) if m.contains("was not defined in pass 1") => s }
      .getOrElse(fail(s"expected the WI-949 missing-scope report, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(span), (1, 11))
    assertEquals(src.split("\n")(0).substring(10), "demo")
  }

  test("an unresolved name is located at the name") {
    val src =
      """namespace demo
        |  sort S
        |    requires nosuchspec
        |  end
        |end""".stripMargin
    val errs = loadErrors(src)
    val span = errs.collectFirst { case LoadError.UnresolvedName("nosuchspec", s, _) => s }
      .getOrElse(fail(s"expected an unresolved-name error, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(span), (3, 14))
    assertEquals(src.split("\n")(2).substring(13, 23), "nosuchspec")
  }

  // ── The shared rendering ─────────────────────────────────────

  test("both families render a location the same way") {
    // The property the two `render`s exist for: which STAGE found a fault does not
    // change how its location reads. Same file, same shape, one renderer.
    val parseAt = parseErrors(
      """namespace demo
        |  sort S
        |    operation g[T = S](x: S) -> S
        |  end
        |end""".stripMargin).find(_.message.contains("carries a default")).get
    val loadAt = loadErrors(
      """namespace v
        |  sort Rel
        |    sort R = ?
        |    operation fix(...a: R, p: Rel) -> Rel
        |  end
        |end""".stripMargin).collectFirst { case e @ LoadError.Other(m, _) if m.contains("LAST") => e }.get
    assert(parseAt.render.matches("""demo\.anthill:\d+:\d+: .*"""), parseAt.render)
    assert(loadAt.render.matches("""demo\.anthill:\d+:\d+: .*"""), loadAt.render)
  }

  test("a locationless span renders the bare message, not a position 0") {
    // `Span.empty` is the one span with no location, and it must not print as
    // `0:0` — a fake position is worse than none.
    assertEquals(Span.empty.render("something went wrong"), "something went wrong")
    assertEquals(Span.empty.hasLocation, false)
    assertEquals(LoadError.Other("something went wrong", Span.empty).render, "something went wrong")
  }

end DiagnosticLocationTest
