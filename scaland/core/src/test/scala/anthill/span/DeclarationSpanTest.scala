package anthill.span

import anthill.parse.{Item, ParsedFile}
import SpanFixture.{assertSpans, pick}

/** WI-947 — one span assertion per DECLARATION SHAPE, at the IR.
  *
  * WHY THIS FILE EXISTS SEPARATELY from `DiagnosticLocationTest`: a declaration's
  * span reaches a user only through whichever diagnostic happens to cite it, and
  * most of these have no diagnostic today. Tested only through diagnostics, ~14 of
  * the productions WI-947 touched were pinned by NOTHING — reverting the `Index`
  * capture in `entityDecl`, `factDecl`, `constDecl`, `namespaceDecl`, `enumDecl`,
  * `effectsSortItem`, `constraintDecl`, `providesDecl`, `proofDeclInner`,
  * `requiresDeclItem`, `sortTypeParam` or `sortBinderMember` left the whole suite
  * green. That is the "it loads clean" failure CLAUDE.md names: the capability was
  * not driven, so a silent regression in it would not have been caught.
  *
  * THE RULE BEING PINNED: a declaration's span begins at its OWN first token — the
  * `visibility` when written, otherwise the keyword — for every shape, with no
  * exceptions. Two shapes have to work for that (`sort` and `operation` have their
  * keyword eaten by a dispatching production, which hands the span back down); the
  * point of testing all of them together is that the exceptions cannot creep back.
  *
  * WI-971 CLOSED THE LIST — `sortTypeParam` and `sortBinderMember` each have a case
  * now, because the WI moved where their span comes from, and `proofDeclInner` got the
  * `proof` line the fixture never had. The first two are not reachable by the
  * line-anchored helpers below (a type param is not written on its own line, and a
  * binder member is not a `sort` declaration), which is why they stayed unpinned while
  * the ten around them were being covered.
  *
  * CONTROL: every assertion is a specific (row, col) checked against the source text
  * at that column, or the exact source slice, so none can pass with a zeroed or stale
  * span. Revert any single production's span capture and exactly its case here fails —
  * except where the whole family now shares one bracket, and breaking `located`'s `~~`
  * fails three of these at once (measured; the other twelve are in `SpanEndTest` and
  * `ParseSpanCoverageTest`).
  */
class DeclarationSpanTest extends munit.FunSuite:

  private def parse(src: String): ParsedFile = SpanFixture.parse(src, "decls.anthill")

  private def allItems(items: Iterable[Item]): Vector[Item] = SpanFixture.allItems(items)

  // WI-971: `spanOf` moved to `SpanFixture` when the corpus audit in
  // `ParseSpanCoverageTest` became its second reader.
  private def spanOf(item: Item): Span = SpanFixture.spanOf(item)

  /** Assert that SOME item of the file starts exactly at the first non-space
    * character of `line` (1-based), and that the line begins with `expectedToken`.
    * Anchoring on "the line's first token" is what makes the assertion legible: the
    * fixture writes one declaration per line, indented, so the expected column is
    * derived from the source rather than hand-counted (a hand-counted column is a
    * second place to make the same mistake).
    */
  private def assertDeclStartsAtLine(
    pf: ParsedFile, src: String, line: Int, expectedToken: String
  ): Unit =
    val text = src.split("\n")(line - 1)
    val col = text.indexWhere(!_.isWhitespace) + 1
    assert(text.trim.startsWith(expectedToken),
      s"fixture drift: line $line is '${text.trim}', expected it to start with '$expectedToken'")
    val spans = allItems(pf.items).map(spanOf)
    assert(spans.exists(s => s.startRow == line && s.startCol == col),
      s"no declaration spans line $line col $col ('$expectedToken'); got " +
      spans.filter(_.startRow == line).map(s => s"${s.startRow}:${s.startCol}").mkString(", "))

  /** WI-970: the same anchoring, for the OTHER end. A declaration written on ONE line
    * must span exactly that line's text — so `end` is asserted against the fixture the
    * start assertions already use, rather than in a file a new production's author
    * would not think to open.
    *
    * Requires exactly one declaration to start at the anchor, and says so if not: two
    * items sharing a start offset would make "the one that spans the line" a choice
    * this helper is not entitled to make silently. */
  private def assertDeclSpansLine(
    pf: ParsedFile, src: String, line: Int, expectedToken: String
  ): Unit =
    val text = src.split("\n")(line - 1)
    val col = text.indexWhere(!_.isWhitespace) + 1
    assert(text.trim.startsWith(expectedToken),
      s"fixture drift: line $line is '${text.trim}', expected it to start with '$expectedToken'")
    val here = allItems(pf.items).map(spanOf).filter(s => s.startRow == line && s.startCol == col)
    assertEquals(here.length, 1,
      s"line $line ('$expectedToken') is anchored by ${here.length} declarations, expected 1")
    assertEquals(src.slice(here.head.start, here.head.end), text.trim)

  // ── The fixture ──────────────────────────────────────────────
  //
  // One declaration per line, so a line number IS a shape. Line numbers are read
  // off this literal, and `assertDeclStartsAtLine` re-derives the column from the
  // text — so adding a line above an existing case fails loudly on the token check
  // rather than silently testing the wrong construct. Which is also why WI-971's lines
  // were APPENDED (23, 24, the `proof` at 25–26) or widened in place (21), rather than
  // grouped with the shapes they belong beside.
  //
  // Two constructs DO share a line, and neither is reached by line: the `F[T]` type
  // param inside line 21 and the `sort ?U` member inside line 24. They are addressed by
  // name in their own cases below, because a type param and a binder member are not
  // declarations a reader writes on a line of their own — which is exactly why they had
  // no case at all until WI-971. The spacing inside `F[T]   ]` is load-bearing: it is
  // the only trailing trivia the type param has, and without it the assertion cannot
  // tell a tight bracket from a whitespace-skipping one.
  //
  //                                                                      line
  private val src =
    """namespace demo
      |  sort Marker
      |  end
      |  entity Point(x: Marker, y: Marker)
      |  fact Point(x: Marker)
      |  const limit: Marker
      |  constraint c1: Point(x: ?a)
      |  rule single(?x) :- Point(x: ?x)
      |  rule { blocked(?x) :- Point(x: ?x) }
      |  internal operation solo(a: Marker) -> Marker
      |  operation { pub2(a: Marker) -> Marker }
      |  enum Color
      |  end
      |  public sort Named
      |    requires Marker
      |    effects E = ?
      |    provides Marker
      |  end
      |  sort ?Binder
      |  sort [Bracketed]
      |  sort Parameterized[A, F[T]   ]
      |  end
      |  sort Alias = Marker
      |  sort ?Structured { sort ?U }
      |  proof Point by auto
      |  end
      |end""".stripMargin

  private lazy val pf = parse(src)

  test("namespace, sort and enum span from their own first token") {
    assertDeclStartsAtLine(pf, src, 1, "namespace")
    assertDeclStartsAtLine(pf, src, 2, "sort")
    assertDeclStartsAtLine(pf, src, 12, "enum")
    // `public sort Named` — the VISIBILITY is the declaration's first token, so the
    // span starts there and not at `sort`.
    assertDeclStartsAtLine(pf, src, 14, "public")
  }

  test("entity, fact, const and constraint span from their keyword") {
    assertDeclStartsAtLine(pf, src, 4, "entity")
    assertDeclStartsAtLine(pf, src, 5, "fact")
    assertDeclStartsAtLine(pf, src, 6, "const")
    assertDeclStartsAtLine(pf, src, 7, "constraint")
  }

  test("a rule spans its `rule` keyword, in both the single and braced spellings") {
    assertDeclStartsAtLine(pf, src, 8, "rule")
    assertDeclStartsAtLine(pf, src, 9, "rule")
  }

  test("an operation spans its own first token, in both spellings") {
    // Line 10 is `internal operation solo(…)`: the visibility, NOT the name — this is
    // the case that regressed on the first cut, where the single spelling started at
    // `solo` while a braced entry started at its visibility.
    assertDeclStartsAtLine(pf, src, 10, "internal")
    assertDeclStartsAtLine(pf, src, 11, "operation")
  }

  test("sort-body clauses span from their keyword") {
    assertDeclStartsAtLine(pf, src, 15, "requires")
    assertDeclStartsAtLine(pf, src, 16, "effects")
    assertDeclStartsAtLine(pf, src, 17, "provides")
  }

  test("the WI-454 type-param binder shapes span from the `sort` keyword") {
    assertDeclStartsAtLine(pf, src, 19, "sort")
    assertDeclStartsAtLine(pf, src, 20, "sort")
  }

  test("WI-971: a `proof` spans from its keyword") {
    // `proofDeclInner` was the last name on the header's list still pinned by nothing —
    // the fixture had no `proof` at all. Its end is on the `end` line, so only the start
    // is reachable here, which is the same coverage every other multi-line shape gets.
    assertDeclStartsAtLine(pf, src, 25, "proof")
  }

  test("WI-970: a one-line declaration ends at its own last character") {
    // The END half of the same rule, for every shape in this fixture that fits on one
    // line. The multi-line shapes (`namespace`, `sort`/`enum` with a body) are absent
    // because their end is on their `end` line, which this fixture's one-per-line
    // anchoring cannot address — they are covered for START only, as before.
    //
    // WHY HERE and not in `SpanEndTest`: `AnthillParser`'s declaration-family note
    // points a new production's author at THIS file. Pinning ends anywhere else means
    // the next declaration production gets a start case and never an end one — which
    // is how the six WI-970 repaired went unnoticed.
    for (line, token) <- Seq(
      4 -> "entity", 5 -> "fact", 6 -> "const", 7 -> "constraint",
      8 -> "rule", 9 -> "rule", 10 -> "internal", 11 -> "operation",
      15 -> "requires", 16 -> "effects", 17 -> "provides",
      // WI-971 added lines 23 and 24 and the three `sort` shapes now share ONE bracket,
      // in the `sortDecl` dispatcher, where each branch used to close its own. 19/20 are
      // the binder forms; 23 is the abstract `sort X = T`, whose end no case reached
      // before (every other named sort in this fixture opens a body, so its end is on a
      // later line); 24 is the with-body binder, whose own span is separate from the
      // member span asserted further down.
      19 -> "sort", 20 -> "sort", 23 -> "sort", 24 -> "sort",
    ) do assertDeclSpansLine(pf, src, line, token)
  }

  test("a desugared type-param's NAME spans its identifier, not the declaration") {
    // WI-947: `desugarSortTypeParam` mints ordinary sort items, and their `Name` is
    // what `Loader.lookupScope` reports through. A `Name` must span its identifier
    // token like every other one — stamping the whole binder's range on it would be a
    // plausible-looking range that is wrong, which is worse than the `mkSpan(0, 0)` it
    // replaced. `F` on line 21 is the sharp case: it has a member list, so its
    // declaration range and its name range genuinely differ.
    val names = allItems(pf.items).collect {
      case Item.AbstractSortItem(s) => s.name
      case Item.SortWithBodyItem(s) => s.name
    }
    val f = names.find(n => pf.symbols.name(n.last) == "F")
      .getOrElse(fail(s"no `F` type param; got ${names.map(n => pf.symbols.name(n.last)).mkString(", ")}"))
    val line21 = src.split("\n")(20)
    assertEquals(f.span.startRow, 21)
    assertEquals(f.span.startCol, line21.indexOf("F[T]") + 1)
    // The NAME is one character long. Before this was split out it covered `F[T]`.
    assertEquals(f.span.end - f.span.start, 1)
  }

  test("WI-971: a type param's DECLARATION span covers its member list") {
    // The OTHER half of the pair above, and the case that pins `sortTypeParam`'s own
    // bracket: `F[T]` is the one shape where the name's range and the declaration's
    // genuinely differ, so asserting the name alone leaves the declaration free to be
    // anything. It was: until WI-971 this span was rebuilt as `mkSpan(nameSpan.start,
    // e)` — the one site in the parser that recovered an offset from a span instead of
    // capturing it — and no test read it. Both ends are live here: an outer `located`
    // that opened after the name would start at `[`, and the fixture's line 21 writes
    // `F[T]   ]` with the spaces there for the other end — a `F[T]` written tight
    // against the closing bracket sits where a whitespace-skipping `~` has nothing to
    // skip, which is exactly why the name assertion above could not see one.
    //
    // CONTROL, measured: hand the declaration `nameSpan` (which is what dropping the
    // outer bracket leaves) and THIS CASE ALONE fails out of 327. The name assertion
    // above stays green — it reads the inner bracket, which the mutation does not
    // touch, and that is the point of splitting the two.
    val fDecl = pick(pf, "`F` type-param declaration") {
      case Item.SortWithBodyItem(s) if pf.symbols.name(s.name.last) == "F" => s.span
    }
    assertSpans(src, fDecl, "F[T]")
  }

  test("WI-971: a structured binder's MEMBER spans its own `sort ?U`") {
    // `sortBinderMember` — the `{ sort ?U }` member form, which this file's header
    // names among the productions reverting left the whole suite green, and which is
    // still not a `sort` DECLARATION, so the line-anchored helpers above cannot reach
    // it (line 24 anchors the enclosing `?Structured`, not the member).
    //
    // It earns a case now because WI-971 MOVED its capture: the trailing `~~ Index`
    // used to sit inside each of the two branches, and the branches now bracket
    // nothing — one `located` wraps the whole `keyword("sort") ~/ (a | b)`. That the
    // alternation's end is the selected branch's end is obviously true and was the same
    // kind of obviously-true claim WI-970 found wrong about `flatMap`.
    val u = pick(pf, "`U` binder member") {
      case Item.AbstractSortItem(s) if pf.symbols.name(s.name.last) == "U" => s.span
    }
    // The ` }` after it is what a whitespace-skipping `~` would swallow.
    assertSpans(src, u, "sort ?U")
  }

end DeclarationSpanTest
