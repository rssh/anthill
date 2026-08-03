package anthill.span

import anthill.parse.{Item, Parser, ParsedFile}

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
  * keyword eaten by a dispatching production, which hands the start back down); the
  * point of testing all of them together is that the exceptions cannot creep back.
  *
  * CONTROL: every assertion is a specific (row, col) checked against the source text
  * at that column, so none can pass with a zeroed or stale span. Revert any single
  * production's `Index` capture and exactly its case here fails.
  */
class DeclarationSpanTest extends munit.FunSuite:

  private def parse(src: String): ParsedFile =
    Parser.parse(src, "decls.anthill") match
      case Right(pf) => pf
      case Left(errs) => fail(s"parse failed: ${errs.map(_.render).mkString("; ")}")

  /** Every item in the file, flattened through the two scope-opening shapes. */
  private def allItems(items: Iterable[Item]): Vector[Item] =
    items.toVector.flatMap { item =>
      item +: (item match
        case Item.NamespaceItem(ns) => allItems(ns.items)
        case Item.SortWithBodyItem(s) => allItems(s.items)
        case _ => Vector.empty)
    }

  private def spanOf(item: Item): Span = item match
    case Item.NamespaceItem(x)     => x.span
    case Item.SortWithBodyItem(x)  => x.span
    case Item.AbstractSortItem(x)  => x.span
    case Item.EntityItem(x)        => x.span
    case Item.FactItem(x)          => x.span
    case Item.ConstItem(x)         => x.span
    case Item.ConstraintItem(x)    => x.span
    case Item.RuleItem(x)          => x.span
    case Item.RuleBlockItem(x)     => x.span
    case Item.OperationItem(x)     => x.span
    case Item.OperationBlockItem(x) => x.span
    case Item.RequiresDeclItem(x)  => x.span
    case Item.ProvidesClauseItem(x) => x.span
    case Item.ProvidesBlockItem(x) => x.span
    case Item.ProofItem(x)         => x.span
    case other => fail(s"no span reader for $other — add one when the shape is added")

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

  // ── The fixture ──────────────────────────────────────────────
  //
  // One declaration per line, so a line number IS a shape. Line numbers are read
  // off this literal, and `assertDeclStartsAtLine` re-derives the column from the
  // text — so adding a line above an existing case fails loudly on the token check
  // rather than silently testing the wrong construct.
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
      |  sort Parameterized[A, F[T]]
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

  test("a desugared type-param's NAME spans its identifier, not the declaration") {
    // WI-947: `desugarSortTypeParam` mints ordinary sort items, and their `Name` is
    // what `Loader.lookupScope` reports through. A `Name` must span its identifier
    // token like every other one — stamping the whole binder's range on it would be a
    // plausible-looking range that is wrong, which is worse than the `mkSpan(0, 0)` it
    // replaced. `sort Parameterized[A, F[T]]` on line 21 is the sharp case: `F` has a
    // member list, so its declaration range and its name range genuinely differ.
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

end DeclarationSpanTest
