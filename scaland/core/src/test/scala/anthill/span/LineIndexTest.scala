package anthill.span

/** WI-947 — the line index, unit-level.
  *
  * CONTROL: every test here fails if `LineIndex.lineCol` is backed out or made to
  * return `(0, 0)`; none of them passes by accident, because each asserts a
  * specific number rather than "some position was produced". The agreement test in
  * particular is the one that would catch a binary-search off-by-one, which a
  * hand-picked example set will not: it compares against a straight-line reference
  * scan at EVERY offset of a source with the awkward shapes (empty lines, a
  * trailing newline, no trailing newline, an astral character).
  */
class LineIndexTest extends munit.FunSuite:

  /** The obvious O(offset) scan, kept as the ORACLE the fast index must agree
    * with — the same role rustland's `reference_line_col` plays for its
    * `LineIndex`. Counts code points for the column, as the real one does. */
  private def referenceLineCol(source: String, offset: Int): (Int, Int) =
    val o = math.max(0, math.min(offset, source.length))
    var row = 1
    var lineStart = 0
    var i = 0
    while i < o do
      if source.charAt(i) == '\n' then
        row += 1
        lineStart = i + 1
      i += 1
    (row, source.codePointCount(lineStart, o) + 1)

  test("the index agrees with a reference scan at every offset") {
    val sources = List(
      "alpha\nbeta\ngamma\n",
      "alpha\nbeta\ngamma",     // no trailing newline
      "\n\n\nx",                // leading empty lines
      "",                       // empty source
      "\n",                     // a single newline
      "aéb\nc😀d\ne" // a 2-byte char and an ASTRAL one (surrogate pair)
    )
    for src <- sources; offset <- 0 to src.length + 2 do
      assertEquals(LineIndex(src).lineCol(offset), referenceLineCol(src, offset),
        s"source ${src.replace("\n", "\\n")}, offset $offset")
  }

  test("rows and columns are 1-based, and both are counted") {
    val idx = LineIndex("alpha\nbeta\ngamma\n")
    assertEquals(idx.lineCol(0), (1, 1))          // first char of the file
    assertEquals(idx.lineCol(4), (1, 5))          // last char of line 1
    assertEquals(idx.lineCol(5), (1, 6))          // the newline itself ends line 1
    assertEquals(idx.lineCol(6), (2, 1))          // first char of line 2
    assertEquals(idx.lineCol(11), (3, 1))         // first char of line 3
  }

  test("a column counts CODE POINTS, so an astral character is one column") {
    // "😀" is one code point spelled as two UTF-16 code units. The offset
    // AFTER it is therefore column 2, not 3 — the unit rustland's `line_col` counts.
    val idx = LineIndex("😀x")
    assertEquals(idx.lineCol(0), (1, 1))
    assertEquals(idx.lineCol(2), (1, 2))
  }

  test("an offset past the end clamps instead of throwing") {
    // The whole-parse-failure path reports `Parsed.Failure.index`, which IS the
    // length when the parse ran out of input — a diagnostic must not become an
    // exception on the way to being printed.
    val idx = LineIndex("ab\ncd")
    assertEquals(idx.lineCol(5), (2, 3))
    assertEquals(idx.lineCol(99), (2, 3))
  }

end LineIndexTest
