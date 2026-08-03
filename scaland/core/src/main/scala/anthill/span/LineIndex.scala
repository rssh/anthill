package anthill.span

/** Line starts for ONE source text, so an offset resolves to `line:col` without
  * re-walking the text from offset 0.
  *
  * WI-947 (rustland's WI-854 twin): built ONCE per file, at the top of
  * [[anthill.parse.AnthillParser.parse]], and used for every span that parse
  * produces. The alternative — resolve a position when a diagnostic is rendered,
  * by scanning the source — is O(N x len) for N diagnostics in one file, which
  * rustland measured at ~50 s for 2100 diagnostics over 2.7 MB. Here the trade is
  * even more clearly worth taking, because scaland resolves EAGERLY: a `Span`
  * stores its row/col, so nothing downstream needs the source text to render a
  * position (see [[Span]]) — but that means one lookup per span CONSTRUCTED, not
  * one per error, and a per-lookup scan would be paid on every clean parse.
  *
  * OFFSETS ARE JAVA STRING INDICES (UTF-16 code units) — fastparse's `Index` over a
  * `String`. COLUMNS COUNT UNICODE CODE POINTS, which is the unit rustland's
  * `LineIndex::line_col` counts (there: characters over byte offsets). The two
  * units differ only for astral characters, and picking the rustland unit is what
  * keeps a diagnostic about the same file readable the same way in both
  * implementations.
  */
final class LineIndex(source: String):

  /** Offset of each line's first character. `starts(0)` is always 0, so this is
    * never empty and a line NUMBER is a `starts` position + 1. Strictly
    * increasing, which is what makes the binary search below exact. */
  private val starts: Array[Int] =
    val buf = scala.collection.mutable.ArrayBuffer(0)
    var i = source.indexOf('\n')
    while i >= 0 do
      buf += i + 1
      i = source.indexOf('\n', i + 1)
    buf.toArray

  /** Whether ANY surrogate code unit occurs in the source — i.e. whether a code-point
    * column can differ from a code-unit one at all. Scanned once, because the answer
    * is almost always no and it turns the column into a subtraction.
    *
    * WITHOUT this, a column costs O(column): `codePointCount` walks the line prefix,
    * so tokens on one line cost O(len^2) in that line's length. Fine for a hand-written
    * source, ruinous for a generated single-line one — the same hazard rustland's
    * `LineIndex` documents and leaves open. Here every span pays it (resolution is
    * eager, not per-diagnostic), so it is closed rather than documented. */
  private val hasSurrogates: Boolean =
    var i = 0
    var found = false
    while i < source.length && !found do
      if Character.isSurrogate(source.charAt(i)) then found = true
      i += 1
    found

  /** The 1-based line containing `offset`. */
  private def lineOf(offset: Int): Int =
    val i = java.util.Arrays.binarySearch(starts, offset)
    // Found: `offset` IS a line start, at 0-based position `i`. Not found:
    // `-i - 1` is the insertion point = how many starts are strictly below
    // `offset`, which is that line's 1-based number.
    if i >= 0 then i + 1 else -i - 1

  /** Resolve an offset to `(row, col)`, both 1-BASED — the numbering an editor
    * shows, and the one rustland renders.
    *
    * An offset past the end of the text clamps to the end rather than throwing:
    * the whole-parse-failure path reports `Parsed.Failure.index`, which is the
    * length itself when the parse ran out of input, and a diagnostic must not
    * become an exception. */
  def lineCol(offset: Int): (Int, Int) =
    val o = math.max(0, math.min(offset, source.length))
    val row = lineOf(o)
    val lineStart = starts(row - 1)
    val col = if hasSurrogates then source.codePointCount(lineStart, o) else o - lineStart
    (row, col + 1)

end LineIndex
