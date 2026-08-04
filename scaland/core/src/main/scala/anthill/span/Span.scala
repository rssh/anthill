package anthill.span

/** Source location for error reporting: a range in one file, plus the `line:col`
  * that range resolves to.
  *
  * OFFSETS ARE JAVA STRING INDICES (UTF-16 code units), not bytes — scaland parses
  * a `String` and fastparse's `Index` counts code units. Hence `start`/`end` and
  * not rustland's `start`/`end`-as-bytes: the twin field there really is a byte
  * offset (it parses `&str` through tree-sitter), and the fields were called
  * `startByte`/`endByte` here until WI-947, which was a name inviting byte
  * arithmetic that does not hold.
  *
  * WI-947: `startRow`/`startCol`/`endRow`/`endCol` are 1-BASED and resolved AT
  * CONSTRUCTION, from the file's [[LineIndex]]. They were hard-coded 0 at every
  * construction site before, so no scaland diagnostic could name a position — the
  * best a user got was a raw offset. Resolving eagerly (rather than at render time,
  * as rustland does) is what lets a `LoadError` raised deep in the loader print
  * `file:line:col` with nothing else in hand: scaland has no source registry to
  * hand a renderer, and a `Span` already carries its own `file`.
  *
  * ROW 0 IS THEREFORE IMPOSSIBLE for a resolved location, and marks the one span
  * that HAS no location, [[Span.empty]] — see [[hasLocation]].
  *
  * THE CONSTRUCTOR IS PRIVATE TO THIS PACKAGE so those four fields cannot be
  * invented: the only ways to a span are [[Span.at]], which resolves them, and
  * [[Span.empty]], which declares there is nothing to resolve. That is the
  * property the old shape could not have — every caller passed `0, 0, 0, 0` and
  * nothing could tell a real row from a placeholder.
  *
  * `end` IS THE CONSTRUCT'S OWN END, exclusive — NOT an upper bound (WI-970; it read
  * as one here until then, which is how EIGHT parser sites came to disagree with the
  * rest, ending wherever the trivia after the construct happened to run out). That is
  * not a loose bound: adjacent constructs' spans overlap under it, so the first
  * containment or caret reader would be WRONG rather than merely coarse. The fastparse
  * spellings that keep it tight are a parser concern and are stated there
  * (`AnthillParser.spanOfToken`); `SpanEndTest` is the invariant as assertions.
  *
  * A ZERO-WIDTH span is this invariant, not an exception to it, when the diagnostic
  * is about a POINT rather than a construct — a parse failure has no construct to
  * bracket (`AnthillParser.parse`, the one such site). It is [[Span.empty]] that
  * makes the different claim: no source text at all.
  *
  * THE END HALF (`end`, `endRow`, `endCol`) HAS NO PRODUCTION READER — only `start`
  * and `formatStart` are consumed, and review flagged resolving it as waste. Kept
  * anyway, deliberately: a span is a RANGE, and one that can locate its start but
  * not its end is a stranger record than one with a field waiting for its first
  * caret renderer. The cost objection is answered where it belongs — a column is a
  * subtraction on any source without surrogates ([[LineIndex]]), so resolving both
  * ends is two subtractions, not two line walks. Revisit if a caret renderer never
  * arrives, not because the fields look idle.
  */
case class Span private[span] (
  file: String,
  start: Int,
  end: Int,
  startRow: Int,
  startCol: Int,
  endRow: Int,
  endCol: Int
):
  /** Whether this span resolved to a position — false only for [[Span.empty]]. */
  def hasLocation: Boolean = startRow > 0

  /** `line:col`, the position half of a rendering. */
  def formatStart: String = s"$startRow:$startCol"

  /** WI-947: the ONE located rendering, shared by EVERY diagnostic family
    * ([[anthill.parse.ParseError.render]], [[anthill.load.LoadError.render]]), so
    * which STAGE found a fault cannot change how its location reads. Before this,
    * a parse failure rendered fastparse's own `Position 128:91` inside a message
    * and a load error rendered nothing locational at all.
    *
    * `file:line:col: message` is the form editors and terminals make clickable, so
    * the FILE must be a path the reader can open — a caller that parses under a
    * module id rather than a path hands this a location nothing can follow (see
    * [[anthill.load.EmbeddedStdlib]], which passes the resolver's own relative path
    * for exactly that reason).
    *
    * TWO cases, not the four a `(file, location)` matrix suggests: the only span
    * without a location is [[Span.empty]], whose file is empty too, so
    * "named file, no position" cannot be constructed. Rustland's
    * `span::render_located` does carry that third shape — it has locationless
    * diagnostics that still know their file, which nothing here produces.
    */
  def render(message: String): String =
    if !hasLocation then message
    else if file.isEmpty then s"$formatStart: $message"
    else s"$file:$formatStart: $message"

object Span:
  /** The span of a construct with no source text behind it — a synthesized IR node,
    * or a diagnostic that genuinely has nowhere to point. It renders as the bare
    * message; it is NOT a "position 0" and must not be used as a stand-in for a
    * position nobody bothered to capture. */
  val empty: Span = Span("", 0, 0, 0, 0, 0, 0)

  /** The span of `[start, end)` in `file`, resolved through that file's index. */
  def at(file: String, index: LineIndex, start: Int, end: Int): Span =
    val (startRow, startCol) = index.lineCol(start)
    val (endRow, endCol) = index.lineCol(end)
    Span(file, start, end, startRow, startCol, endRow, endCol)
