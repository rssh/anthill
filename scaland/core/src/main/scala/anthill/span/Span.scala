package anthill.span

/** Source location for error reporting. */
case class Span(
  file: String,
  startByte: Int,
  endByte: Int,
  startRow: Int,
  startCol: Int,
  endRow: Int,
  endCol: Int
)

object Span:
  val empty: Span = Span("", 0, 0, 0, 0, 0, 0)
