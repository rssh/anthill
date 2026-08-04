package anthill.parse

import anthill.intern.SymbolTable
import scala.collection.mutable.ArrayBuffer

/** Parse entry point — delegates to AnthillParser (fastparse-based).
  *
  * Parses source text directly into IR types (ParsedFile, Item, etc.).
  */
object Parser:

  /** Parse a source string into a ParsedFile. */
  def parse(source: String, fileName: String = "<input>"): Either[IndexedSeq[ParseError], ParsedFile] =
    parseInto(source, fileName, SimpleTermStore())

  /** [[AnthillParser.parseInto]] at this layer — the WI-991 seam, which owns the argument
    * for why it exists and why it is not public. Mirrored here rather than reached
    * through: the empty-source arm below returns without ever calling the delegate, so a
    * seam only on `AnthillParser` would leave `SpanFixture` parsing empty sources into a
    * store it never sees. */
  private[anthill] def parseInto(
    source: String, fileName: String, terms: SimpleTermStore
  ): Either[IndexedSeq[ParseError], ParsedFile] =
    if source.trim.isEmpty then
      Right(ParsedFile(ArrayBuffer.empty, SymbolTable(), terms))
    else
      AnthillParser.parseInto(source, fileName, terms)
