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
    if source.trim.isEmpty then
      val symbols = SymbolTable()
      val terms = SimpleTermStore()
      Right(ParsedFile(ArrayBuffer.empty, symbols, terms))
    else
      AnthillParser.parse(source, fileName)
