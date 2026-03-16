package anthill.parse

import anthill.intern.SymbolTable
import scala.collection.mutable.ArrayBuffer

/** Parse entry point — tree-sitter JNI-based parser.
  *
  * When tree-sitter JNI is available, this will:
  * 1. Parse source string using tree-sitter-anthill grammar
  * 2. Walk the CST via Converter to produce ParsedFile
  *
  * For now, provides a stub and manual IR construction API.
  */
object Parser:

  /** Parse a source string into a ParsedFile.
    * TODO: Implement when tree-sitter JNI is integrated.
    */
  def parse(source: String): Either[IndexedSeq[ParseError], ParsedFile] =
    val symbols = SymbolTable()
    val terms = SimpleTermStore()
    val errors = ArrayBuffer.empty[ParseError]
    val converter = Converter(source, symbols, terms, errors)
    // TODO: tree-sitter CST walking
    if errors.nonEmpty then
      Left(errors.toIndexedSeq)
    else
      Right(ParsedFile(ArrayBuffer.empty, symbols, terms))
