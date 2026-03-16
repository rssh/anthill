package anthill.parse

import anthill.intern.{TermSymbol, SymbolTable}
import anthill.term.{Term, TermId, VarId}
import anthill.span.Span
import scala.collection.mutable.{ArrayBuffer, HashMap}

/** Error from parsing/conversion. */
case class ParseError(message: String, span: Span)

/** CST-to-IR converter. This is the skeleton — tree-sitter JNI binding
  * provides the CST nodes that drive conversion.
  *
  * Variables are scoped per rule/constraint/operation.
  */
class Converter(
  val source: String,
  val symbols: SymbolTable,
  val terms: SimpleTermStore,
  val errors: ArrayBuffer[ParseError]
):
  private var nextVar: Int = 0
  private val varScope: HashMap[TermSymbol, VarId] = HashMap.empty

  def resetVarScope(): Unit =
    varScope.clear()

  def getOrCreateVar(sym: TermSymbol): VarId =
    varScope.getOrElseUpdate(sym, {
      val id = nextVar
      nextVar += 1
      VarId(id, sym)
    })

  def freshAnonymousVar(): VarId =
    val anonSym = symbols.intern("?")
    val id = nextVar
    nextVar += 1
    VarId(id, anonSym)
