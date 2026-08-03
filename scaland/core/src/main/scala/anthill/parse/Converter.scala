package anthill.parse

import anthill.intern.{TermSymbol, SymbolTable}
import anthill.term.{Term, TermId, VarId}
import anthill.span.Span
import scala.collection.mutable.{ArrayBuffer, HashMap}

/** Error from parsing/conversion. */
case class ParseError(message: String, span: Span):
  /** WI-947: `file:line:col: message`, through the ONE located renderer that
    * [[anthill.load.LoadError.render]] also uses — so which STAGE found a fault
    * cannot change how its location reads. Before this, a parse error rendered
    * fastparse's own `Position row:col` buried in the message text on the
    * whole-parse-failure path, and nothing locational at all on every other.
    *
    * Also `toString`, for the same reason it is on `LoadError`: every existing
    * printer interpolates the error rather than calling a renderer by name, and a
    * rendering nothing reaches is a seam with no user. */
  def render: String = span.render(message)

  override def toString: String = render

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
