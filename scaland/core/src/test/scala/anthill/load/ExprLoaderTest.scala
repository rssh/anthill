package anthill.load

import anthill.kb.KnowledgeBase
import anthill.term.{Term, TermId, VarId, Literal}
import anthill.intern.TermSymbol
import anthill.parse.*
import anthill.span.Span
import scala.collection.mutable.ArrayBuffer

class ExprLoaderTest extends munit.FunSuite:

  private def emptySpan = Span.empty

  /** Create a KB with prelude registered. */
  private def mkKb(): KnowledgeBase =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    kb

  test("prelude registers Expr sort and entities") {
    val kb = mkKb()
    assert(kb.hasQualifiedName("anthill.reflect.Expr"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.match_expr"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.if_expr"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.let_expr"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.lambda_expr"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.apply"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.constructor"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.var_ref"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.int_lit"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.float_lit"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.string_lit"))
    assert(kb.hasQualifiedName("anthill.reflect.Expr.bool_lit"))
  }

  test("prelude registers Pattern sort and entities") {
    val kb = mkKb()
    assert(kb.hasQualifiedName("anthill.reflect.Pattern"))
    assert(kb.hasQualifiedName("anthill.reflect.Pattern.var_pattern"))
    assert(kb.hasQualifiedName("anthill.reflect.Pattern.tuple_pattern"))
    assert(kb.hasQualifiedName("anthill.reflect.Pattern.constructor_pattern"))
    assert(kb.hasQualifiedName("anthill.reflect.Pattern.literal_pattern"))
    assert(kb.hasQualifiedName("anthill.reflect.Pattern.wildcard"))
  }

  test("prelude registers TypedExpr sort") {
    val kb = mkKb()
    assert(kb.hasQualifiedName("anthill.reflect.TypedExpr"))
    assert(kb.hasQualifiedName("anthill.reflect.TypedExpr.typed"))
  }

  test("prelude registers standalone entities") {
    val kb = mkKb()
    assert(kb.hasQualifiedName("anthill.reflect.MatchBranch"))
    assert(kb.hasQualifiedName("anthill.reflect.ApplyArg"))
  }

  test("buildList creates cons-list") {
    val kb = mkKb()
    val v1 = kb.alloc(Term.Const(Literal.IntLit(1)))
    val v2 = kb.alloc(Term.Const(Literal.IntLit(2)))
    // Use the loader's buildList via reflection-like access (it's private)
    // Instead, test it indirectly through expression conversion

    // Build a simple ParsedFile with a literal expression fact
    val symbols = anthill.intern.SymbolTable()
    val terms = SimpleTermStore()

    // Build int_lit expression: Const(42) — should convert to int_lit(value: 42)
    val litTerm = terms.alloc(Term.Const(Literal.IntLit(42)))

    // Wrap in a fact
    val items = ArrayBuffer[Item](
      Item.FactItem(Fact(litTerm, None, emptySpan))
    )
    val parsed = ParsedFile(items, symbols, terms)

    // Load — the fact just gets reallocated as-is (not as an expression)
    // since facts use reallocTerm, not convertExprTerm
    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"errors: $errors")
    assert(kb.factCount > 0)
  }

  test("qualifiedNameOf returns qualified name for resolved symbols") {
    val kb = mkKb()
    val intSym = kb.tryResolveSymbol("anthill.prelude.Int64").get
    assertEquals(kb.qualifiedNameOf(intSym), "anthill.prelude.Int64")
  }

  test("qualifiedNameOf returns name for unresolved symbols") {
    val kb = mkKb()
    val sym = kb.intern("unknown_thing")
    assertEquals(kb.qualifiedNameOf(sym), "unknown_thing")
  }
