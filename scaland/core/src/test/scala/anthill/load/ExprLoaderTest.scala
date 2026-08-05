package anthill.load

import anthill.kb.KnowledgeBase

/** What `Prelude.register` puts in a KB for the reflect ENCODING of expressions and
  * patterns — the vocabulary, not a loader.
  *
  * WI-1007: the expression LOADER this file was named for is gone (it was ported ahead
  * of any consumer and never called), and the test that pretended to cover it moved to
  * `LoaderTest` as a driven one.
  *
  * What survives here asserts REGISTRATION ONLY — `hasQualifiedName`, the weak shape the
  * moved test's own docstring indicts. It is left standing because the names are what
  * WI-1009 is about, not because these tests establish anything works: none of these
  * entities has a producer, and four of them are captured by a parse-time marker of the
  * same spelling. Read `Prelude.registerExprSorts`'s WI-1009 note before adding to this.
  */
class ExprLoaderTest extends munit.FunSuite:

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
