package anthill.load

import anthill.kb.KnowledgeBase
import anthill.term.{Term, TermId}
import anthill.parse.{ExprMarker, Parser}

/** The reflect ENCODING of expressions and patterns: what `Prelude.register` puts in a KB
  * for it, and what the loader does with the parse-time forms that would translate INTO it.
  *
  * WI-1007: the expression LOADER this file was named for is gone (ported ahead of any
  * consumer, never called), and the test that pretended to cover it moved to `LoaderTest`
  * as a driven one.
  *
  * WI-1009: what was left here asserted REGISTRATION ONLY — `hasQualifiedName` — which is
  * why this file stayed green through the defect that made those names actively harmful.
  * The parser mints a different vocabulary (`pattern_var`, `match_branch`, …) for the same
  * forms, and four spellings COLLIDE with the entities below; `Loader.reallocTerm` resolves
  * every functor by name, so a marker in a rule body either captured the entity symbol of
  * its spelling or leaked as an undeclared predicate, decided by nothing else. The
  * registration tests could not see either, and still cannot — the four that DRIVE the
  * loaded shape are below them, and they are the ones that fail if the refusal is backed
  * out. Read `anthill.parse.ExprMarker` for the two-layer split. */
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

  // ── WI-1009: a parse-time marker in term position ────────────────────────────

  private def loadSrc(src: String)(using munit.Location): (KnowledgeBase, List[LoadError]) =
    val pf = Parser.parse(src, "<wi1009>").toOption.getOrElse(fail(s"parse failed: $src"))
    val kb = mkKb()
    (kb, Loader.loadAll(kb, IndexedSeq(pf)).toList)

  /** The one clause `r` has, and its one body goal. Fails rather than degrades: the point
    * of every test below is what the KB HOLDS, so "no clause" must not read as "clean". */
  private def soleGoalOf(kb: KnowledgeBase, head: String)(using munit.Location): TermId =
    val sym = kb.tryResolveSymbol(head).getOrElse(fail(s"`$head` must be registered by pass 3"))
    val rid = kb.byFunctor(sym).headOption.getOrElse(fail(s"`$head` has no clause"))
    kb.ruleBody(rid) match
      case IndexedSeq(goal) => goal
      case other            => fail(s"expected one body goal, got ${other.length}")

  /** Every name reachable from `id` — what a "did the marker land in the KB?" assertion
    * needs, and ARITY- and SHAPE-FREE: it answers for whatever the loader lowered to,
    * where a positional probe would have to guess the shape the defect produced. */
  private def namesIn(kb: KnowledgeBase, id: TermId): Set[String] =
    val term = kb.getTerm(id)
    val self = term match
      case fn: Term.Fn   => Set(kb.qualifiedNameOf(fn.functor))
      case Term.Ref(s)   => Set(kb.qualifiedNameOf(s))
      case Term.Ident(s) => Set(kb.qualifiedNameOf(s))
      case _             => Set.empty[String]
    term.subterms.foldLeft(self)((acc, sub) => acc ++ namesIn(kb, sub))

  /** The refusal itself, and that it points at the `lambda` the user wrote.
    *
    * Back the WI-1009 refusal out and this fails on the FIRST assertion: today the load
    * reports nothing at all — the marker resolves to the entity of its spelling and the
    * KB keeps the result. The span is the `lambda` keyword alone, which is the span
    * `lambdaExpr`'s own `spanOfToken` captures (`SpanEndTest` pins the same for `let`). */
  test("WI-1009: a `lambda` in a rule body is refused, at the `lambda`") {
    val src = "rule r(?x) :- p(lambda s -> s)"
    val (_, errors) = loadSrc(src)
    errors match
      case LoadError.ExpressionInTermPosition(marker, span) :: Nil =>
        assertEquals(marker, ExprMarker.LambdaExpr)
        // `SpanFixture.assertSpans` is `private[span]`; this is its one line, and
        // widening a fixture's visibility for one caller is the worse trade.
        assertEquals(src.slice(span.start, span.end), "lambda")
      case other => fail(s"expected ONE marker refusal, got: $other")
  }

  /** THE finding, in its own terms: BOTH defects gone, and gone the same way.
    *
    * Before the refusal, loading this exact source produced (measured, load errors empty):
    * {{{
    * Fn p                                   [bare intern]
    *   Fn anthill.reflect.Expr.lambda_expr  [RESOLVED  <- the marker, captured]
    *     Fn pattern_var                     [bare intern — no entity of that spelling]
    * }}}
    * — an `Entity` symbol applied POSITIONALLY to (pattern, body), which is not the shape
    * `reflect.anthill` declares for it, above a sibling marker that leaked as an
    * undeclared predicate name. Which fate a marker met was decided by whether the parser
    * and the reflect vocabulary happened to agree on a spelling. Both names are asserted
    * here so neither half can be fixed alone; backing the refusal out and probing this
    * fixture's own goal gives `Set(p, anthill.reflect.Expr.lambda_expr, pattern_var, s)`,
    * so both assertions are live and neither is decoration.
    *
    * The goal itself is still built — the loader accumulates and carries on, as it does
    * for an unresolved name — so `Bottom` is a POSITIVE assertion about the slot, not an
    * absence that a vanished clause would also satisfy. */
  test("WI-1009: the refused marker reaches the KB neither captured nor leaked") {
    val (kb, _) = loadSrc("rule r(?x) :- p(lambda s -> s)")
    val goal = soleGoalOf(kb, "r")

    kb.getTerm(goal) match
      case fn: Term.Fn =>
        assertEquals(kb.qualifiedNameOf(fn.functor), "p", "the enclosing goal still loads")
        assertEquals(fn.posArgs.length, 1)
        assertEquals(kb.getTerm(fn.posArgs(0)), Term.Bottom, "the marker's slot is unbuilt")
      case other => fail(s"expected the goal `p(…)`, got $other")

    val names = namesIn(kb, goal)
    assert(!names.contains("anthill.reflect.Expr.lambda_expr"),
      s"CAPTURE: the marker took the reflect entity of its spelling — $names")
    assert(!names.contains("pattern_var"),
      s"LEAK: the pattern marker landed as an undeclared predicate — $names")
  }

  /** A FACT is the loader's other term position, and it takes the same refusal — the
    * refusal lives in `reallocTerm`, which every one of them goes through.
    *
    * Fails without the change for the same reason as the rule-body case. Named separately
    * because a refusal installed at the rule loader instead would pass that one and this. */
  test("WI-1009: a marker in a FACT is refused too") {
    val (_, errors) = loadSrc("fact p(match ?x case _ -> 1)")
    errors match
      case LoadError.ExpressionInTermPosition(marker, _) :: Nil =>
        assertEquals(marker, ExprMarker.MatchExpr)
      case other => fail(s"expected ONE marker refusal, got: $other")
  }

  /** THE CONTROL, and the reason the refusal is keyed on provenance instead of a name
    * blocklist: `lambda_expr` is a REAL name — `reflect.anthill` declares that entity and
    * `Prelude` registers it — so a written call spelled that way must still load and still
    * resolve to the entity. A blocklist on the four colliding spellings would refuse this.
    *
    * PASSES EITHER WAY today, because no refusal existed to over-fire; it is here to fail
    * the day someone re-derives the marker set from a list of strings. */
  test("WI-1009 control: a WRITTEN functor spelled like a marker still resolves") {
    val (kb, errors) = loadSrc("rule r(?x) :- lambda_expr(?x)")
    assert(errors.isEmpty, s"a written call is not a marker: $errors")
    kb.getTerm(soleGoalOf(kb, "r")) match
      case fn: Term.Fn =>
        assertEquals(kb.qualifiedNameOf(fn.functor), "anthill.reflect.Expr.lambda_expr")
      case other => fail(s"expected a goal `Fn`, got $other")
  }
