package anthill.load

import anthill.kb.KnowledgeBase
import anthill.intern.ResolveResult
import anthill.parse.{Parser, ParsedFile, Item, DesugarTarget, Pratt}
import anthill.term.{Term, TermId}

/** ERF7T back-out measured: reverting the parser mints plus implicit reflect
  * exposure fails 18/20 rows, including the runtime and loaded-identity rows.
  * The table and ordinary-call controls pass either way by design.
  * KnowledgeBaseTest separately measures the absolute equation reader (1 failure). */
class DesugarTargetTest extends munit.FunSuite:
  private def parsed(src: String): ParsedFile =
    Parser.parse(src).fold(e => fail(e.toString), identity)

  private def body(src: String): (ParsedFile, IndexedSeq[TermId]) =
    val pf = parsed(s"rule probe(?x, ?d, ?P) :- $src")
    val r = pf.items.collectFirst { case Item.RuleItem(r) => r }.get
    (pf, r.body.get)

  private def functor(pf: ParsedFile, id: TermId): String = pf.terms.get(id) match
    case fn: Term.Fn => pf.symbols.name(fn.functor)
    case other => fail(s"expected application, got $other")

  for (src, address) <- Seq(
    "Foo.f" -> DesugarTarget.FieldAccess,
    "?x.m(1)" -> DesugarTarget.DotApply,
    "?P(1)" -> DesugarTarget.HoApply,
    "[1, 2]" -> DesugarTarget.ListLiteral,
    "{1, 2}" -> DesugarTarget.SetLiteral,
    "(a: 1, b: 2)" -> DesugarTarget.TupleLiteral,
    "!" -> DesugarTarget.Cut,
    "requires(Eq)" -> DesugarTarget.FindDictionary,
    "require[Eq]" -> DesugarTarget.FindDictionary,
    "?d = require[Eq]" -> DesugarTarget.FindDictionary) do
    test(s"converter mint `$src` carries its absolute address") {
      val (pf, goals) = body(src)
      assertEquals(functor(pf, goals.head), address)
    }

  for (src, address) <- Seq(
    "if true then 1 else 2" -> DesugarTarget.IfExpr,
    "let x = 1 in x" -> DesugarTarget.LetExpr,
    "lambda x -> x" -> DesugarTarget.LambdaExpr,
    "match x case _ -> 1" -> DesugarTarget.MatchExpr) do
    test(s"expression mint `$src` carries its address and marker") {
      val pf = parsed(s"operation probe() -> Int64 = $src")
      val op = pf.items.collectFirst { case Item.OperationItem(o) => o }.get
      assertEquals(functor(pf, op.body.get), address)
      assert(pf.terms.markerOf(op.body.get).isDefined, "unsupported expressions retain provenance")
    }

  test("the target table agrees with the parsed addresses and excludes kernel short names") {
    assertEquals(DesugarTarget.all.size, 12)
    for address <- DesugarTarget.all do
      assert(address.startsWith(".."), address)
      if !DesugarTarget.isKernelControl(address) then
        assert(DesugarTarget.is(DesugarTarget.short(address), address))
        assert(DesugarTarget.is(DesugarTarget.qualified(address), address))
  }

  test("goal let and infix binding mint the same connective") {
    val (pf, goals) = body("let ?x = 1, ?d <=> 1, ?d === 1")
    assertEquals(functor(pf, goals(0)), functor(pf, goals(1)))
    assertEquals(functor(pf, goals(1)), Pratt.unifyFunctor)
    assert(functor(pf, goals(1)).startsWith(".."))
    assertEquals(functor(pf, goals(2)), Pratt.structEqFunctor)
    assert(functor(pf, goals(2)).startsWith(".."))
  }

  test("requirement output is carried and ordinary control names remain ordinary") {
    val (pf, goals) = body("require[Eq], ?d = require[Eq], requires(Eq), require(Eq), cut(1), find_dictionary(Eq), requires(Eq, Eq)")
    for i <- 0 to 1 do
      val fn = pf.terms.get(goals(i)).asInstanceOf[Term.Fn]
      assertEquals(fn.namedArgs.map((k, _) => pf.symbols.name(k)).toSeq, Seq("out"))
      assert(pf.terms.get(fn.namedArgs(0)._2).isInstanceOf[Term.Var])
    assertEquals(pf.terms.get(goals(2)).asInstanceOf[Term.Fn].namedArgs.length, 0)
    assertEquals(functor(pf, goals(3)), "require")
    assertEquals(functor(pf, goals(4)), "cut")
    assertEquals(functor(pf, goals(5)), "find_dictionary")
    assertEquals(functor(pf, goals(6)), "requires")
    for address <- Seq(DesugarTarget.Cut, DesugarTarget.FindDictionary, Pratt.unifyFunctor, Pratt.structEqFunctor) do
      intercept[IllegalArgumentException](DesugarTarget.is(DesugarTarget.short(address), address))
  }

  test("literal carriers still resolve and match facts under namespace shadowing") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val pf = parsed("namespace app.anthill\nend\nnamespace app.demo\nsort ListLiteral end\nsort SetLiteral end\nsort TupleLiteral end\nfact stored([1], {2}, (a: 3))\nrule probe :- stored(..anthill.reflect.ListLiteral(1), ..anthill.reflect.SetLiteral(2), ..anthill.reflect.TupleLiteral(a: 3))\nend")
    val errors = Loader.loadAll(kb, IndexedSeq(pf))
    assert(errors.isEmpty, errors.toString)
    val goal = kb.makeNameTermFromSym(kb.resolveSymbol("app.demo.probe"))
    assertEquals(anthill.resolve.SearchStream.resolve(kb, goal).allSolutions(kb).length, 1)
  }

  test("host-name lookup excludes desugar vocabulary and retains metadata") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    for name <- Seq("field_access", "dot_apply", "ho_apply", "ListLiteral", "cut", "find_dictionary") do
      assertEquals(kb.symbols.resolveInScope(name, kb.globalScope), ResolveResult.NotFound, name)
    assert(kb.symbols.resolveInScope("SortInfo", kb.globalScope).denotes)
    assert(kb.tryResolveSymbol(DesugarTarget.qualified(DesugarTarget.FieldAccess)).isDefined)
  }

  test("a sibling anthill namespace cannot capture loaded literal and application targets") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val pf = parsed("namespace app.anthill\nend\nnamespace app.demo\nsort ListLiteral end\nsort SetLiteral end\nsort TupleLiteral end\noperation ho_apply(x: Int64) -> Bool\noperation dot_apply(x: Int64) -> Bool\nrule p(?x, ?P) :- holds([1], {2}, (a: 3)), ?P(?x), ?x.m(1)\nend")
    val errors = Loader.loadAll(kb, IndexedSeq(pf))
    assert(errors.isEmpty, errors.toString)
    val rules = kb.byFunctor(kb.resolveSymbol("app.demo.p"))
    assertEquals(rules.length, 1)
    val goals = kb.ruleBody(rules.head)
    val holds = kb.getTerm(goals.head).asInstanceOf[Term.Fn]
    for (id, address) <- holds.posArgs.toSeq.zip(Seq(DesugarTarget.ListLiteral, DesugarTarget.SetLiteral, DesugarTarget.TupleLiteral)) do
      assertEquals(kb.qualifiedNameOf(kb.getTerm(id).asInstanceOf[Term.Fn].functor), DesugarTarget.qualified(address))
    assertEquals(kb.qualifiedNameOf(kb.getTerm(goals(1)).asInstanceOf[Term.Fn].functor), DesugarTarget.qualified(DesugarTarget.HoApply))
    assertEquals(kb.qualifiedNameOf(kb.getTerm(goals(2)).asInstanceOf[Term.Fn].functor), DesugarTarget.qualified(DesugarTarget.DotApply))
  }
