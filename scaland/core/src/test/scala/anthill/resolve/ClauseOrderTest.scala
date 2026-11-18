package anthill.resolve

import anthill.codegen.scala.StdlibFixture
import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Literal, Term, TermId, Var}

/** WI-20260911-SXZ3G — A RELATION ANSWERS IN CLAUSE ORDER, rustland's `wi_sxz3g_clause_order_test`
  * on this carrier. The discrimination tree keeps a node's edges in a `HashMap`, so a goal with a
  * variable at an indexed position used to get its candidates in the map's order; they are now
  * sorted by `RuleId`, the order the clauses were asserted in (facts before rules, each group in
  * clause order — `KnowledgeBase.query`).
  *
  * The facts are declared 3, 1, 2, so neither the value order nor the map's order is the answer.
  * BACK-OUT, measured 2026-11-18: the sort key back to facts-before-rules alone fails "facts
  * answer in clause order" and "the order holds through a nested walk" (both answered in the
  * map's order, 1, 2, 3). "a bound position answers one row" is the CONTROL, passing either way
  * by design: it never walks the map. */
class ClauseOrderTest extends munit.FunSuite:
  private def fixture: KnowledgeBase = StdlibFixture.kbWith(LoadFixture.parsed(
    """fact p(3)
      |fact p(1)
      |fact p(2)
      |fact q(2, 7)
      |fact q(1, 5)
      |fact q(2, 6)
      |fact q(1, 8)
      |""".stripMargin, "clause-order.anthill"))

  private def int(kb: KnowledgeBase, t: TermId): BigInt = kb.getTerm(t) match
    case Term.Const(Literal.IntLit(n)) => n
    case other => fail(s"expected a bound integer, got $other")

  /** Each answer of `name(?a₁, …, ?aₙ)` over `arity` fresh variables, in the order given. */
  private def answers(kb: KnowledgeBase, name: String, arity: Int): Seq[Seq[BigInt]] =
    val sym = kb.tryResolveSymbol(name).getOrElse(fail(s"missing fixture predicate $name"))
    val vs = IArray.tabulate(arity)(i => kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern(s"a$i"))))))
    val goal = kb.alloc(Term.Fn(sym, vs, IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).toSeq.map { sol =>
      vs.toSeq.map(v => int(kb, kb.reify(v, sol.subst)))
    }

  test("facts answer in clause order, on two independently built KBs") {
    for _ <- 0 until 2 do
      assertEquals(answers(fixture, "p", 1), Seq(3, 1, 2).map(n => Seq(BigInt(n))))
  }

  test("the order holds through a nested walk") {
    assertEquals(
      answers(fixture, "q", 2),
      Seq((2, 7), (1, 5), (2, 6), (1, 8)).map((a, b) => Seq(BigInt(a), BigInt(b))))
  }

  test("a bound position answers one row") {
    val kb = fixture
    val sym = kb.tryResolveSymbol("p").getOrElse(fail("missing p"))
    val goal = kb.alloc(Term.Fn(sym, IArray(kb.alloc(Term.Const(Literal.IntLit(1L)))), IArray.empty))
    assertEquals(SearchStream.resolve(kb, goal).allSolutions(kb).length, 1)
  }
