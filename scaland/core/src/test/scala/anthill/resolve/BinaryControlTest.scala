package anthill.resolve

import anthill.codegen.scala.StdlibFixture
import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Literal, Term, Var}

/** WI-373AW: capability rows fail with binary-control dispatch backed out.
  * Comma controls pass either way. */
class BinaryControlTest extends munit.FunSuite:
  private def fixture: KnowledgeBase = StdlibFixture.kbWith(LoadFixture.parsed(
    """fact left(1)
      |fact left(2)
      |fact right(3)
      |fact keep(2)
      |fact keep(3)
      |rule empty(?x) :- left(9)
      |rule first(?x) :- left(?x) or empty(?x)
      |rule second(?x) :- empty(?x) or right(?x)
      |rule neither(?x) :- empty(?x) or empty(?x)
      |rule both(?x) :- left(?x) or right(?x)
      |rule binaryTail(?x) :- left(?x) or right(?x), keep(?x)
      |rule nested(?x) :- (empty(?x) or left(?x)) or right(?x)
      |rule incoming(?x) :- keep(?x), left(?x) or right(?x)
      |rule duplicate(?x) :- right(?x) or right(?x)
      |rule andTail(?x) :- left(?x) and keep(?x), keep(?x)
      |rule together(?x) :- left(?x) and keep(?x)
      |rule failLeft(?x) :- empty(?x) and right(?x)
      |rule failRight(?x) :- left(?x) and empty(?x)
      |rule comma(?x) :- left(?x), keep(?x)
      |rule delayed(?x) :- not(empty(?x)) and right(?x)
      |rule direct(?x) :- anthill.kernel.push_choice(left(?x), right(?x))
      |rule directAnd(?x) :- anthill.kernel.push_and(left(?x), keep(?x))
      |rule malformed(1) :- anthill.kernel.push_choice(left(1))
      |rule malformedAnd(1) :- anthill.kernel.push_and
      |""".stripMargin, "binary-control.anthill"))

  private def values(kb: KnowledgeBase, name: String): Seq[BigInt] =
    val sym = kb.tryResolveSymbol(name).getOrElse(fail(s"missing fixture predicate $name"))
    val v = kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("answer")))))
    val goal = kb.alloc(Term.Fn(sym, IArray(v), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).toSeq.map { sol =>
      assertEquals(sol.residual, IndexedSeq.empty)
      kb.getTerm(kb.reify(v, sol.subst)) match
        case Term.Const(Literal.IntLit(n)) => n
        case other => fail(s"expected a bound integer, got $other")
    }

  test("choice exhausts branches in order with independent bindings and a shared tail") {
    val kb = fixture
    for (name, expected) <- Seq(
      "first" -> Seq(1, 2), "second" -> Seq(3), "neither" -> Seq.empty,
      "both" -> Seq(1, 2, 3), "binaryTail" -> Seq(2, 3), "nested" -> Seq(1, 2, 3),
      "direct" -> Seq(1, 2, 3), "duplicate" -> Seq(3, 3),
      "comma" -> Seq(2)) do
      assertEquals(values(kb, name), expected.map(BigInt(_)), name)
  }

  test("choice inherits bindings established before the split") {
    // Fact-index order for keep is unspecified; branch order is asserted above.
    assertEquals(values(fixture, "incoming").sorted, Seq(BigInt(2), BigInt(3)))
  }

  test("conjunction shares bindings, backtracks and rotates delayed goals") {
    val kb = fixture
    for (name, expected) <- Seq(
      "together" -> Seq(2), "failLeft" -> Seq.empty, "failRight" -> Seq.empty,
      "delayed" -> Seq(3), "directAnd" -> Seq(2), "andTail" -> Seq(2), "comma" -> Seq(2)) do
      assertEquals(values(kb, name), expected.map(BigInt(_)), name)
  }

  test("comma conjunction is the control and passes without binary dispatch") {
    assertEquals(values(fixture, "comma"), Seq(BigInt(2)))
  }

  test("malformed binary primitives report an error") {
    val kb = fixture
    for name <- Seq("malformed", "malformedAnd") do
      val err = intercept[IllegalArgumentException](values(kb, name))
      assert(err.getMessage.contains("exactly two positional goals"))
  }
