package anthill.load

import anthill.codegen.scala.StdlibFixture
import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, Var}
import anthill.resolve.SearchStream

/** WI-20261012-TCSGT (rustland's ticket) — a structural type written as an entry of a
  * bracket in a term is the type it is: `fact holds(Box[V = (Int64) -> Int64])`.
  *
  * THERE IS NO SCALAND FIX, AND THIS FILE IS THE MEASUREMENT THAT SAYS SO. Rustland's
  * converter read a tuple type and an arrow type in that slot as a name spelled with the
  * entry's text, and the load was refused. Here the parser lowers a bracket's entry as
  * the type it parses as (`AnthillParser.typeExprToRef`, the one lowering a type takes in
  * every position), so the fact stores the type's term and a goal that writes the same
  * type matches it. Scaland drops operation bodies at load (WI-1007), so the rows are the
  * clause's own term: a fact, a goal, a rule's head.
  *
  * JRV1T: use the stdlib fixture because arrow lowering names its TypeExtractor
  * and EffectExpression constructors; unresolved dotted references are refused.
  *
  * Each row is a PAIR: the goal that writes the stored entry answers, and the goal that
  * writes another entry of the same shape does not — so an answer is the entry's and not
  * the bracket's.
  */
class StructuralBracketEntryTest extends munit.FunSuite:

  /** Solutions of `<qn>(?x)`, with the goal built on the resolved SYMBOL so a clause that
    * landed elsewhere counts zero rather than silently matching. */
  private def answers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.freshVar(kb.intern("x"))
    val goal = kb.alloc(Term.Fn(sym, IArray(kb.alloc(Term.Var(Var.Global(v)))), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  /** tag, the stored entry, another entry of its shape. */
  private val shapes = Seq(
    ("Arrow", "(Int64) -> Int64", "(Int64) -> String"),
    ("Nullary", "() -> Int64", "() -> String"),
    ("Named", "(a: Int64, b: Int64)", "(a: Int64, b: String)"),
    ("Positional", "(Int64, String)", "(Int64, Int64)"),
  )

  test("a fact holding a structural entry is matched by the goal that writes it") {
    for (tag, entry, other) <- shapes do
      val ns = s"zzTcsgt$tag"
      val kb = StdlibFixture.kbWith(LoadFixture.parsed(
        s"""namespace $ns
           |  import anthill.prelude.{Int64, String}
           |  sort Box[V]
           |  end
           |  fact holds(Box[V = $entry])
           |  rule same(1)  :- holds(Box[V = $entry])
           |  rule other(1) :- holds(Box[V = $other])
           |  rule down(1)  :- holdsDown(Box[V = Box[V = $entry]])
           |  fact holdsDown(Box[V = Box[V = $entry]])
           |  rule hd(Box[V = $entry]) :- holds(Box[V = $entry])
           |  rule viaHead(1) :- hd(Box[V = $entry])
           |end""".stripMargin,
        s"tcsgt$tag.anthill",
      ))
      assertEquals(answers(kb, s"$ns.same"), 1, s"$tag: the goal that writes the stored entry")
      assertEquals(answers(kb, s"$ns.other"), 0, s"$tag: a goal that writes another entry")
      assertEquals(answers(kb, s"$ns.down"), 1, s"$tag: one bracket down")
      assertEquals(answers(kb, s"$ns.viaHead"), 1, s"$tag: a rule's head holds the entry")
  }

  test("a variable in the entry's place, and one inside it, bind") {
    val kb = StdlibFixture.kbWith(LoadFixture.parsed(
      """namespace zzTcsgtVar
        |  import anthill.prelude.{Int64, String}
        |  sort Box[V]
        |  end
        |  fact holds(Box[V = (Int64) -> String])
        |  rule whole(?v)  :- holds(Box[V = ?v])
        |  rule inside(?r) :- holds(Box[V = (Int64) -> ?r])
        |  rule wrong(?r)  :- holds(Box[V = (String) -> ?r])
        |end""".stripMargin,
      "tcsgtvar.anthill",
    ))
    assertEquals(answers(kb, "zzTcsgtVar.whole"), 1)
    assertEquals(answers(kb, "zzTcsgtVar.inside"), 1)
    assertEquals(answers(kb, "zzTcsgtVar.wrong"), 0)
  }
