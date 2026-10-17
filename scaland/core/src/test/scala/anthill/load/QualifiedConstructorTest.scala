package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, Var}
import anthill.resolve.SearchStream

/** A constructor's qualified name is the reference its one-segment name is (§6.7; user,
  * 2026-10-17): `fact holds(Colour.red)` holds `red`'s symbol, as `fact plain(red)` does, so
  * a goal writing either spelling finds either fact. Rustland's twin is
  * `wi_9wvt7_qualified_constructor_test`.
  *
  * FAILS with the data-slot reading in `Loader.reallocTerm` backed out: the fact holds the
  * `field_access` chain, and `byShort` and `sameTerm` answer nothing. */
class QualifiedConstructorTest extends munit.FunSuite:

  private def answers(kb: KnowledgeBase, qn: String, arity: Int)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val args = IArray.fill(arity)(kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("x"))))))
    val goal = if arity == 0 then kb.alloc(Term.Ref(sym)) else kb.alloc(Term.Fn(sym, args, IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  test("a fact holding a constructor's qualified name holds the constructor") {
    val kb = LoadFixture.loaded(
      """namespace zzqc
        |  sort Colour
        |    entity red
        |    entity green
        |  end
        |  fact holds(Colour.red)
        |  fact plain(red)
        |  rule byShort :- holds(red)
        |  rule byQualified :- plain(Colour.red)
        |  rule sameTerm(?x) :- holds(?x), plain(?x)
        |end
        |""".stripMargin,
      "qualified_ctor.anthill",
    )
    assertEquals(answers(kb, "zzqc.byShort", 0), 1)
    assertEquals(answers(kb, "zzqc.byQualified", 0), 1)
    assertEquals(answers(kb, "zzqc.sameTerm", 1), 1)
  }
