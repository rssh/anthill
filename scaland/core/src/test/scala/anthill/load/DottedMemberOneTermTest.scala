package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, Var}
import anthill.resolve.SearchStream

/** A dotted name's member is the name it spells (§6.7, "The member of the chain is read as a
  * name"), never the symbol the word resolves to where the chain is written: so one written
  * chain is one term in every namespace, and a goal meets the fact holding it from anywhere.
  * Rustland's twin is `wi_tbz4t_dotted_member_one_term_test`.
  *
  * FAIL with the member read in `Loader.reallocTerm` backed out (the member resolved in scope
  * by its `Ref` arm), each measured: `fact holds(zzdm.inner.seven)` written in `zzdm.outer`
  * holds `inner` as the namespace `zzdm.inner`, which the goal written in `zzdm2` does not
  * spell, and the bare namespace name the same; a member imported where the goal is written is
  * held as the imported symbol. The control passes either way, by design: goal and fact written
  * in one namespace. */
class DottedMemberOneTermTest extends munit.FunSuite:

  private def answers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val arg = kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("x")))))
    SearchStream.resolve(kb, kb.alloc(Term.Fn(sym, IArray(arg), IArray.empty))).allSolutions(kb).length

  private lazy val kb = LoadFixture.loaded(
    """namespace zzdm.inner
      |  import anthill.prelude.Int64
      |  operation seven() -> Int64 = 7
      |  sort S
      |    operation eight() -> Int64 = 8
      |  end
      |end
      |namespace zzdm.outer
      |  fact holds(zzdm.inner.seven)
      |  fact holdsNs(zzdm.inner)
      |  rule viaOuter(1) :- holds(zzdm.inner.seven)
      |end
      |namespace zzdm2
      |  import zzdm.outer.{holds, holdsNs}
      |  rule viaOther(1) :- holds(zzdm.inner.seven)
      |  rule viaNs(1) :- holdsNs(zzdm.inner)
      |  fact holdsS(zzdm.inner.S.eight)
      |end
      |namespace zzdm3
      |  import zzdm2.holdsS
      |  import zzdm.inner.S.eight
      |  rule viaImported(1) :- holdsS(zzdm.inner.S.eight)
      |end
      |""".stripMargin,
    "dotted_member.anthill",
  )

  test("control: goal and fact written in one namespace") {
    assertEquals(answers(kb, "zzdm.outer.viaOuter"), 1)
  }

  test("a goal written where the receiver's segment names nothing meets the fact") {
    assertEquals(answers(kb, "zzdm2.viaOther"), 1)
  }

  test("the bare namespace name is met from another namespace") {
    assertEquals(answers(kb, "zzdm2.viaNs"), 1)
  }

  test("a member imported where the goal is written meets the fact") {
    assertEquals(answers(kb, "zzdm3.viaImported"), 1)
  }
