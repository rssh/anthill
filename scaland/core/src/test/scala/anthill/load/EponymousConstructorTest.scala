package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, Var}
import anthill.resolve.SearchStream

/** §6.3 (WI-926) — AN EPONYMOUS CONSTRUCTOR IS ITS SORT. `sort Foo … entity Foo(…) … end`
  * writes `Foo` once and defines ONE symbol, the sort's, playing `Entity` too — which is
  * what the free-standing `entity Foo(…)` is from the other spelling. Rustland has had it
  * since WI-926; scaland defined a nested `Foo.Foo` beside the sort until WI-20261020-80VNX,
  * so the name written inside the sort body and the name written outside it were two
  * symbols, and a fact over one was not found by a goal over the other.
  *
  * BACKED OUT (`Loader.eponymousSortSymbol` answering `None`, measured): `inside` and
  * `outside` answer 1 each instead of 2, the field schema is not the sort's, and an
  * `entity_of` fact names the sort as its own nested constructor's parent. */
class EponymousConstructorTest extends munit.FunSuite:

  private def answers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.freshVar(kb.intern("x"))
    val goal = kb.alloc(Term.Fn(sym, IArray(kb.alloc(Term.Var(Var.Global(v)))), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  test("the name inside the sort body and the name outside it are one symbol") {
    val kb = LoadFixture.loaded(
      """namespace zzep
        |  import anthill.prelude.Int64
        |  sort Foo
        |    entity Foo(x: Int64)
        |    fact Foo(x: 1)
        |    rule inside(?x) :- Foo(x: ?x)
        |  end
        |  fact Foo(x: 2)
        |  rule outside(?x) :- Foo(x: ?x)
        |end
        |""".stripMargin,
      "eponymous.anthill",
    )
    assertEquals(answers(kb, "zzep.Foo.inside"), 2, "the goal inside the body finds both facts")
    assertEquals(answers(kb, "zzep.outside"), 2, "and so does the goal outside it")
    assert(!kb.hasQualifiedName("zzep.Foo.Foo"), "no nested `Foo.Foo` is defined")
    val foo = kb.resolveSymbol("zzep.Foo")
    assertEquals(
      kb.entityFieldNames(foo).map(_.map(kb.resolveSym)), Some(IndexedSeq("x")),
      "the field schema is the sort's own")
    val entityOf = kb.byFunctor(kb.intern("entity_of")).map(kb.ruleHead)
    assert(
      !entityOf.exists(h => kb.getTerm(h) match
        case fn: Term.Fn => fn.posArgs.exists(a => kb.getTerm(a) == Term.Ref(foo))
        case _ => false),
      "an eponymous constructor is not a constructor OF its sort, so no `entity_of` names it")
  }
