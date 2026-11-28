package anthill.resolve

import anthill.codegen.scala.StdlibFixture
import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, Var}

/** WI-20261127-AGR9S (proposal 076 Stage A) — the continuation is a linked chain of scopes,
  * rustland's `wi_agr9s_linked_continuation_test` on this carrier. NO CHANGE OF BEHAVIOUR: these
  * rows hold with the flat copied resolvent too, and are what the representation must keep.
  *
  * - "a side of a choice is no call": DEPTH IS NOT HOW DEEPLY SCOPES ARE NESTED. Each side of
  *   `push_choice` is a scope of its own, at the depth of the goal it splits, so it is asked at
  *   `maxDepth = 0`. FAILS where a scope's depth is counted from its nesting (the side one
  *   deeper). Its CONTROL, a clause body at `maxDepth = 0`, is refused either way.
  * - "a resolvent that grows a goal a level answers at depth": a body with a goal after its
  *   recursive call keeps one scope a level, each sharing its caller's. The answer and its one
  *   proof are the same as on the copied resolvent; what changed is memory, which is measured
  *   on the CLI (`docs/measurements/076-stage-a/`), not here.
  * - "goals that waited come round in the order they waited": the rotation goes behind every
  *   scope and comes back in order once the front is spent (the residual's order).
  *
  * BACK-OUT, measured 2026-11-28: a side of `push_choice` opened one deeper fails the first row
  * (its control passes); the waiting goals turned round unreversed fail the third (two waiting
  * goals cannot tell, so it has three). The second passes either way, by design. */
class LinkedContinuationTest extends munit.FunSuite:
  private def nat(n: Int): String = (0 until n).foldLeft("z")((inner, _) => s"s(p: $inner)")

  private def fixture: KnowledgeBase = StdlibFixture.kbWith(LoadFixture.parsed(
    s"""sort N
      |  entity z
      |  entity s(p: N)
      |end
      |fact left(1)
      |fact ok(1)
      |rule viaRule(?x) :- left(?x)
      |rule split(?x) :- left(?x)
      |fact chain(z)
      |rule chain(s(p: ?n)) :- chain(?n), ok(1)
      |rule deep(1) :- chain(${nat(300)})
      |rule waits(?x) :- not(left(?x)), not(ok(?x)), not(chain(?x))
      |""".stripMargin, "linked-continuation.anthill"))

  private def answers(kb: KnowledgeBase, goal: anthill.term.TermId, config: ResolveConfig) =
    SearchStream.resolve(kb, goal, config).allSolutions(kb).toSeq

  private def call(kb: KnowledgeBase, name: String, arg: anthill.term.TermId) =
    val sym = kb.tryResolveSymbol(name).getOrElse(fail(s"missing fixture predicate $name"))
    kb.alloc(Term.Fn(sym, IArray(arg), IArray.empty))

  private def answerVar(kb: KnowledgeBase) =
    kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("answer")))))

  test("a side of a choice is no call: push_choice answers at maxDepth 0") {
    val kb = fixture
    val choice = kb.tryResolveSymbol("anthill.kernel.push_choice").getOrElse(fail("no push_choice"))
    val x = answerVar(kb)
    val goal = kb.alloc(Term.Fn(choice, IArray(call(kb, "left", x), call(kb, "left", x)), IArray.empty))
    assertEquals(answers(kb, goal, ResolveConfig(maxDepth = 0)).length, 2, "both sides at depth 0")
    // CONTROL: a clause body is one deeper, and is not asked at maxDepth 0.
    assertEquals(answers(kb, call(kb, "viaRule", answerVar(kb)), ResolveConfig(maxDepth = 0)).length, 0)
    assertEquals(answers(kb, call(kb, "viaRule", answerVar(kb)), ResolveConfig(maxDepth = 1)).length, 1)
  }

  test("a resolvent that grows a goal a level answers at depth") {
    val kb = fixture
    val sols = answers(kb, call(kb, "deep", answerVar(kb)), ResolveConfig(maxDepth = 400))
    assertEquals(sols.length, 1)
    assertEquals(sols.head.residual, IndexedSeq.empty)
  }

  test("goals that waited come round in the order they waited") {
    // The three negations wait on `?x`, and each goes behind every other goal: after one lap they
    // are back in the order they were written, which is the residual's order. The rotation
    // queue comes round in waiting order; turned the wrong way, the residual is reversed.
    val kb = fixture
    val x = answerVar(kb)
    val sols = answers(kb, call(kb, "waits", x), ResolveConfig())
    assertEquals(sols.length, 1)
    val heads = sols.head.residual.map(g => kb.getTerm(g) match
      case Term.Fn(_, args, _) => kb.getTerm(args(0)) match
        case Term.Fn(f, _, _) => kb.qualifiedNameOf(f)
        case other => fail(s"unexpected negand $other")
      case other => fail(s"unexpected residual $other"))
    assertEquals(heads.map(_.split('.').last), IndexedSeq("left", "ok", "chain"))
  }
