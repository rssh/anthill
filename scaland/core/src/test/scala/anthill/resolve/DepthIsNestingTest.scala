package anthill.resolve

import anthill.codegen.scala.StdlibFixture
import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, Var}

/** WI-20261115-0WT09 — DEPTH IS NESTING, AND FUEL IS A SEPARATE COUNTER, rustland's
  * `wi_0wt09_depth_is_nesting_test` on this carrier. A clause body is one deeper than the goal
  * the clause answers and every other goal keeps its depth, so two conjuncts need the depth
  * of the deeper one; `maxSteps` bounds the whole search's work.
  *
  * BACK-OUT, measured 2026-11-16 over the four rows: [D] the per-goal depth reverted to the
  * frame's counter (every step bumping every goal) fails "siblings do not add their depths",
  * and "a shallow exponential search is cut by fuel" too — the counted steps pass the depth
  * limit before the fuel runs out; [F] the fuel check removed fails "a shallow exponential
  * search is cut by fuel" (the doubling search, some 130 000 steps for s^16(z), finds its
  * proof); [T] `stepNaf` reading a cut sub-search as "no proof" again (`/code-review`) fails
  * "a negation over a cut search is undecided" — `not(loopy(1))` succeeds definitely. "an
  * infinite descent is still cut by depth" is the CONTROL, passing under all three. */
class DepthIsNestingTest extends munit.FunSuite:
  private def nat(n: Int): String = (0 until n).foldLeft("z")((inner, _) => s"s(p: $inner)")

  private def fixture: KnowledgeBase = StdlibFixture.kbWith(LoadFixture.parsed(
    s"""sort N
      |  entity z
      |  entity s(p: N)
      |end
      |fact walk(z)
      |rule walk(s(p: ?t)) :- walk(?t)
      |rule both(?a, ?b) :- walk(?a), walk(?b)
      |rule walkEight(1) :- walk(${nat(8)})
      |rule bothAlone(1) :- both(${nat(8)}, z)
      |rule bothTwice(1) :- both(${nat(8)}, ${nat(8)})
      |fact tree(z)
      |rule tree(s(p: ?n)) :- tree(?n), tree(?n)
      |rule treeShallow(1) :- tree(${nat(5)})
      |rule treeDeep(1) :- tree(${nat(16)})
      |rule loopy(1) :- loopy(1)
      |rule notLoopy(1) :- not(loopy(1))
      |""".stripMargin, "depth-is-nesting.anthill"))

  /** A stream over `name(?answer)` at `config`, with its solutions drained. */
  private def drained(kb: KnowledgeBase, name: String, config: ResolveConfig)
      : (Int, ResolveStats) =
    val sym = kb.tryResolveSymbol(name).getOrElse(fail(s"missing fixture predicate $name"))
    val v = kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("answer")))))
    val goal = kb.alloc(Term.Fn(sym, IArray(v), IArray.empty))
    val stream = SearchStream.resolve(kb, goal, config)
    val solutions = stream.allSolutions(kb)
    (solutions.length, stream.stats)

  /** The smallest `maxDepth` at which `name(1)` holds. */
  private def depthNeeded(kb: KnowledgeBase, name: String): Int =
    (0 to 200).find(d => drained(kb, name, ResolveConfig(maxDepth = d))._1 > 0)
      .getOrElse(fail(s"$name does not hold at any depth up to 200"))

  test("siblings do not add their depths") {
    val kb = fixture
    val one = depthNeeded(kb, "walkEight")
    val alone = depthNeeded(kb, "bothAlone")
    val twice = depthNeeded(kb, "bothTwice")
    assertEquals(alone, one + 1, "`both`'s clause is one level above the walks")
    assertEquals(twice, alone, s"the second walk adds no depth: $alone for one, $twice for two")
  }

  test("a shallow exponential search is cut by fuel") {
    val kb = fixture
    val config = ResolveConfig(maxSteps = 10000L)
    assertEquals(drained(kb, "treeShallow", config)._1, 1, "s^5(z) fits the fuel")
    val (found, stats) = drained(kb, "treeDeep", config)
    assertEquals(found, 0, "no proof within 10 000 steps")
    assert(stats.truncated && stats.outOfFuel, s"cut by fuel: $stats")
    assert(stats.steps <= 10000L, s"the fuel is the limit: ${stats.steps} steps")
  }

  test("a negation over a cut search is undecided, never a refutation") {
    // `not(loopy(1))`: `loopy`'s search is cut at its depth limit, so it proves nothing — no
    // DEFINITE answer, and the search is incomplete. FAILS with the truncated sub-search read
    // as "no proof" (`not(P)` succeeding definitely, the behaviour before `/code-review`).
    val kb = fixture
    val sym = kb.tryResolveSymbol("notLoopy").getOrElse(fail("missing fixture predicate notLoopy"))
    val v = kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("answer")))))
    val goal = kb.alloc(Term.Fn(sym, IArray(v), IArray.empty))
    val stream = SearchStream.resolve(kb, goal, ResolveConfig())
    val solutions = stream.allSolutions(kb)
    assert(solutions.forall(_.residual.nonEmpty), s"no definite answer: $solutions")
    assert(stream.stats.truncated, s"the search is incomplete: ${stream.stats}")
  }

  test("an infinite descent is still cut by depth") {
    val kb = fixture
    val (found, stats) = drained(kb, "loopy", ResolveConfig())
    assertEquals(found, 0, "loopy has no proof")
    assert(stats.truncated && !stats.outOfFuel, s"cut by depth, not by fuel: $stats")
  }
