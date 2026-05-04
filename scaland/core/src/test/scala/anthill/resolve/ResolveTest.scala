package anthill.resolve

import anthill.kb.KnowledgeBase
import anthill.term.{Term, TermId, VarId, Literal}
import anthill.subst.Substitution
import scala.collection.mutable.ArrayBuffer

class ResolveTest extends munit.FunSuite:

  test("basic fact resolution") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Fact")
    val domain = kb.makeNameTerm("test")
    val fSym = kb.intern("f")
    val v = kb.alloc(Term.Const(Literal.IntLit(42)))
    val fact = kb.alloc(Term.Fn(fSym, IArray(v), IArray.empty))
    kb.assertFact(fact, sort, domain)

    // Query: f(?x)
    val xSym = kb.intern("x")
    val vid = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(vid))
    val pattern = kb.alloc(Term.Fn(fSym, IArray(varX), IArray.empty))

    val stream = SearchStream.resolve(kb, pattern)
    val solutions = stream.allSolutions(kb)
    assertEquals(solutions.length, 1)
    assertEquals(solutions(0).subst.resolve(vid).map(TermId.raw), Some(TermId.raw(v)))
    assert(solutions(0).residual.isEmpty)
  }

  test("multiple fact results") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Fact")
    val domain = kb.makeNameTerm("test")
    val fSym = kb.intern("f")
    val v1 = kb.alloc(Term.Const(Literal.IntLit(1)))
    val v2 = kb.alloc(Term.Const(Literal.IntLit(2)))
    val f1 = kb.alloc(Term.Fn(fSym, IArray(v1), IArray.empty))
    val f2 = kb.alloc(Term.Fn(fSym, IArray(v2), IArray.empty))
    kb.assertFact(f1, sort, domain)
    kb.assertFact(f2, sort, domain)

    val xSym = kb.intern("x")
    val vid = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(vid))
    val pattern = kb.alloc(Term.Fn(fSym, IArray(varX), IArray.empty))

    val solutions = SearchStream.resolve(kb, pattern).allSolutions(kb)
    assertEquals(solutions.length, 2)
    val bindings = solutions.map(_.subst.resolve(vid).map(TermId.raw)).toSet
    assert(bindings.contains(Some(TermId.raw(v1))))
    assert(bindings.contains(Some(TermId.raw(v2))))
  }

  test("backward chaining with rule") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Sort")
    val domain = kb.makeNameTerm("test")
    val parentSym = kb.intern("parent")
    val grandparentSym = kb.intern("grandparent")

    val alice = kb.alloc(Term.Const(Literal.StringLit("alice")))
    val bob = kb.alloc(Term.Const(Literal.StringLit("bob")))
    val charlie = kb.alloc(Term.Const(Literal.StringLit("charlie")))

    // Facts: parent("alice", "bob"), parent("bob", "charlie")
    val f1 = kb.alloc(Term.Fn(parentSym, IArray(alice, bob), IArray.empty))
    val f2 = kb.alloc(Term.Fn(parentSym, IArray(bob, charlie), IArray.empty))
    kb.assertFact(f1, sort, domain)
    kb.assertFact(f2, sort, domain)

    // Rule: grandparent(?x, ?z) :- parent(?x, ?y), parent(?y, ?z)
    val xSym = kb.intern("x"); val ySym = kb.intern("y"); val zSym = kb.intern("z")
    val vx = kb.freshVar(xSym); val vy = kb.freshVar(ySym); val vz = kb.freshVar(zSym)
    val varX = kb.alloc(Term.Var(vx)); val varY = kb.alloc(Term.Var(vy)); val varZ = kb.alloc(Term.Var(vz))

    val head = kb.alloc(Term.Fn(grandparentSym, IArray(varX, varZ), IArray.empty))
    val b1 = kb.alloc(Term.Fn(parentSym, IArray(varX, varY), IArray.empty))
    val b2 = kb.alloc(Term.Fn(parentSym, IArray(varY, varZ), IArray.empty))
    kb.assertRule(head, IndexedSeq(b1, b2), sort, domain)

    // Query: grandparent(?a, ?b)
    val aSym = kb.intern("a"); val bSym = kb.intern("b")
    val va = kb.freshVar(aSym); val vb = kb.freshVar(bSym)
    val varA = kb.alloc(Term.Var(va)); val varB = kb.alloc(Term.Var(vb))
    val query = kb.alloc(Term.Fn(grandparentSym, IArray(varA, varB), IArray.empty))

    val solutions = SearchStream.resolve(kb, query).allSolutions(kb)
    assertEquals(solutions.length, 1)

    // Check: grandparent("alice", "charlie")
    val sol = solutions(0)
    val aBinding = sol.subst.resolve(va).map(t => kb.getTerm(t))
    val bBinding = sol.subst.resolve(vb).map(t => kb.getTerm(t))
    assertEquals(aBinding, Some(Term.Const(Literal.StringLit("alice"))))
    assertEquals(bBinding, Some(Term.Const(Literal.StringLit("charlie"))))
  }

  test("backtracking - no matching rule") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Sort")
    val domain = kb.makeNameTerm("test")
    val fSym = kb.intern("f")
    val v = kb.alloc(Term.Const(Literal.IntLit(42)))
    val fact = kb.alloc(Term.Fn(fSym, IArray(v), IArray.empty))
    kb.assertFact(fact, sort, domain)

    // Query for a different functor
    val gSym = kb.intern("g")
    val xSym = kb.intern("x")
    val vid = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(vid))
    val pattern = kb.alloc(Term.Fn(gSym, IArray(varX), IArray.empty))

    val solutions = SearchStream.resolve(kb, pattern).allSolutions(kb)
    assert(solutions.isEmpty)
  }

  test("depth limit prevents infinite recursion") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Sort")
    val domain = kb.makeNameTerm("test")
    val fSym = kb.intern("f")
    val xSym = kb.intern("x")
    val vx = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(vx))

    // Rule: f(?x) :- f(?x)  (infinite loop)
    val head = kb.alloc(Term.Fn(fSym, IArray(varX), IArray.empty))
    val bodyLit = kb.alloc(Term.Fn(fSym, IArray(varX), IArray.empty))
    kb.assertRule(head, IndexedSeq(bodyLit), sort, domain)

    val aSym = kb.intern("a")
    val va = kb.freshVar(aSym)
    val varA = kb.alloc(Term.Var(va))
    val query = kb.alloc(Term.Fn(fSym, IArray(varA), IArray.empty))

    val config = ResolveConfig(maxDepth = 10)
    val solutions = SearchStream.resolve(kb, query, config).allSolutions(kb)
    // Should terminate (depth limit) with no solutions
    assert(solutions.isEmpty)
  }

  test("lazy list interface") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Fact")
    val domain = kb.makeNameTerm("test")
    val fSym = kb.intern("f")
    for i <- 1 to 5 do
      val v = kb.alloc(Term.Const(Literal.IntLit(i.toLong)))
      val fact = kb.alloc(Term.Fn(fSym, IArray(v), IArray.empty))
      kb.assertFact(fact, sort, domain)

    val xSym = kb.intern("x")
    val vid = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(vid))
    val pattern = kb.alloc(Term.Fn(fSym, IArray(varX), IArray.empty))

    val stream = SearchStream.resolve(kb, pattern)
    val results = stream.toLazyList(kb).take(3).toList
    assertEquals(results.length, 3)
  }

  test("multiple rules and facts combined") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Sort")
    val domain = kb.makeNameTerm("test")
    val colorSym = kb.intern("color")
    val mixSym = kb.intern("mix")

    // Facts
    val red = kb.alloc(Term.Const(Literal.StringLit("red")))
    val blue = kb.alloc(Term.Const(Literal.StringLit("blue")))
    val purple = kb.alloc(Term.Const(Literal.StringLit("purple")))

    val fc1 = kb.alloc(Term.Fn(colorSym, IArray(red), IArray.empty))
    val fc2 = kb.alloc(Term.Fn(colorSym, IArray(blue), IArray.empty))
    val fc3 = kb.alloc(Term.Fn(colorSym, IArray(purple), IArray.empty))
    kb.assertFact(fc1, sort, domain)
    kb.assertFact(fc2, sort, domain)
    kb.assertFact(fc3, sort, domain)

    // Rule: mix(?a, ?b, "purple") :- color(?a), color(?b)
    // (simplified — doesn't check a=red, b=blue)
    val aSym = kb.intern("a"); val bSym = kb.intern("b")
    val va = kb.freshVar(aSym); val vb = kb.freshVar(bSym)
    val varA = kb.alloc(Term.Var(va)); val varB = kb.alloc(Term.Var(vb))

    val mixHead = kb.alloc(Term.Fn(mixSym, IArray(varA, varB, purple), IArray.empty))
    val body1 = kb.alloc(Term.Fn(colorSym, IArray(varA), IArray.empty))
    val body2 = kb.alloc(Term.Fn(colorSym, IArray(varB), IArray.empty))
    kb.assertRule(mixHead, IndexedSeq(body1, body2), sort, domain)

    // Query: mix(?x, ?y, "purple")
    val xSym = kb.intern("x"); val ySym = kb.intern("y")
    val vx = kb.freshVar(xSym); val vy = kb.freshVar(ySym)
    val varX = kb.alloc(Term.Var(vx)); val varY = kb.alloc(Term.Var(vy))
    val query = kb.alloc(Term.Fn(mixSym, IArray(varX, varY, purple), IArray.empty))

    val solutions = SearchStream.resolve(kb, query).allSolutions(kb)
    // 3 colors × 3 colors = 9 combinations
    assertEquals(solutions.length, 9)
  }

  test("peano naturals - structured answer_links (issue #1)") {
    // Regression test for GitHub issue #1:
    // with_fresh_vars must rename variables inside structured answer_links terms.
    //
    // fact nat(zero())
    // rule nat(succ(?n)) :- nat(?n)
    // query nat(?x)
    //
    // Before fix: succ(?n_unbound) — chain is severed.
    // After fix: succ(zero()), succ(succ(zero())), etc.
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Sort")
    val domain = kb.makeNameTerm("test")

    val natSym = kb.intern("nat")
    val zeroSym = kb.intern("zero")
    val succSym = kb.intern("succ")

    // fact: nat(zero())
    val zeroTerm = kb.alloc(Term.Fn(zeroSym, IArray.empty, IArray.empty))
    val natZero = kb.alloc(Term.Fn(natSym, IArray(zeroTerm), IArray.empty))
    kb.assertFact(natZero, sort, domain)

    // rule: nat(succ(?n)) :- nat(?n)
    val nSym = kb.intern("n")
    val vn = kb.freshVar(nSym)
    val varN = kb.alloc(Term.Var(vn))
    val succN = kb.alloc(Term.Fn(succSym, IArray(varN), IArray.empty))
    val natSuccN = kb.alloc(Term.Fn(natSym, IArray(succN), IArray.empty))
    val bodyNatN = kb.alloc(Term.Fn(natSym, IArray(varN), IArray.empty))
    kb.assertRule(natSuccN, IndexedSeq(bodyNatN), sort, domain)

    // query: nat(?x)
    val xSym = kb.intern("x")
    val vx = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(vx))
    val query = kb.alloc(Term.Fn(natSym, IArray(varX), IArray.empty))

    val config = ResolveConfig(maxDepth = 5)
    val solutions = SearchStream.resolve(kb, query, config).allSolutions(kb)

    // Reify each binding and count succ depth
    def succDepth(tid: TermId): Int =
      kb.getTerm(tid) match
        case fn: Term.Fn if kb.resolveSym(fn.functor) == "succ" && fn.posArgs.length == 1 =>
          1 + succDepth(fn.posArgs(0))
        case fn: Term.Fn if kb.resolveSym(fn.functor) == "zero" => 0
        case Term.Var(_) => -1 // unbound variable — this is the bug
        case _ => -2

    val depths = solutions.map { sol =>
      sol.subst.resolve(vx).map { t =>
        val reified = kb.reify(t, sol.subst)
        succDepth(reified)
      }.getOrElse(-3)
    }

    // Key invariant: NO solutions should have unbound variables (depth = -1)
    // Before the fix, recursive solutions had depth -1 (succ(?n_unbound))
    for (d, i) <- depths.zipWithIndex do
      assert(d >= 0, s"solution $i has unbound variable (depth=$d), issue #1 regression")

    // Should have distinct depths (zero, succ(zero), succ(succ(zero)), ...)
    val validDepths = depths.filter(_ >= 0).toSet
    assert(validDepths.contains(0), "should have zero() solution")
    assert(validDepths.contains(1), "should have succ(zero()) solution")
    assert(validDepths.contains(2), "should have succ(succ(zero())) solution")
  }

  // ── WI-172: lazy-substitution acceptance ────────────────────

  /** n-body fixture: `big(?x_0, ?x_1, …, ?x_{n-1}) :- f_0(?x_0), …, f_{n-1}(?x_{n-1})`
    * with one ground fact per body goal. Mirrors rust's `build_n_body_fixture`. */
  private def buildNBodyFixture(n: Int): (KnowledgeBase, TermId) =
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Sort")
    val domain = kb.makeNameTerm("test")
    val bigSym = kb.intern("big")

    val fSyms = (0 until n).map(i => kb.intern(s"f_$i"))
    val vals = (0 until n).map(i => kb.alloc(Term.Const(Literal.StringLit(s"v$i"))))
    val varTerms = (0 until n).map { i =>
      val sym = kb.intern(s"x$i")
      val vid = kb.freshVar(sym)
      kb.alloc(Term.Var(vid))
    }

    val head = kb.alloc(Term.Fn(bigSym, IArray.from(varTerms), IArray.empty))
    val body = (0 until n).map { i =>
      kb.alloc(Term.Fn(fSyms(i), IArray(varTerms(i)), IArray.empty))
    }
    kb.assertRule(head, body.toIndexedSeq, sort, domain)

    for i <- 0 until n do
      val fact = kb.alloc(Term.Fn(fSyms(i), IArray(vals(i)), IArray.empty))
      kb.assertFact(fact, sort, domain)

    val query = kb.alloc(Term.Fn(bigSym, IArray.from(vals), IArray.empty))
    (kb, query)

  test("WI-172: ResolveStats populated on n-body query (smoke)") {
    val (kb, query) = buildNBodyFixture(50)
    val stream = SearchStream.resolve(kb, query, ResolveConfig(maxSolutions = 1))
    val sols = stream.allSolutions(kb)
    assertEquals(sols.length, 1)
    assert(stream.stats.steps > 0, "step counter must increment")
    assert(stream.stats.goalSelections > 0,
      "goalSelections must increment on every stepInit goal selection")
  }

  test("WI-172: goalSelections scales linearly with body size (acceptance)") {
    val small = 100
    val large = 400
    val cfg = ResolveConfig(maxSolutions = 1)

    def run(n: Int): ResolveStats =
      val (kb, query) = buildNBodyFixture(n)
      val stream = SearchStream.resolve(kb, query, cfg)
      val _ = stream.allSolutions(kb)
      stream.stats

    val sSmall = run(small)
    val sLarge = run(large)

    // Linear bound: goalSelections must stay below 8·n. Pre-WI-172 the
    // equivalent work (eager applySubst-each over remaining goals)
    // scaled ~n²/2 ≈ 5_000 (n=100) and ~80_000 (n=400) — far above this.
    assert(sLarge.goalSelections < 8L * large,
      s"goalSelections=${sLarge.goalSelections} for n=$large should be O(n), not O(n²)")

    // Ratio sanity: large/small ≤ ~6× for linear growth (constant slack).
    // Quadratic gives ~16×.
    val ratio = sLarge.goalSelections.toDouble / math.max(1L, sSmall.goalSelections).toDouble
    assert(ratio < 6.0,
      f"growth ratio $ratio%.1f× between n=$small and n=$large indicates super-linear scaling (quadratic ≈ 16×)")
  }
