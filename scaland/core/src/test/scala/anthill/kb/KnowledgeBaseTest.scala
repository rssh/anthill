package anthill.kb

import anthill.term.{Term, TermId, Var, Literal}
import anthill.subst.Substitution

class KnowledgeBaseTest extends munit.FunSuite:

  test("assert and query by sort") {
    val kb = KnowledgeBase()
    val sortAccount = kb.makeNameTerm("Account")
    val domain = kb.makeNameTerm("banking")
    val idSym = kb.intern("account")
    val arg = kb.alloc(Term.Const(Literal.StringLit("A001")))
    val acct = kb.alloc(Term.Fn(idSym, IArray(arg), IArray.empty))
    val fid = kb.assertFact(acct, sortAccount, domain)
    val results = kb.bySort(sortAccount)
    assertEquals(results.length, 1)
  }

  test("entity-of query includes children") {
    val kb = KnowledgeBase()
    val nat = kb.makeNameTerm("Nat")
    val zero = kb.makeNameTerm("zero")
    val domain = kb.makeNameTerm("test")

    kb.registerSort(nat, SortKind.Defined)
    kb.registerSort(zero, SortKind.Constructor)
    kb.registerEntityOf(zero, nat)

    val zeroVal = kb.makeNameTerm("zero")
    val fid = kb.assertFact(zeroVal, zero, domain)

    val results = kb.bySort(nat)
    assertEquals(results.length, 1)
    assert(kb.isEntityOf(zero, nat))
    assert(!kb.isEntityOf(nat, zero))
  }

  test("retract removes from index") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("T")
    val domain = kb.makeNameTerm("d")
    val term = kb.alloc(Term.Const(Literal.IntLit(42)))
    val fid = kb.assertFact(term, sort, domain)
    assertEquals(kb.bySort(sort).length, 1)
    kb.retract(fid)
    assertEquals(kb.bySort(sort).length, 0)
  }

  test("match_term const") {
    val kb = KnowledgeBase()
    val a = kb.alloc(Term.Const(Literal.IntLit(42)))
    val b = kb.alloc(Term.Const(Literal.IntLit(42)))
    val c = kb.alloc(Term.Const(Literal.IntLit(99)))
    assert(kb.matchTerm(a, b).isDefined)
    assert(kb.matchTerm(a, c).isEmpty)
  }

  test("match_term var binds") {
    val kb = KnowledgeBase()
    val xSym = kb.intern("x")
    val vid = kb.freshVar(xSym)
    val varTerm = kb.alloc(Term.Var(Var.Global(vid)))
    val target = kb.alloc(Term.Const(Literal.IntLit(42)))
    val s = kb.matchTerm(varTerm, target).get
    assertEquals(s.resolve(vid).map(TermId.raw), Some(TermId.raw(target)))
  }

  test("match_term var consistency") {
    val kb = KnowledgeBase()
    val xSym = kb.intern("x")
    val vid = kb.freshVar(xSym)
    val varTerm = kb.alloc(Term.Var(Var.Global(vid)))
    val fSym = kb.intern("f")
    val v1 = kb.alloc(Term.Const(Literal.IntLit(1)))
    val v2 = kb.alloc(Term.Const(Literal.IntLit(2)))

    // Pattern: f(?x, ?x), Target: f(1, 1) — should match
    val pattern = kb.alloc(Term.Fn(fSym, IArray(varTerm, varTerm), IArray.empty))
    val targetOk = kb.alloc(Term.Fn(fSym, IArray(v1, v1), IArray.empty))
    assert(kb.matchTerm(pattern, targetOk).isDefined)

    // Target: f(1, 2) — should fail (inconsistent)
    val targetBad = kb.alloc(Term.Fn(fSym, IArray(v1, v2), IArray.empty))
    assert(kb.matchTerm(pattern, targetBad).isEmpty)
  }

  test("nonlinear head doubly concrete unifies (WI-637)") {
    // Mirror of rustland WI-633 `nonlinear_head_doubly_concrete_unifies`.
    // SLD head selection IS unification: the repeated head var `?v` in the
    // fact `unbox0(box(v: ?v), ?v)` binds its two matched query subterms —
    // `some(?x)` and `some(42)` — by UNIFICATION, so `?x = 42`. Before WI-637
    // the discrim leaf double-bound `?v` structurally (some(?x) vs some(42)
    // differ) and dropped the candidate: silent 0 solutions.
    val kb = KnowledgeBase()
    val factSort = kb.makeNameTerm("Fact")
    val domain = kb.makeNameTerm("test")
    val unbox = kb.intern("unbox0")
    val boxSym = kb.intern("box")
    val vField = kb.intern("v")
    val someSym = kb.intern("some")

    // Fact: unbox0(box(v: ?v), ?v) — repeated head var.
    val vv = kb.freshVar(kb.intern("vv"))
    val varV = kb.alloc(Term.Var(Var.Global(vv)))
    val boxV = kb.alloc(Term.Fn(boxSym, IArray.empty, IArray((vField, varV))))
    val head = kb.alloc(Term.Fn(unbox, IArray(boxV, varV), IArray.empty))
    kb.assertFact(head, factSort, domain)

    // Query: unbox0(box(v: some(?x)), some(42)).
    val xv = kb.freshVar(kb.intern("x"))
    val varX = kb.alloc(Term.Var(Var.Global(xv)))
    val someX = kb.alloc(Term.Fn(someSym, IArray(varX), IArray.empty))
    val boxSomeX = kb.alloc(Term.Fn(boxSym, IArray.empty, IArray((vField, someX))))
    val fortyTwo = kb.alloc(Term.Const(Literal.IntLit(42)))
    val some42 = kb.alloc(Term.Fn(someSym, IArray(fortyTwo), IArray.empty))
    val goal = kb.alloc(Term.Fn(unbox, IArray(boxSomeX, some42), IArray.empty))

    val results = kb.query(goal)
    assertEquals(results.length, 1, "repeated head var must unify the two occurrences")
    val (_, s) = results(0)
    assertEquals(
      TermId.raw(kb.reify(varX, s)), TermId.raw(fortyTwo),
      "?x must unify to 42 through the repeated head var"
    )
  }

  test("match_term nonlinear is matching not unification (WI-637)") {
    // Mirror of rustland WI-633 `match_term_nonlinear_is_matching_not_unification`.
    // The boundary the SLD unify path must NOT cross: a nonlinear pattern var
    // `?x` in `f(?x, ?x)` MATCHES only structurally-IDENTICAL target subterms.
    // Against `f(some(?a), some(?b))` with DISTINCT target vars, matchTerm must
    // FAIL — it is one-directional (`unifyRebind = false`); it must NOT unify
    // the two target subterms by binding `?a := ?b`.
    val kb = KnowledgeBase()
    val fSym = kb.intern("f")
    val someSym = kb.intern("some")
    val vid = kb.freshVar(kb.intern("x"))
    val varX = kb.alloc(Term.Var(Var.Global(vid)))
    val pattern = kb.alloc(Term.Fn(fSym, IArray(varX, varX), IArray.empty))

    val someA = kb.alloc(Term.Fn(someSym, IArray(kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("a")))))), IArray.empty))
    val someB = kb.alloc(Term.Fn(someSym, IArray(kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("b")))))), IArray.empty))

    // Target f(some(?a), some(?b)), ?a ≠ ?b — distinct but UNIFIABLE.
    val targetDistinct = kb.alloc(Term.Fn(fSym, IArray(someA, someB), IArray.empty))
    assert(
      kb.matchTerm(pattern, targetDistinct).isEmpty,
      "nonlinear pattern must MATCH (structural identity), not UNIFY distinct target vars"
    )

    // Same structure at both positions (some(?a), some(?a)) → matches.
    val targetSame = kb.alloc(Term.Fn(fSym, IArray(someA, someA), IArray.empty))
    assert(
      kb.matchTerm(pattern, targetSame).isDefined,
      "identical target subterms at the repeated position must match"
    )
  }

  test("nonlinear query var over distinct rule-head vars is a contradiction (WI-637 soundness)") {
    // The boundary the DeBruijn/reflexive-only rule guards: a repeated QUERY var
    // `pair(?n, ?n)` against a RULE whose head has DISTINCT vars
    // `pair(?x, ?y) :- dummy(?x)` must NOT unify `?x := ?y` — those are DeBruijn
    // (reflexive-only), so the candidate is a contradiction (0 solutions), not
    // an unsound extra answer where the body's `?x`/`?y` run decoupled. The SAME
    // head var at both positions (`pair(?x, ?x)`) is consistent → 1 candidate.
    def kbRule(sameVar: Boolean): (KnowledgeBase, TermId) =
      val kb = KnowledgeBase()
      val ruleSort = kb.makeNameTerm("Rule")
      val domain = kb.makeNameTerm("test")
      val pairSym = kb.intern("pair")
      val dummySym = kb.intern("dummy")
      val vx = kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("x")))))
      val vy = if sameVar then vx else kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("y")))))
      val head = kb.alloc(Term.Fn(pairSym, IArray(vx, vy), IArray.empty))
      val body = kb.alloc(Term.Fn(dummySym, IArray(vx), IArray.empty))
      kb.assertRule(head, IndexedSeq(body), ruleSort, domain)
      val vn = kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("n")))))
      val goal = kb.alloc(Term.Fn(pairSym, IArray(vn, vn), IArray.empty))
      (kb, goal)

    val (kbDistinct, goalD) = kbRule(sameVar = false)
    assert(
      kbDistinct.query(goalD).isEmpty,
      "distinct rule-head vars (DeBruijn, reflexive-only) can't unify a repeated query var"
    )

    val (kbSame, goalS) = kbRule(sameVar = true)
    assertEquals(
      kbSame.query(goalS).length, 1,
      "same rule-head var at both positions is consistent with a repeated query var"
    )
  }

  test("query by pattern") {
    val kb = KnowledgeBase()
    val factSort = kb.makeNameTerm("Fact")
    val domain = kb.makeNameTerm("test")
    val parentSym = kb.intern("parent")
    val alice = kb.alloc(Term.Const(Literal.StringLit("alice")))
    val bob = kb.alloc(Term.Const(Literal.StringLit("bob")))
    val charlie = kb.alloc(Term.Const(Literal.StringLit("charlie")))

    val fact1 = kb.alloc(Term.Fn(parentSym, IArray(alice, bob), IArray.empty))
    val fact2 = kb.alloc(Term.Fn(parentSym, IArray(bob, charlie), IArray.empty))
    kb.assertFact(fact1, factSort, domain)
    kb.assertFact(fact2, factSort, domain)

    // Query: parent(?x, "bob")
    val xSym = kb.intern("x")
    val vid = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(Var.Global(vid)))
    val pattern = kb.alloc(Term.Fn(parentSym, IArray(varX, bob), IArray.empty))

    val results = kb.query(pattern)
    assertEquals(results.length, 1)
    val (_, s) = results(0)
    assertEquals(s.resolve(vid).map(TermId.raw), Some(TermId.raw(alice)))
  }

  test("assert rule with body") {
    val kb = KnowledgeBase()
    val ruleSort = kb.makeNameTerm("Rule")
    val domain = kb.makeNameTerm("test")
    val parentSym = kb.intern("parent")
    val grandparentSym = kb.intern("grandparent")

    val xSym = kb.intern("x"); val ySym = kb.intern("y"); val zSym = kb.intern("z")
    val vx = kb.freshVar(xSym); val vy = kb.freshVar(ySym); val vz = kb.freshVar(zSym)
    val varX = kb.alloc(Term.Var(Var.Global(vx))); val varY = kb.alloc(Term.Var(Var.Global(vy))); val varZ = kb.alloc(Term.Var(Var.Global(vz)))

    val head = kb.alloc(Term.Fn(grandparentSym, IArray(varX, varZ), IArray.empty))
    val b1 = kb.alloc(Term.Fn(parentSym, IArray(varX, varY), IArray.empty))
    val b2 = kb.alloc(Term.Fn(parentSym, IArray(varY, varZ), IArray.empty))

    val rid = kb.assertRule(head, IndexedSeq(b1, b2), ruleSort, domain)
    assertEquals(kb.ruleBody(rid).length, 2)
    assertEquals(kb.factCount, 0)
    assertEquals(kb.ruleCount, 1)
  }

  test("apply_subst replaces vars") {
    val kb = KnowledgeBase()
    val fSym = kb.intern("f")
    val xSym = kb.intern("x")
    val vid = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(Var.Global(vid)))
    val v = kb.alloc(Term.Const(Literal.IntLit(42)))
    val term = kb.alloc(Term.Fn(fSym, IArray(varX), IArray.empty))

    val s = Substitution()
    s.bind(vid, v)
    val result = kb.applySubst(term, s)
    kb.getTerm(result) match
      case fn: Term.Fn => assertEquals(TermId.raw(fn.posArgs(0)), TermId.raw(v))
      case other => fail(s"expected Fn, got $other")
  }

  test("standardize apart produces fresh vars") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Rule")
    val domain = kb.makeNameTerm("test")
    val fSym = kb.intern("f"); val gSym = kb.intern("g")
    val xSym = kb.intern("x")
    val vx = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(Var.Global(vx)))

    val head = kb.alloc(Term.Fn(fSym, IArray(varX), IArray.empty))
    val bodyLit = kb.alloc(Term.Fn(gSym, IArray(varX), IArray.empty))
    val rid = kb.assertRule(head, IndexedSeq(bodyLit), sort, domain)
    val (newHead, newBody) = kb.standardizeApart(rid)

    assertNotEquals(TermId.raw(newHead), TermId.raw(head))
    val headVars = kb.collectVars(newHead)
    assertEquals(headVars.length, 1)
    assertNotEquals(headVars(0), vx)

    assertEquals(newBody.length, 1)
    val bodyVars = kb.collectVars(newBody(0))
    assertEquals(bodyVars.length, 1)
    assertEquals(headVars(0), bodyVars(0))
  }

  test("collect_vars finds all") {
    val kb = KnowledgeBase()
    val fSym = kb.intern("f")
    val xSym = kb.intern("x"); val ySym = kb.intern("y")
    val vx = kb.freshVar(xSym); val vy = kb.freshVar(ySym)
    val varX = kb.alloc(Term.Var(Var.Global(vx))); val varY = kb.alloc(Term.Var(Var.Global(vy)))
    val term = kb.alloc(Term.Fn(fSym, IArray(varX, varY, varX), IArray.empty))
    val vars = kb.collectVars(term)
    assertEquals(vars.length, 2)
    assert(vars.contains(vx))
    assert(vars.contains(vy))
  }

  test("subst_term replaces name") {
    val kb = KnowledgeBase()
    val t = kb.makeNameTerm("T")
    val int = kb.makeNameTerm("Int")
    val optionSym = kb.intern("Option")
    val optionT = kb.alloc(Term.Fn(optionSym, IArray(t), IArray.empty))
    val result = kb.substTerm(optionT, t, int)
    kb.getTerm(result) match
      case fn: Term.Fn =>
        assertEquals(fn.posArgs.length, 1)
        assertEquals(TermId.raw(fn.posArgs(0)), TermId.raw(int))
      case other => fail(s"expected Fn, got $other")
  }

  test("isEquation recognizes both `eq` and `unify` heads (WI-528)") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Rule")
    val domain = kb.makeNameTerm("d")
    val xSym = kb.intern("x")
    val vx = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(Var.Global(vx)))
    val fSym = kb.intern("f"); val gSym = kb.intern("g")
    val fx = kb.alloc(Term.Fn(fSym, IArray(varX), IArray.empty))
    val gx = kb.alloc(Term.Fn(gSym, IArray(varX), IArray.empty))

    // Legacy `=`-spelled equation: head functor "eq", 2 args, empty body.
    val eqSym = kb.intern("eq")
    val eqHead = kb.alloc(Term.Fn(eqSym, IArray(fx, gx), IArray.empty))
    val eqRid = kb.assertRule(eqHead, IndexedSeq.empty, sort, domain)
    assert(kb.isEquation(eqRid), "an `eq`-headed empty-body rule is an equation")

    // Migrated `<=>`-spelled equation (proposal 049): head functor "unify".
    val unifySym = kb.intern("unify")
    val uHead = kb.alloc(Term.Fn(unifySym, IArray(fx, gx), IArray.empty))
    val uRid = kb.assertRule(uHead, IndexedSeq.empty, sort, domain)
    assert(kb.isEquation(uRid), "a `unify`-headed empty-body rule is an equation")

    // A `unify` head with a non-empty body is NOT an equation.
    val guard = kb.alloc(Term.Fn(gSym, IArray(varX), IArray.empty))
    val uBodyRid = kb.assertRule(uHead, IndexedSeq(guard), sort, domain)
    assert(!kb.isEquation(uBodyRid), "a `unify`-headed rule with a body is not an equation")

    // A `unify` head with the wrong positional arity is NOT an equation.
    val uUnary = kb.alloc(Term.Fn(unifySym, IArray(fx), IArray.empty))
    val uUnaryRid = kb.assertRule(uUnary, IndexedSeq.empty, sort, domain)
    assert(!kb.isEquation(uUnaryRid), "a unary `unify` head is not an equation")

    // An unrelated binary functor is NOT an equation.
    val hSym = kb.intern("h")
    val hHead = kb.alloc(Term.Fn(hSym, IArray(fx, gx), IArray.empty))
    val hRid = kb.assertRule(hHead, IndexedSeq.empty, sort, domain)
    assert(!kb.isEquation(hRid), "a non-eq/unify functor is not an equation")

    // A functor that RESOLVES to a qualified symbol — short name "unify",
    // qualified name "anthill.kernel.unify", as a real stdlib load produces —
    // is still recognized: isEquation reads the SHORT name, not symbol identity
    // and not the qualified name. This is the exact case the name-based check
    // guards (its raw id differs from bare `intern("unify")`, so the old
    // identity check would have wrongly returned false). (WI-528)
    val scopeRaw = kb.makeNameTerm("_global").raw
    val resolvedUnify = kb.symbols.define(
      "unify", "anthill.kernel.unify", anthill.intern.SymbolKind.Operation, scopeRaw)
    assertNotEquals(anthill.intern.TermSymbol.raw(resolvedUnify),
      anthill.intern.TermSymbol.raw(unifySym),
      "the resolved symbol must differ from the bare interned one")
    val rHead = kb.alloc(Term.Fn(resolvedUnify, IArray(fx, gx), IArray.empty))
    val rRid = kb.assertRule(rHead, IndexedSeq.empty, sort, domain)
    assert(kb.isEquation(rRid), "a resolved `anthill.kernel.unify` head is still an equation")
  }

  test("fact count and rule count") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("S")
    val domain = kb.makeNameTerm("d")
    val fSym = kb.intern("f"); val gSym = kb.intern("g")
    val v = kb.alloc(Term.Const(Literal.IntLit(1)))
    val fact = kb.alloc(Term.Fn(fSym, IArray(v), IArray.empty))
    kb.assertFact(fact, sort, domain)

    val xSym = kb.intern("x")
    val vx = kb.freshVar(xSym)
    val varX = kb.alloc(Term.Var(Var.Global(vx)))
    val head = kb.alloc(Term.Fn(fSym, IArray(varX), IArray.empty))
    val bodyLit = kb.alloc(Term.Fn(gSym, IArray(varX), IArray.empty))
    kb.assertRule(head, IndexedSeq(bodyLit), sort, domain)

    assertEquals(kb.factCount, 1)
    assertEquals(kb.ruleCount, 1)
  }
