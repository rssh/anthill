package anthill.kb

import anthill.term.{Term, TermId, Literal}
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
    val varTerm = kb.alloc(Term.Var(vid))
    val target = kb.alloc(Term.Const(Literal.IntLit(42)))
    val s = kb.matchTerm(varTerm, target).get
    assertEquals(s.resolve(vid).map(TermId.raw), Some(TermId.raw(target)))
  }

  test("match_term var consistency") {
    val kb = KnowledgeBase()
    val xSym = kb.intern("x")
    val vid = kb.freshVar(xSym)
    val varTerm = kb.alloc(Term.Var(vid))
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
    val varX = kb.alloc(Term.Var(vid))
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
    val varX = kb.alloc(Term.Var(vx)); val varY = kb.alloc(Term.Var(vy)); val varZ = kb.alloc(Term.Var(vz))

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
    val varX = kb.alloc(Term.Var(vid))
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
    val varX = kb.alloc(Term.Var(vx))

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
    val varX = kb.alloc(Term.Var(vx)); val varY = kb.alloc(Term.Var(vy))
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
    val varX = kb.alloc(Term.Var(vx))
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
    val varX = kb.alloc(Term.Var(vx))
    val head = kb.alloc(Term.Fn(fSym, IArray(varX), IArray.empty))
    val bodyLit = kb.alloc(Term.Fn(gSym, IArray(varX), IArray.empty))
    kb.assertRule(head, IndexedSeq(bodyLit), sort, domain)

    assertEquals(kb.factCount, 1)
    assertEquals(kb.ruleCount, 1)
  }
