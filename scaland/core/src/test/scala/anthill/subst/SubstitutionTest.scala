package anthill.subst

import anthill.term.{Term, TermId, TermStore, Var, VarId, Literal}
import anthill.intern.TermSymbol

class SubstitutionTest extends munit.FunSuite:

  private def sym(n: Int): TermSymbol = TermSymbol.fromRaw(n)

  test("bind and resolve") {
    val store = TermStore()
    val t = store.alloc(Term.Const(Literal.IntLit(42)))
    val v = VarId(0, sym(0))
    val s = Substitution()
    s.bind(v, t)
    assertEquals(s.resolve(v).map(TermId.raw), Some(TermId.raw(t)))
  }

  test("resolve unbound returns None") {
    val s = Substitution()
    val v = VarId(0, sym(0))
    assertEquals(s.resolve(v), None)
  }

  test("contradiction on conflicting bindings") {
    val store = TermStore()
    val t1 = store.alloc(Term.Const(Literal.IntLit(1)))
    val t2 = store.alloc(Term.Const(Literal.IntLit(2)))
    val v = VarId(0, sym(0))
    val s = Substitution()
    s.bind(v, t1)
    assert(!s.isContradiction)
    s.bind(v, t2)
    assert(s.isContradiction)
    // First binding is kept
    assertEquals(s.resolve(v).map(TermId.raw), Some(TermId.raw(t1)))
  }

  test("idempotent rebinding is not a contradiction") {
    val store = TermStore()
    val t = store.alloc(Term.Const(Literal.IntLit(42)))
    val v = VarId(0, sym(0))
    val s = Substitution()
    s.bind(v, t)
    s.bind(v, t)
    assert(!s.isContradiction)
  }

  test("parent chain resolution") {
    val store = TermStore()
    val t = store.alloc(Term.Const(Literal.IntLit(42)))
    val v = VarId(0, sym(0))
    val parent = Substitution()
    parent.bind(v, t)
    val child = Substitution.withParent(parent)
    assertEquals(child.resolve(v).map(TermId.raw), Some(TermId.raw(t)))
  }

  test("child shadows parent") {
    val store = TermStore()
    val t1 = store.alloc(Term.Const(Literal.IntLit(1)))
    val t2 = store.alloc(Term.Const(Literal.IntLit(2)))
    val v = VarId(0, sym(0))
    val parent = Substitution()
    parent.bind(v, t1)
    val child = Substitution.withParent(parent)
    child.bind(v, t2)
    assertEquals(child.resolve(v).map(TermId.raw), Some(TermId.raw(t2)))
  }

  test("bindCompressed flattens chains") {
    val store = TermStore()
    val v1 = VarId(1, sym(0))
    val v2 = VarId(2, sym(1))
    val vTerm = store.alloc(Term.Var(Var.Global(v1)))
    val concrete = store.alloc(Term.Const(Literal.IntLit(99)))
    val s = Substitution()
    // v2 -> Var(v1)
    s.bind(v2, vTerm)
    // Now bind v1 -> 99, which should compress v2 -> 99 as well
    s.bindCompressed(Seq((v1, concrete)), store)
    assertEquals(s.resolve(v1).map(TermId.raw), Some(TermId.raw(concrete)))
    assertEquals(s.resolve(v2).map(TermId.raw), Some(TermId.raw(concrete)))
  }

  // ── WI-172: isEmpty fast path ────────────────────────────────

  test("isEmpty: fresh substitution is empty") {
    assert(Substitution().isEmpty)
  }

  test("isEmpty: substitution with one binding is not empty") {
    val store = TermStore()
    val t = store.alloc(Term.Const(Literal.IntLit(1)))
    val v = VarId(0, sym(0))
    val s = Substitution()
    s.bind(v, t)
    assert(!s.isEmpty)
  }

  test("isEmpty: child of empty parent with no own bindings is empty") {
    val parent = Substitution()
    val child = Substitution.withParent(parent)
    assert(child.isEmpty)
  }

  test("isEmpty: child of non-empty parent is not empty (parent supplies bindings)") {
    val store = TermStore()
    val t = store.alloc(Term.Const(Literal.IntLit(1)))
    val v = VarId(0, sym(0))
    val parent = Substitution()
    parent.bind(v, t)
    val child = Substitution.withParent(parent)
    // Child has no own bindings, but parent does — applying this subst
    // is NOT a no-op, so isEmpty must be false.
    assert(!child.isEmpty)
  }
