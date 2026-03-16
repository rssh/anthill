package anthill.term

import anthill.intern.TermSymbol

class TermStoreTest extends munit.FunSuite:

  private def sym(n: Int): TermSymbol = TermSymbol.fromRaw(n)

  test("hash-consing deduplicates identical terms") {
    val store = TermStore()
    val a = store.alloc(Term.Const(Literal.IntLit(42)))
    val b = store.alloc(Term.Const(Literal.IntLit(42)))
    assertEquals(TermId.raw(a), TermId.raw(b))
    assertEquals(store.size, 1)
  }

  test("different constants get different ids") {
    val store = TermStore()
    val a = store.alloc(Term.Const(Literal.IntLit(1)))
    val b = store.alloc(Term.Const(Literal.IntLit(2)))
    assertNotEquals(TermId.raw(a), TermId.raw(b))
    assertEquals(store.size, 2)
  }

  test("Fn term deduplication with structural equality") {
    val store = TermStore()
    val inner = store.alloc(Term.Const(Literal.IntLit(1)))
    val fn1 = store.alloc(Term.Fn(sym(0), IArray(inner), IArray.empty))
    val fn2 = store.alloc(Term.Fn(sym(0), IArray(inner), IArray.empty))
    assertEquals(TermId.raw(fn1), TermId.raw(fn2))
    assertEquals(store.size, 2) // inner + fn
  }

  test("Fn subterms returns positional and named args") {
    val store = TermStore()
    val a = store.alloc(Term.Const(Literal.IntLit(1)))
    val b = store.alloc(Term.Const(Literal.IntLit(2)))
    val fn = store.alloc(Term.Fn(sym(0), IArray(a), IArray((sym(1), b))))
    val subs = store.get(fn).subterms
    assertEquals(subs.length, 2)
    assertEquals(TermId.raw(subs(0)), TermId.raw(a))
    assertEquals(TermId.raw(subs(1)), TermId.raw(b))
  }

  test("arity counts positional and named args") {
    val store = TermStore()
    val a = store.alloc(Term.Const(Literal.IntLit(1)))
    val fn = store.alloc(Term.Fn(sym(0), IArray(a, a), IArray((sym(1), a))))
    assertEquals(store.get(fn).arity, 3)
  }

  test("infix desugared to Fn") {
    val store = TermStore()
    val a = store.alloc(Term.Const(Literal.IntLit(1)))
    val b = store.alloc(Term.Const(Literal.IntLit(2)))
    // a + b represented as add(a, b)
    val sum = store.alloc(Term.Fn(sym(0), IArray(a, b), IArray.empty))
    val subs = store.get(sum).subterms
    assertEquals(subs.length, 2)
    assertEquals(TermId.raw(subs(0)), TermId.raw(a))
    assertEquals(TermId.raw(subs(1)), TermId.raw(b))
  }

  test("OrderedDouble NaN equality") {
    val store = TermStore()
    val a = store.alloc(Term.Const(Literal.FloatLit(OrderedDouble(Double.NaN))))
    val b = store.alloc(Term.Const(Literal.FloatLit(OrderedDouble(Double.NaN))))
    assertEquals(TermId.raw(a), TermId.raw(b))
  }

  test("VarId equality uses only id, not name") {
    val v1 = VarId(1, sym(10))
    val v2 = VarId(1, sym(20))
    assertEquals(v1, v2)
    assertEquals(v1.hashCode(), v2.hashCode())
  }

  test("Bottom and Ref terms") {
    val store = TermStore()
    val bot = store.alloc(Term.Bottom)
    val bot2 = store.alloc(Term.Bottom)
    assertEquals(TermId.raw(bot), TermId.raw(bot2))

    val r1 = store.alloc(Term.Ref(sym(5)))
    val r2 = store.alloc(Term.Ref(sym(5)))
    assertEquals(TermId.raw(r1), TermId.raw(r2))
  }
