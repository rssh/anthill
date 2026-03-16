package anthill.parse

import anthill.intern.{TermSymbol, SymbolTable}
import anthill.term.{Term, TermId, Literal}

class ParseTest extends munit.FunSuite:

  test("Pratt parser - left associative addition") {
    // 1 + 2 + 3  should be  +( +(1, 2), 3 )
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val plus = st.intern("+")
    val v1 = terms.alloc(Term.Const(Literal.IntLit(1)))
    val v2 = terms.alloc(Term.Const(Literal.IntLit(2)))
    val v3 = terms.alloc(Term.Const(Literal.IntLit(3)))

    val result = Pratt.desugar(
      IndexedSeq(v1, v2, v3),
      IndexedSeq(plus, plus),
      st.name,
      terms.alloc
    )

    // Result should be +(+(1, 2), 3)
    terms.get(result) match
      case fn: Term.Fn =>
        assertEquals(st.name(fn.functor), "+")
        assertEquals(fn.posArgs.length, 2)
        // Left child should be +(1, 2)
        terms.get(fn.posArgs(0)) match
          case inner: Term.Fn =>
            assertEquals(st.name(inner.functor), "+")
          case other => fail(s"expected Fn, got $other")
        // Right child should be 3
        terms.get(fn.posArgs(1)) match
          case Term.Const(Literal.IntLit(3)) => // ok
          case other => fail(s"expected Const(3), got $other")
      case other => fail(s"expected Fn, got $other")
  }

  test("Pratt parser - right associative power") {
    // 2 ^ 3 ^ 4  should be  ^(2, ^(3, 4))
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val pow = st.intern("^")
    val v2 = terms.alloc(Term.Const(Literal.IntLit(2)))
    val v3 = terms.alloc(Term.Const(Literal.IntLit(3)))
    val v4 = terms.alloc(Term.Const(Literal.IntLit(4)))

    val result = Pratt.desugar(
      IndexedSeq(v2, v3, v4),
      IndexedSeq(pow, pow),
      st.name,
      terms.alloc
    )

    terms.get(result) match
      case fn: Term.Fn =>
        assertEquals(st.name(fn.functor), "^")
        // Left child should be 2
        terms.get(fn.posArgs(0)) match
          case Term.Const(Literal.IntLit(2)) => // ok
          case other => fail(s"expected Const(2), got $other")
        // Right child should be ^(3, 4)
        terms.get(fn.posArgs(1)) match
          case inner: Term.Fn =>
            assertEquals(st.name(inner.functor), "^")
          case other => fail(s"expected Fn, got $other")
      case other => fail(s"expected Fn, got $other")
  }

  test("Pratt parser - precedence: + vs *") {
    // 1 + 2 * 3  should be  +(1, *(2, 3))
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val plus = st.intern("+")
    val times = st.intern("*")
    val v1 = terms.alloc(Term.Const(Literal.IntLit(1)))
    val v2 = terms.alloc(Term.Const(Literal.IntLit(2)))
    val v3 = terms.alloc(Term.Const(Literal.IntLit(3)))

    val result = Pratt.desugar(
      IndexedSeq(v1, v2, v3),
      IndexedSeq(plus, times),
      st.name,
      terms.alloc
    )

    terms.get(result) match
      case fn: Term.Fn =>
        assertEquals(st.name(fn.functor), "+")
        // Left should be 1
        terms.get(fn.posArgs(0)) match
          case Term.Const(Literal.IntLit(1)) => // ok
          case other => fail(s"expected Const(1), got $other")
        // Right should be *(2, 3)
        terms.get(fn.posArgs(1)) match
          case inner: Term.Fn =>
            assertEquals(st.name(inner.functor), "*")
          case other => fail(s"expected Fn, got $other")
      case other => fail(s"expected Fn, got $other")
  }

  test("Pratt parser - single operand") {
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val v = terms.alloc(Term.Const(Literal.IntLit(42)))
    val result = Pratt.desugar(IndexedSeq(v), IndexedSeq.empty, st.name, terms.alloc)
    assertEquals(TermId.raw(result), TermId.raw(v))
  }

  test("SimpleTermStore allocates sequentially") {
    val terms = SimpleTermStore()
    val t1 = terms.alloc(Term.Const(Literal.IntLit(1)))
    val t2 = terms.alloc(Term.Const(Literal.IntLit(1)))
    // No hash-consing — same content gets different ids
    assertNotEquals(TermId.raw(t1), TermId.raw(t2))
    assertEquals(terms.size, 2)
  }

  test("Converter var scope") {
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val errors = scala.collection.mutable.ArrayBuffer.empty[ParseError]
    val conv = Converter("", st, terms, errors)

    val xSym = st.intern("x")
    val v1 = conv.getOrCreateVar(xSym)
    val v2 = conv.getOrCreateVar(xSym)
    assertEquals(v1, v2) // same var within scope

    conv.resetVarScope()
    val v3 = conv.getOrCreateVar(xSym)
    assertNotEquals(v1.id, v3.id) // different after reset
  }

  test("ParsedFile structure") {
    val result = Parser.parse("")
    assert(result.isRight)
    val parsed = result.toOption.get
    assert(parsed.items.isEmpty)
  }
