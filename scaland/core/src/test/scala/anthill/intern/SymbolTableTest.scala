package anthill.intern

class SymbolTableTest extends munit.FunSuite:

  test("intern deduplicates") {
    val st = SymbolTable()
    val a = st.intern("foo")
    val b = st.intern("foo")
    assertEquals(TermSymbol.raw(a), TermSymbol.raw(b))
    assertEquals(st.name(a), "foo")
  }

  test("define creates new entry in different scopes") {
    val st = SymbolTable()
    val s1 = st.define("foo", "A.foo", SymbolKind.Operation, 10)
    val s2 = st.define("foo", "B.foo", SymbolKind.Operation, 20)
    assertNotEquals(TermSymbol.raw(s1), TermSymbol.raw(s2))
    assertEquals(st.name(s1), "foo")
    assertEquals(st.name(s2), "foo")
    assert(st.isResolved(s1))
    assert(st.isResolved(s2))
  }

  test("define same scope reuses") {
    val st = SymbolTable()
    val s1 = st.define("Foo", "A.Foo", SymbolKind.Sort, 10)
    val s2 = st.define("Foo", "A.Foo", SymbolKind.Namespace, 10)
    assertEquals(TermSymbol.raw(s1), TermSymbol.raw(s2))
  }

  test("resolve in scope - local") {
    val st = SymbolTable()
    val s = st.define("eq", "Eq.eq", SymbolKind.Operation, 100)
    st.resolveInScope("eq", 100) match
      case ResolveResult.Found(found) => assertEquals(TermSymbol.raw(found), TermSymbol.raw(s))
      case other => fail(s"expected Found, got $other")
  }

  test("resolve in scope - parent") {
    val st = SymbolTable()
    val eqSym = st.define("eq", "Eq.eq", SymbolKind.Operation, 100)
    st.addExport(100, "eq")
    st.addParent(200, ScopeInclusion(parentScopeRaw = 100, instantiationTermRaw = 0, isEnclosing = false))

    st.resolveInScope("eq", 200) match
      case ResolveResult.Found(found) => assertEquals(TermSymbol.raw(found), TermSymbol.raw(eqSym))
      case other => fail(s"expected Found, got $other")
  }

  test("resolve excludes type params") {
    val st = SymbolTable()
    st.define("T", "Eq.T", SymbolKind.Sort, 100)
    st.addExport(100, "T")
    st.addTypeParam(100, "T")

    val eqSym = st.define("eq", "Eq.eq", SymbolKind.Operation, 100)
    st.addExport(100, "eq")

    st.addParent(200, ScopeInclusion(parentScopeRaw = 100, instantiationTermRaw = 0, isEnclosing = false))

    st.resolveInScope("T", 200) match
      case ResolveResult.NotFound => // expected
      case other => fail(s"expected NotFound for type param, got $other")

    st.resolveInScope("eq", 200) match
      case ResolveResult.Found(found) => assertEquals(TermSymbol.raw(found), TermSymbol.raw(eqSym))
      case other => fail(s"expected Found, got $other")
  }

  test("resolve ambiguous") {
    val st = SymbolTable()
    st.define("foo", "A.foo", SymbolKind.Operation, 100)
    st.addExport(100, "foo")
    st.define("foo", "B.foo", SymbolKind.Operation, 200)
    st.addExport(200, "foo")

    st.addParent(300, ScopeInclusion(parentScopeRaw = 100, instantiationTermRaw = 0, isEnclosing = false))
    st.addParent(300, ScopeInclusion(parentScopeRaw = 200, instantiationTermRaw = 0, isEnclosing = false))

    st.resolveInScope("foo", 300) match
      case ResolveResult.Ambiguous(candidates) => assertEquals(candidates.length, 2)
      case other => fail(s"expected Ambiguous, got $other")
  }

  test("local shadows parent") {
    val st = SymbolTable()
    st.define("foo", "A.foo", SymbolKind.Operation, 100)
    st.addExport(100, "foo")

    val localFoo = st.define("foo", "B.foo", SymbolKind.Operation, 200)
    st.addParent(200, ScopeInclusion(parentScopeRaw = 100, instantiationTermRaw = 0, isEnclosing = false))

    st.resolveInScope("foo", 200) match
      case ResolveResult.Found(found) => assertEquals(TermSymbol.raw(found), TermSymbol.raw(localFoo))
      case other => fail(s"expected Found (local), got $other")
  }
