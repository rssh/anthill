package anthill.intern

class SymbolTableTest extends munit.FunSuite:

  /** WI-976: a scope is MINTED from a symbol. These cases used to pass bare integers
    * (`10`, `100`, `300`) as scopes, which is what "scope-hood is untyped" looked like
    * from the outside — the table accepted a number that named nothing, so the unit
    * tests exercised a shape the loader could never produce. `SymbolTable.scopeOf` is the
    * only way in now (WI-990: minted THROUGH the table whose symbol it is), so the scopes
    * here are the same kind of thing the loader threads.
    *
    * WI-1004: the return type is `st.ScopeId` — a scope belongs to the table that issued
    * it, so this helper cannot be written without naming which one. */
  private def scopeOf(st: SymbolTable, name: String): st.ScopeId =
    st.scopeOf(st.intern(name))

  test("intern deduplicates") {
    val st = SymbolTable()
    val a = st.intern("foo")
    val b = st.intern("foo")
    assertEquals(TermSymbol.raw(a), TermSymbol.raw(b))
    assertEquals(st.name(a), "foo")
  }

  test("define creates new entry in different scopes") {
    val st = SymbolTable()
    val s1 = st.define("foo", "A.foo", SymbolKind.Operation, scopeOf(st, "A"))
    val s2 = st.define("foo", "B.foo", SymbolKind.Operation, scopeOf(st, "B"))
    assertNotEquals(TermSymbol.raw(s1), TermSymbol.raw(s2))
    assertEquals(st.name(s1), "foo")
    assertEquals(st.name(s2), "foo")
    assert(st.isResolved(s1))
    assert(st.isResolved(s2))
  }

  test("define same scope reuses") {
    val st = SymbolTable()
    val a = scopeOf(st, "A")
    val s1 = st.define("Foo", "A.Foo", SymbolKind.Sort, a)
    val s2 = st.define("Foo", "A.Foo", SymbolKind.Namespace, a)
    assertEquals(TermSymbol.raw(s1), TermSymbol.raw(s2))
  }

  test("resolve in scope - local") {
    val st = SymbolTable()
    val eq = scopeOf(st, "Eq")
    val s = st.define("eq", "Eq.eq", SymbolKind.Operation, eq)
    st.resolveInScope("eq", eq) match
      case ResolveResult.Found(found) => assertEquals(TermSymbol.raw(found), TermSymbol.raw(s))
      case other => fail(s"expected Found, got $other")
  }

  test("resolve in scope - parent") {
    val st = SymbolTable()
    val eq = scopeOf(st, "Eq")
    val user = scopeOf(st, "User")
    val eqSym = st.define("eq", "Eq.eq", SymbolKind.Operation, eq)
    st.addParent(user, eq, isEnclosing = false)

    st.resolveInScope("eq", user) match
      case ResolveResult.Found(found) => assertEquals(TermSymbol.raw(found), TermSymbol.raw(eqSym))
      case other => fail(s"expected Found, got $other")
  }

  test("resolve excludes type params") {
    val st = SymbolTable()
    val eq = scopeOf(st, "Eq")
    val user = scopeOf(st, "User")
    st.define("T", "Eq.T", SymbolKind.Sort, eq)
    st.addTypeParam(eq, "T")

    val eqSym = st.define("eq", "Eq.eq", SymbolKind.Operation, eq)

    st.addParent(user, eq, isEnclosing = false)

    st.resolveInScope("T", user) match
      case ResolveResult.NotFound => // expected
      case other => fail(s"expected NotFound for type param, got $other")

    st.resolveInScope("eq", user) match
      case ResolveResult.Found(found) => assertEquals(TermSymbol.raw(found), TermSymbol.raw(eqSym))
      case other => fail(s"expected Found, got $other")
  }

  test("resolve ambiguous") {
    val st = SymbolTable()
    val a = scopeOf(st, "A")
    val b = scopeOf(st, "B")
    val c = scopeOf(st, "C")
    st.define("foo", "A.foo", SymbolKind.Operation, a)
    st.define("foo", "B.foo", SymbolKind.Operation, b)

    st.addParent(c, a, isEnclosing = false)
    st.addParent(c, b, isEnclosing = false)

    st.resolveInScope("foo", c) match
      case ResolveResult.Ambiguous(candidates) => assertEquals(candidates.length, 2)
      case other => fail(s"expected Ambiguous, got $other")
  }

  test("local shadows parent") {
    val st = SymbolTable()
    val a = scopeOf(st, "A")
    val b = scopeOf(st, "B")
    st.define("foo", "A.foo", SymbolKind.Operation, a)

    val localFoo = st.define("foo", "B.foo", SymbolKind.Operation, b)
    st.addParent(b, a, isEnclosing = false)

    st.resolveInScope("foo", b) match
      case ResolveResult.Found(found) => assertEquals(TermSymbol.raw(found), TermSymbol.raw(localFoo))
      case other => fail(s"expected Found (local), got $other")
  }

  /** WI-20261020-80VNX (rustland's `intern::tests`, WI-20260902-JB6RS step 0) — a
    * constructor's TYPE FACE is another identity over the same declaration: the table
    * answers it as it answers the declaration, and nothing else does.
    *
    * BACKED OUT (`TermSymbol.index` returning the whole value, i.e. not masking): the table
    * reads index past the end of `defs` and throw, and the `scopeOf` row fails the same
    * way. The identity block passes either way, BY DESIGN — the bit is what makes the two
    * unequal, masked or not. */
  test("a type face is another identity over the same declaration") {
    val st = SymbolTable()
    val scope = scopeOf(st, "shapes")
    val c = st.define("Foo", "shapes.Foo", SymbolKind.Sort, scope)
    st.addKind(c, SymbolKind.Entity)
    val face = c.typeFace

    assertEquals(face.index, c.index, "one table slot")
    assertEquals(st.name(face), "Foo")
    st.get(face) match
      case SymbolDef.Resolved(_, qualified, _, _) => assertEquals(qualified, "shapes.Foo")
      case other => fail(s"a face reads its declaration: $other")
    assertEquals(st.get(face).kindsSet, Set(SymbolKind.Sort, SymbolKind.Entity))
    assert(st.isResolved(face))
    assertEquals(st.scopeOf(face), st.scopeOf(c), "a face owns its declaration's scope")
    assertEquals(st.symbolOf(st.scopeOf(face)), c, "and the owner is the plain symbol")

    assertNotEquals(face, c)
    assertEquals(Set(c, face).size, 2, "the two hash apart")
    assert(face.isTypeFace && !c.isTypeFace)
    assertEquals(face.plain, c)
    assertEquals(c.plain, c, "plain is identity on a plain symbol")
    assertEquals(TermSymbol.fromRaw(face.raw), face, "the raw value round-trips the face")
    assertEquals(TermSymbol.fromRaw(face.index), c, "a slot is the plain symbol")
  }

  /** The table holds declarations only: a write keyed on a face is a caller confusing the
    * type with its declaration, refused loudly. */
  test("the table refuses a type face") {
    val st = SymbolTable()
    val c = st.define("Foo", "Foo", SymbolKind.Sort, scopeOf(st, "ns"))
    val refused = intercept[IllegalArgumentException](st.addKind(c.typeFace, SymbolKind.Entity))
    assert(refused.getMessage.contains("a type face is not a declaration"), refused.getMessage)
    intercept[IllegalArgumentException](
      st.addImport(scopeOf(st, "other"), "Foo", c.typeFace, ImportOrigin.Builtin))
  }
