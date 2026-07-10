package anthill.kb

import anthill.intern.TermSymbol
import anthill.term.{Literal, OrderedDouble, Term, TermId, Value, Var, VarId}

/** The carrier-neutral read API: a hash-consed `TermId` and a non-interned
  * `Value` must read — and compare — identically.
  */
class TermViewTest extends munit.FunSuite:

  private def noPos: IndexedSeq[Value] = Vector.empty
  private def noNamed: IndexedSeq[(TermSymbol, Value)] = Vector.empty

  private def headOf(kb: KnowledgeBase, t: TermId): ViewHead = TermView[TermId].head(t, kb)
  private def headOf(kb: KnowledgeBase, v: Value): ViewHead = TermView[Value].head(v, kb)

  // ── Heads, per carrier ────────────────────────────────────────

  test("TermId heads mirror the Term shape") {
    val kb = KnowledgeBase()
    val f = kb.intern("f")
    val arg = kb.alloc(Term.Const(Literal.IntLit(1)))

    assertEquals(headOf(kb, kb.alloc(Term.Const(Literal.IntLit(7)))), ViewHead.Const(Literal.IntLit(7)))
    assertEquals(headOf(kb, kb.alloc(Term.Ref(f))), ViewHead.Ref(f))
    assertEquals(headOf(kb, kb.alloc(Term.Ident(f))), ViewHead.Ident(f))
    assertEquals(headOf(kb, kb.alloc(Term.Bottom)), ViewHead.Bottom)

    val v = Var.Global(VarId(0, f))
    assertEquals(headOf(kb, kb.alloc(Term.Var(v))), ViewHead.Var(v))

    val fn = kb.alloc(Term.Fn(f, IArray(arg), IArray((f, arg))))
    assertEquals(headOf(kb, fn), ViewHead.Functor(Some(f), 1, 1))
  }

  test("Value scalar heads are the matching Literal consts") {
    val kb = KnowledgeBase()
    assertEquals(headOf(kb, Value.IntVal(7)), ViewHead.Const(Literal.IntLit(7)))
    assertEquals(headOf(kb, Value.BigIntVal(BigInt(7))), ViewHead.Const(Literal.BigIntLit(BigInt(7))))
    assertEquals(headOf(kb, Value.BoolVal(true)), ViewHead.Const(Literal.BoolLit(true)))
    assertEquals(headOf(kb, Value.StrVal("s")), ViewHead.Const(Literal.StringLit("s")))
    assertEquals(headOf(kb, Value.FloatVal(1.5)), ViewHead.Const(Literal.FloatLit(OrderedDouble(1.5))))
  }

  test("functor-less aggregates view as Functor(None, ..)") {
    val kb = KnowledgeBase()
    assertEquals(headOf(kb, Value.UnitVal), ViewHead.Functor(None, 0, 0))
    assertEquals(headOf(kb, Value.Tuple(Vector(Value.IntVal(1)), noNamed)), ViewHead.Functor(None, 1, 0))
    assertEquals(headOf(kb, Value.UnitVal).functorSym, None)
  }

  test("unit and the empty tuple are the same head, hence equal") {
    // Both read as Functor(None, 0, 0). Intentional, and matches rustland.
    val kb = KnowledgeBase()
    assert(viewsStructurallyEqual(kb, Value.UnitVal, Value.Tuple(noPos, noNamed)))
  }

  // ── WI-436: a 0-ary constructor canonicalizes to Ref ──────────

  test("nullary registered constructor reads as Ref on every carrier") {
    val kb = KnowledgeBase()
    val list = kb.makeNameTerm("List")
    val nilFn = kb.makeNameTerm("nil") // Term.Fn(nil, [], [])
    kb.registerEntityOf(nilFn, list)
    val nilSym = kb.intern("nil")
    val nilRef = kb.alloc(Term.Ref(nilSym))

    // All three spellings of the same 0-ary constructor read as `Ref(nil)`.
    assertEquals(headOf(kb, nilFn), ViewHead.Ref(nilSym))
    assertEquals(headOf(kb, nilRef), ViewHead.Ref(nilSym))
    assertEquals(headOf(kb, Value.Entity(nilSym, noPos, noNamed)), ViewHead.Ref(nilSym))

    // ... and therefore compare equal across carriers and spellings.
    assert(viewsStructurallyEqual(kb, nilFn, nilRef))
    assert(viewsStructurallyEqual(kb, nilFn, Value.Entity(nilSym, noPos, noNamed)))
    assert(viewsStructurallyEqual(kb, nilRef, Value.Entity(nilSym, noPos, noNamed)))
  }

  test("the constructor gate is kind-isolated: a non-constructor nullary Fn stays a Functor") {
    val kb = KnowledgeBase()
    val natFn = kb.makeNameTerm("Nat") // a sort name, never registered as a constructor
    val natSym = kb.intern("Nat")
    val natRef = kb.alloc(Term.Ref(natSym))

    assert(!kb.isConstructorSymbol(natSym))
    assertEquals(headOf(kb, natFn), ViewHead.Functor(Some(natSym), 0, 0))
    assertEquals(headOf(kb, natRef), ViewHead.Ref(natSym))
    assert(!viewsStructurallyEqual(kb, natFn, natRef))

    // Both spellings still answer `functorSym` with the same symbol.
    assertEquals(headOf(kb, natFn).functorSym, Some(natSym))
    assertEquals(headOf(kb, natRef).functorSym, Some(natSym))
  }

  // ── Cross-carrier structural equality ─────────────────────────

  test("a Value.Entity equals its interned Term.Fn twin") {
    val kb = KnowledgeBase()
    val f = kb.intern("f")
    val one = kb.alloc(Term.Const(Literal.IntLit(1)))
    val fn = kb.alloc(Term.Fn(f, IArray(one), IArray.empty))
    val ent = Value.Entity(f, Vector(Value.IntVal(1)), noNamed)

    assert(viewsStructurallyEqual(kb, fn, ent))
    assert(viewsStructurallyEqual(kb, ent, fn))
    // The derived `==` cannot see this: different carriers, different cases.
    // Exactly why `viewsStructurallyEqual` exists.
    assert(Value.Term(fn) != ent)
  }

  test("a Value.Term is interchangeable with its TermId") {
    val kb = KnowledgeBase()
    val f = kb.intern("f")
    val one = kb.alloc(Term.Const(Literal.IntLit(1)))
    val fn = kb.alloc(Term.Fn(f, IArray(one), IArray.empty))

    assert(viewsStructurallyEqual(kb, fn, Value.Term(fn)))
    assertEquals(headOf(kb, Value.Term(fn)), headOf(kb, fn))
    assertEquals(TermView[Value].namedKeys(Value.Term(fn), kb), TermView[TermId].namedKeys(fn, kb))
  }

  test("nested and mixed carriers recurse structurally") {
    val kb = KnowledgeBase()
    val f = kb.intern("f")
    val g = kb.intern("g")
    val one = kb.alloc(Term.Const(Literal.IntLit(1)))
    val gFn = kb.alloc(Term.Fn(g, IArray(one), IArray.empty))
    val fFn = kb.alloc(Term.Fn(f, IArray(gFn), IArray.empty))

    val allValue = Value.Entity(f, Vector(Value.Entity(g, Vector(Value.IntVal(1)), noNamed)), noNamed)
    // A Value parent holding an already-interned child — the bridge case.
    val mixed = Value.Entity(f, Vector(Value.Term(gFn)), noNamed)

    assert(viewsStructurallyEqual(kb, fFn, allValue))
    assert(viewsStructurallyEqual(kb, fFn, mixed))
    assert(viewsStructurallyEqual(kb, allValue, mixed))

    val wrong = Value.Entity(f, Vector(Value.Entity(g, Vector(Value.IntVal(2)), noNamed)), noNamed)
    assert(!viewsStructurallyEqual(kb, fFn, wrong))
  }

  test("named args compare by key, across carriers") {
    val kb = KnowledgeBase()
    val f = kb.intern("f")
    val a = kb.intern("a")
    val b = kb.intern("b")
    val one = kb.alloc(Term.Const(Literal.IntLit(1)))
    val two = kb.alloc(Term.Const(Literal.IntLit(2)))
    val fn = kb.alloc(Term.Fn(f, IArray.empty, IArray((a, one), (b, two))))

    val ent = Value.Entity(f, noPos, Vector((a, Value.IntVal(1)), (b, Value.IntVal(2))))
    assert(viewsStructurallyEqual(kb, fn, ent))

    // A differing child under a shared key.
    val badVal = Value.Entity(f, noPos, Vector((a, Value.IntVal(1)), (b, Value.IntVal(9))))
    assert(!viewsStructurallyEqual(kb, fn, badVal))

    // A differing key at the same arity — `b` is absent, so the lookup fails.
    val badKey = Value.Entity(f, noPos, Vector((a, Value.IntVal(1)), (f, Value.IntVal(2))))
    assert(!viewsStructurallyEqual(kb, fn, badKey))

    // A differing named arity.
    val short = Value.Entity(f, noPos, Vector((a, Value.IntVal(1))))
    assert(!viewsStructurallyEqual(kb, fn, short))
  }

  test("an aggregate never equals a functor application of the same shape") {
    val kb = KnowledgeBase()
    val f = kb.intern("f")
    val tup = Value.Tuple(Vector(Value.IntVal(1)), noNamed)
    val ent = Value.Entity(f, Vector(Value.IntVal(1)), noNamed)
    assert(!viewsStructurallyEqual(kb, tup, ent))
    assert(viewsStructurallyEqual(kb, tup, Value.Tuple(Vector(Value.IntVal(1)), noNamed)))
  }

  // ── Variables compare by full Var identity ────────────────────

  test("vars compare by kind and VarId, so distinct skolems never conflate") {
    val kb = KnowledgeBase()
    val n = kb.intern("x")
    val v1 = VarId(1, n)
    val v2 = VarId(2, n)

    def t(v: Var): TermId = kb.alloc(Term.Var(v))

    assert(viewsStructurallyEqual(kb, t(Var.Global(v1)), t(Var.Global(v1))))
    assert(!viewsStructurallyEqual(kb, t(Var.Global(v1)), t(Var.Global(v2))))
    // Same VarId, different kind: a flex Global is not the Rigid skolem.
    assert(!viewsStructurallyEqual(kb, t(Var.Global(v1)), t(Var.Rigid(v1))))
    assert(viewsStructurallyEqual(kb, t(Var.DeBruijn(0)), t(Var.DeBruijn(0))))
    assert(!viewsStructurallyEqual(kb, t(Var.DeBruijn(0)), t(Var.DeBruijn(1))))
    // Carriers agree: a Value.Var reads as the Term.Var.
    assert(viewsStructurallyEqual(kb, t(Var.Global(v1)), Value.Var(Var.Global(v1))))
  }

  test("indexVar surfaces every var kind and nothing else") {
    val kb = KnowledgeBase()
    val n = kb.intern("x")
    val rigid = Var.Rigid(VarId(3, n))
    assertEquals(TermView[TermId].indexVar(kb.alloc(Term.Var(rigid)), kb), Some(rigid))
    assertEquals(TermView[Value].indexVar(Value.Var(rigid), kb), Some(rigid))
    assertEquals(TermView[Value].indexVar(Value.Term(kb.alloc(Term.Var(rigid))), kb), Some(rigid))
    assertEquals(TermView[Value].indexVar(Value.IntVal(1), kb), None)
    assertEquals(TermView[TermId].indexVar(kb.alloc(Term.Bottom), kb), None)
  }

  // ── Constants ─────────────────────────────────────────────────

  test("NaN floats compare equal across carriers") {
    val kb = KnowledgeBase()
    val nanTerm = kb.alloc(Term.Const(Literal.FloatLit(OrderedDouble(Double.NaN))))
    assert(viewsStructurallyEqual(kb, nanTerm, Value.FloatVal(Double.NaN)))
    assert(!viewsStructurallyEqual(kb, nanTerm, Value.FloatVal(1.0)))
  }

  test("a const never equals a var or a functor") {
    val kb = KnowledgeBase()
    val f = kb.intern("f")
    val one = kb.alloc(Term.Const(Literal.IntLit(1)))
    assert(!viewsStructurallyEqual(kb, one, Value.Var(Var.Global(VarId(0, f)))))
    assert(!viewsStructurallyEqual(kb, one, Value.Entity(f, noPos, noNamed)))
    assert(!viewsStructurallyEqual(kb, one, kb.alloc(Term.Bottom)))
  }

  // ── Child access ──────────────────────────────────────────────

  test("posArg is bounds-checked on both carriers") {
    val kb = KnowledgeBase()
    val f = kb.intern("f")
    val one = kb.alloc(Term.Const(Literal.IntLit(1)))
    val fn = kb.alloc(Term.Fn(f, IArray(one), IArray.empty))
    val ent = Value.Entity(f, Vector(Value.IntVal(1)), noNamed)

    // An interned child surfaces as Value.Term, not as a bare TermId.
    assertEquals(TermView[TermId].posArg(fn, kb, 0), Some(Value.Term(one)))
    assertEquals(TermView[TermId].posArg(fn, kb, 1), None)
    assertEquals(TermView[TermId].posArg(fn, kb, -1), None)
    assertEquals(TermView[Value].posArg(ent, kb, 0), Some(Value.IntVal(1)))
    assertEquals(TermView[Value].posArg(ent, kb, 1), None)
    assertEquals(TermView[Value].posArg(ent, kb, -1), None)
    // A leaf has no children.
    assertEquals(TermView[TermId].posArg(one, kb, 0), None)
    assertEquals(TermView[Value].posArg(Value.IntVal(1), kb, 0), None)
  }

  test("a child of either carrier is itself a view, and they compare across carriers") {
    val kb = KnowledgeBase()
    val f = kb.intern("f")
    val one = kb.alloc(Term.Const(Literal.IntLit(1)))
    val fn = kb.alloc(Term.Fn(f, IArray(one), IArray.empty))
    val ent = Value.Entity(f, Vector(Value.IntVal(1)), noNamed)

    val termChild = TermView[TermId].posArg(fn, kb, 0).get   // Value.Term(one)
    val valueChild = TermView[Value].posArg(ent, kb, 0).get  // Value.IntVal(1)
    // Different carriers, same denoted term — this is the recursion step that
    // makes viewsStructurallyEqual carrier-blind all the way down.
    assert(viewsStructurallyEqual(kb, termChild, valueChild))
    assert(termChild != valueChild) // ... and the derived `==` cannot see it
  }

  test("hash-consed identity implies structural equality") {
    val kb = KnowledgeBase()
    val f = kb.intern("f")
    val one = kb.alloc(Term.Const(Literal.IntLit(1)))
    val a = kb.alloc(Term.Fn(f, IArray(one), IArray.empty))
    val b = kb.alloc(Term.Fn(f, IArray(one), IArray.empty))
    assertEquals(TermId.raw(a), TermId.raw(b))
    assert(viewsStructurallyEqual(kb, a, b))
  }
