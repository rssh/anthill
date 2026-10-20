package anthill.kb

import anthill.intern.{SymbolKind, TermSymbol}
import anthill.term.{Term, TermId, Var}
import anthill.resolve.SearchStream

/** WI-20261020-80VNX (rustland's `kb::jb6rs_type_face_reads_the_declaration_tests`,
  * WI-20260902-JB6RS steps 1–2) — a constructor's TYPE FACE, over the three shapes a
  * constructor is declared in: sort-nested (`Colour.red`, `Colour.green`), eponymous
  * (`sort Foo … entity Foo(…) … end`) and free-standing (`entity Bar(…)`).
  *
  * BACKED OUT, each alone (measured):
  *  * `Decl.of` keeping the bit: every declaration-keyed read misses for a face — the
  *    kind, field, parent and children rows fail;
  *  * `isConstructorSymbol` answering for a face: the predicate row fails;
  *  * `isEntityOf` comparing name TERMS rather than declarations: the entity-of rows fail;
  *    reading the parent without dropping `sup`'s face: the `Mixed[]` row fails;
  *  * `namesOnlyAType`'s face arm: the names-only-a-type row fails;
  *  * `reflectKind`'s face arm: the `kind` row fails (`entity`).
  * The plain-sort rows pass either way, BY DESIGN: a sort with no constructor of its name
  * never gets a face, and that is what they pin. The identity rows of the second test pass
  * either way BY DESIGN too — they are what the bit buys, and fail only if `TermSymbol`'s
  * equality stopped seeing it. */
class TypeFaceTest extends munit.FunSuite:

  private val src =
    """namespace zzfaces
      |  import anthill.prelude.Int64
      |  sort Colour
      |    entity red
      |    entity green(v: Int64)
      |  end
      |  sort Foo
      |    sort X = ?
      |    entity Foo(a: X)
      |  end
      |  entity Bar(n: Int64)
      |  sort Mixed
      |    entity Mixed(a: Int64)
      |    entity other
      |  end
      |end
      |""".stripMargin

  private val constructors =
    Seq("zzfaces.Colour.red", "zzfaces.Colour.green", "zzfaces.Foo", "zzfaces.Bar")

  test("a type face answers what its declaration answers") {
    val kb = LoadFixture.loaded(src, "faces.anthill")
    for qn <- constructors do
      val c = kb.resolveSymbol(qn)
      val face = kb.typeFaceOf(c)
      assert(face.isTypeFace && face != c, s"$qn: a constructor has a type face")
      assertEquals(kb.typeFaceOf(face), face, s"$qn: idempotent")
      val faceT = kb.alloc(Term.Ref(face))
      val cT = kb.alloc(Term.Ref(c))
      assertEquals(kb.sortKind(faceT), kb.sortKind(cT), s"$qn: sort kind")
      assertEquals(kb.entityParentSort(faceT), kb.entityParentSort(cT), s"$qn: parent")
      assertEquals(kb.entityFieldNames(face), kb.entityFieldNames(c), s"$qn: field names")
      assertEquals(kb.sortChildren(faceT), kb.sortChildren(cT), s"$qn: children")
      assert(!kb.isConstructorSymbol(face), s"$qn: a type face is never a constructor")
      assertEquals(kb.isConstructorSymbol(face.plain), kb.isConstructorSymbol(c), s"$qn: its declaration is")
      assertEquals(kb.symbols.get(face), kb.symbols.get(c), s"$qn: the table reads the declaration")
      assertEquals(kb.reflectKind(face), Some(SymbolKind.Sort), s"$qn: the type is a sort")
      // An instance is an entity of its OWN type, nested or not — `red` of `red[]` as
      // `Foo` of `Foo[]`.
      assert(kb.isEntityOf(cT, faceT), s"$qn: an instance is of its own type")
      kb.entityParentSort(cT).foreach { parent =>
        assertEquals(kb.isEntityOf(faceT, parent), kb.isEntityOf(cT, parent), s"$qn: entity-of")
      }

    // The nested constructors name their sort, through either face; what makes the
    // parent rows above a measurement and not `None == None`.
    val colour = kb.makeNameTermFromSym(kb.resolveSymbol("zzfaces.Colour"))
    val red = kb.resolveSymbol("zzfaces.Colour.red")
    assertEquals(kb.entityParentSort(kb.alloc(Term.Ref(kb.typeFaceOf(red)))), Some(colour))
    assertEquals(kb.sortChildren(colour).length, 2)
    // The parent is reached by its type face too, when it has one.
    assert(kb.isEntityOf(kb.alloc(Term.Ref(red)), colour))

    // A parent that is itself a constructor — an eponymous variant beside a sibling,
    // which §6.3 admits — is reached by its type face: `other` is an entity of the type
    // `Mixed[]`, as of `Mixed`.
    val mixed = kb.resolveSymbol("zzfaces.Mixed")
    val other = kb.alloc(Term.Ref(kb.resolveSymbol("zzfaces.Mixed.other")))
    assert(kb.isEntityOf(other, kb.alloc(Term.Ref(mixed))), "the control: by the name")
    assert(kb.isEntityOf(other, kb.alloc(Term.Ref(kb.typeFaceOf(mixed)))), "by the type face")

    // Of its own type only as an ENTITY: two spellings of a name that is no entity are not
    // an entity and its sort.
    val plainSym = kb.intern("zzfaces.unresolved")
    assert(!kb.isEntityOf(kb.alloc(Term.Ident(plainSym)), kb.alloc(Term.Ref(plainSym))))

    // A face names only a type, whatever its declaration also is.
    for qn <- constructors do
      val c = kb.resolveSymbol(qn)
      assert(kb.namesOnlyAType(kb.typeFaceOf(c)), s"$qn: its type face names only a type")
      assert(!kb.namesOnlyAType(c), s"$qn: the constructor is applied")

    // A sort with no constructor of its name has ONE face.
    for qn <- Seq("zzfaces.Colour", "anthill.prelude.Int64") do
      val s = kb.resolveSymbol(qn)
      assertEquals(kb.typeFaceOf(s), s, s"$qn: no constructor, no second face")
  }

  /** The declaration tables hold declarations: a write keyed on a face is refused, and a
    * face is no quoted field's owner — its bracket binds type parameters, not fields. */
  test("a declaration table refuses a type face, and a face quotes no field") {
    val kb = LoadFixture.loaded(src, "faces.anthill")
    val bar = kb.resolveSymbol("zzfaces.Bar")
    val face = kb.typeFaceOf(bar)
    intercept[IllegalArgumentException](kb.registerSort(kb.alloc(Term.Ref(face)), SortKind.Defined))
    intercept[IllegalArgumentException](kb.registerEntityFields(face, IndexedSeq.empty))
    val n = kb.intern("n")
    kb.registerQuotedField(bar, n)
    assert(kb.isQuotedField(bar, n), "the control: the declaration's field is quoted")
    assert(!kb.isQuotedField(face, n), "a face's bracket binds no field")
  }

  /** A reader that matches a constructor by NAME reads its instance, never its type:
    * `none[]` is no absent option and `some[…]` no wrapped one (`Facts.instanceNamed`),
    * and the empty-list VALUE is no name, so `[]` is not an entity of `ListLiteral`. The
    * stdlib declares the three. */
  test("a constructor's type is not read as its instance by name") {
    val kb = anthill.codegen.scala.StdlibFixture.kbWith()
    val none = kb.resolveSymbol("anthill.prelude.Option.none")
    val some = kb.resolveSymbol("anthill.prelude.Option.some")
    assertEquals(Facts.optionArg(kb, kb.alloc(Term.Ref(none))), Facts.OptionArg.Absent, "the control")
    assertEquals(Facts.optionArg(kb, kb.alloc(Term.Ref(kb.typeFaceOf(none)))), Facts.OptionArg.NotAnOption,
      "`none[]` is the type")
    val one = kb.alloc(Term.Const(anthill.term.Literal.IntLit(1)))
    assertEquals(Facts.optionArg(kb, kb.alloc(Term.Fn(kb.typeFaceOf(some), IArray(one), IArray.empty))),
      Facts.OptionArg.NotAnOption, "`some[…]` is the type")
    val list = kb.resolveSymbol("anthill.reflect.ListLiteral")
    val emptyList = kb.alloc(Term.Fn(list, IArray.empty, IArray.empty))
    assert(emptyList != kb.alloc(Term.Ref(list)), "fixture: `[]` is the empty-literal node")
    assert(!kb.isEntityOf(emptyList, kb.alloc(Term.Ref(list))), "`[]` is a value, not the name")
  }

  private def unary(kb: KnowledgeBase, f: TermSymbol, a: TermId): TermId =
    kb.alloc(Term.Fn(f, IArray(a), IArray.empty))

  private def solutions(kb: KnowledgeBase, goal: TermId): Int =
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  /** A constructor's type and its instance are NEVER ONE TERM — through the store and
    * through resolution (the discrimination tree, then unify). The measured collision at
    * the start of rustland's ticket, with ONE label on both sides: `fact held(Foo[X =
    * Int64])` was found by `:- held(Foo(X: ?v))`. */
  test("a type face and its constructor are never one term") {
    val kb = LoadFixture.loaded(src, "faces.anthill")
    val held = kb.intern("zzfaces.held")
    val domain = kb.symbols.scopeOf(kb.resolveSymbol("zzfaces"))
    val factSort = kb.makeNameTerm("Fact")
    for qn <- Seq("zzfaces.Colour.red", "zzfaces.Foo", "zzfaces.Bar") do
      val c = kb.resolveSymbol(qn)
      val face = kb.typeFaceOf(c)
      val faceRef = kb.alloc(Term.Ref(face))
      val cRef = kb.alloc(Term.Ref(c))
      assertEquals(kb.alloc(Term.Fn(face, IArray.empty, IArray.empty)), faceRef, s"$qn: `Foo[]` is the bare type")
      assertNotEquals(faceRef, cRef, qn)
      assertNotEquals(faceRef, kb.alloc(Term.Fn(c, IArray.empty, IArray.empty)), qn)

      val rid = kb.assertFact(unary(kb, held, faceRef), factSort, domain)
      assertEquals(solutions(kb, unary(kb, held, cRef)), 0, s"$qn: the instance does not find the type")
      assertEquals(solutions(kb, unary(kb, held, faceRef)), 1, s"$qn: the type finds itself")
      kb.retract(rid)
      val rid2 = kb.assertFact(unary(kb, held, cRef), factSort, domain)
      assertEquals(solutions(kb, unary(kb, held, faceRef)), 0, s"$qn: the type does not find the instance")
      kb.retract(rid2)

    val foo = kb.resolveSymbol("zzfaces.Foo")
    val x = kb.intern("X")
    val int64 = kb.alloc(Term.Ref(kb.resolveSymbol("anthill.prelude.Int64")))
    val ty = kb.alloc(Term.Fn(kb.typeFaceOf(foo), IArray.empty, IArray((x, int64))))
    kb.assertFact(unary(kb, held, ty), factSort, domain)
    val v = kb.alloc(Term.Var(Var.Global(kb.freshVar(x))))
    val pattern = kb.alloc(Term.Fn(foo, IArray.empty, IArray((x, v))))
    assertEquals(solutions(kb, unary(kb, held, pattern)), 0,
      "`held(Foo(X: ?v))` does not find `held(Foo[X = Int64])`")
    assertEquals(solutions(kb, unary(kb, held, ty)), 1, "the control: the type finds itself")
  }
