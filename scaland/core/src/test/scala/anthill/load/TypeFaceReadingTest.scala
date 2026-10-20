package anthill.load

import anthill.codegen.scala.StdlibFixture
import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Literal, Term, Var}
import anthill.resolve.SearchStream

/** WI-20261020-80VNX — A CONSTRUCTOR'S TYPE AND ITS INSTANCE ARE TWO TERMS (rustland's
  * `wi_jb6rs_type_face_test`, WI-20260902-JB6RS). A constructor is a sort in its own right
  * (kernel-language.md §6.3), so its one declaration has two readings, and a name is read
  * by its context (§4.4, *A name has a reading in each context*): in a type context — a
  * bracket's binding — a constructor is its TYPE, named by the declaration's type face; in
  * a data context it is its INSTANCE; and its type written as data takes the bracket,
  * `red[]`. For every constructor: one nested in a sort, an eponymous one, a free-standing
  * one. Only a BARE name falls back to another reading: `S(…)` over a name that is only a
  * type applies nothing and is refused.
  *
  * Rustland's rows that read an operation body, the typer's field check, the query
  * converter or the JSON store have no scaland twin — scaland has none of the four. The
  * positional = named normalization of a bracket in a clause (`Pair.both[Int64, String]`)
  * is WI-20260908-9WVT7's cef5913b in rustland, not ported (WI-20260823-53W12).
  *
  * BACKED OUT, each part alone (measured), the rows named fail:
  *  * a binding's own bracket recorded as one (`typeExprToRef`'s `Parameterized`):
  *    `nestedIsTheType`;
  *  * `KnowledgeBase.typeFaceOf` minting nothing (answering the plain symbol): every
  *    type/instance row — the two are one term again;
  *  * the bracket's face in `Loader.reallocTerm` (`isTypeApp`): the bracket rows;
  *  * a type-position name's face (`isTypeName` in the `Term.Ref` arm), or the parser
  *    recording it (`typeExprToRef`'s `Simple`): `bindingJoinsTheType`, `arrowIsTheType`,
  *    `arrowBareIsTheType`, `callBracketIsTheType`.
  *    `bareBindingIsTheType` and `fieldedBindingIsTheType` pass either way BY DESIGN —
  *    `Box[V = red]` and `Box[V = red[]]` are one parse term, the binding a type
  *    context — and pin that the two spellings stay one;
  *  * the parser's empty bracket (`instArgsList`'s `rep(0)`): the fixtures do not parse;
  *  * the canon exempting a sort again: `bareFindsBracket`, `sortTyBare` and the store rows;
  *  * the `SortAppliedAsData` refusal, or its `quoted` gate: the refusal rows;
  *  * `reflectKind`'s face arm: `typeKind` answers `entity`;
  *  * `extract_sort_ref` keeping the face: `faceNamesItsSort` answers 0.
  * `instanceFindsInstance` and `typeFindsType` pass either way BY DESIGN — they are the
  * controls that the facts are found at all. */
class TypeFaceReadingTest extends munit.FunSuite:

  private def answers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.freshVar(kb.intern("x"))
    val goal = kb.alloc(Term.Fn(sym, IArray(kb.alloc(Term.Var(Var.Global(v)))), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  private def bound(kb: KnowledgeBase, qn: String)(using munit.Location): IndexedSeq[Term] =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.freshVar(kb.intern("x"))
    val vt = kb.alloc(Term.Var(Var.Global(v)))
    val goal = kb.alloc(Term.Fn(sym, IArray(vt), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).map(s => kb.getTerm(kb.reify(vt, s.subst))).toIndexedSeq

  private val face =
    """namespace zzface
      |  import anthill.prelude.Int64
      |  sort Colour
      |    entity red
      |    entity green(v: Int64)
      |  end
      |  sort Box
      |    sort V = ?
      |    entity box(v: V)
      |  end
      |  sort Foo
      |    sort X = ?
      |    entity Foo(X: X)
      |  end
      |  fact held(red[])
      |  fact inst(red)
      |  fact boxed(Box[V = red])
      |  fact heldFoo(Foo[X = Int64])
      |  fact boxedFoo(Box[V = Foo[X = Int64]])
      |  rule nestedIsTheType(1) :- boxedFoo(Box[V = ?t]), heldFoo(?t)
      |  rule bindingJoinsTheType(1) :- boxed(Box[V = ?t]), held(?t)
      |  fact built(box[V = red](v: 1))
      |  rule callBracketIsTheType(1) :- built(box[V = ?t](v: 1)), held(?t)
      |  rule typeFindsType(1) :- held(red[])
      |  rule instanceFindsType(1) :- held(red)
      |  rule typeFindsInstance(1) :- inst(red[])
      |  rule instanceFindsInstance(1) :- inst(red)
      |  rule bareBindingIsTheType(1) :- boxed(Box[V = red[]])
      |end
      |""".stripMargin

  /** A bracket in a fact, a rule head or a rule body is the TYPE, and a fact over the type
    * and a fact over the instance answer only their own spelling. A bare constructor named
    * as a bracket's BINDING is the type too: `Box[V = red]` is `Box[V = red[]]`. */
  test("a bracket in a clause is the type") {
    val kb = LoadFixture.loaded(face, "face.anthill")
    assertEquals(answers(kb, "zzface.typeFindsType"), 1, "`red[]` finds the type")
    assertEquals(answers(kb, "zzface.instanceFindsType"), 0, "`red` does not find the type")
    assertEquals(answers(kb, "zzface.typeFindsInstance"), 0, "`red[]` does not find the instance")
    assertEquals(answers(kb, "zzface.instanceFindsInstance"), 1, "`red` finds the instance")
    assertEquals(answers(kb, "zzface.bareBindingIsTheType"), 1, "a binding is read in a type context")
    assertEquals(answers(kb, "zzface.bindingJoinsTheType"), 1,
      "the bare name a bracket binds is the type `red[]` written at the top")
    assertEquals(answers(kb, "zzface.callBracketIsTheType"), 1,
      "a construction's call-site bracket binds the type, as the bare bracket does")
    assertEquals(answers(kb, "zzface.nestedIsTheType"), 1,
      "a bracket nested in a binding is the type, the term the bracket at the top builds")
  }

  /** A name written in an arrow or a tuple type inside a binding is in a TYPE position
    * too, so a constructor there is its type — written bare or with its empty bracket,
    * which in a type position is the bare name. Rustland reads the interior of a type
    * written in a clause through its type lowering. The stdlib is loaded for the
    * structural lowering's own vocabulary (`TypeExtractor.Arrow`). */
  test("a name in a structural type written in a binding is the type") {
    val kb = StdlibFixture.kbWith(LoadFixture.parsed(
      """namespace zzarrow
        |  import anthill.prelude.Int64
        |  sort Colour
        |    entity red
        |  end
        |  sort Box
        |    sort V = ?
        |    entity box(v: V)
        |  end
        |  fact held(red[])
        |  fact arrowed(Box[V = (red[]) -> Int64])
        |  fact arrowedBare(Box[V = (red) -> Int64])
        |  fact tupled(Box[V = (a: red, b: Int64)])
        |  rule arrowIsTheType(1) :- arrowed(Box[V = (?t) -> Int64]), held(?t)
        |  rule arrowBareIsTheType(1) :- arrowedBare(Box[V = (?t) -> Int64]), held(?t)
        |  rule tupleIsTheType(1) :- tupled(Box[V = (a: ?t, b: Int64)]), held(?t)
        |end
        |""".stripMargin,
      "arrow.anthill",
    ))
    assertEquals(answers(kb, "zzarrow.arrowIsTheType"), 1, "`red[]` written in an arrow is the type")
    assertEquals(answers(kb, "zzarrow.arrowBareIsTheType"), 1, "and so is the bare `red` there")
    assertEquals(answers(kb, "zzarrow.tupleIsTheType"), 1, "and a tuple type's component")
  }

  /** An eponymous or free-standing entity — one name that is both a sort and its
    * constructor — has a type face too. The collision measured at the start of rustland's
    * ticket: over `entity Foo(X: X)`, whose field is labelled like its sort's parameter,
    * `fact held(Foo[X = Int64])` was found by the instance pattern `held(Foo(X: ?v))`; and
    * over a fieldless `entity Baz`, `Baz[]` and `Baz()` were one term. */
  test("an eponymous or free-standing entity's type is not its instance") {
    val kb = LoadFixture.loaded(
      """namespace zzepon
        |  import anthill.prelude.Int64
        |  sort Foo
        |    sort X = ?
        |    entity Foo(X: X)
        |  end
        |  entity Baz
        |  fact held(Foo[X = Int64])
        |  fact heldBaz(Baz[])
        |  rule typeFindsType(1) :- held(Foo[X = Int64])
        |  rule instanceFindsType(1) :- held(Foo(X: ?v))
        |  rule bazTypeFindsType(1) :- heldBaz(Baz[])
        |  rule bazInstanceFindsType(1) :- heldBaz(Baz())
        |  rule bazBareFindsType(1) :- heldBaz(Baz)
        |end
        |""".stripMargin,
      "epon.anthill",
    )
    assertEquals(answers(kb, "zzepon.typeFindsType"), 1)
    assertEquals(answers(kb, "zzepon.instanceFindsType"), 0, "the instance pattern does not find the type")
    assertEquals(answers(kb, "zzepon.bazTypeFindsType"), 1)
    assertEquals(answers(kb, "zzepon.bazInstanceFindsType"), 0, "`Baz()` does not find `Baz[]`")
    assertEquals(answers(kb, "zzepon.bazBareFindsType"), 0, "nor does the bare `Baz`, its instance")
  }

  /** A BARE constructor name in a DATA context is its INSTANCE (§4.4), and its TYPE is
    * written `Item[]`: the two never meet. A bracket's binding is a type context in a rule
    * body as in a fact, so a fielded entity named there is its type, not its pattern. A
    * fieldless constructor's two spellings are one term in the store, and a user's own
    * entity spelled like a reflect collection-literal form is an ordinary entity.
    *
    * What rustland's twin also asserts and scaland cannot: that a bare FIELDED constructor
    * in a data slot is the all-fields-fresh pattern — scaland has no partial-entity
    * expansion at all (WI-20260902-T8H1W) — and every operation-body row. */
  test("a bare constructor in a data context is its instance") {
    val kb = LoadFixture.loaded(
      """namespace zzread
        |  import anthill.prelude.Int64
        |  sort Box
        |    sort V = ?
        |    entity box(v: V)
        |  end
        |  entity Baz
        |  entity Item(n: Int64)
        |  entity TypeBox(t: Int64)
        |  entity ListLiteral
        |  fact boxedItem(Box[V = Item])
        |  fact heldT(Item[])
        |  fact TypeBox(t: Item[])
        |  rule fieldedBindingIsTheType(1) :- boxedItem(Box[V = Item[]])
        |  rule bareIsNotTheType(1) :- heldT(Item)
        |  rule bracketIsTheType(1) :- heldT(Item[])
        |  rule typedFieldHoldsTheType(1) :- TypeBox(t: Item[])
        |end
        |""".stripMargin,
      "reading.anthill",
    )
    assertEquals(answers(kb, "zzread.bareIsNotTheType"), 0, "the bare name is not the type")
    assertEquals(answers(kb, "zzread.bracketIsTheType"), 1, "`Item[]` is")
    assertEquals(answers(kb, "zzread.typedFieldHoldsTheType"), 1, "a field holds the type written there")
    assertEquals(answers(kb, "zzread.fieldedBindingIsTheType"), 1,
      "a fielded entity as a bracket's binding is its type, not its pattern")
    val baz = kb.resolveSymbol("zzread.Baz")
    assertEquals(kb.alloc(Term.Fn(baz, IArray.empty, IArray.empty)), kb.alloc(Term.Ref(baz)),
      "`Baz()` and `Baz` are one term")
    val own = kb.resolveSymbol("zzread.ListLiteral")
    assertEquals(kb.alloc(Term.Fn(own, IArray.empty, IArray.empty)), kb.alloc(Term.Ref(own)),
      "a user's `ListLiteral()` is its bare name")
  }

  /** `kind` reports a constructor's TYPE as a sort and its instance as the entity
    * (`KnowledgeBase.reflectKind`); `extract_sort_ref` answers the sort's NAME for a type
    * written with its face, so a carrier written `Foo[X = Int64]` joins a fact that names
    * `Foo`. */
  test("kind and extract_sort_ref read a type face") {
    val kb = LoadFixture.loaded(
      """namespace zzrefl
        |  import anthill.prelude.Int64
        |  import anthill.reflect.kind
        |  import anthill.reflect.typing.extract_sort_ref
        |  sort Colour
        |    entity red
        |  end
        |  sort Foo
        |    sort X = ?
        |    entity Foo(X: X)
        |  end
        |  fact named(Foo)
        |  rule typeKind(?k) :- kind(red[], ?k)
        |  rule instanceKind(?k) :- kind(red, ?k)
        |  rule faceNamesItsSort(1) :- extract_sort_ref(Foo[X = Int64], ?n), named(?n)
        |end
        |""".stripMargin,
      "refl.anthill",
    )
    def str(s: String) = Term.Const(Literal.StringLit(s))
    assertEquals(bound(kb, "zzrefl.typeKind"), IndexedSeq(str("sort")), "the type `red[]` is a sort")
    assertEquals(bound(kb, "zzrefl.instanceKind"), IndexedSeq(str("entity")), "the instance `red` is the entity")
    assertEquals(answers(kb, "zzrefl.faceNamesItsSort"), 1, "`extract_sort_ref(Foo[X = Int64])` names `Foo`")
  }

  private val sortApps =
    """namespace zzsortapp
      |  import anthill.prelude.Int64
      |  sort Shape
      |    entity circle(r: Int64)
      |  end
      |  sort Tag
      |    sort T = ?
      |  end
      |  fact holds(Shape[])
      |  fact sortTy(Int64[])
      |  fact Tag[T = Int64]
      |  rule bareFindsBracket(1) :- holds(Shape)
      |  rule bracketFindsBracket(1) :- holds(Shape[])
      |  rule sortTyBare(1) :- sortTy(Int64)
      |  rule tagByBracket(?q) :- Tag[T = ?q]
      |end
      |""".stripMargin

  /** A sort with no constructor of its name has ONE reading, its type: its bare name and
    * its empty bracket are one term (the canon exempting no sort), and its PARENTHESIZED
    * spelling names nothing to apply — `Shape()` and `Tag(T: ?q)` are refused in a fact
    * and in a rule body, where they used to be the type in silence (`Tag(T: ?q)` answered
    * from `fact Tag[T = Int64]`). Each is reported once, and a rule HEAD that resolves to
    * the sort is refused alike. */
  test("a sort has one reading and names nothing to apply") {
    val kb = LoadFixture.loaded(sortApps, "sortapp.anthill")
    assertEquals(answers(kb, "zzsortapp.bareFindsBracket"), 1, "`Shape` is `Shape[]`")
    assertEquals(answers(kb, "zzsortapp.bracketFindsBracket"), 1)
    assertEquals(answers(kb, "zzsortapp.sortTyBare"), 1, "`Int64[]` is `Int64`")
    assertEquals(bound(kb, "zzsortapp.tagByBracket"),
      IndexedSeq(kb.getTerm(kb.alloc(Term.Ref(kb.resolveSymbol("anthill.prelude.Int64"))))),
      "the bracket goal answers from the fact")
    val shape = kb.resolveSymbol("zzsortapp.Shape")
    assertEquals(kb.alloc(Term.Fn(shape, IArray.empty, IArray.empty)), kb.alloc(Term.Ref(shape)),
      "one term in the store")

    for (decl, sort) <- Seq(
        ("rule viaParens(?q) :- Tag(T: ?q)", "Tag"),
        ("rule shapeNullary(1) :- holds(Shape())", "Shape"),
        ("fact holds2(Shape())", "Shape")) do
      val src = sortApps.stripSuffix("end\n") + s"  $decl\nend\n"
      val parsed = LoadFixture.parsed(src, "sortapp2.anthill")
      val kb2 = KnowledgeBase()
      Prelude.register(kb2)
      LoadFixture.registerKernel(kb2)
      val errs = Loader.loadAll(kb2, IndexedSeq(parsed)).map(_.toString)
      assertEquals(errs.count(_.contains(s"`$sort(…)` is an application")), 1,
        s"`$decl` is refused, once: $errs")

    // A rule head that resolves to the sort applies it, and is refused too — it mints no
    // predicate of the sort's name (§4.4; rustland's row reaches the same refusal).
    val headErrs = {
      val kb3 = KnowledgeBase()
      Prelude.register(kb3)
      LoadFixture.registerKernel(kb3)
      Loader.loadAll(kb3, IndexedSeq(LoadFixture.parsed(
        sortApps.stripSuffix("end\n") + "  rule Shape(1) :- holds(Shape)\nend\n", "sorthead.anthill")))
        .map(_.toString)
    }
    assertEquals(headErrs.count(_.contains("`Shape(…)` is an application")), 1, s"$headErrs")
  }

  /** Inside a field declared `anthill.reflect.Term` — or a `List` or `Option` of one — the
    * pattern is QUOTED, as written, so `Tag(T: 1)` there is held, not refused — in a
    * fact, and in the rule-body goal that searches for it alike. Rustland reads the field's declared type through its typer;
    * scaland records it (`Loader.QuotedFieldPass`). The stdlib is loaded for
    * `anthill.reflect.Term`. A field declared at any other type is no quote: the control. */
  test("a field declared Term quotes what is written in it") {
    val kb = StdlibFixture.kbWith(LoadFixture.parsed(
      """namespace zzquoted
        |  import anthill.prelude.Int64
        |  import anthill.reflect.Term
        |  sort Tag
        |    sort T = ?
        |  end
        |  entity holdsQ(pattern: Term)
        |  entity holdsQs(patterns: List[T = Term], maybe: Option[T = Term])
        |  fact holdsQ(pattern: Tag(T: 1))
        |  fact holdsQ(Tag(T: 2))
        |  fact holdsQs(patterns: [Tag(T: 3)], maybe: some(Tag(T: 4)))
        |  rule found(1) :- holdsQ(pattern: Tag(T: 1))
        |end
        |""".stripMargin,
      "quoted.anthill",
    ))
    assertEquals(answers(kb, "zzquoted.found"), 1, "the goal's quoted pattern finds the fact's")
    // THE CONTROL, over the stdlib too, so `anthill.reflect.Term` is declared and the
    // field's type is what decides: an `Int64` field, and a `List` of one, quote nothing.
    val control = LoadFixture.parsed(
      """namespace zzunquoted
        |  import anthill.prelude.Int64
        |  sort Tag
        |    sort T = ?
        |  end
        |  entity holdsI(pattern: Int64, patterns: List[T = Int64])
        |  fact holdsI(pattern: Tag(T: 1), patterns: [Tag(T: 2)])
        |end
        |""".stripMargin,
      "unquoted.anthill",
    )
    val kb2 = KnowledgeBase()
    Prelude.register(kb2)
    val errs = Loader.loadProgram(kb2, StdlibFixture.parsed, IndexedSeq(control)).map(_.toString)
    assertEquals(errs.count(_.contains("`Tag(…)` is an application")), 2,
      s"an Int64 field quotes nothing, nor a list of them: $errs")
  }
