package anthill.load

import anthill.kb.{KnowledgeBase, SortKind}
import anthill.term.{Term, TermId, VarId, Literal}
import anthill.intern.TermSymbol
import anthill.parse.*
import anthill.span.Span
import anthill.resolve.{SearchStream, ResolveConfig}
import anthill.subst.Substitution
import scala.collection.mutable.ArrayBuffer

class LoaderTest extends munit.FunSuite:

  private def emptySpan = Span.empty

  /** Helper to build a manual ParsedFile with facts and rules. */
  private def buildSimpleParsedFile(): (ParsedFile, Int) =
    val symbols = anthill.intern.SymbolTable()
    val terms = SimpleTermStore()

    // Build: parent("alice", "bob") and parent("bob", "charlie")
    val parentSym = symbols.intern("parent")
    val alice = terms.alloc(Term.Const(Literal.StringLit("alice")))
    val bob = terms.alloc(Term.Const(Literal.StringLit("bob")))
    val charlie = terms.alloc(Term.Const(Literal.StringLit("charlie")))

    val fact1Term = terms.alloc(Term.Fn(parentSym, IArray(alice, bob), IArray.empty))
    val fact2Term = terms.alloc(Term.Fn(parentSym, IArray(bob, charlie), IArray.empty))

    // Build rule: grandparent(?x, ?z) :- parent(?x, ?y), parent(?y, ?z)
    val grandparentSym = symbols.intern("grandparent")
    val xSym = symbols.intern("x"); val ySym = symbols.intern("y"); val zSym = symbols.intern("z")
    val vx = VarId(0, xSym); val vy = VarId(1, ySym); val vz = VarId(2, zSym)
    val varX = terms.alloc(Term.Var(vx)); val varY = terms.alloc(Term.Var(vy)); val varZ = terms.alloc(Term.Var(vz))

    val ruleHead = terms.alloc(Term.Fn(grandparentSym, IArray(varX, varZ), IArray.empty))
    val ruleBody1 = terms.alloc(Term.Fn(parentSym, IArray(varX, varY), IArray.empty))
    val ruleBody2 = terms.alloc(Term.Fn(parentSym, IArray(varY, varZ), IArray.empty))

    val items = ArrayBuffer[Item](
      Item.FactItem(Fact(fact1Term, None, emptySpan)),
      Item.FactItem(Fact(fact2Term, None, emptySpan)),
      Item.RuleItem(Rule(
        label = None,
        heads = IndexedSeq(RuleHead.TermHead(ruleHead)),
        body = Some(IndexedSeq(ruleBody1, ruleBody2)),
        meta = None,
        span = emptySpan
      ))
    )

    val parsed = ParsedFile(items, symbols, terms)
    (parsed, TermSymbol.raw(grandparentSym))

  test("prelude registers primitive sorts") {
    val kb = KnowledgeBase()
    Prelude.register(kb)

    assert(kb.hasQualifiedName("anthill.prelude.Int64"))
    assert(kb.hasQualifiedName("anthill.prelude.String"))
    assert(kb.hasQualifiedName("anthill.prelude.Float"))
    assert(kb.hasQualifiedName("anthill.prelude.Bool"))

    val intSym = kb.tryResolveSymbol("anthill.prelude.Int64").get
    val intTerm = kb.makeNameTermFromSym(intSym)
    assertEquals(kb.sortKind(intTerm), Some(SortKind.Defined))
  }

  test("prelude registers kernel meta sorts") {
    val kb = KnowledgeBase()
    Prelude.register(kb)

    assert(kb.hasQualifiedName("anthill.reflect.Sort"))
    assert(kb.hasQualifiedName("anthill.reflect.Fact"))
    assert(kb.hasQualifiedName("anthill.reflect.Rule"))
    assert(kb.hasQualifiedName("anthill.reflect.Entity"))
  }

  test("load facts into KB") {
    val kb = KnowledgeBase()
    Prelude.register(kb)

    val (parsed, _) = buildSimpleParsedFile()
    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")

    // Should have 2 facts + 1 rule
    assertEquals(kb.factCount, 2)
    assertEquals(kb.ruleCount, 1)
  }

  test("end-to-end: load and resolve grandparent") {
    val kb = KnowledgeBase()
    Prelude.register(kb)

    val (parsed, _) = buildSimpleParsedFile()
    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")

    // Query: grandparent(?a, ?b)
    val gpSym = kb.intern("grandparent")
    val aSym = kb.intern("a"); val bSym = kb.intern("b")
    val va = kb.freshVar(aSym); val vb = kb.freshVar(bSym)
    val varA = kb.alloc(Term.Var(va)); val varB = kb.alloc(Term.Var(vb))
    val query = kb.alloc(Term.Fn(gpSym, IArray(varA, varB), IArray.empty))

    val solutions = SearchStream.resolve(kb, query).allSolutions(kb)
    assertEquals(solutions.length, 1)

    val sol = solutions(0)
    val aBinding = sol.subst.resolve(va).map(t => kb.getTerm(t))
    val bBinding = sol.subst.resolve(vb).map(t => kb.getTerm(t))
    assertEquals(aBinding, Some(Term.Const(Literal.StringLit("alice"))))
    assertEquals(bBinding, Some(Term.Const(Literal.StringLit("charlie"))))
  }

  test("load namespace with scoping") {
    val kb = KnowledgeBase()
    Prelude.register(kb)

    val symbols = anthill.intern.SymbolTable()
    val terms = SimpleTermStore()

    val colorSym = symbols.intern("color")
    val red = terms.alloc(Term.Const(Literal.StringLit("red")))
    val factTerm = terms.alloc(Term.Fn(colorSym, IArray(red), IArray.empty))

    val nsName = Name.simple(symbols.intern("Colors"), emptySpan)
    val ns = Namespace(
      name = nsName,
      imports = IndexedSeq.empty,
      items = IndexedSeq(Item.FactItem(Fact(factTerm, None, emptySpan))),
      span = emptySpan
    )
    val items = ArrayBuffer[Item](Item.NamespaceItem(ns))
    val parsed = ParsedFile(items, symbols, terms)

    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")

    assert(kb.hasQualifiedName("Colors"))
    assertEquals(kb.factCount, 1)
  }

  test("load sort with entity-of") {
    val kb = KnowledgeBase()
    Prelude.register(kb)

    val symbols = anthill.intern.SymbolTable()
    val terms = SimpleTermStore()

    val natName = Name.simple(symbols.intern("Nat"), emptySpan)
    val zeroName = Name.simple(symbols.intern("Zero"), emptySpan)

    val zeroEntity = Entity(
      visibility = None,
      name = zeroName,
      fields = IndexedSeq.empty,
      meta = None,
      span = emptySpan
    )

    val natSort = SortWithBody(
      visibility = None,
      name = natName,
      descriptions = IndexedSeq.empty,
      imports = IndexedSeq.empty,
      items = IndexedSeq(Item.EntityItem(zeroEntity)),
      meta = None,
      span = emptySpan
    )

    val items = ArrayBuffer[Item](Item.SortWithBodyItem(natSort))
    val parsed = ParsedFile(items, symbols, terms)

    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")

    assert(kb.hasQualifiedName("Nat"))
    assert(kb.hasQualifiedName("Nat.Zero"))

    val natSym = kb.tryResolveSymbol("Nat").get
    val natTerm = kb.makeNameTermFromSym(natSym)
    val zeroSym = kb.tryResolveSymbol("Nat.Zero").get
    val zeroTerm = kb.makeNameTermFromSym(zeroSym)

    assert(kb.isEntityOf(zeroTerm, natTerm))
    assertEquals(kb.sortKind(natTerm), Some(SortKind.Defined))
    assertEquals(kb.sortKind(zeroTerm), Some(SortKind.Constructor))
  }

  test("prelude registers collection literal entities") {
    val kb = KnowledgeBase()
    Prelude.register(kb)

    assert(kb.hasQualifiedName("anthill.reflect.ListLiteral"))
    assert(kb.hasQualifiedName("anthill.reflect.SetLiteral"))
    assert(kb.hasQualifiedName("anthill.reflect.TupleLiteral"))
    assert(kb.hasQualifiedName("anthill.reflect.SortInfo"))
    assert(kb.hasQualifiedName("anthill.reflect.FieldInfo"))
  }

  test("ListLiteral term loads into KB") {
    val kb = KnowledgeBase()
    Prelude.register(kb)

    val symbols = anthill.intern.SymbolTable()
    val terms = SimpleTermStore()

    // Build: fact Task("T-001", tags: ListLiteral("rust", "core"))
    // First define namespace test with sort Status + entity Task
    val testNs = Name.simple(symbols.intern("test"), emptySpan)
    val taskName = Name.simple(symbols.intern("Task"), emptySpan)
    val idField = FieldDecl(symbols.intern("id"), TypeExpr.Simple(Name.simple(symbols.intern("String"), emptySpan)))
    val tagsField = FieldDecl(symbols.intern("tags"), TypeExpr.Simple(Name.simple(symbols.intern("List"), emptySpan)))
    val taskEntity = Entity(None, taskName, IndexedSeq(idField, tagsField), None, emptySpan)
    val taskSortName = Name.simple(symbols.intern("TaskSort"), emptySpan)
    val taskSort = SortWithBody(None, taskSortName, IndexedSeq.empty, IndexedSeq.empty,
      IndexedSeq(Item.EntityItem(taskEntity)), None, emptySpan)
    val ns = Namespace(testNs, IndexedSeq.empty,
      IndexedSeq(Item.SortWithBodyItem(taskSort)), emptySpan)

    // Build the ListLiteral term
    val listLitSym = symbols.intern("ListLiteral")
    val rust = terms.alloc(Term.Const(Literal.StringLit("rust")))
    val core = terms.alloc(Term.Const(Literal.StringLit("core")))
    val listTerm = terms.alloc(Term.Fn(listLitSym, IArray(rust, core), IArray.empty))

    // Build fact: Task("T-001", tags: ListLiteral("rust", "core"))
    val taskSym = symbols.intern("Task")
    val idSym = symbols.intern("id")
    val tagsSym = symbols.intern("tags")
    val idVal = terms.alloc(Term.Const(Literal.StringLit("T-001")))
    val factTerm = terms.alloc(Term.Fn(taskSym, IArray.empty,
      IArray((idSym, idVal), (tagsSym, listTerm))))
    val fact = Fact(factTerm, None, emptySpan)

    val items = ArrayBuffer[Item](
      Item.NamespaceItem(ns),
      Item.FactItem(fact)
    )
    val parsed = ParsedFile(items, symbols, terms)

    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(kb.factCount > 0, s"should have loaded facts, got ${kb.factCount}, errors: $errors")

    // Verify the ListLiteral functor resolved to the global import
    val listLitResolved = kb.tryResolveSymbol("anthill.reflect.ListLiteral")
    assert(listLitResolved.isDefined, "ListLiteral should be a resolved symbol")
  }

  test("entityParentSort and isConstructorSymbol") {
    val kb = KnowledgeBase()
    Prelude.register(kb)

    val symbols = anthill.intern.SymbolTable()
    val terms = SimpleTermStore()

    val colorName = Name.simple(symbols.intern("Color"), emptySpan)
    val redName = Name.simple(symbols.intern("Red"), emptySpan)
    val blueName = Name.simple(symbols.intern("Blue"), emptySpan)

    val redEntity = Entity(None, redName, IndexedSeq.empty, None, emptySpan)
    val blueEntity = Entity(None, blueName, IndexedSeq.empty, None, emptySpan)
    val colorSort = SortWithBody(None, colorName, IndexedSeq.empty, IndexedSeq.empty,
      IndexedSeq(Item.EntityItem(redEntity), Item.EntityItem(blueEntity)), None, emptySpan)

    val items = ArrayBuffer[Item](Item.SortWithBodyItem(colorSort))
    val parsed = ParsedFile(items, symbols, terms)

    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")

    val colorSym = kb.tryResolveSymbol("Color").get
    val colorTerm = kb.makeNameTermFromSym(colorSym)
    val redSym = kb.tryResolveSymbol("Color.Red").get
    val redTerm = kb.makeNameTermFromSym(redSym)
    val blueSym = kb.tryResolveSymbol("Color.Blue").get
    val blueTerm = kb.makeNameTermFromSym(blueSym)

    // entityParentSort
    assertEquals(kb.entityParentSort(redTerm), Some(colorTerm))
    assertEquals(kb.entityParentSort(blueTerm), Some(colorTerm))
    assertEquals(kb.entityParentSort(colorTerm), None)

    // isConstructorSymbol
    assert(kb.isConstructorSymbol(redSym), "Red should be a constructor symbol")
    assert(kb.isConstructorSymbol(blueSym), "Blue should be a constructor symbol")
    assert(!kb.isConstructorSymbol(colorSym), "Color should not be a constructor symbol")
  }

  // WI-528 (proposal 049): a `<=>`-spelled equation parses (Pratt maps `<=>` to
  // the `unify` functor), loads without error, and the loaded rule is recognized
  // as an equation — so `SearchStream` excludes it from ordinary SLD candidates
  // exactly like a legacy `=`/`eq` equation. This is the whole pipeline the
  // stdlib migration (WI-526) rides on.
  test("WI-528: a `<=>`-spelled equation loads and is recognized as an equation") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val parsed = Parser.parse("rule f(?x) <=> g(?x)", "<wi528>")
      .toOption.getOrElse(fail("parse failed"))
    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")

    // `<=>` desugars the whole rule to head `unify(f(?x), g(?x))`, empty body.
    // With no kernel.anthill loaded, the `unify` functor interns bare, so
    // byFunctor(intern("unify")) finds it.
    val unifyRules = kb.byFunctor(kb.intern("unify"))
    assertEquals(unifyRules.length, 1, "one unify-headed rule loaded")
    assert(kb.isEquation(unifyRules(0)), "the loaded `<=>` rule is an equation")
  }

  // WI-582: a typed rule pattern `?x: T` parses to a `typed_var(?x, type: T)`
  // marker; the loader STRIPS it back to the bare `?x` (scaland has no typer, so
  // the bound is dropped, not enforced), keeping the head matchable as `p(?x)`.
  test("WI-582: a typed rule pattern loads with a BARE head (marker stripped)") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val parsed = Parser.parse(
      """rule q(42)
        |rule p(?x: Numeric) :- q(?x)""".stripMargin, "<wi582load>")
      .toOption.getOrElse(fail("parse failed"))
    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")

    // The head `p(?x: Numeric)` strips to the bare `p(?x)`: the ground query
    // `p(42)` resolves through the body `q(42)`. Were the marker NOT stripped,
    // the head arg would be `typed_var(?x, …)` (a Fn) and `p(42)` would not unify.
    val pSym = kb.intern("p")
    val fortyTwo = kb.alloc(Term.Const(Literal.IntLit(42)))
    val query = kb.alloc(Term.Fn(pSym, IArray(fortyTwo), IArray.empty))
    val solutions = SearchStream.resolve(kb, query).allSolutions(kb)
    assertEquals(solutions.length, 1, "the bare typed head resolves the ground query")
  }

  // WI-582 (review): the strip is gated on the EXACT marker shape (functor
  // `typed_var` + one pos arg + a `type` named arg). A user functor merely NAMED
  // `typed_var` must NOT be stripped — matching by name alone would crash on a
  // 0-arg call and silently drop args from a 2-arg call (mirrors rustland's guard).
  test("WI-582: a non-marker functor named `typed_var(a, b)` loads intact (not stripped)") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val parsed = Parser.parse("rule typed_var(1, 2)", "<wi582guard2>")
      .toOption.getOrElse(fail("parse failed"))
    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")
    // Stripped-by-name would rewrite the head to the literal `1` (no `typed_var`
    // rule); the tightened guard leaves it as the 2-ary functor.
    assertEquals(kb.byFunctor(kb.intern("typed_var")).length, 1,
      "the non-marker `typed_var` rule loads as itself")
  }

  test("WI-582: a bare `typed_var()` (0 args) does not crash the loader") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val parsed = Parser.parse("rule typed_var()", "<wi582guard0>")
      .toOption.getOrElse(fail("parse failed"))
    // Matching by name alone would do `posArgs(0)` → IndexOutOfBounds; the guard
    // requires exactly one pos arg, so this loads as an ordinary 0-ary functor.
    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")
    assertEquals(kb.byFunctor(kb.intern("typed_var")).length, 1)
  }

  // WI-451/WI-452 (§5.4): the enclosing-list HK sort type-param form loads, and
  // both the higher-kinded carrier `F` and the simple param `A` register as type
  // parameters of the enclosing sort (the marker the resolver/codegen read; scaland
  // emits no `SortAlias` backing var — it has no typer).
  test("WI-452: `sort CpsMonad[F[T], A]` registers F and A as type params") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val parsed = Parser.parse(
      """sort CpsMonad[F[T], A]
        |  operation unit(x: A) -> F
        |end""".stripMargin, "<wi452>").toOption.getOrElse(fail("parse failed"))
    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")

    val globalRaw = kb.makeNameTerm("_global").raw
    val cpsSym = kb.symbols.scope(globalRaw).flatMap(_.locals.get("CpsMonad"))
      .getOrElse(fail("CpsMonad not defined in global scope"))
    val cpsScope = kb.symbols.scope(kb.makeNameTermFromSym(cpsSym).raw)
      .getOrElse(fail("no CpsMonad scope"))
    assert(cpsScope.typeParams.contains("F"), s"F should be a type param, got ${cpsScope.typeParams}")
    assert(cpsScope.typeParams.contains("A"), s"A should be a type param, got ${cpsScope.typeParams}")
  }
