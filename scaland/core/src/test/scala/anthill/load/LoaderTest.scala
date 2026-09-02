package anthill.load

import anthill.kb.{KnowledgeBase, SortKind}
import anthill.term.{Term, TermId, Var, VarId, Literal}
import anthill.intern.{TermSymbol, SymbolDef, SymbolKind}
import anthill.parse.*
import anthill.span.Span
import anthill.resolve.{SearchStream, ResolveConfig}
import anthill.subst.Substitution
import scala.collection.mutable.ArrayBuffer

class LoaderTest extends munit.FunSuite:

  /** The symbol a top-level rule HEAD carries. Since the pass-3 port
    * (WI-894/896/898) a rule-introduced functor is a REGISTERED symbol, distinct
    * from the bare intern of the same string — so a `byFunctor` lookup must ask the
    * symbol table, not `intern`. */
  private def ruleFunctor(kb: KnowledgeBase, name: String): TermSymbol =
    kb.tryResolveSymbol(name)
      .getOrElse(fail(s"`$name` should be registered as a rule-introduced functor"))

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

    val fact1Term = terms.allocAt(Term.Fn(parentSym, IArray(alice, bob), IArray.empty), Span.empty)
    val fact2Term = terms.allocAt(Term.Fn(parentSym, IArray(bob, charlie), IArray.empty), Span.empty)

    // Build rule: grandparent(?x, ?z) :- parent(?x, ?y), parent(?y, ?z)
    val grandparentSym = symbols.intern("grandparent")
    val xSym = symbols.intern("x"); val ySym = symbols.intern("y"); val zSym = symbols.intern("z")
    val vx = VarId(0, xSym); val vy = VarId(1, ySym); val vz = VarId(2, zSym)
    val varX = terms.alloc(Term.Var(Var.Global(vx))); val varY = terms.alloc(Term.Var(Var.Global(vy))); val varZ = terms.alloc(Term.Var(Var.Global(vz)))

    val ruleHead = terms.allocAt(Term.Fn(grandparentSym, IArray(varX, varZ), IArray.empty), Span.empty)
    val ruleBody1 = terms.allocAt(Term.Fn(parentSym, IArray(varX, varY), IArray.empty), Span.empty)
    val ruleBody2 = terms.allocAt(Term.Fn(parentSym, IArray(varY, varZ), IArray.empty), Span.empty)

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

  /** A file whose ONLY declaration is `namespace Colors` holding one `color("red")`
    * fact — the minimal scope-descent fixture. Built fresh per call: a `ParsedFile`
    * carries its own symbol table and term store, so two KBs must not share one. */
  private def buildNamespacedParsedFile(): ParsedFile =
    val symbols = anthill.intern.SymbolTable()
    val terms = SimpleTermStore()
    val colorSym = symbols.intern("color")
    val red = terms.alloc(Term.Const(Literal.StringLit("red")))
    val factTerm = terms.allocAt(Term.Fn(colorSym, IArray(red), IArray.empty), Span.empty)
    val ns = Namespace(
      name = Name.simple(symbols.intern("Colors"), emptySpan),
      imports = IndexedSeq.empty,
      items = IndexedSeq(Item.FactItem(Fact(factTerm, None, emptySpan))),
      span = emptySpan
    )
    ParsedFile(ArrayBuffer[Item](Item.NamespaceItem(ns)), symbols, terms)

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

    // Query: grandparent(?a, ?b).
    // `grandparent` is a RULE-INTRODUCED functor, so since the pass-3 port
    // (WI-894/896/898) it is a REGISTERED symbol, not a bare intern — the query must
    // name the same symbol the head does or it matches nothing.
    val gpSym = ruleFunctor(kb, "grandparent")
    val aSym = kb.intern("a"); val bSym = kb.intern("b")
    val va = kb.freshVar(aSym); val vb = kb.freshVar(bSym)
    val varA = kb.alloc(Term.Var(Var.Global(va))); val varB = kb.alloc(Term.Var(Var.Global(vb)))
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

    val errors = Loader.loadAll(kb, IndexedSeq(buildNamespacedParsedFile()))
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
    val listTerm = terms.allocAt(Term.Fn(listLitSym, IArray(rust, core), IArray.empty), Span.empty)

    // Build fact: Task("T-001", tags: ListLiteral("rust", "core"))
    val taskSym = symbols.intern("Task")
    val idSym = symbols.intern("id")
    val tagsSym = symbols.intern("tags")
    val idVal = terms.alloc(Term.Const(Literal.StringLit("T-001")))
    val factTerm = terms.allocAt(Term.Fn(taskSym, IArray.empty,
      IArray((idSym, idVal), (tagsSym, listTerm))), Span.empty)
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

  /** WI-985 — AN ENTITY'S PARENT IS ITS ENCLOSING SORT, AND A NAMESPACE IS NOT ONE.
    *
    * Driven through the `is_entity_of` BUILTIN rather than `kb.isEntityOf`, because the
    * builtin is what the stdlib actually consults: `reflect/typing.anthill`'s `entity_of`
    * rule guards `scope(?x, ?sort)` with it precisely so a namespace-level entity yields
    * no parent, and before this WI it yielded the namespace.
    *
    * CONTROL, and it takes both halves. MEASURED by deleting both `isSortScope` gates:
    * the SECOND assertion fails — `Loose` answers 1 solution where 0 is right — and it is
    * the only failure in the suite, 337 of 338 still passing. The FIRST passes either way
    * BY DESIGN: it is the sort-body case the gate must not touch, and it is here because
    * a gate that answered 0 for everything would satisfy the second assertion alone. */
  test("WI-985: a namespace-level entity has no parent sort; a sort-body one does") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val parsed = Parser.parse(
      """namespace demo
        |  entity Loose(x: Nat)
        |  sort Holder
        |    entity Tight(y: Nat)
        |  end
        |end""".stripMargin, "<wi985>")
      .toOption.getOrElse(fail("parse failed"))
    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")

    def solutionsOf(child: String, parent: String): Int =
      val goal = kb.alloc(Term.Fn(
        kb.resolveSymbol("anthill.reflect.typing.is_entity_of"),
        IArray(
          kb.makeNameTermFromSym(kb.resolveSymbol(child)),
          kb.makeNameTermFromSym(kb.resolveSymbol(parent))),
        IArray.empty))
      SearchStream.resolve(kb, goal).allSolutions(kb).length

    assertEquals(solutionsOf("demo.Holder.Tight", "demo.Holder"), 1,
      "a sort-body entity IS an entity of its sort")
    assertEquals(solutionsOf("demo.Loose", "demo"), 0,
      "a namespace-level entity is NOT an entity of the namespace enclosing it")
  }

  // ── WI-20260902-CZJ2N: the two nullary spellings are ONE predicate ────

  /** THE TICKET'S OWN 2x2, DRIVEN. `rule tgtA :- b(1)` and `rule tgtB() :- b(1)` are two
    * spellings of one nullary predicate, and each of the four goals must answer.
    *
    * BEFORE: `aa` 1, `ab` 0, `ba` 0, `bb` 1 — each spelling answered its own and neither
    * answered the other's, on a program that loads clean. scaland had no nullary canon at
    * all (`KnowledgeBase.alloc` was a plain `terms.alloc`), and its discrimination tree
    * keyed a bare name under `DiscrimKey.RefKey` — a second key space — so the split was
    * at the STORE and at the INDEX, where no view-layer bridge could reach it.
    *
    * BACKED OUT at either half — the canon in `KnowledgeBase.alloc`, or the `Term.Ref`
    * arm of `SubstTree`'s six walks — the `ab` and `ba` rows fail while `aa` and `bb`
    * pass, which is what says the axis is the SPELLING and not the predicate machinery.
    */
  test("WI-20260902-CZJ2N: a nullary predicate answers in BOTH goal spellings") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val parsed = Parser.parse(
      """rule bczj(1)
        |rule tgtA :- bczj(1)
        |rule tgtB() :- bczj(1)
        |rule aa(1) :- tgtA
        |rule ab(1) :- tgtA()
        |rule ba(1) :- tgtB
        |rule bb(1) :- tgtB()""".stripMargin, "<czj2n>")
      .toOption.getOrElse(fail("parse failed"))
    val errors = Loader.loadAll(kb, IndexedSeq(parsed))
    assert(errors.isEmpty, s"Load errors: $errors")

    val one = kb.alloc(Term.Const(Literal.IntLit(1)))
    for name <- Seq("aa", "ab", "ba", "bb") do
      val query = kb.alloc(Term.Fn(ruleFunctor(kb, name), IArray(one), IArray.empty))
      assertEquals(
        SearchStream.resolve(kb, query).allSolutions(kb).length, 1,
        s"`$name` must answer — the head and the goal are one predicate however each is spelled")
  }

  /** THE STORE IS WHERE IT LIVES, asserted directly so the row above cannot pass by some
    * later layer papering over two terms. */
  test("WI-20260902-CZJ2N: `f()` and `f` are ONE TermId, unless `f` is a SORT") {
    val kb = KnowledgeBase()
    val g = kb.globalScope
    val pred = kb.symbols.define("holds", "holds", SymbolKind.Goal, g)
    assertEquals(
      kb.alloc(Term.Fn(pred, IArray.empty, IArray.empty)),
      kb.alloc(Term.Ref(pred)),
      "a name with no TYPE reading has one nullary term")

    val sort = kb.symbols.define("Shape", "Shape", SymbolKind.Sort, g)
    assert(
      kb.alloc(Term.Fn(sort, IArray.empty, IArray.empty)) != kb.alloc(Term.Ref(sort)),
      "a SORT keeps both — `Ref(S)` is the dispatch wildcard, `Fn(S)` the concrete " +
        "spec identity (§8.3 / WI-391 / WI-387)")
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
    val pSym = ruleFunctor(kb, "p")
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
    assertEquals(kb.byFunctor(ruleFunctor(kb, "typed_var")).length, 1,
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
    assertEquals(kb.byFunctor(ruleFunctor(kb, "typed_var")).length, 1)
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

    val cpsSym = kb.symbols.scope(kb.globalScope).flatMap(_.locals.get("CpsMonad"))
      .getOrElse(fail("CpsMonad not defined in global scope"))
    val cpsScope = kb.symbols.scope(kb.symbols.scopeOf(cpsSym))
      .getOrElse(fail("no CpsMonad scope"))
    assert(cpsScope.typeParams.contains("F"), s"F should be a type param, got ${cpsScope.typeParams}")
    assert(cpsScope.typeParams.contains("A"), s"A should be a type param, got ${cpsScope.typeParams}")
  }

  /** WI-949: the scan passes and the loader walk ONE scope spine, so a scope they
    * cannot find gets ONE answer — reported, not skipped. Before WI-949 pass 2 and the
    * loader each `foreach`-skipped a miss while pass 3 reported it; a skip abandons the
    * whole subtree (imports unwired, rule heads unregistered, facts never asserted)
    * with no diagnostic at all.
    *
    * `Loader.load` without `scanDefinitions` is the only reachable miss — `loadAll`
    * runs the defining pass over every file first. Back the change out and THIS test
    * fails: the loader returns no errors and drops the namespace's fact in silence.
    * The CONTROL is `load namespace with scoping`, which takes the same fixture through
    * the full pipeline and still loads clean — it passes either way by design, and is
    * what says the error here is about the missing scope and not about the file. */
  test("WI-949: a scope the loader cannot find is reported, not silently skipped") {
    val unscanned = KnowledgeBase()
    Prelude.register(unscanned)
    val errors = Loader.load(unscanned, buildNamespacedParsedFile())
    assert(
      errors.exists {
        case LoadError.Other(msg, _) => msg.contains("Colors")
        case _ => false
      },
      s"a scope that cannot be entered must be reported, and named: $errors")
    // The fact IS dropped — which is precisely why the drop may not be silent.
    assertEquals(unscanned.factCount, 0)
    // The control — the same file through the full pipeline — is
    // `load namespace with scoping`, which shares this fixture.
  }

  /** WI-1007 — the limitation the Expr conversion cluster was deleted to stop
    * pretending away: scaland PARSES an operation body and does not load it.
    *
    * It replaces a test in `ExprLoaderTest` named "buildList creates cons-list" that
    * called no builder and converted no expression — its own comment said so ("facts use
    * reallocTerm, not convertExprTerm"). It loaded a literal fact and asserted
    * `factCount > 0`, which is how ~250 lines of conversion machinery sat unreachable
    * under a green suite for five months.
    *
    * CONTROL, in the same load and the same resolver call shape: `marker(?x)` — a fact —
    * yields its solution. So the operation's zero is the BODY's absence, not a dead
    * fixture or an unwired KB. Back the DELETION out and this test still passes: the
    * cluster had no caller, so nothing observable changes either way — that IS the
    * finding, and no test can be written that catches it. What this one catches is the
    * reverse direction: the day `LoadPass` grows the body arm its WI-1007 comment
    * describes, `inc` acquires a clause and this test fails, which is exactly when
    * someone must revisit it. */
  test("WI-1007: an operation's body is parsed and NOT loaded — the goal has no clause") {
    val src =
      """operation inc(x: Int64) -> Int64
        |  = add(x, 1)
        |
        |fact marker(1)""".stripMargin
    val pf = Parser.parse(src, "<wi1007>").toOption.getOrElse(fail("parse failed"))

    // The body IS parsed — the drop is the loader's, not the parser's. Top-level, so
    // finding it needs no descent: a walk here would be a shallower fourth copy of
    // `SpanFixture.allItems`, and the copy that forgets a scope shape fails as "no
    // operation in the fixture" rather than as the missing descent it is.
    val op = pf.items.collectFirst { case Item.OperationItem(o) => o }
      .getOrElse(fail("fixture drift: no operation in the parsed file"))
    assert(op.body.isDefined, "the parser must carry the body; WI-1007 is about the loader")

    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errors = Loader.loadAll(kb, IndexedSeq(pf))
    assert(errors.isEmpty, s"Load errors: $errors")

    // Pass 1 defines the name, so the zero below is not a vanished symbol.
    val incSym = kb.tryResolveSymbol("inc").getOrElse(fail("`inc` must be defined"))
    kb.symbols.get(incSym) match
      case SymbolDef.Resolved(_, _, SymbolKind.Operation, _) => ()
      case other => fail(s"`inc` should be an Operation, got $other")

    def solutionsOf(sym: TermSymbol): Int =
      val arg = kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("a")))))
      SearchStream.resolve(kb, kb.alloc(Term.Fn(sym, IArray(arg), IArray.empty)))
        .allSolutions(kb).length

    // CONTROL: the fact in the same file resolves through this very call shape.
    // `marker` interns UNQUALIFIED — a fact's functor is a predicate name reached by
    // `resolveName`'s intern rung, not a declaration a scope prefixes.
    assertEquals(solutionsOf(kb.intern("marker")), 1, "the control fact must resolve")

    // The body would have been `inc`'s only definition.
    assertEquals(solutionsOf(incSym), 0, "no clause: the body was not loaded")
    // ARITY-FREE, and the stronger half: `byFunctor` is keyed on the functor symbol
    // alone, so this covers every shape a future body-loading port could lower to —
    // where a second `solutionsOf` at a guessed arity would re-probe the same bucket.
    assert(kb.byFunctor(incSym).isEmpty, "no clause at any arity: the body was not loaded")
  }
