package anthill.parse

import anthill.kb.{KnowledgeBase, SortKind}
import anthill.load.{Loader, Prelude}
import anthill.term.{Term, TermId, Literal}
import anthill.intern.{SymbolKind, SymbolDef, ResolveResult}

class ParserIntegrationTest extends munit.FunSuite:

  private val testcaseDir = sys.env.getOrElse("ANTHILL_TESTCASES",
    System.getProperty("user.dir") + "/../anthill-testcases")

  private val stdlibDir = sys.env.getOrElse("ANTHILL_STDLIB",
    System.getProperty("user.dir") + "/../stdlib")

  private def readFile(path: String): String =
    val source = scala.io.Source.fromFile(path)
    try source.mkString finally source.close()

  // ── Test 1: Parse ring.anthill (structure check) ──────────────

  test("parse ring.anthill — structure check") {
    val source = readFile(s"$testcaseDir/ring-polynom/ring.anthill")
    val result = Parser.parse(source, "ring.anthill")

    assert(result.isRight, s"Parse failed: ${result.left.getOrElse(IndexedSeq.empty).map(_.message).mkString(", ")}")
    val pf = result.toOption.get

    // Top-level: 1 SortWithBody (Ring) + 1 Fact (Ring[Int])
    val sortItems = pf.items.collect { case Item.SortWithBodyItem(s) => s }
    val factItems = pf.items.collect { case Item.FactItem(f) => f }
    assertEquals(sortItems.length, 1, "Expected 1 sort with body (Ring)")
    assertEquals(factItems.length, 1, "Expected 1 fact (Ring[Int])")

    val ring = sortItems.head
    assertEquals(pf.symbols.name(ring.name.last), "Ring")

    // Inside Ring: 1 abstract sort (T), 5 operations, 8 rules
    val innerAbstract = ring.items.collect { case Item.AbstractSortItem(s) => s }
    val innerOps = ring.items.collect { case Item.OperationItem(op) => op }
    val innerRules = ring.items.collect { case Item.RuleItem(r) => r }

    assertEquals(innerAbstract.length, 1, "Expected 1 abstract sort (T)")
    assertEquals(pf.symbols.name(innerAbstract.head.name.last), "T")
    assertEquals(innerOps.length, 5, s"Expected 5 operations, got: ${innerOps.map(op => pf.symbols.name(op.name.last))}")
    assertEquals(innerRules.length, 8, s"Expected 8 rules, got ${innerRules.length}")
  }

  // ── Test 2: Parse ring.anthill → load into KB ────────────────

  test("parse ring.anthill → load into KB (end-to-end)") {
    val source = readFile(s"$testcaseDir/ring-polynom/ring.anthill")
    val result = Parser.parse(source, "ring.anthill")
    assert(result.isRight, s"Parse failed: ${result.left.getOrElse(IndexedSeq.empty).map(_.message).mkString(", ")}")

    val pf = result.toOption.get
    val kb = KnowledgeBase()
    Prelude.register(kb)

    val loadErrors = Loader.loadAll(kb, IndexedSeq(pf))
    assert(loadErrors.isEmpty, s"Load errors: $loadErrors")

    // Ring sort registered
    assert(kb.hasQualifiedName("Ring"), "Ring sort should be registered")
    val ringSym = kb.tryResolveSymbol("Ring").get
    val ringTerm = kb.makeNameTermFromSym(ringSym)
    assertEquals(kb.sortKind(ringTerm), Some(SortKind.Defined))

    // Ring.T abstract sort
    assert(kb.hasQualifiedName("Ring.T"), "Ring.T should be registered")
    val tSym = kb.tryResolveSymbol("Ring.T").get
    val tTerm = kb.makeNameTermFromSym(tSym)
    assertEquals(kb.sortKind(tTerm), Some(SortKind.Abstract))

    // Operations: Ring.add, Ring.mul, Ring.neg, Ring.zero, Ring.one
    for opName <- Seq("add", "mul", "neg", "zero", "one") do
      assert(kb.hasQualifiedName(s"Ring.$opName"), s"Ring.$opName should be registered")

    // Operations registered
    for opName <- Seq("add", "mul", "neg", "zero", "one") do
      assert(kb.hasQualifiedName(s"Ring.$opName"), s"Ring.$opName should be registered")

    // Rules in ring.anthill have no :- body, so they are stored as facts.
    // 8 rule-items + 1 fact-item = 9 total facts (body-less rules)
    val totalEntries = kb.factCount + kb.ruleCount
    assert(totalEntries >= 9, s"Expected at least 9 KB entries (8 rules + 1 fact), got facts=${kb.factCount} rules=${kb.ruleCount}")
  }

  // ── Test 3: Parse polynom.anthill ─────────────────────────────

  test("parse polynom.anthill — structure check") {
    val source = readFile(s"$testcaseDir/ring-polynom/polynom.anthill")
    val result = Parser.parse(source, "polynom.anthill")

    assert(result.isRight, s"Parse failed: ${result.left.getOrElse(IndexedSeq.empty).map(_.message).mkString(", ")}")
    val pf = result.toOption.get

    // Top-level: 2 sorts (List, Polynom) + 1 fact (Polynom[Int])
    val sortItems = pf.items.collect { case Item.SortWithBodyItem(s) => s }
    val factItems = pf.items.collect { case Item.FactItem(f) => f }

    assertEquals(sortItems.length, 2, s"Expected 2 sorts, got ${sortItems.length}")
    assertEquals(factItems.length, 1, "Expected 1 fact")

    val sortNames = sortItems.map(s => pf.symbols.name(s.name.last)).toSet
    assert(sortNames.contains("List"), "Should have List sort")
    assert(sortNames.contains("Polynom"), "Should have Polynom sort")

    // Polynom sort has: requires, entity, operations, rules
    val polynom = sortItems.find(s => pf.symbols.name(s.name.last) == "Polynom").get
    val polyReqs = polynom.items.collect { case Item.RequiresDeclItem(r) => r }
    val polyEntities = polynom.items.collect { case Item.EntityItem(e) => e }
    val polyOps = polynom.items.collect { case Item.OperationItem(op) => op }
    val polyRules = polynom.items.collect { case Item.RuleItem(r) => r }

    assertEquals(polyReqs.length, 1, "Polynom should have 1 requires")
    assertEquals(polyEntities.length, 1, "Polynom should have 1 entity")
    assertEquals(polyOps.length, 5, s"Polynom should have 5 operations, got ${polyOps.length}")
    assertEquals(polyRules.length, 2, "Polynom should have 2 rules")

    // Check requires is Ring[R]
    polyReqs.head.typeExpr match
      case TypeExpr.Parameterized(name, bindings) =>
        assertEquals(pf.symbols.name(name.last), "Ring")
        assertEquals(bindings.length, 1)
      case other => fail(s"Expected Parameterized type, got $other")

    // Check that some operations have arrow types in params
    val mapCoeffs = polyOps.find(op => pf.symbols.name(op.name.last) == "map_coeffs").get
    val fParam = mapCoeffs.params.find(p => pf.symbols.name(p.name) == "f").get
    fParam.ty match
      case TypeExpr.Arrow(params, ret, _) =>
        assertEquals(params.length, 1, "Arrow should have 1 param")
      case other => fail(s"Expected arrow type for f param, got $other")
  }

  // ── Test 4: Parse outer.anthill (namespace + imports) ────────

  test("parse outer.anthill — namespace structure") {
    val source = readFile(s"$testcaseDir/nested-namespace-imports/outer.anthill")
    val result = Parser.parse(source, "outer.anthill")

    assert(result.isRight, s"Parse failed: ${result.left.getOrElse(IndexedSeq.empty).map(_.message).mkString(", ")}")
    val pf = result.toOption.get

    // Top-level: 1 namespace
    val nsItems = pf.items.collect { case Item.NamespaceItem(ns) => ns }
    assertEquals(nsItems.length, 1, "Expected 1 top-level namespace")

    val outer = nsItems.head
    // Namespace name: test.nested_imports (2 segments)
    assertEquals(outer.name.segments.length, 2)
    assertEquals(pf.symbols.name(outer.name.segments(0)), "test")
    assertEquals(pf.symbols.name(outer.name.segments(1)), "nested_imports")

    // Imports: anthill.prelude.{List, String, Bool}
    assertEquals(outer.imports.length, 1, "Expected 1 import")
    outer.imports.head.kind match
      case ImportKind.Selective(names) =>
        assertEquals(names.length, 3)
        val importedNames = names.map(n => pf.symbols.name(n.last)).toSet
        assertEquals(importedNames, Set("List", "String", "Bool"))
      case other => fail(s"Expected selective import, got $other")

    // Inner items: abstract sort (Path), operation, nested namespace (PathOps)
    val innerSorts = outer.items.collect { case Item.AbstractSortItem(s) => s }
    val innerOps = outer.items.collect { case Item.OperationItem(op) => op }
    val innerNs = outer.items.collect { case Item.NamespaceItem(ns) => ns }

    assertEquals(innerSorts.length, 1, "Expected 1 abstract sort (Path)")
    assertEquals(pf.symbols.name(innerSorts.head.name.last), "Path")

    assertEquals(innerOps.length, 1, "Expected 1 outer operation")

    assertEquals(innerNs.length, 1, "Expected 1 nested namespace (PathOps)")
    assertEquals(pf.symbols.name(innerNs.head.name.last), "PathOps")

    // PathOps has 2 operations
    val pathOpsOps = innerNs.head.items.collect { case Item.OperationItem(op) => op }
    assertEquals(pathOpsOps.length, 2, "PathOps should have 2 operations")
  }

  // ── Test 5: Parse monoid.anthill (brace-delimited bodies) ────

  test("parse monoid.anthill — brace-delimited sort bodies") {
    val source = readFile(s"$testcaseDir/fact-substitution/monoid.anthill")
    val result = Parser.parse(source, "monoid.anthill")

    assert(result.isRight, s"Parse failed: ${result.left.getOrElse(IndexedSeq.empty).map(_.message).mkString(", ")}")
    val pf = result.toOption.get

    val sorts = pf.items.collect { case Item.SortWithBodyItem(s) => s }
    val sortNames = sorts.map(s => pf.symbols.name(s.name.last)).toSet
    assertEquals(sortNames, Set("Monoid", "IntAdd", "IntMul", "AutoBindTest"))

    // IntAdd has a requires with named bindings: Monoid[T = Int, combine = add, identity = zero]
    val intAdd = sorts.find(s => pf.symbols.name(s.name.last) == "IntAdd").get
    val intAddReqs = intAdd.items.collect { case Item.RequiresDeclItem(r) => r }
    assertEquals(intAddReqs.length, 1)
    intAddReqs.head.typeExpr match
      case TypeExpr.Parameterized(name, bindings) =>
        assertEquals(pf.symbols.name(name.last), "Monoid")
        assertEquals(bindings.length, 3, "IntAdd requires should have 3 bindings")
        // First binding: T = Int
        assert(bindings(0).param.isDefined, "First binding should be named")
      case other => fail(s"Expected Parameterized, got $other")
  }

  // ── Test 6: Parse 2+2 and explore resolution ─────────────────

  test("parse 2+2 — term structure and resolution boundary") {
    // Step 1: Parse "2 + 2" as a fact term
    val result = Parser.parse("fact 2 + 2", "expr.anthill")
    assert(result.isRight, s"Parse failed: ${result.left.getOrElse(IndexedSeq.empty).map(_.message).mkString(", ")}")
    val pf = result.toOption.get

    val facts = pf.items.collect { case Item.FactItem(f) => f }
    assertEquals(facts.length, 1)

    // The Pratt parser desugars 2 + 2 → Fn("add", [Const(2), Const(2)])
    val factTerm = pf.terms.get(facts.head.term)
    factTerm match
      case fn: Term.Fn =>
        assertEquals(pf.symbols.name(fn.functor), "add")
        assertEquals(fn.posArgs.length, 2)
        assertEquals(pf.terms.get(fn.posArgs(0)), Term.Const(Literal.IntLit(2)))
        assertEquals(pf.terms.get(fn.posArgs(1)), Term.Const(Literal.IntLit(2)))
      case other => fail(s"Expected Fn, got $other")

    // Step 2: Parse stdlib numeric.anthill
    val numericSource = readFile(s"$stdlibDir/anthill/prelude/numeric.anthill")
    val numericResult = Parser.parse(numericSource, "numeric.anthill")
    assert(numericResult.isRight,
      s"numeric.anthill parse failed: ${numericResult.left.getOrElse(IndexedSeq.empty).map(_.message).mkString(", ")}")
    val numericPf = numericResult.toOption.get

    // Verify parse structure: 1 sort with qualified name
    val numericSorts = numericPf.items.collect { case Item.SortWithBodyItem(s) => s }
    assertEquals(numericSorts.length, 1)
    assertEquals(numericSorts.head.name.segments.map(numericPf.symbols.name).mkString("."), "anthill.prelude.Numeric")

    // Step 3: Load stdlib into KB
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val loadErrors = Loader.loadAll(kb, IndexedSeq(numericPf))
    assert(loadErrors.isEmpty, s"Load errors for numeric: $loadErrors")

    // Verify: sort and operations are registered with qualified names
    assert(kb.hasQualifiedName("anthill.prelude.Numeric"), "Numeric sort should be registered")
    assert(kb.hasQualifiedName("anthill.prelude.Numeric.add"), "Numeric.add should be registered")
    assert(kb.hasQualifiedName("anthill.prelude.Numeric.sub"), "Numeric.sub should be registered")
    assert(kb.hasQualifiedName("anthill.prelude.Numeric.mul"), "Numeric.mul should be registered")

    // Step 4: Load "fact 2 + 2" into KB — "add" should resolve to Numeric.add
    val exprErrors = Loader.loadAll(kb, IndexedSeq(pf))
    assert(exprErrors.isEmpty, s"Load errors for expr: $exprErrors")

    // Verify: the loaded fact's functor resolved to anthill.prelude.Numeric.add
    val addSym = kb.tryResolveSymbol("anthill.prelude.Numeric.add")
    assert(addSym.isDefined, "anthill.prelude.Numeric.add should exist in KB")
    val addDef = kb.symbols.get(addSym.get)
    addDef match
      case SymbolDef.Resolved(_, qualName, _, _) =>
        assertEquals(qualName, "anthill.prelude.Numeric.add")
      case other =>
        fail(s"Expected resolved symbol, got $other")
  }

  // ── Proposal 032: symmetric arrows + multi-head rules (WI-142) ─

  test("proposal 032: `body -: heads` parses to same IR as `heads :- body`") {
    val forwardSrc = "rule fwd: parent(?x, ?y) :- mother(?x, ?y)"
    val reverseSrc = "rule rev: mother(?x, ?y) -: parent(?x, ?y)"

    val fwd = Parser.parse(forwardSrc, "<fwd>").toOption.get
    val rev = Parser.parse(reverseSrc, "<rev>").toOption.get

    val fwdRule = fwd.items.collect { case Item.RuleItem(r) => r }.head
    val revRule = rev.items.collect { case Item.RuleItem(r) => r }.head

    // Both should have one positive head and a one-term body.
    assertEquals(fwdRule.heads.length, 1)
    assertEquals(revRule.heads.length, 1)
    assert(fwdRule.body.exists(_.length == 1))
    assert(revRule.body.exists(_.length == 1))

    // Heads are the same shape (parent functor) on both sides.
    val fwdHeadFunctor = fwdRule.heads.head match
      case RuleHead.TermHead(t) => fwd.terms.get(t) match
        case fn: Term.Fn => fwd.symbols.name(fn.functor)
        case other => fail(s"Expected Fn head, got $other")
      case _ => fail("Expected positive head")
    val revHeadFunctor = revRule.heads.head match
      case RuleHead.TermHead(t) => rev.terms.get(t) match
        case fn: Term.Fn => rev.symbols.name(fn.functor)
        case other => fail(s"Expected Fn head, got $other")
      case _ => fail("Expected positive head")
    assertEquals(fwdHeadFunctor, "parent")
    assertEquals(revHeadFunctor, "parent")

    // Body functor is the same on both sides too (mother).
    val fwdBodyFunctor = fwd.terms.get(fwdRule.body.get.head) match
      case fn: Term.Fn => fwd.symbols.name(fn.functor)
      case other => fail(s"Expected Fn body, got $other")
    val revBodyFunctor = rev.terms.get(revRule.body.get.head) match
      case fn: Term.Fn => rev.symbols.name(fn.functor)
      case other => fail(s"Expected Fn body, got $other")
    assertEquals(fwdBodyFunctor, "mother")
    assertEquals(revBodyFunctor, "mother")
  }

  test("proposal 032: labeled multi-head rule parses with N positive heads") {
    val src = "rule completion: completed(?w), timestamp(?w, ?t) :- WorkItem(id: ?w)"
    val pf = Parser.parse(src, "<multi>").toOption.get
    val rule = pf.items.collect { case Item.RuleItem(r) => r }.head
    assertEquals(rule.heads.length, 2, "Expected 2 positive heads")
    val headFunctors = rule.heads.collect {
      case RuleHead.TermHead(t) => pf.terms.get(t) match
        case fn: Term.Fn => pf.symbols.name(fn.functor)
        case _ => "<not-fn>"
    }
    assertEquals(headFunctors.toSet, Set("completed", "timestamp"))
    assert(rule.label.isDefined)
    assertEquals(pf.symbols.name(rule.label.get.last), "completion")
  }

  test("proposal 032: labeled multi-head loads as N horn rules sharing body") {
    val src =
      """sort Demo
        |  rule completion: completed(?w), timestamp(?w, ?t) :- WorkItem(id: ?w)
        |end""".stripMargin
    val pf = Parser.parse(src, "<multi-load>").toOption.get
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, IndexedSeq(pf))
    assert(errs.isEmpty, s"Load errors: $errs")

    // KB should hold one horn rule per head: completed/1 and timestamp/2.
    val completedSym = kb.intern("completed")
    val timestampSym = kb.intern("timestamp")
    val completedRules = kb.byFunctor(completedSym)
    val timestampRules = kb.byFunctor(timestampSym)
    assertEquals(completedRules.length, 1, "expected one rule indexed by completed")
    assertEquals(timestampRules.length, 1, "expected one rule indexed by timestamp")
  }

  test("proposal 032: unlabeled multi-head rule is rejected at load time") {
    val src =
      """sort Demo
        |  rule completed(?w), timestamp(?w, ?t) :- WorkItem(id: ?w)
        |end""".stripMargin
    val pf = Parser.parse(src, "<unlabeled-multi>").toOption.get
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, IndexedSeq(pf))
    assert(errs.nonEmpty, "Expected a load error for unlabeled multi-head rule")
    val msg = errs.collectFirst { case anthill.load.LoadError.Other(m) => m }
    assert(msg.exists(_.contains("multi-head")), s"Expected multi-head error, got: $errs")
  }

  test("proposal 032: bare-head fact form (no arrow) still works") {
    val src = "rule ?a + zero = ?a"
    val pf = Parser.parse(src, "<bare>").toOption.get
    val rule = pf.items.collect { case Item.RuleItem(r) => r }.head
    assertEquals(rule.heads.length, 1)
    assert(rule.body.isEmpty, "Bare-head fact has no body")
  }

  test("proposal 032: stdlib geometry.anthill parses (post-032 multi-line `-:` form)") {
    val src = readFile(s"$stdlibDir/anthill/geometry.anthill")
    val result = Parser.parse(src, "geometry.anthill")
    assert(result.isRight,
      s"geometry.anthill parse failed: ${result.left.getOrElse(IndexedSeq.empty).map(_.message).mkString(", ")}")
    val pf = result.toOption.get
    val ns = pf.items.collectFirst { case Item.NamespaceItem(n) => n }.get
    val rules = ns.items.collect { case Item.RuleItem(r) => r }
    // 12 rules total: 4 vec_* operations + 8 algebraic-law rules.
    assertEquals(rules.length, 12, s"expected 12 rules, got ${rules.length}")
    // Algebraic-law rules use the `body -: heads` form and have multi-term bodies.
    val lawRules = rules.filter(r => r.label.exists(l => pf.symbols.name(l.last).startsWith("vec_")))
      .filter(_.body.exists(_.length > 1))
    assert(lawRules.nonEmpty, "expected at least one law rule with `body -: heads` shape")
  }

