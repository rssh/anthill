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

  private val examplesDir = sys.env.getOrElse("ANTHILL_EXAMPLES",
    System.getProperty("user.dir") + "/../examples")

  private def readFile(path: String): String =
    val source = scala.io.Source.fromFile(path)
    try source.mkString finally source.close()

  /** Resolve the functor name of a term that's expected to be a `Term.Fn`. */
  private def fnFunctor(pf: ParsedFile, t: TermId): String = pf.terms.get(t) match
    case fn: Term.Fn => pf.symbols.name(fn.functor)
    case other => fail(s"Expected Term.Fn, got $other")

  /** Resolve the functor name of a positive head; fails the test on `Bottom`. */
  private def headFunctor(pf: ParsedFile, head: RuleHead): String = head match
    case RuleHead.TermHead(t) => fnFunctor(pf, t)
    case RuleHead.Bottom => fail("Expected positive head, got Bottom")

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

    assertEquals(headFunctor(fwd, fwdRule.heads.head), "parent")
    assertEquals(headFunctor(rev, revRule.heads.head), "parent")
    assertEquals(fnFunctor(fwd, fwdRule.body.get.head), "mother")
    assertEquals(fnFunctor(rev, revRule.body.get.head), "mother")
  }

  test("proposal 032: labeled multi-head rule parses with N positive heads") {
    val src = "rule completion: completed(?w), timestamp(?w, ?t) :- WorkItem(id: ?w)"
    val pf = Parser.parse(src, "<multi>").toOption.get
    val rule = pf.items.collect { case Item.RuleItem(r) => r }.head
    assertEquals(rule.heads.length, 2, "Expected 2 positive heads")
    assertEquals(rule.heads.map(headFunctor(pf, _)).toSet, Set("completed", "timestamp"))
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

  // ── Proposals 025 + 031: proof / provides / enum (WI-152) ─────

  test("proposal 025: single-tactic `proof X by <strategy> end` parses") {
    val src =
      """sort Demo
        |  rule p(?x) :- q(?x)
        |
        |  proof p
        |    by z3(logic: "LRA")
        |  end
        |end""".stripMargin
    val res = Parser.parse(src, "<single-tactic>")
    assert(res.isRight, s"parse failed: ${res.left.toOption.map(_.map(_.message).mkString("; "))}")
    val pf = res.toOption.get
    val sort = pf.items.collectFirst { case Item.SortWithBodyItem(s) => s }
      .getOrElse(fail("expected SortWithBody"))
    val proofs = sort.items.collect { case Item.ProofItem(p) => p }
    assertEquals(proofs.length, 1, "expected one proof in sort body")
    val p = proofs.head
    assertEquals(pf.symbols.name(p.target.last), "p")
    assert(p.strategy.isDefined, "expected strategy")
    assertEquals(pf.symbols.name(p.strategy.get.name), "z3")
    assert(p.body.isEmpty, "single-tactic body has no inner clause")
  }

  test("proposal 031: structured-proof body parses with steps + concluding clause") {
    // Mirrors examples/webots-modelling/lf1/safety_common.anthill's
    // step_distance_lemma — two `rule` step rules with `using` cites
    // and `by trust(...)`, then a concluding `using ... by z3(...)`.
    val src =
      """sort Demo
        |  rule step_distance_lemma:
        |    distance_at_step(?k, ?d_prev),
        |    distance_at_step(?k_next, ?d_next)
        |    -: lte(abs(?d_next - ?d_prev), ?delta)
        |
        |  proof step_distance_lemma
        |    rule h_geometric: lte(abs(?d_next - ?d_prev), ?v_diff_scaled)
        |      using triangle_inequality
        |      by trust(reason: "Reverse triangle inequality")
        |
        |    rule h_envelope: lte(?v_diff_scaled, ?delta)
        |      using velocity_envelope
        |      by trust(reason: "Velocity envelope")
        |
        |    using h_geometric, h_envelope
        |    by z3(logic: "LRA")
        |  end
        |end""".stripMargin
    val result = Parser.parse(src, "<structured-proof>")
    assert(result.isRight, s"parse failed: ${result.left.toOption.map(_.map(_.message).mkString("; "))}")
    val pf = result.toOption.get
    val sort = pf.items.collectFirst { case Item.SortWithBodyItem(s) => s }.get
    val proofs = sort.items.collect { case Item.ProofItem(p) => p }
    assertEquals(proofs.length, 1)
    val p = proofs.head
    assertEquals(pf.symbols.name(p.target.last), "step_distance_lemma")
    p.body match
      case Some(ProofBody.Structured(steps, conclude)) =>
        assertEquals(steps.length, 2, "expected 2 step rules")
        // Step 1: h_geometric, cites triangle_inequality, by trust(...)
        val s1 = steps(0)
        assertEquals(pf.symbols.name(s1.rule.label.get.last), "h_geometric")
        assertEquals(s1.usingNames.length, 1)
        assertEquals(pf.symbols.name(s1.usingNames.head.last), "triangle_inequality")
        assertEquals(pf.symbols.name(s1.strategy.name), "trust")
        // Step 2: h_envelope, cites velocity_envelope
        val s2 = steps(1)
        assertEquals(pf.symbols.name(s2.rule.label.get.last), "h_envelope")
        assertEquals(s2.usingNames.length, 1)
        assertEquals(pf.symbols.name(s2.usingNames.head.last), "velocity_envelope")
        // Conclude: using h_geometric, h_envelope; by z3(...)
        assert(conclude.isDefined, "expected concluding clause")
        val c = conclude.get
        assertEquals(c.usingNames.length, 2)
        assertEquals(c.usingNames.map(n => pf.symbols.name(n.last)).toSet, Set("h_geometric", "h_envelope"))
        assertEquals(pf.symbols.name(c.strategy.name), "z3")
      case other => fail(s"expected Structured body, got $other")
  }

  test("proposal 025: `enum NAME ... end` parses with kind = Enum") {
    val src =
      """enum Drone
        |  entity Leader
        |  entity Follower
        |end""".stripMargin
    val pf = Parser.parse(src, "<enum>").toOption.get
    val sort = pf.items.collectFirst { case Item.SortWithBodyItem(s) => s }.get
    assertEquals(sort.kind, SortDeclKind.Enum)
    val entities = sort.items.collect { case Item.EntityItem(e) => e }
    assertEquals(entities.length, 2)
    assertEquals(entities.map(e => pf.symbols.name(e.name.last)).toSet, Set("Leader", "Follower"))
  }

  test("proposal 025: `provides Spec` clause parses inside sort body") {
    val src =
      """sort IntStack
        |  provides Stack[T = Int]
        |end""".stripMargin
    val pf = Parser.parse(src, "<provides-clause>").toOption.get
    val sort = pf.items.collectFirst { case Item.SortWithBodyItem(s) => s }.get
    val provides = sort.items.collect { case Item.ProvidesClauseItem(pc) => pc }
    assertEquals(provides.length, 1)
    provides.head.spec match
      case TypeExpr.Parameterized(n, bs) =>
        assertEquals(pf.symbols.name(n.last), "Stack")
        assertEquals(bs.length, 1)
      case other => fail(s"expected Parameterized spec, got $other")
  }

  test("proposal 025: standalone `provides Spec language anthill ... end` block parses") {
    val src =
      """provides Stack[T = Int]
        |  language anthill
        |  rule push(?s, ?x) = cons(head: ?x, tail: ?s)
        |end""".stripMargin
    val pf = Parser.parse(src, "<provides-block>").toOption.get
    val blocks = pf.items.collect { case Item.ProvidesBlockItem(pb) => pb }
    assertEquals(blocks.length, 1)
    val b = blocks.head
    assertEquals(pf.symbols.name(b.language), "anthill")
    val ruleItems = b.items.collect { case ProvidesItem.RuleI(r) => r }
    assertEquals(ruleItems.length, 1)
  }

  test("WI-152: examples/webots-modelling/lf1/safety_common.anthill parses (structured-proof example)") {
    val src = readFile(s"$examplesDir/webots-modelling/lf1/safety_common.anthill")
    val result = Parser.parse(src, "safety_common.anthill")
    assert(result.isRight,
      s"safety_common.anthill parse failed: ${result.left.toOption.map(_.map(_.message).mkString("; "))}")
    val pf = result.toOption.get
    val ns = pf.items.collectFirst { case Item.NamespaceItem(n) => n }
      .getOrElse(fail("expected namespace"))
    assertEquals(ns.name.segments.map(pf.symbols.name).mkString("."),
      "anthill.examples.lf1.safety.common")

    // The file declares `enum Drone` (proposal 025) plus a structured-proof
    // body for `step_distance_lemma` (proposal 031) — the two surfaces
    // WI-152 adds. Assert both are seen by the parser.
    val sortItems = ns.items.collect { case Item.SortWithBodyItem(s) => s }
    val drone = sortItems.find(s => pf.symbols.name(s.name.last) == "Drone")
      .getOrElse(fail("expected enum Drone"))
    assertEquals(drone.kind, SortDeclKind.Enum)

    val proofs = ns.items.collect { case Item.ProofItem(p) => p }
    val stepDistance = proofs.find(p => pf.symbols.name(p.target.last) == "step_distance_lemma")
      .getOrElse(fail("expected proof step_distance_lemma"))
    stepDistance.body match
      case Some(ProofBody.Structured(steps, conclude)) =>
        assert(steps.nonEmpty, "structured proof should have step rules")
        assert(conclude.isDefined, "structured proof should have concluding clause")
      case other => fail(s"expected Structured body for step_distance_lemma, got $other")
  }

  test("WI-152: stdlib witness.anthill parses end-to-end") {
    val src = readFile(s"$stdlibDir/anthill/realization/witness.anthill")
    val result = Parser.parse(src, "witness.anthill")
    assert(result.isRight,
      s"witness.anthill parse failed: ${result.left.toOption.map(_.map(_.message).mkString("; "))}")
    val pf = result.toOption.get
    val ns = pf.items.collectFirst { case Item.NamespaceItem(n) => n }
      .getOrElse(fail("expected namespace"))
    val nsName = ns.name.segments.map(pf.symbols.name).mkString(".")
    assertEquals(nsName, "anthill.realization.witness")

    // Sorts: ProofWitness (with 6 entity constructors), SmtVerdict (3 entities)
    val sorts = ns.items.collect { case Item.SortWithBodyItem(s) => s }
    val sortNames = sorts.map(s => pf.symbols.name(s.name.last)).toSet
    assert(sortNames.contains("ProofWitness"), s"expected ProofWitness sort, got $sortNames")
    assert(sortNames.contains("SmtVerdict"), s"expected SmtVerdict sort, got $sortNames")

    // ProofWitness has 6 entity constructors per witness.anthill:
    //   SmtDischarge, SldDerivation, MetaCompose,
    //   ScopeAxiom, Specialization, TrustedAxiom.
    val proofWitness = sorts.find(s => pf.symbols.name(s.name.last) == "ProofWitness").get
    val pwEntities = proofWitness.items.collect { case Item.EntityItem(e) => e }
    assertEquals(pwEntities.length, 6, s"expected 6 ProofWitness constructors, got ${pwEntities.map(e => pf.symbols.name(e.name.last))}")
  }

  test("WI-152: proof loader emits opaque proof_decl fact") {
    val src =
      """sort Demo
        |  rule p(?x) :- q(?x)
        |
        |  proof p
        |    by z3(logic: "LRA")
        |  end
        |end""".stripMargin
    val pf = Parser.parse(src, "<proof-load>").toOption.get
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, IndexedSeq(pf))
    assert(errs.isEmpty, s"Load errors: $errs")
    // The proof emits an opaque `proof_decl` fact under ProofRecord.
    val proofDeclSym = kb.intern("proof_decl")
    val byFunctor = kb.byFunctor(proofDeclSym)
    assertEquals(byFunctor.length, 1, "expected one proof_decl fact in KB")
  }

