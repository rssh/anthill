package anthill.parse

import anthill.kb.{KnowledgeBase, SortKind}
import anthill.load.{EmbeddedStdlib, FileSourceResolver, Loader, LoadError, Prelude}
import anthill.term.{Term, TermId, Literal}
import anthill.intern.{SymbolKind, SymbolDef, ResolveResult}

import java.nio.file.Paths

class ParserIntegrationTest extends munit.FunSuite:

  private val testcaseDir = sys.env.getOrElse("ANTHILL_TESTCASES",
    System.getProperty("user.dir") + "/../anthill-testcases")

  private val stdlibDir = sys.env.getOrElse("ANTHILL_STDLIB",
    System.getProperty("user.dir") + "/../stdlib")

  private val examplesDir = sys.env.getOrElse("ANTHILL_EXAMPLES",
    System.getProperty("user.dir") + "/../examples")

  /** The Rust-side binding files (proposal 038). Not `stdlib/` — a binding file is
    * per-language and lives with its host, which is why a stdlib-only parse never saw
    * the nested `provides` clause below. */
  private val stlDir = sys.env.getOrElse("ANTHILL_STL",
    System.getProperty("user.dir") + "/../rustland/anthill-stl/anthill")

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

    // The sorts are nested inside `namespace test.monoid { … }`, so descend
    // into the namespace's items (the parser nests, matching rustland).
    val ns = pf.items.collectFirst { case Item.NamespaceItem(n) => n }
      .getOrElse(fail("expected namespace test.monoid"))
    val sorts = ns.items.collect { case Item.SortWithBodyItem(s) => s }
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
        assertEquals(pf.symbols.name(fn.functor), anthill.parse.Pratt.addFunctor)
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

    // Step 3: Load the stdlib chain into a KB.
    //
    // WI-992: the chain, not `numeric.anthill` alone. Its `requires PartialOrd[T]` names
    // a spec declared in `ordered.anthill`, and that requirement is now RESOLVED — so
    // loading this file by itself reports the missing spec, correctly, where the
    // parameterized `requires` used to be dropped unread. This is the one test of the
    // eight WI-988 measured whose fixture (not whose code) was the thing at fault.
    val kb = kbWithStdlib()

    // Verify: sort and operations are registered with qualified names.
    //
    // WI-20260825-1WBZT — `add` / `sub` / `mul` are DECLARED by the syntax category each
    // operator mints (`stdlib/anthill/prelude/arithmetic.anthill`), not by the `Numeric`
    // bundle, which declares nothing and reaches them by `provides`. The absence rows
    // below are the half that matters: without them this test passes on a KB where
    // `Numeric` declares its own five again beside the categories' — which is the
    // duplication that ticket removed (`Numeric.add` and `algebra.Ring.add` were two
    // different operations under one spelling).
    assert(kb.hasQualifiedName("anthill.prelude.Numeric"), "Numeric sort should be registered")
    assert(kb.hasQualifiedName("anthill.prelude.Additive"), "Additive sort should be registered")
    assert(
      kb.hasQualifiedName("anthill.prelude.Multiplicative"),
      "Multiplicative sort should be registered"
    )
    assert(kb.hasQualifiedName("anthill.prelude.Additive.add"), "Additive.add should be registered")
    assert(kb.hasQualifiedName("anthill.prelude.Additive.sub"), "Additive.sub should be registered")
    assert(
      kb.hasQualifiedName("anthill.prelude.Multiplicative.mul"),
      "Multiplicative.mul should be registered"
    )
    for gone <- IndexedSeq(
        "anthill.prelude.Numeric.add",
        "anthill.prelude.Numeric.sub",
        "anthill.prelude.Numeric.mul"
      )
    do
      assert(
        !kb.hasQualifiedName(gone),
        s"$gone must NOT be a second declaration — one spec declares each short name"
      )

    // Step 4: Load "fact 2 + 2" into KB — "add" should resolve to Additive.add
    val exprErrors = Loader.loadAll(kb, IndexedSeq(pf))
    assert(exprErrors.isEmpty, s"Load errors for expr: $exprErrors")

    // Verify: the loaded fact's functor resolved to anthill.prelude.Additive.add
    val addSym = kb.tryResolveSymbol("anthill.prelude.Additive.add")
    assert(addSym.isDefined, "anthill.prelude.Additive.add should exist in KB")
    val addDef = kb.symbols.get(addSym.get)
    addDef match
      case SymbolDef.Resolved(_, qualName, _, _) =>
        assertEquals(qualName, "anthill.prelude.Additive.add")
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
    val msg = errs.collectFirst { case anthill.load.LoadError.Other(m, _) => m }
    assert(msg.exists(_.contains("multi-head")), s"Expected multi-head error, got: $errs")
  }

  test("proposal 032: bare-head fact form (no arrow) still works") {
    val src = "rule ?a + zero = ?a"
    val pf = Parser.parse(src, "<bare>").toOption.get
    val rule = pf.items.collect { case Item.RuleItem(r) => r }.head
    assertEquals(rule.heads.length, 1)
    assert(rule.body.isEmpty, "Bare-head fact has no body")
  }

  // WI-935 moved geometry's multi-line `-:` law rules OUT of this file: the four
  // vec_* relational rules and their eight per-component laws are gone (the
  // members are now `sort Vec3`'s bodied operations, and the laws live on
  // `anthill.prelude.algebra.VectorSpace` over the abstract `V`).
  //
  // So this no longer covers the post-032 `-:` form, and it does not pretend to:
  // MEASURED, the whole stdlib now has exactly TWO `-:` rules left
  // (prelude/int64.anthill, prelude/bigint.anthill — forall-quantifier bodies, a
  // different construct), so there is no stdlib fixture of the multi-line law
  // shape to re-point at. What survives here is the narrower claim its assertion
  // actually makes: geometry declares no namespace-level rules at all.
  // Re-establishing `-:` coverage needs a fixture, not a file swap.
  test("WI-935: stdlib geometry.anthill declares no namespace-level rules") {
    val src = readFile(s"$stdlibDir/anthill/geometry.anthill")
    val result = Parser.parse(src, "geometry.anthill")
    assert(result.isRight,
      s"geometry.anthill parse failed: ${result.left.getOrElse(IndexedSeq.empty).map(_.message).mkString(", ")}")
    val pf = result.toOption.get
    val ns = pf.items.collectFirst { case Item.NamespaceItem(n) => n }.get
    // Geometry now declares NO namespace-level rules at all — the four vec_*
    // relational clauses were a hand-written stand-in for a reading the prover
    // derives from the body (WI-669), and were deleted with the WI-138 lift.
    assertEquals(ns.items.collect { case Item.RuleItem(r) => r }.length, 0,
      "WI-935: geometry declares no namespace-level rules")

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

  test("WI-862: `default provides` marks THAT clause, and only that one") {
    val src =
      """sort ListOrd
        |  default provides Ord[T = List[T = E]]
        |  provides PartialOrd[T = List[T = E]]
        |end""".stripMargin
    val pf = Parser.parse(src, "<default-provides>").toOption.get
    val sort = pf.items.collectFirst { case Item.SortWithBodyItem(s) => s }.get
    val provides = sort.items.collect { case Item.ProvidesClauseItem(pc) => pc }
    assertEquals(provides.length, 2)
    assertEquals(provides.head.isDefault, true)
    // THE CONTROL, and it is what makes the first assertion mean something: a modifier
    // that leaked across clauses would mark both, and a parser that read `default` as
    // an item of its own would leave the marked clause unmarked while still parsing.
    assertEquals(provides(1).isDefault, false)
  }

  test("WI-862: `default` is a modifier in that one position and an identifier elsewhere") {
    // PASSES EITHER WAY, AND UNREACHABLE BY CONSTRUCTION — said here rather than left to
    // be discovered, because the arm reads like a control and is not one. Reservation is
    // unrepresentable in this parser: `ident` is `identToken.map(intern)` with no
    // keyword-exclusion set, and `keyword(kw)` is `identToken.filter(_ == kw)` — a
    // filter, not a reservation — so adding `keyword("default")` to `providesDecl`
    // cannot take the word away from an identifier position. The fixture never even
    // reaches the new production: `operationDecl` precedes `providesDecl` in
    // `declaration` and consumes this whole item. Kept as a standing property of the
    // surface (the corpus does name a parameter `default`), so a FUTURE change that
    // introduced a reserved-word set would be caught here.
    val src =
      """sort Cfg
        |  operation pick(default: Int64) -> Int64 = default
        |end""".stripMargin
    val pf = Parser.parse(src, "<default-ident>").toOption.get
    val sort = pf.items.collectFirst { case Item.SortWithBodyItem(s) => s }.get
    val ops = sort.items.collect { case Item.OperationItem(o) => o }
    assertEquals(ops.length, 1)
    assertEquals(ops.head.params.map(p => pf.symbols.name(p.name)).toList, List("default"))
  }

  test("WI-869: a `provides Spec :- goals` tail parses and its conditions are kept") {
    val src =
      """sort Pair
        |  provides PartialEq[Pair] :- PartialEq[A], PartialEq[B]
        |  provides Eq[Pair]
        |end""".stripMargin
    val pf = Parser.parse(src, "<conditional-provides>").toOption.get
    val sort = pf.items.collectFirst { case Item.SortWithBodyItem(s) => s }.get
    val provides = sort.items.collect { case Item.ProvidesClauseItem(pc) => pc }
    assertEquals(provides.length, 2)
    // The CONDITIONED one keeps both goals, each a spec instantiation…
    assertEquals(provides.head.conditions.length, 2)
    val condNames = provides.head.conditions.map {
      case TypeExpr.Parameterized(n, _) => pf.symbols.name(n.last)
      case other                        => fail(s"expected Parameterized condition, got $other")
    }
    assertEquals(condNames.toList, List("PartialEq", "PartialEq"))
    // …and the UNCONDITIONED sibling keeps none, which is the control: a tail that
    // leaked across clauses would give this one two as well.
    assertEquals(provides(1).conditions.length, 0)
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

  test("WI-862: a `provides Spec` clause INSIDE a binding block parses (the shipped stl)") {
    // THE ACCEPTANCE, and it is a corpus assertion rather than a fixture: WI-862 retired
    // the `fact` spelling of a provision, and the 21 rows across these five files moved
    // to `provides` — written inside `provides <Carrier> language rust … end`, where a
    // binding block opens the carrier's scope. scaland had no arm for that position, so
    // MEASURED before this change: every one of these five was
    // `Left(bool.anthill:7:13: parse error: found " PartialEq")`. A parser that cannot
    // read the shipped binding files is not a reference parser.
    val files = IndexedSeq("bool", "bigint", "float", "int64", "string")
    for f <- files do
      val src = readFile(s"$stlDir/$f.anthill")
      val result = Parser.parse(src, s"$f.anthill")
      assert(result.isRight,
        s"$f.anthill must parse; got ${result.left.toOption.map(_.map(_.message).mkString("; "))}")
    // …and the clauses are KEPT, not skipped: a `.rep` arm that matched and dropped
    // would leave the files parsing with nothing recorded, which the assertion above
    // cannot tell apart from success.
    val pf = Parser.parse(readFile(s"$stlDir/bool.anthill"), "bool.anthill").toOption.get
    val ns = pf.items.collectFirst { case Item.NamespaceItem(n) => n }.get
    val block = ns.items.collectFirst { case Item.ProvidesBlockItem(pb) => pb }.get
    val nested = block.items.collect { case ProvidesItem.ProvidesClauseI(pc) => pc }
    assertEquals(nested.length, 2)
    assertEquals(
      nested.map(pc => pc.spec match {
        case TypeExpr.Parameterized(n, _) => pf.symbols.name(n.last)
        case other                        => fail(s"expected Parameterized spec, got $other")
      }).toList,
      List("PartialEq", "Eq"))
    // The control for the modifier one production over: none of these is marked.
    assert(nested.forall(!_.isDefault), "no stl provision is marked `default`")
  }

  test("WI-862: `default` on a provides BLOCK is refused, not silently marked") {
    // scaland shares ONE production between the clause and the block, so this exclusion
    // has to be stated; rustland's grammar gives them separate productions and only the
    // clause takes the modifier, so it has no such form to refuse. Driven because an
    // untested error arm is an error arm that may not fire — and the failure direction
    // here is a mark parsed onto a construct that declares no provision to key it.
    val src =
      """default provides Stack[T = Int]
        |  language anthill
        |  rule push(?s, ?x) = cons(head: ?x, tail: ?s)
        |end""".stripMargin
    val errs = Parser.parse(src, "<default-provides-block>").left.toOption
      .getOrElse(fail("a `default` on a provides BLOCK must be refused"))
    assert(errs.exists(_.message.contains("not a `provides ... language ... end` block")),
      s"the refusal must name the construct it is refusing; got ${errs.map(_.message)}")
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

  // ── WI-153: stdlib alignment — load the four stdlib files end-to-end ─

  /** Read and parse a stdlib file via the same SourceResolver code path
    * used by [[anthill.load.EmbeddedStdlib]] at startup.
    */
  private def parseStdlibFile(path: String): ParsedFile =
    val resolver = FileSourceResolver(IndexedSeq(Paths.get(stdlibDir)))
    val src = resolver.resolve(path) match
      case Right(s) => s
      case Left(msg) => fail(s"resolver failed for $path: $msg")
    val res = Parser.parse(src, s"$path.anthill")
    assert(res.isRight, s"$path parse failed: ${res.left.toOption.map(_.map(_.message).mkString("; "))}")
    res.toOption.get

  /** Drop load errors for symbols scaland's Prelude hasn't wired up yet —
    * the prelude typeclasses (Eq/Ord/Numeric), the parametric
    * collections (List/Option), and reflect.Term. Delete this filter once
    * those modules are loaded as part of EmbeddedStdlib.
    */
  /** No tolerated load errors after WI-161 — the full stdlib chain loads
    * cleanly. Per-file tests below now load `EmbeddedStdlib` so transitive
    * imports resolve. Kept as a no-op predicate for symmetry with earlier
    * WI iterations and to make any new gap fail loudly.
    */
  private def isToleratedLoadError(e: LoadError): Boolean = false

  /** Single-pass count of items whose `partial` is defined for them.
    * Replaces the more verbose `items.collect { case … => 1 }.sum`.
    */
  private def countItems(items: Iterable[Item])(partial: PartialFunction[Item, Any]): Int =
    items.count(partial.isDefinedAt)

  /** Sum a per-item integer measurement, with a default of 0 for items
    * the partial function does not match. Used for `OperationBlockItem`
    * vs `OperationItem` (one contributes `entries.length`, the other 1).
    */
  private def sumItems(items: Iterable[Item])(measure: PartialFunction[Item, Int]): Int =
    items.foldLeft(0)((n, it) => n + measure.applyOrElse(it, (_: Item) => 0))

  test("WI-153: stdlib algebra.anthill parses + loads with expected counts") {
    val pf = parseStdlibFile("anthill.prelude.algebra")
    val ns = pf.items.collectFirst { case Item.NamespaceItem(n) => n }
      .getOrElse(fail("expected namespace"))
    assertEquals(ns.name.segments.map(pf.symbols.name).mkString("."), "anthill.prelude.algebra")

    val sorts = ns.items.collect { case Item.SortWithBodyItem(s) => s }
    assertEquals(sorts.map(s => pf.symbols.name(s.name.last)).toSet, Set("Ring", "VectorSpace"))

    // Ring: 1 abstract sort (T), ZERO operations, 2 `provides` clauses, 2 laws.
    //
    // WI-20260825-1WBZT — IT DECLARED FIVE OPERATIONS AND SEVEN LAWS, and both numbers
    // went down for one reason: every operator now names a SYNTAX CATEGORY that owns the
    // operation it mints (`stdlib/anthill/prelude/arithmetic.anthill`), and `Ring`
    // reaches `add`/`sub`/`neg`/`zero` and `mul`/`one` by `provides` instead of by a
    // SECOND declaration of names `anthill.prelude.Numeric` also carried. Five laws went
    // with the operations that state them (`add_comm`/`add_assoc`/`add_identity` to
    // `Additive`, `mul_assoc`/`mul_identity` to `Multiplicative`); `mul_comm` and
    // `distrib` stay, because `distrib` reads BOTH operations and `mul_comm` is a claim
    // about multiplication that only a COMMUTATIVE ring makes.
    val ring = sorts.find(s => pf.symbols.name(s.name.last) == "Ring").get
    assertEquals(countItems(ring.items) { case Item.AbstractSortItem(_) => }, 1)
    val ringOps = sumItems(ring.items) {
      case Item.OperationBlockItem(b) => b.entries.length
      case Item.OperationItem(_)      => 1
    }
    assertEquals(ringOps, 0, "Ring declares NO operation: it provides the categories that do")
    assertEquals(
      countItems(ring.items) { case Item.ProvidesClauseItem(_) => },
      2,
      "…by two `provides` clauses — `Additive` and `Multiplicative`"
    )
    val ringRules = sumItems(ring.items) {
      case Item.RuleBlockItem(b) => b.entries.length
      case Item.RuleItem(_)      => 1
    }
    assertEquals(ringRules, 2, "Ring keeps only `mul_comm` and `distrib`")

    // VectorSpace: 2 abstract sorts (V, F), 1 requires (Ring[F]), 4 ops, 8 laws
    // (WI-935 added `vec_sub_def`).
    val vs = sorts.find(s => pf.symbols.name(s.name.last) == "VectorSpace").get
    assertEquals(countItems(vs.items) { case Item.AbstractSortItem(_) => }, 2)
    assertEquals(countItems(vs.items) { case Item.RequiresDeclItem(_) => }, 1)
    val vsOps = sumItems(vs.items) { case Item.OperationBlockItem(b) => b.entries.length }
    assertEquals(vsOps, 4, "VectorSpace should expose 4 operations (vec_add/sub/scale/zero)")
    val vsRules = sumItems(vs.items) { case Item.RuleBlockItem(b) => b.entries.length }
    // 8, not 7: WI-935 added `vec_sub_def` — the one WI-137 geometry law with no
    // abstract counterpart — when it retired the per-component copies.
    assertEquals(vsRules, 8, "VectorSpace should declare 8 algebraic-law rules")

    // Loads cleanly into a KB primed with Prelude — TOGETHER WITH arithmetic.anthill,
    // which WI-20260825-1WBZT made it depend on. It used to be self-contained "except for
    // `?` placeholders for abstract T/V/F"; now `Ring provides Additive` /
    // `provides Multiplicative` and `VectorSpace`'s scalar-side laws name
    // `Additive.{add,sub,zero}` / `Multiplicative.{mul,one}`, so the categories have to be
    // in the KB. `EmbeddedStdlib` already loads `arithmetic` ahead of `numeric` and
    // `algebra` for the same reason.
    //
    // THE IMPORT IS WHAT FAILS LOUDLY, and it is worth knowing which half does: with
    // `arithmetic` left out, `VectorSpace`'s `import anthill.prelude.{Additive,
    // Multiplicative}` reports "unresolved name 'Additive' in scope 'anthill.prelude'"
    // — while `Ring`'s `provides Additive[T = T]` says nothing at all, because an
    // unresolved provision target degrades to an interned name. That asymmetry is why the
    // import is written out rather than left to the `provides` chain.
    val arithmeticPf = parseStdlibFile("anthill.prelude.arithmetic")
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, IndexedSeq(arithmeticPf, pf))
    assert(errs.isEmpty, s"load errors: $errs")
    assert(kb.hasQualifiedName("anthill.prelude.Additive.add"))
    assert(kb.hasQualifiedName("anthill.prelude.Multiplicative.mul"))
    assert(kb.hasQualifiedName("anthill.prelude.algebra.Ring"))
    assert(kb.hasQualifiedName("anthill.prelude.algebra.VectorSpace"))
    // WI-20260825-1WBZT: `Ring.add` is NOT a name any more — `add` is declared once, by
    // `anthill.prelude.Additive`, and `Ring` reaches it through `provides`. The absence
    // is the assertion: a second declaration under the same short name is exactly what
    // the syntax-category rule removes, and `algebra.anthill` would otherwise be free to
    // reintroduce one silently.
    assert(!kb.hasQualifiedName("anthill.prelude.algebra.Ring.add"),
      "`Ring` must declare no `add`: one spec declares each short name")
    assert(kb.hasQualifiedName("anthill.prelude.algebra.VectorSpace.vec_add"))
  }

  test("WI-153: stdlib float.anthill parses + loads (depends on algebra)") {
    val algebraPf = parseStdlibFile("anthill.prelude.algebra")
    val floatPf = parseStdlibFile("anthill.prelude.float")

    // proposal 038: Float is now a top-level `sort anthill.prelude.Float`
    // (was `namespace`), and its typeclass-satisfaction facts moved to the
    // per-language binding files — stdlib holds the pure spec.
    val ns = floatPf.items.collectFirst { case Item.SortWithBodyItem(s) => s }
      .getOrElse(fail("expected sort"))
    assertEquals(ns.name.segments.map(floatPf.symbols.name).mkString("."), "anthill.prelude.Float")

    // No satisfaction facts in stdlib (moved to bindings); 32 operations,
    // 5 rules, 6 constraints — a sort with no inner sorts.
    assertEquals(countItems(ns.items) { case Item.FactItem(_) => }, 0,
      "Float spec should declare no satisfaction facts (moved to bindings)")
    val opCount = sumItems(ns.items) {
      case Item.OperationBlockItem(b) => b.entries.length
      case Item.OperationItem(_)      => 1
    }
    // WI-876: 28 + the four comparisons (`gt`/`gte`/`lt`/`lte`). `Float` DECLARES
    // them now because its host implementations are keyed per carrier — its
    // binding's `operation_map` names the IEEE functions — where they used to be
    // registered on the `PartialOrd` spec op and serve every carrier at once.
    // WI-881: + the IEEE `max`/`min` pair. `max`/`min` live on `Ord`, which
    // `Float` does not provide, so before this there was no way to take the maximum
    // of two floats at all — and `Ord`'s `gte`-based derivation would have been
    // the wrong answer anyway (not commutative with a NaN operand).
    // WI-880: + `add`/`sub`/`mul`, and for the reason WI-876 gave for the
    // comparisons one paragraph up. They were registered on the `Additive` /
    // `Multiplicative` SPEC ops, where ONE implementation served every carrier and
    // told the three apart by TESTING ITS OPERANDS — and the three are genuinely
    // different operations: `Float`'s SATURATE to an infinity, `Int64`'s RAISE on
    // overflow, `BigInt`'s cannot overflow. `Float` declares its own so its binding's
    // `operation_map` has something to key `float_add` to.
    assertEquals(opCount, 37, "Float should expose 37 operations")
    assertEquals(countItems(ns.items) { case Item.RuleItem(_) => }, 5,
      "Float should declare 5 algebraic rules (neg, abs, recip, tau, nonEqRefl)")
    assertEquals(countItems(ns.items) { case Item.ConstraintItem(_) => }, 6,
      "Float should declare 6 constraints")

    // Loaded as part of the full stdlib chain — Eq/Ord/Numeric resolve.
    val kb = kbWithStdlib()
    assert(kb.hasQualifiedName("anthill.prelude.Float"))
    assert(kb.hasQualifiedName("anthill.prelude.Float.sqrt"))
    assert(kb.hasQualifiedName("anthill.prelude.Float.atan2"))
    assert(kb.hasQualifiedName("anthill.prelude.Float.pi"))
  }

  test("WI-153: stdlib geometry.anthill loads end-to-end (depends on algebra + Float)") {
    val algebraPf = parseStdlibFile("anthill.prelude.algebra")
    val floatPf = parseStdlibFile("anthill.prelude.float")
    val geomPf = parseStdlibFile("anthill.geometry")

    val ns = geomPf.items.collectFirst { case Item.NamespaceItem(n) => n }
      .getOrElse(fail("expected namespace"))
    assertEquals(ns.name.segments.map(geomPf.symbols.name).mkString("."), "anthill.geometry")

    // WI-935 reshaped this file. `Vec3` is now a SORT with an eponymous
    // constructor and four bodied `VectorSpace` members, so only `EulerAngles`
    // remains a namespace-level entity; the four vec_* relational rules and
    // their eight per-component laws are GONE (the relational reading is derived
    // from the body — WI-669 — and the laws moved to the spec, over abstract V).
    //
    // Still no satisfaction fact in stdlib: `VectorSpace[Vec3, Float]` lives in
    // the per-language binding layer (rust-side WI-343), because it depends on
    // `Ring[Float]` — a binding fact — so the claim is unsound in a stdlib-only
    // load. (Same pattern as Float's facts above.)
    assertEquals(countItems(ns.items) { case Item.EntityItem(_) => }, 1,
      "geometry exposes 1 namespace-level entity (EulerAngles); Vec3 is a sort")
    assertEquals(countItems(ns.items) { case Item.SortWithBodyItem(_) => }, 1,
      "geometry exposes 1 sort (Vec3, eponymous constructor + 4 members)")
    assertEquals(countItems(ns.items) { case Item.FactItem(_) => }, 0,
      "geometry's VectorSpace[Vec3, Float] satisfaction moved to the binding layer")
    assertEquals(countItems(ns.items) { case Item.RuleItem(_) => }, 0,
      "WI-935: geometry declares no namespace-level rules")

    val kb = kbWithStdlib()
    assert(kb.hasQualifiedName("anthill.geometry.Vec3"))
    assert(kb.hasQualifiedName("anthill.geometry.EulerAngles"))
  }

  test("WI-153: stdlib witness.anthill loads end-to-end with full sort/entity counts") {
    val pf = parseStdlibFile("anthill.realization.witness")
    val ns = pf.items.collectFirst { case Item.NamespaceItem(n) => n }
      .getOrElse(fail("expected namespace"))
    assertEquals(ns.name.segments.map(pf.symbols.name).mkString("."), "anthill.realization.witness")

    // 2 inner sorts (ProofWitness, SmtVerdict), 2 top-level entities
    // (SortBinding, MetaTacticContract).
    val sorts = ns.items.collect { case Item.SortWithBodyItem(s) => s }
    assertEquals(sorts.map(s => pf.symbols.name(s.name.last)).toSet,
      Set("ProofWitness", "SmtVerdict"))
    val topEntities = ns.items.collect { case Item.EntityItem(e) => e }
    assertEquals(topEntities.map(e => pf.symbols.name(e.name.last)).toSet,
      Set("SortBinding", "MetaTacticContract"))

    // ProofWitness: 6 constructors; SmtVerdict: 3.
    val proofWitness = sorts.find(s => pf.symbols.name(s.name.last) == "ProofWitness").get
    assertEquals(countItems(proofWitness.items) { case Item.EntityItem(_) => }, 6)
    val smtVerdict = sorts.find(s => pf.symbols.name(s.name.last) == "SmtVerdict").get
    assertEquals(countItems(smtVerdict.items) { case Item.EntityItem(_) => }, 3)

    val kb = kbWithStdlib()
    assert(kb.hasQualifiedName("anthill.realization.witness.ProofWitness"))
    assert(kb.hasQualifiedName("anthill.realization.witness.ProofWitness.SmtDischarge"))
    assert(kb.hasQualifiedName("anthill.realization.witness.SortBinding"))
    assert(kb.hasQualifiedName("anthill.realization.witness.MetaTacticContract"))
  }

  test("WI-153: EmbeddedStdlib parses every advertised stdlib path") {
    val (parsed, errors) = EmbeddedStdlib.parseFromDir(Paths.get(stdlibDir))
    assert(errors.isEmpty, s"stdlib parse errors: $errors")
    assertEquals(parsed.length, EmbeddedStdlib.stdlibPaths.length,
      "every advertised stdlib path should yield a ParsedFile")
  }

  test("WI-153: EmbeddedStdlib loads as a single KB load pass") {
    val kb = kbWithStdlib()
    for qn <- Seq(
        "anthill.prelude.algebra.Ring",
        "anthill.prelude.algebra.VectorSpace",
        "anthill.prelude.Float",
        "anthill.prelude.Float.sqrt",
        "anthill.geometry.Vec3",
        "anthill.realization.witness.ProofWitness")
    do assert(kb.hasQualifiedName(qn), s"$qn should be registered after stdlib load")
  }

  // ── WI-155 / WI-161 helpers shared by witness + ProofRecord tests ─

  /** Cached parse of every stdlib file in EmbeddedStdlib — used by tests
    * that need the full chain so transitive imports resolve cleanly.
    */
  private lazy val stdlibParsedFiles: IndexedSeq[ParsedFile] =
    val (parsed, errs) = EmbeddedStdlib.parseFromDir(Paths.get(stdlibDir))
    assert(errs.isEmpty, s"stdlib parse errors: $errs")
    parsed

  /** Look up a named argument on a Fn term and follow it through the KB. */
  private def namedArg(kb: KnowledgeBase, fn: Term.Fn, name: String): TermId =
    val sym = kb.intern(name)
    fn.namedArgs.find(_._1 == sym).map(_._2)
      .getOrElse(fail(s"missing named arg `$name`"))

  /** Resolve a functor Symbol to its qualified name; fails the test if unresolved. */
  private def functorQn(kb: KnowledgeBase, sym: anthill.intern.TermSymbol): String =
    kb.symbols.get(sym) match
      case anthill.intern.SymbolDef.Resolved(_, qn, _, _) => qn
      case other => fail(s"functor unresolved: $other")

  /** Build a KB pre-loaded with the full stdlib chain. Used by per-file
    * tests to make transitive imports resolve cleanly. The file under test
    * is typically already in the chain — no need to add it again.
    */
  private def kbWithStdlib(): KnowledgeBase =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, stdlibParsedFiles)
    assert(errs.filterNot(isToleratedLoadError).isEmpty,
      s"unexpected load errors: $errs")
    kb

  /** As above, but also loads a user file alongside the stdlib chain. */
  private def kbWithStdlibAndUser(userPf: ParsedFile): KnowledgeBase =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, stdlibParsedFiles :+ userPf)
    assert(errs.filterNot(isToleratedLoadError).isEmpty,
      s"unexpected load errors: $errs")
    kb

  /** Backwards-compat alias used by the WI-155 ProofRecord round-trip tests. */
  private def kbWithWitnessSchema(userPf: ParsedFile): KnowledgeBase =
    kbWithStdlibAndUser(userPf)

  test("WI-155: stdlib realization.anthill parses end-to-end") {
    val pf = parseStdlibFile("anthill.realization.realization")
    val ns = pf.items.collectFirst { case Item.NamespaceItem(n) => n }
      .getOrElse(fail("expected namespace"))
    assertEquals(ns.name.segments.map(pf.symbols.name).mkString("."), "anthill.realization")
    val entityNames = ns.items.collect { case Item.EntityItem(e) => pf.symbols.name(e.name.last) }.toSet
    // ProofRecord, ProofStrategyOpen, ProofStrategyKind, ProofBodyNone,
    // ProofBodyHints, ProofBodyQuery, ProofStep, ProofConcludeClause,
    // ParametricBinding (et al.) — minimum subset we rely on.
    for needed <- Seq("ProofRecord", "ProofStrategyOpen", "ProofBodyNone", "ParametricBinding") do
      assert(entityNames.contains(needed), s"expected entity $needed, got $entityNames")
  }

  test("WI-155: ProofRecord fact with witness + state_hash round-trips through parser + loader") {
    // User-authored ProofRecord fact citing a TrustedAxiom witness — the
    // simplest witness shape per witness.anthill. The fact must round-trip
    // (parse + load + KB lookup retrieves the same named-args). Fully
    // qualified names sidestep the entities-inside-sorts selective-import
    // gap (a separate scaland resolver issue, tracked via WI-163's family).
    val src =
      """namespace test.proofs
        |  fact anthill.realization.ProofRecord(
        |    rule: "demo.foo.requires.Eq_T",
        |    strategy: anthill.realization.ProofStrategyOpen,
        |    body: anthill.realization.ProofBodyNone,
        |    result: anthill.realization.Pending,
        |    dependencies: nil,
        |    using: nil,
        |    witness: anthill.realization.witness.ProofWitness.TrustedAxiom(reason: "demo"),
        |    state_hash: "abc123",
        |    parametric_context: nil)
        |end""".stripMargin
    val userPf = Parser.parse(src, "<proof-record>") match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.message).mkString("; ")}")
    val kb = kbWithWitnessSchema(userPf)

    val proofRecordSym = kb.tryResolveSymbol("anthill.realization.ProofRecord")
      .getOrElse(fail("ProofRecord symbol not registered"))
    val records = kb.byFunctor(proofRecordSym)
    assertEquals(records.length, 1, "expected exactly one ProofRecord fact")

    val recordHead = kb.getTerm(kb.ruleHead(records.head)) match
      case fn: Term.Fn => fn
      case other => fail(s"expected Fn at fact head, got $other")

    kb.getTerm(namedArg(kb, recordHead, "state_hash")) match
      case Term.Const(Literal.StringLit(s)) => assertEquals(s, "abc123")
      case other => fail(s"expected StringLit('abc123') for state_hash, got $other")

    val witnessFn = kb.getTerm(namedArg(kb, recordHead, "witness")) match
      case w: Term.Fn => w
      case other => fail(s"expected Fn for witness term, got $other")
    assert(functorQn(kb, witnessFn.functor).endsWith("TrustedAxiom"),
      s"expected witness functor TrustedAxiom, got ${functorQn(kb, witnessFn.functor)}")
    kb.getTerm(namedArg(kb, witnessFn, "reason")) match
      case Term.Const(Literal.StringLit(s)) => assertEquals(s, "demo")
      case other => fail(s"expected StringLit('demo') for reason, got $other")
  }

  test("WI-155: SmtDischarge witness with SmtVerdict round-trips") {
    // A ProofRecord whose witness is the more structured SmtDischarge —
    // exercises the full witness schema including SmtVerdict.Unsat.
    val src =
      """namespace test.proofs
        |  fact anthill.realization.ProofRecord(
        |    rule: "demo.bar",
        |    strategy: anthill.realization.ProofStrategyOpen,
        |    body: anthill.realization.ProofBodyNone,
        |    result: anthill.realization.Pending,
        |    dependencies: nil,
        |    using: nil,
        |    witness: anthill.realization.witness.ProofWitness.SmtDischarge(
        |      backend: "z3",
        |      logic: "QF_LRA",
        |      document_hash: "deadbeef",
        |      verdict: anthill.realization.witness.SmtVerdict.Unsat(),
        |      core: none),
        |    state_hash: "h1",
        |    parametric_context: nil)
        |end""".stripMargin
    val userPf = Parser.parse(src, "<smt-record>") match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.message).mkString("; ")}")
    val kb = kbWithWitnessSchema(userPf)

    val proofRecordSym = kb.tryResolveSymbol("anthill.realization.ProofRecord")
      .getOrElse(fail("ProofRecord symbol not registered"))
    val records = kb.byFunctor(proofRecordSym)
    assertEquals(records.length, 1)

    val recordHead = kb.getTerm(kb.ruleHead(records.head)) match
      case fn: Term.Fn => fn
      case other => fail(s"expected Fn at fact head, got $other")
    val witnessFn = kb.getTerm(namedArg(kb, recordHead, "witness")) match
      case w: Term.Fn => w
      case other => fail(s"expected Fn for witness, got $other")
    // WI-20260902-CZJ2N: `Unsat` is a NULLARY constructor and is stored bare, so the
    // verdict arrives as `Term.Ref`. The claim is the NAME, not the spelling.
    val verdictSym = kb.getTerm(namedArg(kb, witnessFn, "verdict")) match
      case Term.Fn(functor, _, _) => functor
      case Term.Ref(sym)          => sym
      case other => fail(s"expected a verdict application, got $other")
    assert(functorQn(kb, verdictSym).endsWith("Unsat"),
      s"expected Unsat, got ${functorQn(kb, verdictSym)}")
  }

  // ── WI-163: bare `eq(?x, ?y)` resolves to PartialEq.eq with no ambiguity ─

  test("WI-163: bare `eq(?x, ?y)` in a rule resolves to anthill.prelude.PartialEq.eq") {
    // Pre-fix this would have produced AmbiguousSymbol(eq, [anthill.prelude.eq,
    // …]). Post-fix the structural-op shim is gone and `eq` resolves uniquely
    // through the loaded eq.anthill typeclass. WI-644 moved the `eq`/`neq`
    // OPERATIONS into `PartialEq` (Eq now just `requires PartialEq[T]` + the
    // reflexivity law), so the unique resolution is `PartialEq.eq`.
    val src =
      """sort Demo
        |  rule same(?x, ?y) :- eq(?x, ?y)
        |end""".stripMargin
    val eqPf = parseStdlibFile("anthill.prelude.eq")
    val userPf = Parser.parse(src, "<eq-test>") match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.message).mkString("; ")}")

    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, IndexedSeq(eqPf, userPf))
    val unrelated = errs.filterNot(isToleratedLoadError)
    assert(unrelated.isEmpty, s"unexpected load errors: $unrelated")

    // Find the same/2 rule and walk into its body to confirm `eq` resolved
    // to anthill.prelude.PartialEq.eq (not the would-be-ambiguous anthill.prelude.eq).
    // `same` is the rule's head functor — a RULE-INTRODUCED symbol since the pass-3
    // port (WI-894/896/898), registered as `Demo.same`; it used to be a bare intern,
    // which is why this lookup changed with that pass and not with anything about `eq`.
    val sameSym = kb.tryResolveSymbol("Demo.same")
      .getOrElse(fail("`same` should be registered as a rule-introduced functor"))
    val rules = kb.byFunctor(sameSym)
    assertEquals(rules.length, 1)
    val body = kb.ruleBody(rules.head)
    assertEquals(body.length, 1)
    kb.getTerm(body.head) match
      case fn: Term.Fn =>
        assertEquals(functorQn(kb, fn.functor), "anthill.prelude.PartialEq.eq",
          "bare eq(?x, ?y) should resolve uniquely to PartialEq.eq (WI-644)")
      case other => fail(s"expected Fn for body atom, got $other")
  }


  // ── Rust parser resync: the two LOAD-side halves ──────────────────

  /** WI-727: "at most one variadic capture, and trailing" is checked in the loader,
    * not the parser — the diagnostic quotes the QUALIFIED operation name, which only
    * the loader has. Both messages mirror rustland's. These fail on the pre-resync
    * loader in the opposite direction: `...` did not parse at all, so nothing reached
    * the check. */
  private def loadOpSource(src: String): IndexedSeq[LoadError] =
    val pf = Parser.parse(src, "<variadic>") match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.message).mkString("; ")}")
    val kb = KnowledgeBase()
    Prelude.register(kb)
    Loader.loadAll(kb, IndexedSeq(pf)).toIndexedSeq

  test("WI-727: a trailing single `...` capture loads clean") {
    val errs = loadOpSource(
      """namespace v
        |  sort Rel
        |    sort R = ?
        |    operation fix(p: Rel, ...args: R) -> Rel
        |  end
        |end""".stripMargin)
    assert(errs.isEmpty, s"unexpected load errors: $errs")
  }

  test("WI-727: a NON-TRAILING capture is refused, naming the qualified operation") {
    val errs = loadOpSource(
      """namespace v
        |  sort Rel
        |    sort R = ?
        |    operation fix(...args: R, p: Rel) -> Rel
        |  end
        |end""".stripMargin)
    val m = errs.collectFirst { case LoadError.Other(msg, _) if msg.contains("variadic") => msg }
      .getOrElse(fail(s"expected a variadic refusal, got: $errs"))
    assert(m.contains("v.Rel.fix"), m)
    assert(m.contains("LAST parameter"), m)
  }

  test("WI-727: TWO captures are refused") {
    val errs = loadOpSource(
      """namespace v
        |  sort Rel
        |    sort R = ?
        |    operation fix(...a: R, ...b: R) -> Rel
        |  end
        |end""".stripMargin)
    val m = errs.collectFirst { case LoadError.Other(msg, _) if msg.contains("variadic") => msg }
      .getOrElse(fail(s"expected a variadic refusal, got: $errs"))
    assert(m.contains("at most one"), m)
  }

  /** WI-853: a TOP-LEVEL import feeds `<global>`, the scope a file's top-level
    * declarations are defined in. Drives the capability rather than the parse: the
    * imported short name must actually RESOLVE afterwards. */
  test("WI-853: a top-level import puts the imported name in scope at `<global>`") {
    val provider = Parser.parse(
      """namespace lib
        |  sort Widget853
        |    sort T = ?
        |  end
        |end""".stripMargin, "<provider>").toOption.getOrElse(fail("provider parse failed"))
    val user = Parser.parse(
      "import lib.{Widget853}\nfact Uses(w: 1)", "<user>")
      .toOption.getOrElse(fail("user parse failed"))

    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, IndexedSeq(provider, user)).filterNot(isToleratedLoadError)
    assert(errs.isEmpty, s"unexpected load errors: $errs")

    kb.symbols.resolveInScope("Widget853", kb.globalScope) match
      case ResolveResult.Found(sym) =>
        kb.symbols.get(sym) match
          case SymbolDef.Resolved(_, qn, _, _) => assertEquals(qn, "lib.Widget853")
          case other => fail(s"expected a resolved symbol, got $other")
      case other =>
        fail(s"`Widget853` should resolve at <global> through the top-level import, got $other")
  }

  // ── Pass 3 + 4: rule-introduced functors, deferred predicate imports ──
  //   Port of rustland WI-295 / WI-894 / WI-896 / WI-898. Before it, every test
  //   below either failed to resolve the imported name or minted a symbol it
  //   should not have; the whole shared stdlib failed to LOAD on the first one.

  private def loadFixture(src: String): (KnowledgeBase, IndexedSeq[LoadError]) =
    val pf = Parser.parse(src, "<pass3>") match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.message).mkString("; ")}")
    val kb = KnowledgeBase()
    Prelude.register(kb)
    (kb, Loader.loadAll(kb, IndexedSeq(pf)).toIndexedSeq)

  private def kindOf(kb: KnowledgeBase, qualified: String): Option[SymbolKind] =
    kb.symbols.byQualifiedName.get(qualified).map(kb.symbols.get).collect {
      case SymbolDef.Resolved(_, _, kind, _) => kind
    }

  /** The `ite` shape verbatim: a functor NO declaration names, introduced by its
    * equations alone and reached from another sort by a selective import. */
  private val rulePredicateFixture =
    """namespace p3
      |  sort Boolish
      |    rule {
      |      ite_true:  ite(true, ?t, ?e) <=> ?t
      |      ite_false: ite(false, ?t, ?e) <=> ?e
      |    }
      |    rule likes(?a, ?b) :- ite(?a, ?b, ?a)
      |  end
      |  sort User
      |    import p3.Boolish.{ite}
      |    rule uses(?x) :- ite(?x, 1, 2)
      |  end
      |end""".stripMargin

  test("WI-898: an EQUATION head introduces its LHS functor, not the connective") {
    val (kb, errs) = loadFixture(rulePredicateFixture)
    assert(errs.isEmpty, s"unexpected load errors: $errs")
    assertEquals(kindOf(kb, "p3.Boolish.ite"), Some(SymbolKind.EquationFunctor))
    assertEquals(kb.symbols.byQualifiedName.get("p3.Boolish.eq"), None,
      "the `=` connective must not be introduced as a functor")
  }

  test("WI-896: a PREDICATE head introduces a Goal") {
    val (kb, _) = loadFixture(rulePredicateFixture)
    assertEquals(kindOf(kb, "p3.Boolish.likes"), Some(SymbolKind.Goal))
    assertEquals(kindOf(kb, "p3.User.uses"), Some(SymbolKind.Goal))
  }

  test("WI-295: a selective import of a rule-introduced functor resolves") {
    val (kb, errs) = loadFixture(rulePredicateFixture)
    assert(errs.isEmpty, s"unexpected load errors: $errs")
    val userScope = kb.symbols.byQualifiedName.get("p3.User")
      .map(kb.symbols.scopeOf)
      .getOrElse(fail("p3.User should be registered"))
    kb.symbols.resolveInScope("ite", userScope) match
      case ResolveResult.Found(sym) =>
        kb.symbols.get(sym) match
          case SymbolDef.Resolved(_, qn, _, _) => assertEquals(qn, "p3.Boolish.ite")
          case other => fail(s"expected a resolved symbol, got $other")
      case other => fail(s"`ite` should resolve in p3.User through the import, got $other")
  }

  test("WI-295: an import naming nothing at all is STILL an error after the retry") {
    val (_, errs) = loadFixture(
      """namespace p3b
        |  sort Boolish
        |    rule ite(true, ?t, ?e) <=> ?t
        |  end
        |  sort User
        |    import p3b.Boolish.{nosuchname}
        |  end
        |end""".stripMargin)
    assert(errs.exists { case LoadError.UnresolvedName("nosuchname", _, _) => true; case _ => false },
      s"expected an unresolved-name error for the deferred import, got: $errs")
  }

  test("WI-618: a MINTED subject introduces nothing (accessor and infix desugars)") {
    val (kb, _) = loadFixture(
      """namespace p3c
        |  sort S
        |    rule ?x.m(?y) :- holds(?x)
        |    rule ?a + ?b = ?c :- holds(?a)
        |  end
        |end""".stripMargin)
    for minted <- Seq("dot_apply", "add", "eq") do
      assertEquals(kb.symbols.byQualifiedName.get(s"p3c.S.$minted"), None,
        s"`$minted` is the desugar's own functor and must not be introduced")
  }

  test("a head naming a DECLARED operation introduces nothing (no second meaning)") {
    val (kb, _) = loadFixture(
      """namespace p3d
        |  sort S
        |    sort T = ?
        |    operation f(x: T) -> T
        |    rule f(?x) = ?x
        |  end
        |end""".stripMargin)
    assertEquals(kindOf(kb, "p3d.S.f"), Some(SymbolKind.Operation),
      "the operation keeps its kind — the rule head references it, it does not redefine it")
  }

  test("a QUALIFIED head introduces nothing") {
    val (kb, _) = loadFixture(
      """namespace p3e
        |  sort S
        |    rule Other.isEmpty(?s) = true
        |  end
        |end""".stripMargin)
    assertEquals(kb.symbols.byQualifiedName.get("p3e.S.Other.isEmpty"), None)
    assertEquals(kb.symbols.byQualifiedName.get("p3e.S.isEmpty"), None)
  }

  test("a MULTI-HEAD rule introduces nothing") {
    val (kb, _) = loadFixture(
      """namespace p3f
        |  sort S
        |    rule pair_law: h1(?x), h2(?x) :- holds(?x)
        |  end
        |end""".stripMargin)
    for h <- Seq("h1", "h2") do
      assertEquals(kb.symbols.byQualifiedName.get(s"p3f.S.$h"), None,
        s"`$h` is one of several heads — a multi-head rule introduces nothing")
  }

  /** The mint guard and the reference resolver must answer a SHORT name the same way.
    * Pass 3 registers an unqualified `byQualifiedName` entry for every top-level rule
    * head, and while `resolveName` took that entry ahead of scope, a sort's law about
    * its own operation was indexed under an unrelated global predicate of the same
    * short name — with no diagnostic. Fails without the dotted-only rung in
    * `resolveName`; unaffected by anything else in the pass-3 port. */
  test("a scope's own rule clauses are not captured by a same-named global functor") {
    val globalRule = Parser.parse("rule p(?y) :- q(?y)", "_global")
      .toOption.getOrElse(fail("global parse failed"))
    val scoped = Parser.parse(
      """namespace n
        |  sort S
        |    sort T = ?
        |    operation p(x: T) -> T
        |    rule p(?x) :- q(?x)
        |  end
        |end""".stripMargin, "<scoped>").toOption.getOrElse(fail("scoped parse failed"))

    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, IndexedSeq(globalRule, scoped)).filterNot(isToleratedLoadError)
    assert(errs.isEmpty, s"unexpected load errors: $errs")

    val globalP = kb.symbols.byQualifiedName.get("p").getOrElse(fail("global `p` should exist"))
    val scopedP = kb.symbols.byQualifiedName.get("n.S.p").getOrElse(fail("`n.S.p` should exist"))
    assertEquals(kb.byFunctor(globalP).length, 1, "the global rule keeps exactly its own clause")
    assertEquals(kb.byFunctor(scopedP).length, 1, "S's law is indexed under S's own operation")
  }

  /** The pass-4 retry must try the SAME rungs pass 2 tried. Here the import names the
    * enclosing NAMESPACE, so the functor is one scope deeper and only
    * `findInNestedScope` finds it — a retry that looked up the exact qualified string
    * `p4.ite` alone would refuse a name that is plainly there. */
  test("WI-295: a deferred import resolves through the nested-scope rung too") {
    val (kb, errs) = loadFixture(
      """namespace p4
        |  sort Boolish
        |    rule ite(true, ?t, ?e) <=> ?t
        |  end
        |  sort User
        |    import p4.{ite}
        |  end
        |end""".stripMargin)
    assert(errs.isEmpty, s"unexpected load errors: $errs")
    val userScope = kb.symbols.byQualifiedName.get("p4.User")
      .map(kb.symbols.scopeOf).getOrElse(fail("p4.User should be registered"))
    kb.symbols.resolveInScope("ite", userScope) match
      case ResolveResult.Found(sym) =>
        kb.symbols.get(sym) match
          case SymbolDef.Resolved(_, qn, _, _) => assertEquals(qn, "p4.Boolish.ite")
          case other => fail(s"expected a resolved symbol, got $other")
      case other => fail(s"`ite` should resolve through the namespace-path import, got $other")
  }

  /** A 2-ary head spelled as an ordinary CALL is a predicate, not an equation — the
    * connective test is guarded by parse provenance, so a user functor that happens to
    * be named `eq` is not mistaken for the `=` desugar and dropped. */
  test("WI-618: a written `eq(?a, ?b)` head is a predicate, not an equation") {
    val (kb, _) = loadFixture(
      """namespace p5
        |  sort S
        |    rule eq(?a, ?b)
        |  end
        |end""".stripMargin)
    assertEquals(kindOf(kb, "p5.S.eq"), Some(SymbolKind.Goal),
      "a written call introduces a Goal; only the infix desugar makes an equation")
  }

  // ── WI-1090: `===` is a test, not a defining connective ──

  /** `===` sits in the TEST column of the spec's equality table (§"Equality: test vs.
    * bind, structural vs. semantic"), beside `=`, with `<=>` alone in the bind column
    * and named there as "the connective of equational rule heads". So a bodyless `lhs
    * === rhs` reads as a definition and can never be one, and the loader says so
    * instead of storing a clause nothing will ever consult.
    *
    * Ported with rustland's half (WI-1090), which measured what the silence cost: the
    * subject was stamped an equation-functor owning zero clauses, `[simp]` could never
    * fire it, and the only diagnostic reached the author at a CITATION, blaming a
    * missing equation that was written three lines up. */
  test("WI-1090: a bodyless `===` head is refused and names `<=>` as the substitute") {
    val (kb, errs) = loadFixture(
      """namespace p1090
        |  sort S
        |    rule g1090(?x) === ?x
        |  end
        |end""".stripMargin)
    assert(errs.exists(e => e.toString.contains("`===` is the structural identity TEST")),
      s"a bodyless `===` head must be refused at the rule; got $errs")
    assert(errs.exists(e => e.toString.contains("g1090") && e.toString.contains("Write `<=>`")),
      s"the message must name the subject and the connective that defines it; got $errs")
    assertEquals(kindOf(kb, "p1090.S.g1090"), None,
      "and nothing is introduced under it \u2014 `===` has no subject to introduce")
  }

  /** A fact IS a bodyless rule (§6.1), so the same head one keyword away is the same
    * dead clause. Rustland shipped the rule side alone and its review found this
    * spelling loading clean; both sides carry the row now. */
  test("WI-1090: the `fact` spelling of a `===` head is refused too") {
    val (_, errs) = loadFixture(
      """namespace p1090b
        |  sort S
        |    fact g1090(1) === g1090(1)
        |  end
        |end""".stripMargin)
    assert(errs.exists(e => e.toString.contains("`===` is the structural identity TEST")),
      s"`fact lhs === rhs` is a bodyless rule and must be refused; got $errs")
  }

  /** THE LIMIT, in both directions the refusal could have overreached: a rule with a
    * BODY is an ordinary law about the operator (`totalfloat.anthill` writes one), and
    * a `<=>` head one character apart is a real equation whose subject IS introduced.
    * Without this row the refusal could be widened to every `===` head — which would
    * refuse the standard library — and nothing would notice. */
  test("WI-1090: a bodied law about `===`, and the `<=>` twin, both still load") {
    val (kb, errs) = loadFixture(
      """namespace p1090c
        |  sort S
        |    rule same1090(?x) :- ?x === 1
        |    rule g1090(?x) <=> ?x
        |  end
        |end""".stripMargin)
    assert(errs.isEmpty, s"neither shape is a bodyless `===` head; got $errs")
    assertEquals(kindOf(kb, "p1090c.S.g1090"), Some(SymbolKind.EquationFunctor),
      "`<=>` is the connective of equational rule heads, so its subject IS introduced")
  }

  // ── WI-888: `=` is a test too, so it does not head an equation either ──

  /** THE SAME TABLE ROW AS `===`, one connective over. The spec's equality table puts
    * `=` in the TEST column beside `===`, and `<=>` alone in the BIND column — and only
    * a connective that BINDS can head an equation, the head unifying the redex with its
    * LHS and deriving the RHS. WI-1090 held `===` to that; WI-888 holds `=` to it.
    *
    * IT WAS NOT THE SAME DEFECT, which is why the message differs and this test asserts
    * on the `=` wording rather than reusing the `===` needle. A `===` head was silently
    * useless; an `=` head FIRED (rustland's WI-884 drove all four connective ×
    * attribute combinations, and the answer tracked the `[simp]` tag alone). So this
    * refusal finishes proposal 049's migration — build step 6, WI-526, which relabelled
    * 40 heads and left 44 in the stdlib — rather than repairing a silence, and the
    * message owes the author the substitute spelling instead of a diagnosis. */
  test("WI-888: a bodyless `=` head is refused and names `<=>` as the substitute") {
    val (kb, errs) = loadFixture(
      """namespace p888
        |  sort S
        |    rule g888(?x) = ?x
        |  end
        |end""".stripMargin)
    assert(errs.exists(e => e.toString.contains("`=` is the semantic equality TEST")),
      s"a bodyless `=` head must be refused at the rule; got $errs")
    assert(errs.exists(e => e.toString.contains("Write `g888(…) <=> …`")),
      s"the message must name the subject and the connective that defines it; got $errs")
    assertEquals(kindOf(kb, "p888.S.g888"), None,
      "and nothing is introduced under it \u2014 `=` has no subject to introduce")
  }

  /** The `[simp]` tag has NO bearing on it, which is the half a reader of the pre-WI-888
    * behaviour would get backwards: the tag decided everything there and decides nothing
    * here. `reflect.anthill` and `bool.anthill` both shipped this exact combination. */
  test("WI-888: a `[simp]` tag does not admit the `=` spelling") {
    val (_, errs) = loadFixture(
      """namespace p888b
        |  sort S
        |    rule g888(?x) = ?x [simp]
        |  end
        |end""".stripMargin)
    assert(errs.exists(e => e.toString.contains("`=` is the semantic equality TEST")),
      s"`[simp]` does not admit a bodyless `=` head; got $errs")
  }

  /** THE BOUNDARY WI-888 DID NOT MOVE, and the row that stops the refusal being widened
    * into a tidier rule: a GUARDED equation keeps its `=` spelling, because proposal 049
    * draws the migration line at the EMPTY BODY and `map.anthill` writes one directly
    * beneath its `<=>` siblings. Passes with and without WI-888, by design. */
  test("WI-888: a guarded `=` equation keeps its spelling") {
    val (_, errs) = loadFixture(
      """namespace p888c
        |  sort S
        |    rule p888(?x) :- ?x === 1
        |    rule g888(?x) = ?x :- p888(?x)
        |  end
        |end""".stripMargin)
    assert(errs.isEmpty, s"a guarded `=` equation is not a bodyless head; got $errs")
  }

  /** THE DEFECT THE RELABEL SURFACED, mirrored from rustland. A namespace that declares
    * its own `unify` must not capture the MINTED `<=>` connective: `<=>` is
    * structural-only and never dispatches (proposal 049's Invariant), so a same-named
    * symbol in scope is a collision, not an override.
    *
    * This is `reflect.anthill`'s shape reduced to one file — that file declares
    * `unify(a: Term, b: Term, kb: KB)` for proposal 049's term-level face, and the three
    * `rule fact_monotonicity(…) <=> constant() [simp]` rules WI-888 rewrote in that same
    * namespace resolved their connective onto it, filing three clauses under a 3-ary
    * reflect operation. They loaded clean and fired nothing. scaland loads
    * `reflect.anthill`, so it had the identical defect; found by review after the
    * rustland half shipped alone.
    *
    * Asserted on WHICH FUNCTOR OWNS THE CLAUSE rather than on firing, because scaland has
    * no normalizer to fire it — the misfiling IS the defect, and it is what a later
    * reader of `byFunctor(kernel.unify)` would miss. Backing out
    * `Loader.mintedConnectiveSymbol` moves the clause to `p888d.S.unify` and both
    * assertions fail.
    *
    * The local declaration must stay CALLABLE, which is the second row: a WRITTEN
    * `unify(a, b, c)` call is not minted (WI-948), so it keeps the ordinary ladder. */
  test("WI-888: a local `unify` declaration does not capture the `<=>` connective") {
    val (kb, errs) = loadFixture(
      """namespace anthill.kernel
        |  operation unify(a: Int64, b: Int64) -> Bool
        |end
        |
        |namespace p888d
        |  sort S
        |    operation unify(a: Int64, b: Int64, c: Int64) -> Int64 = a
        |    rule g888d(?x) <=> ?x [simp]
        |  end
        |end""".stripMargin)
    assert(errs.isEmpty, s"the fixture must load; got $errs")
    val kernelUnify = kb.symbols.byQualifiedName.getOrElse("anthill.kernel.unify",
      fail("the fixture declares `anthill.kernel.unify`"))
    val localUnify = kb.symbols.byQualifiedName.getOrElse("p888d.S.unify",
      fail("the fixture declares a local `unify` to shadow with"))
    assertEquals(kb.byFunctor(kernelUnify).length, 1,
      "the `<=>` head belongs to the kernel primitive")
    assertEquals(kb.byFunctor(localUnify).length, 0,
      "\u2026and NOT to the same-named local declaration the scope ladder would have found")
  }

  // ── WI-992: a dotted declaration lives in the namespace it names ──

  /** `sort wi992.Spec` written at a file's top level, and a sibling requiring it by its
    * SHORT name. Deliberately NOT under `anthill.prelude`: every non-primitive sort
    * declared there is linked into `<global>` by `autoImportPrelude`, which would give
    * `spin` a second route and make the drive below pass for the wrong reason. */
  private val dottedSiblingFixture =
    """sort wi992.Spec
      |  sort T = ?
      |  operation spin(x: T) -> T
      |end
      |
      |sort wi992.User
      |  sort T = ?
      |  requires Spec[T]
      |end""".stripMargin

  test("WI-992: a dotted declaration's SIBLING resolves by its short name") {
    val (kb, errs) = loadFixture(dottedSiblingFixture)
    assert(errs.isEmpty, s"unexpected load errors: $errs")

    // The namespace the source never wrote, synthesized because a name asked for it.
    assertEquals(kindOf(kb, "wi992"), Some(SymbolKind.Namespace))
    assertEquals(kindOf(kb, "wi992.Spec"), Some(SymbolKind.Sort))

    val userScope = kb.symbols.byQualifiedName.get("wi992.User")
      .map(kb.symbols.scopeOf).getOrElse(fail("wi992.User should be registered"))
    kb.symbols.resolveInScope("Spec", userScope) match
      case ResolveResult.Found(sym) => assertEquals(functorQn(kb, sym), "wi992.Spec")
      case other => fail(s"`Spec` should resolve from its sibling `wi992.User`, got $other")
  }

  /** THE acceptance, driven: a requirement LINKS A PARENT SCOPE — that is the whole of
    * what `requires` does in scaland, which has no typer — so the requires-chain
    * inheritance the stdlib documents (WI-614) is exactly "an operation of the required
    * spec resolves from inside the requiring sort". `spin` is declared nowhere else and
    * `wi992.Spec` is linked into nothing else, so this is the only route to it.
    *
    * CONTROL, measured, one per half of WI-992 (345 pass with both):
    *   - back out `ensureNamespacePath` → 11 fail, 334 pass. This one and the sibling
    *     test above report `unresolved name 'Spec' in scope 'wi992.User'`; the other
    *     eight are the stdlib sites WI-988 measured, which is the whole reason this
    *     ticket exists.
    *   - restore `case TypeExpr.Parameterized(_, _) => None` in `processRequires` →
    *     2 fail, 343 pass: this one with `spin … got NotFound` and the stdlib link test
    *     below. NO error is reported for either, and the sibling test still passes
    *     because `Spec` still resolves. That silence is what let the gap survive — a
    *     load-clean assertion cannot see it, and 24 of the stdlib's 26 requirements are
    *     the parameterized form. */
  test("WI-992: a parameterized `requires` links the spec, so its operation is inherited") {
    val (kb, errs) = loadFixture(dottedSiblingFixture)
    assert(errs.isEmpty, s"unexpected load errors: $errs")

    val userScope = kb.symbols.byQualifiedName.get("wi992.User")
      .map(kb.symbols.scopeOf).getOrElse(fail("wi992.User should be registered"))
    kb.symbols.resolveInScope("spin", userScope) match
      case ResolveResult.Found(sym) => assertEquals(functorQn(kb, sym), "wi992.Spec.spin")
      case other =>
        fail(s"`spin` should be inherited through `requires Spec[T]`, got $other")
  }

  /** The measured site the ticket was written from: `anthill/prelude/eq.anthill:35`.
    * Structural, and deliberately so — `PartialEq` is auto-imported into `<global>`
    * alongside every other prelude spec, so resolving `eq` from inside `Eq` succeeds
    * through that route whether or not the requirement linked anything. The drive lives
    * in the `wi992.*` fixture above, which has no second route; this asserts the link
    * itself, on the real declaration, and fails when the parameterized arm is backed
    * out. */
  test("WI-869: a provision's `:- goals` link the spec scope, as a `requires` does") {
    val kb = kbWithStdlib()
    val scopeOf = (qn: String) =>
      kb.symbols.byQualifiedName.get(qn).map(kb.symbols.scopeOf)
        .getOrElse(fail(s"$qn should be registered"))
    val pairScope = scopeOf("anthill.prelude.Pair")
    val parents = kb.symbols.scope(pairScope).map(_.parents.map(_.parent).toSet)
      .getOrElse(fail("anthill.prelude.Pair should have a scope"))
    // `Pair` declares NO sort-level `requires` — every one of its four requirements is
    // a provision condition. MEASURED: before conditions were routed through the same
    // resolution, moving `requires PartialEq[A]` into `provides PartialEq[Pair] :-
    // PartialEq[A]` removed these links silently and `sbt test` stayed green.
    for (spec <- List("anthill.prelude.PartialEq", "anthill.prelude.Eq",
                      "anthill.prelude.PartialOrd", "anthill.prelude.Ord"))
      assert(parents.contains(scopeOf(spec)),
        s"`provides … :- $spec[…]` should link $spec; parents = " +
        parents.map(p => kb.scopeDisplayName(p)).mkString(", "))
  }

  test("WI-992: stdlib `sort anthill.prelude.Eq` has PartialEq as a parent scope") {
    val kb = kbWithStdlib()
    val eqScope = kb.symbols.byQualifiedName.get("anthill.prelude.Eq")
      .map(kb.symbols.scopeOf).getOrElse(fail("anthill.prelude.Eq should be registered"))
    val partialEq = kb.symbols.byQualifiedName.get("anthill.prelude.PartialEq")
      .map(kb.symbols.scopeOf).getOrElse(fail("anthill.prelude.PartialEq should be registered"))
    val parents = kb.symbols.scope(eqScope).map(_.parents.map(_.parent).toSet)
      .getOrElse(fail("anthill.prelude.Eq should have a scope"))
    assert(parents.contains(partialEq),
      s"`requires PartialEq[T]` should link PartialEq; parents = " +
      parents.map(p => kb.scopeDisplayName(p)).mkString(", "))
  }
