package anthill.parse

import anthill.intern.{TermSymbol, SymbolTable}
import anthill.term.{Term, TermId, Literal}

class ParseTest extends munit.FunSuite:

  test("Pratt parser - left associative addition") {
    // 1 + 2 + 3  should be  add(add(1, 2), 3)
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val plus = st.intern("+")
    val v1 = terms.alloc(Term.Const(Literal.IntLit(1)))
    val v2 = terms.alloc(Term.Const(Literal.IntLit(2)))
    val v3 = terms.alloc(Term.Const(Literal.IntLit(3)))

    val result = Pratt.desugar(
      IndexedSeq(v1, v2, v3),
      IndexedSeq(plus, plus),
      st.name,
      terms.alloc,
      st.intern
    )

    // Result should be add(add(1, 2), 3)
    terms.get(result) match
      case fn: Term.Fn =>
        assertEquals(st.name(fn.functor), "add")
        assertEquals(fn.posArgs.length, 2)
        // Left child should be add(1, 2)
        terms.get(fn.posArgs(0)) match
          case inner: Term.Fn =>
            assertEquals(st.name(inner.functor), "add")
          case other => fail(s"expected Fn, got $other")
        // Right child should be 3
        terms.get(fn.posArgs(1)) match
          case Term.Const(Literal.IntLit(3)) => // ok
          case other => fail(s"expected Const(3), got $other")
      case other => fail(s"expected Fn, got $other")
  }

  test("Pratt parser - right associative power") {
    // 2 ^ 3 ^ 4  should be  pow(2, pow(3, 4))
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val pow = st.intern("^")
    val v2 = terms.alloc(Term.Const(Literal.IntLit(2)))
    val v3 = terms.alloc(Term.Const(Literal.IntLit(3)))
    val v4 = terms.alloc(Term.Const(Literal.IntLit(4)))

    val result = Pratt.desugar(
      IndexedSeq(v2, v3, v4),
      IndexedSeq(pow, pow),
      st.name,
      terms.alloc,
      st.intern
    )

    terms.get(result) match
      case fn: Term.Fn =>
        assertEquals(st.name(fn.functor), "pow")
        // Left child should be 2
        terms.get(fn.posArgs(0)) match
          case Term.Const(Literal.IntLit(2)) => // ok
          case other => fail(s"expected Const(2), got $other")
        // Right child should be pow(3, 4)
        terms.get(fn.posArgs(1)) match
          case inner: Term.Fn =>
            assertEquals(st.name(inner.functor), "pow")
          case other => fail(s"expected Fn, got $other")
      case other => fail(s"expected Fn, got $other")
  }

  test("Pratt parser - precedence: + vs *") {
    // 1 + 2 * 3  should be  add(1, mul(2, 3))
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val plus = st.intern("+")
    val times = st.intern("*")
    val v1 = terms.alloc(Term.Const(Literal.IntLit(1)))
    val v2 = terms.alloc(Term.Const(Literal.IntLit(2)))
    val v3 = terms.alloc(Term.Const(Literal.IntLit(3)))

    val result = Pratt.desugar(
      IndexedSeq(v1, v2, v3),
      IndexedSeq(plus, times),
      st.name,
      terms.alloc,
      st.intern
    )

    terms.get(result) match
      case fn: Term.Fn =>
        assertEquals(st.name(fn.functor), "add")
        // Left should be 1
        terms.get(fn.posArgs(0)) match
          case Term.Const(Literal.IntLit(1)) => // ok
          case other => fail(s"expected Const(1), got $other")
        // Right should be mul(2, 3)
        terms.get(fn.posArgs(1)) match
          case inner: Term.Fn =>
            assertEquals(st.name(inner.functor), "mul")
          case other => fail(s"expected Fn, got $other")
      case other => fail(s"expected Fn, got $other")
  }

  test("Pratt parser - single operand") {
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val v = terms.alloc(Term.Const(Literal.IntLit(42)))
    val result = Pratt.desugar(IndexedSeq(v), IndexedSeq.empty, st.name, terms.alloc, st.intern)
    assertEquals(TermId.raw(result), TermId.raw(v))
  }

  test("SimpleTermStore allocates sequentially") {
    val terms = SimpleTermStore()
    val t1 = terms.alloc(Term.Const(Literal.IntLit(1)))
    val t2 = terms.alloc(Term.Const(Literal.IntLit(1)))
    // No hash-consing — same content gets different ids
    assertNotEquals(TermId.raw(t1), TermId.raw(t2))
    assertEquals(terms.size, 2)
  }

  test("Converter var scope") {
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val errors = scala.collection.mutable.ArrayBuffer.empty[ParseError]
    val conv = Converter("", st, terms, errors)

    val xSym = st.intern("x")
    val v1 = conv.getOrCreateVar(xSym)
    val v2 = conv.getOrCreateVar(xSym)
    assertEquals(v1, v2) // same var within scope

    conv.resetVarScope()
    val v3 = conv.getOrCreateVar(xSym)
    assertNotEquals(v1.id, v3.id) // different after reset
  }

  test("ParsedFile structure") {
    val result = Parser.parse("")
    assert(result.isRight)
    val parsed = result.toOption.get
    assert(parsed.items.isEmpty)
  }

  // ── WI-154: rule attribute flags + bare-flag desugar (proposal 025.X) ─

  private def ruleMeta(src: String): (ParsedFile, IndexedSeq[MetaEntry]) =
    val pf = Parser.parse(src, "<flags>").toOption.get
    val rule = pf.items.collectFirst { case Item.RuleItem(r) => r }.get
    val entries = rule.meta.map(_.entries).getOrElse(IndexedSeq.empty)
    (pf, entries)

  private def assertBottom(pf: ParsedFile, t: TermId, label: String): Unit =
    pf.terms.get(t) match
      case Term.Bottom => ()
      case other => fail(s"$label should store Term.Bottom, got $other")

  test("WI-154: bare `[simp]` parses identically to `[simp: true]` for key presence") {
    val (pfBare, bare) = ruleMeta("rule ?a + zero = ?a [simp]")
    val (pfFull, full) = ruleMeta("rule ?a + zero = ?a [simp: true]")

    assertEquals(bare.length, 1)
    assertEquals(full.length, 1)
    assertEquals(pfBare.symbols.name(bare.head.key.last), "simp")
    assertEquals(pfFull.symbols.name(full.head.key.last), "simp")
    assertBottom(pfBare, bare.head.value, "bare [simp]")
  }

  test("WI-154: multiple flags `[simp, unfold, hint]` all parse as bare entries") {
    val (pf, entries) = ruleMeta("rule ?a + zero = ?a [simp, unfold, hint]")
    assertEquals(entries.length, 3)
    val keys = entries.map(e => pf.symbols.name(e.key.last)).toSet
    assertEquals(keys, Set("simp", "unfold", "hint"))
    for e <- entries do
      assertBottom(pf, e.value, s"bare flag ${pf.symbols.name(e.key.last)}")
  }

  test("WI-154: mixed bare and keyed entries `[simp, agent: \"x\"]`") {
    val (pf, entries) = ruleMeta("""rule ?a + zero = ?a [simp, agent: "x"]""")
    assertEquals(entries.length, 2)
    val keys = entries.map(e => pf.symbols.name(e.key.last))
    assertEquals(keys, IndexedSeq("simp", "agent"))
    assertBottom(pf, entries(0).value, "bare simp")
    pf.terms.get(entries(1).value) match
      case Term.Const(Literal.StringLit("x")) => ()
      case other => fail(s"expected StringLit(\"x\") for agent, got $other")
  }

  // ── WI-162: parser features unblocking the full stdlib chain ────

  private def probeOk(name: String, src: String): Unit =
    Parser.parse(src, name) match
      case Right(_) => ()
      case Left(es) => fail(s"$name parse failed: ${es.map(_.message).mkString("; ")}")

  private val stdlibDir = sys.env.getOrElse("ANTHILL_STDLIB",
    System.getProperty("user.dir") + "/../stdlib")

  private def probeStdlibOk(relPath: String): Unit =
    val src = scala.io.Source.fromFile(s"$stdlibDir/$relPath")
    val text = try src.mkString finally src.close()
    probeOk(relPath, text)

  test("WI-162: nested function calls (e.g. not(not(?a)))") {
    // Pre-fix the inner paren-expr backtrack failed under `~/` cut.
    probeOk("nested-not", "rule p: not(not(?a)) = ?a")
    probeOk("paren-arg",  "fact not((?a))")
    probeOk("paren-only", "fact (?a)")
  }

  test("WI-162: bare `effects` clause on operation declaration") {
    probeOk("effects-bare",
      """sort Demo
        |  sort Effect = ?
        |  operation foo() -> Int
        |    effects Effect
        |end""".stripMargin)
  }

  test("WI-162: var-as-functor call `?P(?lo)` (HO predicate application)") {
    probeOk("var-call",
      """sort Demo
        |  rule induction(?P, ?lo) :- ?P(?lo)
        |end""".stripMargin)
  }

  test("WI-162: empty set literal `{}` in fact binding") {
    probeOk("empty-set-binding",
      """sort Demo
        |  fact Foo[Effect = {}]
        |end""".stripMargin)
  }

  test("WI-162: nested implication body `(t1, … -: u1, …)` (induction principle)") {
    probeOk("nested-impl-forall",
      """sort Demo
        |  rule induction(?P, ?lo, ?hi)
        |    :- ?P(?lo),
        |       (forall(?n),
        |          gte(?n, ?lo), lt(?n, ?hi), ?P(?n)
        |          -: ?P(add(?n, 1)))
        |end""".stripMargin)
  }

  test("WI-162: doc-comment block `{< … >}` (used by stdlib sort.anthill)") {
    probeOk("doc-comment",
      """{< this is a doc comment
         |   spanning multiple lines >}
         |sort Demo end""".stripMargin)
  }

  test("WI-162: each of the 6 stdlib files previously blocked now parses") {
    Seq(
      "anthill/prelude/bool.anthill",
      "anthill/prelude/int.anthill",
      "anthill/prelude/iteration.anthill",
      "anthill/prelude/collection.anthill",
      "anthill/prelude/list.anthill",
      "anthill/reflect/reflect.anthill",
    ).foreach(probeStdlibOk)
  }

  test("WI-166: match expression without trailing `end` (indentation-delimited)") {
    probeOk("match-no-end",
      """sort Demo
        |  operation single(x: Foo) -> Int =
        |    match x
        |      case Foo(a, _) -> a
        |  operation next() -> Int = 0
        |end""".stripMargin)
  }

  test("WI-166: cli/help.anthill (single-arm match-no-end) parses cleanly") {
    probeStdlibOk("anthill/cli/help.anthill")
  }

  test("WI-167: cli/parse.anthill (nested matches without `end`) parses cleanly") {
    probeStdlibOk("anthill/cli/parse.anthill")
  }

  // ── Arrow type effect annotations (mirrors rustland 9615010) ────

  /** Pull the arrow type out of `operation run(f: <arrow>) -> B`. */
  private def parseArrowParam(src: String): TypeExpr.Arrow =
    val full =
      s"""sort Demo
         |  sort A = ?
         |  sort B = ?
         |  sort Modifies = ?
         |  sort Reads = ?
         |  operation run(f: $src) -> B
         |end""".stripMargin
    val pf = Parser.parse(full, "<arrow>").toOption.get
    val ops = pf.items.collect { case Item.SortWithBodyItem(s) => s }
      .head.items.collect { case Item.OperationItem(o) => o }
    val arrow = ops.head.params.head.ty
    arrow match
      case a: TypeExpr.Arrow => a
      case other => fail(s"expected Arrow, got $other")

  test("arrow type without effects: `(A) -> B` has empty effects") {
    val a = parseArrowParam("(A) -> B")
    assertEquals(a.effects.length, 0)
  }

  test("arrow type single effect: `(A) -> B @ Modifies`") {
    val a = parseArrowParam("(A) -> B @ Modifies")
    assertEquals(a.effects.length, 1)
  }

  test("arrow type effect set: `(A) -> B @ {Modifies, Reads}`") {
    val a = parseArrowParam("(A) -> B @ {Modifies, Reads}")
    assertEquals(a.effects.length, 2)
  }

  /** Helper for negative cases — parser must reject the source. */
  private def parseRejected(src: String, label: String): Unit =
    val full =
      s"""sort Demo
         |  sort A = ?
         |  sort B = ?
         |  sort Modifies = ?
         |  operation run(f: $src) -> B
         |end""".stripMargin
    Parser.parse(full, "<arrow>") match
      case Right(_) => fail(s"expected parse failure for $label")
      case Left(_) => ()

  test("arrow type empty braced effect set `@ {}` is rejected") {
    parseRejected("(A) -> B @ {}", "empty braced effect set")
  }

  test("arrow type trailing comma `@ {Modifies,}` is rejected") {
    parseRejected("(A) -> B @ {Modifies,}", "trailing comma in effect set")
  }

  // ── WI-092: effect-set tightened to `_effect_type` ─────────────

  /** Wrap an `effects <clause>` operation in a `Demo` sort body. */
  private def parseEffects(clause: String): Boolean =
    val full =
      s"""sort Demo
         |  sort A = ?
         |  sort B = ?
         |  sort Modifies = ?
         |  sort Reads = ?
         |  operation foo() -> Int
         |    effects $clause
         |end""".stripMargin
    Parser.parse(full, "<effects>").isRight

  test("WI-092: single effect type `Modifies` parses") {
    assert(parseEffects("Modifies"))
  }

  test("WI-092: variable effect `?E` parses") {
    assert(parseEffects("?E"))
  }

  test("WI-092: braced effect set `{Modifies, Reads}` parses") {
    assert(parseEffects("{Modifies, Reads}"))
  }

  test("WI-092: tuple effect `(A, B)` is rejected (not an `_effect_type`)") {
    assert(!parseEffects("(A, B)"))
  }

  test("WI-092: arrow type inside a braced effect set is rejected") {
    assert(!parseEffects("{(A) -> B}"))
  }

  // ── WI-185: let-binding type annotation ────────────────────────

  /** Extract the single operation declared in a `Demo` sort body. */
  private def parseDemoOp(opSrc: String): (ParsedFile, Operation) =
    val full =
      s"""sort Demo
         |  sort T = ?
         |  sort Int = ?
         |  sort Term = ?
         |  sort Map = ?
         |  sort String = ?
         |$opSrc
         |end""".stripMargin
    val pf = Parser.parse(full, "<op>").toOption
      .getOrElse(fail(s"parse failed: $opSrc"))
    val op = pf.items.collect { case Item.SortWithBodyItem(s) => s }
      .head.items.collect { case Item.OperationItem(o) => o }.head
    (pf, op)

  /** Named-arg keys of a `Fn` term, by interned name. */
  private def namedKeys(pf: ParsedFile, tid: TermId): Set[String] =
    pf.terms.get(tid) match
      case fn: Term.Fn => fn.namedArgs.map((k, _) => pf.symbols.name(k)).toSet
      case other => fail(s"expected Fn, got $other")

  test("WI-185: `let x : T = …` carries a `type_name` named arg") {
    val (pf, op) = parseDemoOp(
      "  operation f() -> Int =\n    let x : T = 1 in x")
    val body = op.body.getOrElse(fail("operation has no body"))
    pf.terms.get(body) match
      case fn: Term.Fn =>
        assertEquals(pf.symbols.name(fn.functor), "let_expr")
        assertEquals(fn.posArgs.length, 3)
        assert(namedKeys(pf, body).contains("type_name"),
          s"expected type_name named arg, got ${namedKeys(pf, body)}")
      case other => fail(s"expected let_expr Fn, got $other")
  }

  test("WI-185: bare `let x = …` has no `type_name` named arg") {
    val (pf, op) = parseDemoOp(
      "  operation f() -> Int =\n    let x = 1 in x")
    val body = op.body.getOrElse(fail("operation has no body"))
    assert(!namedKeys(pf, body).contains("type_name"))
  }

  // ── WI-269 Phase A: operation type parameters ──────────────────

  test("WI-269: operation type param `[E]` is captured, no default") {
    val (pf, op) = parseDemoOp("  operation g[E](t: Term) -> Int")
    assertEquals(op.typeParams.length, 1)
    assertEquals(pf.symbols.name(op.typeParams.head.name), "E")
    assertEquals(op.typeParams.head.default, None)
  }

  test("WI-269: type params with default `[A, B = Int]`") {
    val (pf, op) = parseDemoOp("  operation g[A, B = Int](t: Term) -> Int")
    assertEquals(op.typeParams.map(tp => pf.symbols.name(tp.name)),
      IndexedSeq("A", "B"))
    assertEquals(op.typeParams(0).default, None)
    op.typeParams(1).default match
      case Some(TypeExpr.Simple(n)) => assertEquals(pf.symbols.name(n.last), "Int")
      case other => fail(s"expected default Simple(Int), got $other")
  }

  test("WI-269: no type-param list ⇒ empty typeParams") {
    val (_, op) = parseDemoOp("  operation g(t: Term) -> Int")
    assertEquals(op.typeParams.length, 0)
  }

  test("WI-269: instantiation callee `Map[K = String](x)` carries `type_args`") {
    val (pf, op) = parseDemoOp(
      "  operation f() -> Int =\n    Map[K = String](x)")
    val body = op.body.getOrElse(fail("operation has no body"))
    pf.terms.get(body) match
      case fn: Term.Fn =>
        assertEquals(pf.symbols.name(fn.functor), "Map")
        assert(namedKeys(pf, body).contains("type_args"),
          s"expected type_args named arg, got ${namedKeys(pf, body)}")
      case other => fail(s"expected call Fn, got $other")
  }

  // ── WI-288: typeExprToRef lowers arrow / tuple types ───────────

  /** Value term of a `Fn`'s named arg, by interned name. */
  private def namedArg(pf: ParsedFile, tid: TermId, key: String): TermId =
    pf.terms.get(tid) match
      case fn: Term.Fn =>
        fn.namedArgs.collectFirst { case (k, v) if pf.symbols.name(k) == key => v }
          .getOrElse(fail(s"no named arg `$key` on $tid"))
      case other => fail(s"expected Fn, got $other")

  /** Functor name of a `Fn` term. */
  private def functorName(pf: ParsedFile, tid: TermId): String =
    pf.terms.get(tid) match
      case fn: Term.Fn => pf.symbols.name(fn.functor)
      case other => fail(s"expected Fn, got $other")

  test("WI-288/WI-361: arrow type `(T) -> Int` lowers to `TypeExtractor.Arrow`") {
    val (pf, op) = parseDemoOp(
      "  operation f() -> Int =\n    let x : (T) -> Int = 1 in x")
    val tn = namedArg(pf, op.body.getOrElse(fail("no body")), "type_name")
    assertEquals(functorName(pf, tn), "anthill.prelude.TypeExtractor.Arrow")
  }

  test("WI-288/WI-361: named tuple `(a: T, b: Int)` lowers to `TypeExtractor.NamedTuple`") {
    val (pf, op) = parseDemoOp(
      "  operation f() -> Int =\n    let x : (a: T, b: Int) = 1 in x")
    val tn = namedArg(pf, op.body.getOrElse(fail("no body")), "type_name")
    assertEquals(functorName(pf, tn), "anthill.prelude.TypeExtractor.NamedTuple")
  }

  test("WI-288/WI-361: positional tuple `(T, Int)` lowers to `TypeExtractor.NamedTuple`") {
    val (pf, op) = parseDemoOp(
      "  operation f() -> Int =\n    let x : (T, Int) = 1 in x")
    val tn = namedArg(pf, op.body.getOrElse(fail("no body")), "type_name")
    assertEquals(functorName(pf, tn), "anthill.prelude.TypeExtractor.NamedTuple")
  }

  /** Walks the entire stdlib tree and asserts every .anthill file parses.
    * Locks in the WI-162/166/167 parser-coverage achievement: as new
    * stdlib modules are added, this test catches a parser regression
    * before it bites a downstream consumer.
    */
  test("scaland parser covers the whole stdlib (every .anthill file parses)") {
    import java.nio.file.{Files, Paths}
    import scala.jdk.CollectionConverters.*
    val root = Paths.get(stdlibDir)
    val files = Files.walk(root).iterator.asScala.toList
      .filter(_.toString.endsWith(".anthill"))
    val failures = files.flatMap { p =>
      val rel = root.relativize(p).toString
      val src = scala.io.Source.fromFile(p.toFile)
      val text = try src.mkString finally src.close()
      Parser.parse(text, rel) match
        case Right(_) => None
        case Left(es) => Some(s"$rel: ${es.head.message}")
    }
    assert(failures.isEmpty, s"stdlib files failing to parse:\n  ${failures.mkString("\n  ")}")
  }
