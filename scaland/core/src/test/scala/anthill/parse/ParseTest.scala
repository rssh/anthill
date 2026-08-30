package anthill.parse

import anthill.intern.{TermSymbol, SymbolTable}
import anthill.term.{Term, TermId, Literal}
import anthill.span.Span

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
      IndexedSeq((plus, Span.empty), (plus, Span.empty)),
      st.name,
      terms.allocAt,
      st.intern
    )

    // Result should be add(add(1, 2), 3)
    terms.get(result) match
      case fn: Term.Fn =>
        assertEquals(st.name(fn.functor), Pratt.addFunctor)
        assertEquals(fn.posArgs.length, 2)
        // Left child should be add(1, 2)
        terms.get(fn.posArgs(0)) match
          case inner: Term.Fn =>
            assertEquals(st.name(inner.functor), Pratt.addFunctor)
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
      IndexedSeq((pow, Span.empty), (pow, Span.empty)),
      st.name,
      terms.allocAt,
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
      IndexedSeq((plus, Span.empty), (times, Span.empty)),
      st.name,
      terms.allocAt,
      st.intern
    )

    terms.get(result) match
      case fn: Term.Fn =>
        assertEquals(st.name(fn.functor), Pratt.addFunctor)
        // Left should be 1
        terms.get(fn.posArgs(0)) match
          case Term.Const(Literal.IntLit(1)) => // ok
          case other => fail(s"expected Const(1), got $other")
        // Right should be mul(2, 3)
        terms.get(fn.posArgs(1)) match
          case inner: Term.Fn =>
            assertEquals(st.name(inner.functor), Pratt.mulFunctor)
          case other => fail(s"expected Fn, got $other")
      case other => fail(s"expected Fn, got $other")
  }

  test("Pratt parser - single operand") {
    val st = SymbolTable()
    val terms = SimpleTermStore()
    val v = terms.alloc(Term.Const(Literal.IntLit(42)))
    val result = Pratt.desugar(IndexedSeq(v), IndexedSeq.empty, st.name, terms.allocAt, st.intern)
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
      "anthill/prelude/int64.anthill",
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

  // ── WI-451: enclosing-list sort type-param binders (§5.4) ──────

  test("WI-451: `sort CpsMonad[F[T], A]` desugars into marked HK carrier + simple param") {
    val pf = Parser.parse(
      """sort CpsMonad[F[T], A]
        |  operation unit(x: A) -> F
        |end""".stripMargin, "<wi451>").toOption
      .getOrElse(fail("parse failed"))
    val st = pf.symbols
    val cps = pf.items.collect { case Item.SortWithBodyItem(s) => s }.head

    // Higher-kinded `F[T]` → a `SortWithBody` MARKED `isTypeParam`, whose body is
    // the recursively-desugared member `T` (an AbstractSort with a `?` definition).
    val fParam = cps.items.collect {
      case Item.SortWithBodyItem(s) if st.name(s.name.last) == "F" => s
    }.head
    assert(fParam.isTypeParam, "F must be marked is_type_param")
    val tMember = fParam.items.collect { case Item.AbstractSortItem(a) => a }.head
    assertEquals(st.name(tMember.name.last), "T")
    assert(tMember.definition.isInstanceOf[TypeExpr.Variable],
      s"T must desugar to a `?` variable, got ${tMember.definition}")

    // Simple param `A` → `sort A = ?` (an AbstractSort with a fresh `?`).
    val aParam = cps.items.collect {
      case Item.AbstractSortItem(a) if st.name(a.name.last) == "A" => a
    }.head
    assert(aParam.definition.isInstanceOf[TypeExpr.Variable],
      s"A must desugar to a `?` variable, got ${aParam.definition}")

    // Params are PREPENDED before the members that reference them.
    val firstOpIdx = cps.items.indexWhere(_.isInstanceOf[Item.OperationItem])
    val fIdx = cps.items.indexWhere {
      case Item.SortWithBodyItem(s) => st.name(s.name.last) == "F"
      case _ => false
    }
    assert(fIdx < firstOpIdx, "type params must precede the operation members")
  }

  test("WI-451: a plain nested `sort F { … }` stays UNMARKED (concrete nested sort)") {
    val pf = Parser.parse(
      """sort Outer
        |  sort F
        |    sort T = ?
        |  end
        |end""".stripMargin, "<wi451-unmarked>").toOption
      .getOrElse(fail("parse failed"))
    val st = pf.symbols
    val outer = pf.items.collect { case Item.SortWithBodyItem(s) => s }.head
    val f = outer.items.collect {
      case Item.SortWithBodyItem(s) if st.name(s.name.last) == "F" => s
    }.head
    assert(!f.isTypeParam, "an unmarked `sort F { … }` must NOT be a type param")
  }

  test("WI-451: a type-param list with no body (`sort X[A] = T`) is a loud parse error") {
    Parser.parse("sort Bad[A] = Int64", "<wi451-reject>") match
      case Right(_) => fail("expected parse failure for `sort X[A] = T`")
      case Left(_)  => ()
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

  test("arrow type empty braced effect set `@ {}` parses as the closed-empty row (WI-440)") {
    // WI-440: `@ {}` / `effects {}` is the explicit pure / closed-empty row
    // (`commaSep`, not `commaSep1`). Previously rejected; now an empty effect set.
    val a = parseArrowParam("(A) -> B @ {}")
    assertEquals(a.effects.length, 0)
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

  // WI-087: operation attributes via a `meta [...]` clause (re-ported from the
  // retired wi068 branch — unblocks the C++ mapping codegen, which reads op meta).
  test("WI-087: operation `meta [...]` clause is captured in Operation.meta") {
    val (pf, op) = parseDemoOp("""  operation get() -> T meta [inline, CppName: "get_t"]""")
    val keys = op.meta.map(_.entries).getOrElse(IndexedSeq.empty)
      .map(e => pf.symbols.name(e.key.last)).toSet
    assertEquals(keys, Set("inline", "CppName"))
  }

  test("WI-087: `meta [...]` composes with an effects clause") {
    probeOk("op-meta-effects",
      """sort Demo
        |  sort Modifies = ?
        |  operation put(x: T) -> T
        |    effects Modifies
        |    meta [host: "rust"]
        |end""".stripMargin)
  }


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

  test("WI-269: operation type param `[E]` is captured") {
    val (pf, op) = parseDemoOp("  operation g[E](t: Term) -> Int")
    assertEquals(op.typeParams.length, 1)
    assertEquals(pf.symbols.name(op.typeParams.head.name), "E")
  }

  // WI-850: a type-param DEFAULT is REFUSED, not stored. It still PARSES — that is
  // what lets the message name the operation and the parameter instead of failing as
  // an unexpected `=`. (This test used to assert the default was captured; nothing
  // ever read it, and the loader minted a fresh var from the NAME alone.)
  test("WI-850: an operation type-param default `[B = Int]` is refused, naming both") {
    val src =
      """sort Demo
        |  sort Int = ?
        |  sort Term = ?
        |  operation g[A, B = Int](t: Term) -> Int
        |end""".stripMargin
    Parser.parse(src, "<op>") match
      case Right(_) => fail("expected a refusal for the type-param default")
      case Left(errs) =>
        assertEquals(errs.length, 1, s"one error, got: ${errs.map(_.message)}")
        val m = errs.head.message
        assert(m.contains("operation `g`"), m)
        assert(m.contains("type parameter `B`"), m)
        assert(m.contains("`B = Int`"), m)
  }

  test("WI-850: a bare type-param list carries no refusal") {
    val (pf, op) = parseDemoOp("  operation g[A, B](t: Term) -> Int")
    assertEquals(op.typeParams.map(tp => pf.symbols.name(tp.name)), IndexedSeq("A", "B"))
  }

  // ── WI-950: a refusal belongs to the production that recorded it ─────────
  //   Three productions refuse from inside a fastparse `.map` — the WI-639
  //   projection-label checks, the braced-`operation`-block visibility refusal,
  //   and the WI-850 type-param default. A `.map` runs when ITS production
  //   succeeds, which is not the same as the enclosing parse accepting that
  //   text, so a shared error buffer kept the refusal across the backtrack.
  //   WHAT EACH TEST HOLDS DOWN — the three `assertOnlyParseFailure` tests and
  //   `drops interior comments and newlines` fail on the pre-WI-950 parser (two
  //   errors instead of one, and a message carrying the author's comment). The
  //   rest are controls that pass on the pre-WI-950 parser and fail on a WRONG
  //   fix, which is what makes them worth keeping: `still surfaces` catches
  //   scoping that truncates refusals the parse accepted; `survives a later
  //   syntax error` catches scoping the TOP production, which discards refusals
  //   about declarations that parsed; and the `-`-bearing identifier catches
  //   normalising a `.!` source capture instead of rendering the tree, since an
  //   anthill identifier may contain `-`.

  private def assertOnlyParseFailure(label: String, src: String): Unit =
    Parser.parse(src, "<wi950>") match
      case Right(_) => fail(s"$label: expected the parse to fail")
      case Left(errs) =>
        assertEquals(errs.length, 1,
          s"$label: expected only the parse failure, got: ${errs.map(_.message).mkString("; ")}")
        assert(errs.head.message.startsWith("parse error: "),
          s"$label: expected the parse failure, got: ${errs.head.message}")

  test("WI-950: a discarded type-param-default refusal does not survive the parse") {
    // The entry parses (recording the WI-850 refusal), then the closing `}` fails
    // under the `~/` cut and the whole declaration is discarded with it.
    assertOnlyParseFailure("braced block",
      """sort Demo
        |  sort A = ?
        |  sort B = ?
        |  operation { g[T = Int](x: A) -> B  <garbage> }
        |end""".stripMargin)
    assertOnlyParseFailure("single operation",
      """sort Demo
        |  sort A = ?
        |  sort B = ?
        |  operation g[T = Int](x: A) -> B <garbage>
        |end""".stripMargin)
  }

  test("WI-950: a discarded projection refusal does not survive the parse") {
    // The projection parses inside the literal (recording the duplicate-key
    // refusal); the unterminated literal then discards the term it was built for.
    assertOnlyParseFailure("unclosed set literal", "fact p({?y.(a, a))")
    assertOnlyParseFailure("unclosed list literal", "fact p([?y.(a, a), 1)")
  }

  test("WI-950: a discarded visibility refusal does not survive the parse") {
    // The `operation` declaration parses (recording the refusal), then the sort
    // body's missing `end` discards the declaration.
    assertOnlyParseFailure("unterminated sort body",
      """sort Demo
        |  sort A = ?
        |  internal operation { g(x: A) -> A }""".stripMargin)
  }

  test("WI-950: a refusal the parse DID accept still surfaces") {
    for (label, src) <- Seq(
      "type-param default" ->
        """sort Demo
          |  sort A = ?
          |  sort B = ?
          |  operation g[T = Int](x: A) -> B
          |end""".stripMargin,
      "projection" -> "fact p({?y.(a, a)})",
      "block visibility" ->
        """sort Demo
          |  sort A = ?
          |  internal operation { g(x: A) -> A }
          |end""".stripMargin,
    ) do
      Parser.parse(src, "<wi950>") match
        case Right(_) => fail(s"$label: expected a refusal")
        case Left(errs) =>
          assertEquals(errs.length, 1,
            s"$label: expected exactly the refusal, got: ${errs.map(_.message).mkString("; ")}")
          assert(!errs.head.message.startsWith("parse error: "),
            s"$label: expected the refusal, got: ${errs.head.message}")
  }

  test("WI-950: a refusal about an ACCEPTED declaration survives a later syntax error") {
    // `sourceFile` deliberately does not scope: the operation below parses, so its
    // refusal is live even though the file as a whole does not. Scoping the top
    // production (the shape the first cut of WI-950 shipped) reports ONLY the
    // syntax error here, and the author learns about the default one run later.
    val src =
      """sort Demo
        |  sort A = ?
        |  sort B = ?
        |  operation g[T = A](x: A) -> B
        |end
        |fact p(""".stripMargin
    Parser.parse(src, "<wi950>") match
      case Right(_) => fail("expected the parse to fail")
      case Left(errs) =>
        val msgs = errs.map(_.message)
        assert(msgs.exists(_.contains("type parameter `T` carries a default")),
          s"the accepted declaration's refusal must survive; got: ${msgs.mkString("; ")}")
        assert(msgs.exists(_.startsWith("parse error: ")),
          s"the syntax error must be reported too; got: ${msgs.mkString("; ")}")
  }

  // WI-950: the refusal quotes the default back to the author, and it renders the
  // parsed `TypeExpr` to do it. A `.!` source capture spans whatever trivia was
  // written inside the type, and normalising THAT needs the whole token model — not
  // just the comment forms. `renderTypeExpr` has no lexer to keep in sync.

  private def assertQuotedDefault(src: String, expected: String): Unit =
    Parser.parse(src, "<wi950>") match
      case Right(_) => fail("expected a refusal for the type-param default")
      case Left(errs) =>
        assertEquals(errs.length, 1, errs.map(_.message).mkString("; "))
        val m = errs.head.message
        assert(m.contains(s"`T = $expected`"), s"expected `T = $expected`; got: $m")
        assert(!m.contains("\n"), m)

  test("WI-950: the quoted type-param default drops interior comments and newlines") {
    assertQuotedDefault(
      """sort Demo
        |  sort A = ?
        |  sort B = ?
        |  sort List = ?
        |  operation g[T = List[ {- note -} Int
        |        ]](x: A) -> B
        |end""".stripMargin,
      "List[Int]")
  }

  test("WI-950: a `-`-bearing identifier in the quoted default is not truncated") {
    // An anthill identifier may contain `-` (`Tokens.identToken`), so `my--type` is
    // ONE token whose `--` is not a line comment. Anything that re-lexes a source
    // capture to strip trivia truncates this to `my` and then RECOMMENDS the
    // truncation — quoting a type the author never wrote.
    assertQuotedDefault(
      """sort Demo
        |  sort A = ?
        |  sort B = ?
        |  sort my--type = ?
        |  operation g[T = my--type](x: A) -> B
        |end""".stripMargin,
      "my--type")
  }

  test("WI-950: a string literal in the quoted default keeps its contents and quotes") {
    // `"a -- b"` is a string, not a line comment; the literal is re-encoded from the
    // parsed `StringLit`, so the quoted default is source the author could paste back.
    assertQuotedDefault(
      """sort Demo
        |  sort A = ?
        |  sort B = ?
        |  sort Tagged = ?
        |  operation g[T = Tagged["a -- b"]](x: A) -> B
        |end""".stripMargin,
      """Tagged["a -- b"]""")
  }

  test("WI-950: a value-in-type and a named binding render in the quoted default") {
    assertQuotedDefault(
      """sort Demo
        |  sort A = ?
        |  sort B = ?
        |  sort Vector = ?
        |  sort Int64 = ?
        |  operation g[T = Vector[E = Int64, 3]](x: A) -> B
        |end""".stripMargin,
      "Vector[E = Int64, 3]")
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

  /** Short (last `.`-segment) functor name of a `Fn` term — mirrors rustland's
    * `resolve_sym`, since parse-time symbols keep their full interned string. */
  private def shortFunctor(pf: ParsedFile, tid: TermId): String =
    val n = functorName(pf, tid)
    val i = n.lastIndexOf('.')
    if i >= 0 then n.substring(i + 1) else n

  test("WI-288/WI-361: arrow type `(T) -> Int` lowers to `TypeExtractor.Arrow`") {
    val (pf, op) = parseDemoOp(
      "  operation f() -> Int =\n    let x : (T) -> Int = 1 in x")
    val tn = namedArg(pf, op.body.getOrElse(fail("no body")), "type_name")
    assertEquals(functorName(pf, tn), "anthill.prelude.TypeExtractor.Arrow")
  }

  test("WI-340: arrow effects lower to a canonical `effects_rows(EffectExpression)` row") {
    // Effects written in REVERSE alphabetical order to prove the canonical sort
    // reorders them `Modifies` before `Reads` (mirrors rustland's
    // load_arrow_type_with_effect_set_canonical_row). scaland has no typer, so
    // the undeclared effect bases parse purely syntactically.
    val (pf, op) = parseDemoOp(
      "  operation f() -> Int =\n    let x : (A) -> B @ {Reads[host], Modifies[host]} = 1 in x")
    val arrow = namedArg(pf, op.body.getOrElse(fail("no body")), "type_name")
    assertEquals(shortFunctor(pf, arrow), "Arrow")

    // The `effects` field is the `effects_rows` wrapper, NOT a prelude cons-list.
    val effectsField = namedArg(pf, arrow, "effects")
    assertEquals(shortFunctor(pf, effectsField), "EffectsRows")

    // Walk the right-folded `merge(present(l), merge(…, empty_row))` chain,
    // collecting the present-label types in order.
    def collect(node: TermId): List[TermId] =
      shortFunctor(pf, node) match
        case "empty_row" => Nil
        case "present"   => List(namedArg(pf, node, "label"))
        case "merge" =>
          val left = namedArg(pf, node, "left")
          val here =
            if shortFunctor(pf, left) == "present" then List(namedArg(pf, left, "label")) else Nil
          here ++ collect(namedArg(pf, node, "right"))
        case other => fail(s"unexpected EffectExpression head `$other`")
    val labels = collect(namedArg(pf, effectsField, "effects_expr"))
    assertEquals(labels.length, 2, "row should carry two present labels")

    // Each label is the parameterized effect `Fn{Modifies/Reads, …}`; the
    // canonical sort put them in alphabetical order regardless of source order.
    assertEquals(labels.map(l => shortFunctor(pf, l)), List("Modifies", "Reads"))
  }

  test("WI-340: canonical row keeps distinct same-base effects but collapses true duplicates") {
    // rustland de-duplicates by hash-consed TermId, so structurally-distinct
    // atoms all survive; scaland must match that with a fully-structural key,
    // not a lossy display name that would collapse same-base parameterized
    // effects (whose bindings ride as POSITIONAL args) into one.
    def presentLabels(effectSrc: String): List[TermId] =
      val (pf, op) = parseDemoOp(
        s"  operation f() -> Int =\n    let x : (A) -> B @ {$effectSrc} = 1 in x")
      val effectsField =
        namedArg(pf, namedArg(pf, op.body.getOrElse(fail("no body")), "type_name"), "effects")
      def collect(node: TermId): List[TermId] =
        shortFunctor(pf, node) match
          case "empty_row" => Nil
          case "present"   => List(namedArg(pf, node, "label"))
          case "merge" =>
            val left = namedArg(pf, node, "left")
            val here =
              if shortFunctor(pf, left) == "present" then List(namedArg(pf, left, "label")) else Nil
            here ++ collect(namedArg(pf, node, "right"))
          case other => fail(s"unexpected EffectExpression head `$other`")
      collect(namedArg(pf, effectsField, "effects_expr"))

    // Distinct same-base parameterized effects must BOTH survive the dedup.
    assertEquals(presentLabels("Modify[a], Modify[b]").length, 2,
      "structurally-distinct `Modify[a]`/`Modify[b]` must both survive")
    // A literal duplicate effect collapses to a single atom.
    assertEquals(presentLabels("Reads, Reads").length, 1,
      "a literal duplicate effect collapses to one atom")
  }

  test("WI-562: a plain-term op body after an `=`-ending ensures clause is captured, not swallowed") {
    // `ensures result = mul(2, x)` ends in `=`; the trailing `= mul(2, x)` is the
    // operation BODY, not a chained equality (equality is non-associative). The
    // clause keeps the single `result = mul(2, x)` eq goal and the body survives.
    val (pf, op) = parseDemoOp(
      "  operation double(x: Int) -> Int\n    ensures result = mul(2, x) = mul(2, x)")
    assert(op.body.isDefined,
      "plain-term operation body must not be swallowed into the ensures clause")
    assertEquals(op.ensures.length, 1, "exactly one ensures clause")
    assertEquals(op.ensures.head.length, 1, "the clause holds one (binary) eq goal, not a chained one")
    // The `=` is MINTED, so it carries its address; the body `mul(2, x)` is WRITTEN, so
    // it is an ordinary short name. WI-20260825-KD9SW: same shape, two functors.
    assertEquals(functorName(pf, op.ensures.head.head), Pratt.eqFunctor)
    assertEquals(functorName(pf, op.body.get), "mul")
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

  // ── Parser parity with current rust grammar (2026-06-26 resync) ─────

  // WI-084: term-level named constants.
  test("WI-084: bodyless `const NAME : T` parses + defines a Const item") {
    val pf = Parser.parse(
      """sort Demo
        |  sort Float = ?
        |  const infinity: Float
        |end""".stripMargin, "<const>").toOption.getOrElse(fail("parse failed"))
    val c = pf.items.collect { case Item.SortWithBodyItem(s) => s }.head
      .items.collectFirst { case Item.ConstItem(c) => c }.getOrElse(fail("no const"))
    assertEquals(pf.symbols.name(c.name.last), "infinity")
    assert(c.value.isEmpty, "bodyless const must have no value")
  }

  test("WI-084: `const NAME : T = expr` captures the body") {
    val pf = Parser.parse(
      """sort Demo
        |  sort Float = ?
        |  const tau: Float = mul(2.0, pi)
        |end""".stripMargin, "<const2>").toOption.getOrElse(fail("parse failed"))
    val c = pf.items.collect { case Item.SortWithBodyItem(s) => s }.head
      .items.collectFirst { case Item.ConstItem(c) => c }.getOrElse(fail("no const"))
    assert(c.value.isDefined, "const with `= expr` must carry a value")
  }

  // WI-478: guarded effect-row elements `E :- guard`.
  test("WI-478: braced guarded effect `{ Error[X] :- eq(b, 0) }` parses") {
    assert(parseEffects("{ Error[X] :- eq(b, 0) }"), "braced guarded effect should parse")
  }

  test("WI-478: single bare guarded effect `Error[X] :- isEmpty(s)` parses") {
    assert(parseEffects("Error[X] :- isEmpty(s)"), "bare guarded effect should parse")
  }

  test("WI-478: parenthesized conjunctive guard `( E :- p, q )` parses") {
    assert(parseEffects("{ ( Error[X] :- p(a), q(b) ) }"), "paren guarded effect should parse")
  }

  test("WI-478: a guarded effect lowers to a `guarded(label, guards)` term") {
    val (pf, op) = parseDemoOp("  operation f() -> Int\n    effects { Error :- eq(b, 0) }")
    val eff = op.effects.head.typeExpr
    eff match
      case TypeExpr.EffectGuarded(_, guard) => assertEquals(guard.length, 1)
      case other => fail(s"expected EffectGuarded, got $other")
  }

  // WI-522: `<=>` unify operator + goal-position `let`.
  test("WI-522: `<=>` in a rule head lowers to the `unify` functor") {
    val pf = Parser.parse("rule neg(?a) <=> sub(0.0, ?a)", "<unify>").toOption
      .getOrElse(fail("parse failed"))
    val rule = pf.items.collectFirst { case Item.RuleItem(r) => r }.getOrElse(fail("no rule"))
    val head = rule.heads.collectFirst { case RuleHead.TermHead(t) => t }.getOrElse(fail("no head"))
    assertEquals(functorName(pf, head), "unify")
  }

  test("WI-522: goal-position `let ?v = expr` lowers to a `unify` goal") {
    val pf = Parser.parse("rule p(?x) :- let ?y = f(?x), q(?y)", "<letgoal>").toOption
      .getOrElse(fail("parse failed"))
    val body = pf.items.collectFirst { case Item.RuleItem(r) => r }.flatMap(_.body)
      .getOrElse(fail("no body"))
    assertEquals(functorName(pf, body(0)), "unify")
  }

  // WI-615 / proposal 051: `===` structural identity test lowers to `struct_eq`.
  test("WI-615: `===` in a rule body lowers to the `struct_eq` functor") {
    val pf = Parser.parse("rule same(?x, ?y) :- ?x === ?y", "<structeq>").toOption
      .getOrElse(fail("parse failed"))
    val body = pf.items.collectFirst { case Item.RuleItem(r) => r }.flatMap(_.body)
      .getOrElse(fail("no body"))
    assertEquals(functorName(pf, body(0)), "struct_eq")
  }

  // WI-568: the cut control primitive `!`.
  test("WI-568: a bare `!` rule-body goal lowers to `cut()` (not prefix negation)") {
    val pf = Parser.parse("rule p(?x) :- q(?x), !, r(?x)", "<cut>").toOption
      .getOrElse(fail("parse failed"))
    val body = pf.items.collectFirst { case Item.RuleItem(r) => r }.flatMap(_.body)
      .getOrElse(fail("no body"))
    assertEquals(body.length, 3)
    assertEquals(functorName(pf, body(1)), "cut")
  }

  // WI-20260825-P9Y67: the functor is the ADDRESS now, mirroring rustland — `!` names
  // `..anthill.kernel.not` outright so no declaration in scope can capture it. The SHAPE
  // is what WI-568 is about and it is unchanged; only the spelling of the head moved.
  test("WI-568: `! atom` stays prefix negation `not(atom)`") {
    val pf = Parser.parse("rule p(?x) :- ! q(?x)", "<not>").toOption
      .getOrElse(fail("parse failed"))
    val body = pf.items.collectFirst { case Item.RuleItem(r) => r }.flatMap(_.body)
      .getOrElse(fail("no body"))
    assertEquals(functorName(pf, body(0)), Pratt.notFunctor)
  }

  // WI-027: bounded quantification `(forall/some ?x in xs: body)`.
  test("WI-027: `(forall ?x in xs: P(?x))` lowers to `forall_in`") {
    val pf = Parser.parse("rule allp(?xs) :- (forall ?x in ?xs: p(?x))", "<forall_in>").toOption
      .getOrElse(fail("parse failed"))
    val body = pf.items.collectFirst { case Item.RuleItem(r) => r }.flatMap(_.body)
      .getOrElse(fail("no body"))
    assertEquals(functorName(pf, body(0)), "forall_in")
  }

  test("WI-027: `(some ?x in xs: P(?x))` lowers to `some_in`") {
    val pf = Parser.parse("rule somep(?xs) :- (some ?x in ?xs: p(?x))", "<some_in>").toOption
      .getOrElse(fail("parse failed"))
    val body = pf.items.collectFirst { case Item.RuleItem(r) => r }.flatMap(_.body)
      .getOrElse(fail("no body"))
    assertEquals(functorName(pf, body(0)), "some_in")
  }

  test("WI-027: an ordinary paren expr `(a + b)` still parses (bounded-quant backtracks)") {
    probeOk("paren-after-boundedq", "rule p(?x) :- eq(?x, (1 + 2))")
  }

  test("WI-027: a bounded-quant body admits a goal-position `let` (rule_body, not bare term)") {
    probeOk("boundedq-goal", "rule p(?xs) :- (forall ?x in ?xs: let ?y = f(?x), q(?y))")
  }

  test("WI-027: an anonymous `?` binder in a bounded quantifier is rejected (loud, not silent)") {
    Parser.parse("rule p(?xs) :- (forall ? in ?xs: q(?x))", "<anon-binder>") match
      case Right(_) => fail("expected rejection of anonymous bounded-quant binder")
      case Left(_)  => ()
  }

  // WI-517: type-annotated lambda binders.
  test("WI-517: single typed lambda binder `lambda (x: Int) -> x` parses") {
    probeOk("typed-lambda", "sort Demo\n  sort Int = ?\n  operation f() -> Int =\n    g(lambda (x: Int) -> x)\nend")
  }

  test("WI-517: typed tuple binder `lambda (a: A, b: B) -> add(a, b)` parses") {
    probeOk("typed-lambda-tuple",
      "sort Demo\n  sort A = ?\n  sort B = ?\n  operation f() -> A =\n    g(lambda (a: A, b: B) -> add(a, b))\nend")
  }

  // ccb5cf1d: a lambda is admissible as a NAMED-arg value.
  test("lambda as a named-arg value `f(k: lambda x -> g(x))` parses") {
    probeOk("named-lambda",
      "sort Demo\n  sort Int = ?\n  operation f() -> Int =\n    h(k: lambda x -> g(x), j: 2)\nend")
  }

  // WI-562: a `requires` clause must not swallow the operation body `=`.
  test("WI-562: `operation … requires Eq[T] = match …` parses the body") {
    val (pf, op) = parseDemoOp(
      "  operation member(x: T) -> Int requires Eq[T] =\n    match x\n      case nil() -> 0")
    assertEquals(op.requires.length, 1)
    assert(op.body.isDefined, "the `= match …` must parse as the operation body")
  }

  // ── WI-840: the NAMED requirement slot (proposal 058 §4.7) ──────────
  //
  // A named slot is a type PARAMETER — that is what lets a chosen witness enter a
  // TYPE (`SortedSet[T = String, O = ByLength]`), which an ANONYMOUS slot cannot do
  // because nothing named its witness. scaland mirrors the SURFACE and the IR (it
  // has no operation loading, a pre-existing divergence), so what these pin is that
  // both spellings parse and that the binder is carried, not dropped.

  test("WI-840: an op-scoped `requires <name>: Spec[…]` binds a type parameter") {
    val (pf, op) = parseDemoOp(
      "  operation biFold(x: T, n: Int) -> T\n" +
      "    requires neq(n, 0), lo: Ord[T], hi: Ord[T]")
    // Three goals in one clause: the value precondition keeps its place, so the
    // binders' recorded positions index the whole requirement list (§4.7 wrinkle 1 —
    // the op-scoped list is OVERLOADED, and a binder must coexist with predicates in
    // that same comma list).
    assertEquals(op.requires.length, 1)
    assertEquals(op.requires.head.length, 3)
    assertEquals(
      op.typeParams.map(tp => (pf.symbols.name(tp.name), tp.requirementSlot)),
      IndexedSeq(("lo", Some(1)), ("hi", Some(2)))
    )
  }

  test("WI-840: an anonymous op-scoped `requires` declares no type parameter") {
    val (_, op) = parseDemoOp("  operation member(x: T) -> Int requires Eq[T]")
    assertEquals(op.requires.length, 1)
    assert(op.typeParams.isEmpty, "an anonymous slot is a constraint, not a parameter")
  }

  test("WI-840: a sort-level `requires O: Ord[T]` carries its binder") {
    val pf = Parser.parse(
      "sort Box\n  sort T = ?\n  requires O: Ord[T]\n  requires Eq[T]\nend", "<slot>")
      .toOption.getOrElse(fail("parse failed"))
    val decls = pf.items.collect { case Item.SortWithBodyItem(s) => s }
      .head.items.collect { case Item.RequiresDeclItem(r) => r }
    assertEquals(decls.length, 2)
    assertEquals(decls.head.binder.map(b => pf.symbols.name(b.last)), Some("O"))
    assertEquals(decls(1).binder, None,
      "the anonymous form must still parse to a binder-less declaration")
  }

  // The dual: a clause `= goal` with a plain-TERM rhs (not an expr-body keyword)
  // stays an equality goal, NOT the operation body — matching rust's GLR.
  test("a clause `ensures result = x` keeps `=` as the eq goal (no spurious body)") {
    val (pf, op) = parseDemoOp("  operation abs(x: Int) -> Int ensures result = x")
    assertEquals(op.ensures.length, 1)
    assertEquals(functorName(pf, op.ensures.head.head), Pratt.eqFunctor)
    assert(op.body.isEmpty, "`= x` is the ensures eq goal, not an operation body")
  }

  // WI-454: per-statement non-rigid type-variable binder sugar.
  test("WI-454: `sort ?X` desugars to an abstract type-param sort") {
    val pf = Parser.parse("sort Demo\n  sort ?X\nend", "<sortvar>").toOption
      .getOrElse(fail("parse failed"))
    val inner = pf.items.collect { case Item.SortWithBodyItem(s) => s }.head.items
    val x = inner.collectFirst { case Item.AbstractSortItem(a) if pf.symbols.name(a.name.last) == "X" => a }
    assert(x.isDefined, s"expected abstract sort `X`, got $inner")
  }

  test("WI-454: `sort [X]` bracket binder parses") {
    probeOk("sort-bracket", "sort Demo\n  sort [X]\nend")
  }

  test("WI-454: structured binder `sort ?F { sort ?T }` marks F as a type param") {
    val pf = Parser.parse("sort Demo\n  sort ?F { sort ?T }\nend", "<sorthk>").toOption
      .getOrElse(fail("parse failed"))
    val f = pf.items.collect { case Item.SortWithBodyItem(s) => s }.head.items
      .collectFirst { case Item.SortWithBodyItem(s) if pf.symbols.name(s.name.last) == "F" => s }
      .getOrElse(fail("no F binder"))
    assert(f.isTypeParam, "structured binder F must be marked isTypeParam")
  }

  // WI-538: in-body / control-flow proof statement.
  test("WI-538: in-body `proof T by derivation end <body>` parses") {
    probeOk("inbody-proof",
      "sort Demo\n  sort Int = ?\n  operation f() -> Int =\n    proof t by derivation end g(x)\nend")
  }

  /** Walks the entire stdlib tree and asserts every .anthill file parses.
    * Locks in the WI-162/166/167 parser-coverage achievement: as new
    * stdlib modules are added, this test catches a parser regression
    * before it bites a downstream consumer.
    */
  // WI-876: the `operation_map` clause — which host FUNCTION realizes one of a
  // carrier's operations. Added to the kernel language by rustland; scaland must be
  // able to PARSE a binding file that uses it (`rustland/anthill-stl/anthill/*.anthill`
  // all do), or it cannot read the shipped bindings at all.
  test("WI-876: `operation_map` in a binding block parses") {
    val src = """
namespace test
  provides Int64 language rust
    artifact "src/int.rs"
    carrier { Int64: "i64" }
    operation_map { compare: "ordered_compare", gt: "ordered_gt" }
  end
end
"""
    val pf = Parser.parse(src, "opmap.anthill") match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.message).mkString(", ")}")
    val nsItems = pf.items.collect { case Item.NamespaceItem(ns) => ns }.head.items
    val blocks = nsItems.collect { case Item.ProvidesBlockItem(b) => b }
    assertEquals(blocks.length, 1)
    val maps = blocks.head.items.collect { case ProvidesItem.OperationMapI(es) => es }
    assertEquals(maps.length, 1, "one operation_map clause")
    assertEquals(maps.head.length, 2, "two entries")
    assertEquals(maps.head.map(e => pf.symbols.name(e.operation)).toList,
                 List("compare", "gt"))
  }

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

  // ── WI-424: value-in-type + effect-rows (port rust WI-302/375/373) ──
  //   Re-ported from the retired wi068 branch onto main's current parser.

  private def factTerm(src: String): (ParsedFile, Term) =
    val pf = Parser.parse(src, "<fact>").toOption.getOrElse(fail(s"parse failed: $src"))
    val fact = pf.items.collectFirst { case Item.FactItem(f) => f }
      .getOrElse(fail(s"no fact in: $src"))
    (pf, pf.terms.get(fact.term))

  /** Return type of a single `get()` op in a Demo body (parsed). */
  private def parseReturnType(retSrc: String): (ParsedFile, TypeExpr) =
    val (pf, op) = parseDemoOp(s"  operation get() -> $retSrc")
    (pf, op.returnType)

  // WI-302: a literal value in a type-argument slot → Denoted.
  test("WI-302: positional literal `Vector[Int, 3]` parses as a Denoted binding") {
    val (pf, te) = parseReturnType("Vector[Int, 3]")
    te match
      case TypeExpr.Parameterized(_, bindings) =>
        assertEquals(bindings.length, 2)
        bindings(1).bound match
          case TypeExpr.Denoted(v) =>
            pf.terms.get(v) match
              case Term.Const(Literal.IntLit(3)) => ()
              case other => fail(s"expected IntLit(3), got $other")
          case other => fail(s"expected Denoted, got $other")
      case other => fail(s"expected Parameterized, got $other")
  }

  test("WI-302: named literal binding `Fin[n = 8]` parses as Denoted") {
    val (pf, te) = parseReturnType("Fin[n = 8]")
    te match
      case TypeExpr.Parameterized(_, bs) if bs.length == 1 =>
        assertEquals(bs.head.param.map(p => pf.symbols.name(p.last)), Some("n"))
        assert(bs.head.bound.isInstanceOf[TypeExpr.Denoted], s"expected Denoted, got ${bs.head.bound}")
      case other => fail(s"expected single-binding Parameterized, got $other")
  }

  test("WI-302: literal type-arg lowers to the raw literal term") {
    val (pf, t) = factTerm("fact Vector[Int, 3]")
    t match
      case Term.Fn(f, pos, _) =>
        assertEquals(pf.symbols.name(f), "Vector")
        assertEquals(pos.length, 2)
        pf.terms.get(pos(1)) match
          case Term.Const(Literal.IntLit(3)) => ()
          case other => fail(s"expected IntLit(3) raw term, got $other")
      case other => fail(s"expected Vector Fn, got $other")
  }

  // WI-375: a written effect-row in a type-argument slot → EffectRow.
  test("WI-375: empty effect-row `Stream[E = {}]` parses as EffectRow([])") {
    val (pf, te) = parseReturnType("Stream[E = {}]")
    te match
      case TypeExpr.Parameterized(_, bs) if bs.length == 1 =>
        assertEquals(bs.head.param.map(p => pf.symbols.name(p.last)), Some("E"))
        bs.head.bound match
          case TypeExpr.EffectRow(effs) => assertEquals(effs.length, 0)
          case other => fail(s"expected EffectRow, got $other")
      case other => fail(s"expected Parameterized, got $other")
  }

  test("WI-375: effect-row `Stream[E = {Modify[c]}]` parses as EffectRow([Modify])") {
    val (pf, te) = parseReturnType("Stream[E = {Modify[c]}]")
    te match
      case TypeExpr.Parameterized(_, bs) if bs.length == 1 =>
        bs.head.bound match
          case TypeExpr.EffectRow(effs) => assertEquals(effs.length, 1)
          case other => fail(s"expected EffectRow, got $other")
      case other => fail(s"expected Parameterized, got $other")
  }

  test("WI-375: effect-row lowers to an `effects_rows(...)` term") {
    val (pf, t) = factTerm("fact Stream[E = {Modify[c]}]")
    t match
      case Term.Fn(_, _, named) =>
        val e = named.find((k, _) => pf.symbols.name(k) == "E").map(_._2)
          .getOrElse(fail("no E named arg"))
        pf.terms.get(e) match
          case Term.Fn(g, _, _) => assertEquals(pf.symbols.name(g), "effects_rows")
          case other => fail(s"expected effects_rows, got $other")
      case other => fail(s"expected Stream Fn, got $other")
  }

  // WI-373: projection types parse as dotted names — no special grammar.
  test("WI-373: projection type `Stream[l.T]` parses as a dotted name (no new node)") {
    val (pf, te) = parseReturnType("Stream[l.T]")
    te match
      case TypeExpr.Parameterized(_, bs) if bs.length == 1 =>
        bs.head.bound match
          case TypeExpr.Simple(n) =>
            assertEquals(n.segments.map(pf.symbols.name).mkString("."), "l.T")
          case other => fail(s"expected Simple(l.T), got $other")
      case other => fail(s"expected Parameterized, got $other")
  }

  // ── WI-278b: value-receiver dot forms lower to `dot_apply` ──
  //   Re-ported from the retired wi068 branch onto main's current parser.

  test("WI-278: value-receiver field `?x.field` lowers to dot_apply(receiver, name)") {
    val (pf, t) = factTerm("fact ?x.field")
    t match
      case Term.Fn(f, pos, named) =>
        assertEquals(pf.symbols.name(f), "dot_apply")
        assertEquals(pos.length, 2)
        assert(pf.terms.get(pos(0)).isInstanceOf[Term.Var], "receiver should be a Var")
        pf.terms.get(pos(1)) match
          case Term.Ident(s) => assertEquals(pf.symbols.name(s), "field")
          case other => fail(s"expected Ident(field), got $other")
      case other => fail(s"expected dot_apply Fn, got $other")
  }

  test("WI-278: method call `?x.method(?a, ?b)` → dot_apply with args") {
    val (pf, t) = factTerm("fact ?x.method(?a, ?b)")
    t match
      case Term.Fn(f, pos, _) =>
        assertEquals(pf.symbols.name(f), "dot_apply")
        assertEquals(pos.length, 4) // receiver, Ident(method), a, b
        pf.terms.get(pos(1)) match
          case Term.Ident(s) => assertEquals(pf.symbols.name(s), "method")
          case other => fail(s"expected Ident(method), got $other")
      case other => fail(s"expected dot_apply Fn, got $other")
  }

  test("WI-278: chained value dots `?x.a.b` nest dot_apply") {
    val (pf, t) = factTerm("fact ?x.a.b")
    t match
      case Term.Fn(f, pos, _) =>
        assertEquals(pf.symbols.name(f), "dot_apply")
        pf.terms.get(pos(0)) match
          case Term.Fn(inner, _, _) => assertEquals(pf.symbols.name(inner), "dot_apply")
          case other => fail(s"expected inner dot_apply, got $other")
      case other => fail(s"expected dot_apply Fn, got $other")
  }

  test("WI-278: name receiver `Foo.bar` keeps field_access (not dot_apply)") {
    val (pf, t) = factTerm("fact Foo.bar")
    t match
      case Term.Fn(f, _, _) => assertEquals(pf.symbols.name(f), "field_access")
      case other => fail(s"expected field_access Fn, got $other")
  }

  // ── Parser parity with current rust grammar (post-2026-06-26 features) ──

  /** Whether `tid`'s term tree contains a `Fn` with functor short/full name
    * `target` anywhere (used to locate a marker inside a rule head). */
  private def findFunctor(pf: ParsedFile, tid: TermId, target: String): Boolean =
    pf.terms.get(tid) match
      case fn: Term.Fn =>
        pf.symbols.name(fn.functor) == target ||
          fn.posArgs.exists(findFunctor(pf, _, target)) ||
          fn.namedArgs.exists { case (_, v) => findFunctor(pf, v, target) }
      case _ => false

  // WI-620: `pattern_paren` — a parenthesized single binder is grouping, not a 1-tuple.
  test("WI-620: `lambda (x) -> x` groups a single binder (unwraps to a bare pattern_var)") {
    val (pf, op) = parseDemoOp("  operation f() -> Int =\n    lambda (x) -> x")
    val body = op.body.getOrElse(fail("no lambda body"))
    pf.terms.get(body) match
      case fn: Term.Fn =>
        assertEquals(pf.symbols.name(fn.functor), "lambda_expr")
        // The `(x)` param unwraps to a bare `pattern_var`, NOT a `pattern_tuple`.
        assertEquals(functorName(pf, fn.posArgs(0)), "pattern_var")
      case other => fail(s"expected lambda_expr, got $other")
  }

  test("WI-620: parenthesized grouping is transparent in a match case `case (x) -> …`") {
    probeOk("wi620-match",
      """sort Demo
        |  sort Int = ?
        |  operation f(y: Int) -> Int =
        |    match y case (x) -> x
        |end""".stripMargin)
  }

  test("WI-620: grouping in a `let (x) = …` binder + nested `((y))` both parse") {
    probeOk("wi620-let",
      """sort Demo
        |  sort Int = ?
        |  operation f(z: Int) -> Int =
        |    let (x) = z in
        |    lambda ((y)) -> x
        |end""".stripMargin)
  }

  // WI-582: typed rule patterns `?x: T` in a rule LHS.
  test("WI-582: `add(?x: Numeric, 0)` LHS carries a `typed_var` marker") {
    val pf = Parser.parse("rule add(?x: Numeric, 0) = ?x", "<wi582>")
      .toOption.getOrElse(fail("parse failed"))
    val rule = pf.items.collectFirst { case Item.RuleItem(r) => r }.getOrElse(fail("no rule"))
    val head = rule.heads.collectFirst { case RuleHead.TermHead(t) => t }.getOrElse(fail("no head"))
    assert(findFunctor(pf, head, "typed_var"),
      "the typed LHS arg `?x: Numeric` must lower to a `typed_var` marker")
  }

  test("WI-582: the `[T]` introducer head `add[T](?x: T, 0) :- Numeric[T]` parses") {
    probeOk("wi582-introducer", "rule add[T](?x: T, 0) = ?x :- Numeric[T]")
  }

  // WI-639: distributive dot projection `x.(m1, …, mn)`.
  private def assertProjectionRejected(src: String, needle: String): Unit =
    Parser.parse(src, "<wi639-reject>") match
      case Left(es) =>
        assert(es.exists(_.message.contains(needle)),
          s"expected a `$needle` error, got: ${es.map(_.message).mkString("; ")}")
      case Right(_) => fail(s"expected parse to fail: $src")

  // ── WI-1131: arity one is NAMED-only ───────────────────────────────────────
  //
  // Scaland's `tupleLiteralOrParenExpr` already built the one-field named literal
  // (the `case Right((k, v))` branch); nothing measured it, and nothing pinned the
  // two verdicts around it. The shared `wi777` corpus fixes ACCEPT/REJECT across
  // both implementations; these rows fix the SHAPE, which a verdict cannot see —
  // returning the bare `1` for `(a: 1)` would "accept" just as well.
  //
  // BACK-OUT — MEASURED, three independent halves, each run on its own:
  //   * `case Right((k, v)) => v` (the named element handed back like a grouping):
  //     3 red, 1 green — the two named rows fail with `expected TupleLiteral, got
  //     Const(IntLit(1))`, and the `(1,)` row goes red only because that run also
  //     disabled the refusal.
  //   * `if false && trailingComma.isDefined`: the `(1,)` row goes red and the
  //     source parses CLEAN — the silent accept-as-grouping this refusal replaced.
  //   * dropping the `!")"` lookahead (restoring the bare `("," ~/ fnArg).rep`):
  //     3 red — `(a: 1,)` and `(1, 2,)` become `parse failed`, and `(1,)`'s
  //     diagnostic degrades to `parse error: found ")"`. That is the row's point:
  //     rustland has always accepted `(1, 2,)`, and scaland never did.
  //   * `(1)`-stays-grouping and `(1,,)`-still-refused pass under every back-out,
  //     by design: neither reaches the changed branches. They are the controls for
  //     the boundary, not evidence about the named form.

  test("WI-1131: `(a: 1)` is a one-component named TupleLiteral, not grouping") {
    val (pf, t) = factTerm("fact (a: 1)")
    t match
      case fn: Term.Fn =>
        assertEquals(pf.symbols.name(fn.functor), "TupleLiteral")
        assertEquals(fn.posArgs.length, 0)
        assertEquals(fn.namedArgs.map((k, _) => pf.symbols.name(k)).toSeq, Seq("a"))
      case other => fail(s"expected TupleLiteral, got $other")
  }

  test("WI-1131: the trailing comma is admitted at arity one too") {
    val (pf, t) = factTerm("fact (a: 1,)")
    t match
      case fn: Term.Fn =>
        assertEquals(pf.symbols.name(fn.functor), "TupleLiteral")
        assertEquals(fn.namedArgs.map((k, _) => pf.symbols.name(k)).toSeq, Seq("a"))
      case other => fail(s"expected TupleLiteral, got $other")
  }

  test("WI-1131 control: a single parenthesized term stays grouping") {
    val (_, t) = factTerm("fact (1)")
    t match
      case fn: Term.Fn => fail(s"`(1)` must be grouping, got a ${fn.getClass.getSimpleName}")
      case _           => ()
  }

  test("WI-1131: a trailing comma at 2+ parses too, as it always has in rustland") {
    val (pf, t) = factTerm("fact (1, 2,)")
    t match
      case fn: Term.Fn =>
        assertEquals(pf.symbols.name(fn.functor), "TupleLiteral")
        assertEquals(fn.posArgs.length, 2)
      case other => fail(s"expected TupleLiteral, got $other")
  }

  test("WI-1131 control: a doubled comma `(1,,)` is still refused") {
    assert(Parser.parse("fact (1,,)", "<wi1131>").isLeft, "`(1,,)` must not parse")
  }

  test("WI-1131: `(1,)` is refused, by a message naming the arity-one rule") {
    Parser.parse("fact (1,)", "<wi1131>") match
      case Left(es) =>
        val joined = es.map(_.message).mkString("; ")
        assert(joined.contains("one-element tuple literal must name its component"),
          s"the refusal must name the rule, got: $joined")
      case Right(_) => fail("`(1,)` must not parse as a tuple literal")
  }

  test("WI-639: `?x.(a, b)` desugars to a named `TupleLiteral` keyed by the members") {
    val (pf, t) = factTerm("fact ?x.(a, b)")
    t match
      case fn: Term.Fn =>
        assertEquals(pf.symbols.name(fn.functor), "TupleLiteral")
        assertEquals(fn.namedArgs.map((k, _) => pf.symbols.name(k)).toSet, Set("a", "b"))
        // Each column is the SAME accessor `?x.a` builds (value receiver ⇒ dot_apply).
        for (_, v) <- fn.namedArgs do assertEquals(functorName(pf, v), "dot_apply")
      case other => fail(s"expected TupleLiteral, got $other")
  }

  test("WI-639: rename `?x.(a: f1, b: f2)` keys by the LABELS, accesses the MEMBERS") {
    val (pf, t) = factTerm("fact ?x.(a: f1, b: f2)")
    t match
      case fn: Term.Fn =>
        assertEquals(fn.namedArgs.map((k, _) => pf.symbols.name(k)).toSet, Set("a", "b"))
        val aAccess = fn.namedArgs.collectFirst { case (k, v) if pf.symbols.name(k) == "a" => v }.get
        // dot_apply(?x, Ident(f1)) — the accessed member is `f1`, not the label `a`.
        pf.terms.get(aAccess) match
          case acc: Term.Fn =>
            pf.terms.get(acc.posArgs(1)) match
              case Term.Ident(m) => assertEquals(pf.symbols.name(m), "f1")
              case other => fail(s"expected member Ident(f1), got $other")
          case other => fail(s"expected accessor Fn, got $other")
      case other => fail(s"expected TupleLiteral, got $other")
  }

  // WI-20260818-YQB1Y (052 OQ5, option A): a single member NO LONGER 1-collapses.
  // `?x.(f)` is the one-field named tuple `(f: ?x.f)`, and a single RENAME keeps its
  // key too — where both used to yield the bare accessor `?x.f` and drop the label.
  // Asserting the KEY, not just the tuple: returning `(<anything>: ?x.f)` would
  // satisfy a shape-only check while losing exactly what the change is about.
  //
  // CONTROL: both rows FAIL on a back-out — the pre-change parser hands back the
  // `dot_apply` accessor, so `expected TupleLiteral, got Fn(dot_apply)`.
  test("WI-YQB1Y: a single member `?x.(f)` is the one-field tuple `(f: ?x.f)`") {
    for (src, key) <- Seq("fact ?x.(f)" -> "f", "fact ?x.(a: f)" -> "a") do
      val (pf, t) = factTerm(src)
      t match
        case fn: Term.Fn =>
          assertEquals(pf.symbols.name(fn.functor), "TupleLiteral", src)
          assertEquals(fn.namedArgs.length, 1, s"$src: one keyed component")
          assertEquals(pf.symbols.name(fn.namedArgs(0)._1), key, s"$src: result key")
          assertEquals(functorName(pf, fn.namedArgs(0)._2), "dot_apply", s"$src: accessor")
        case other => fail(s"$src: expected TupleLiteral, got $other")
  }

  // The named-only rule now applies at ARITY ONE too: `?x.(_1)` builds `(_1: ?x._1)`,
  // whose key collides with the positional-tuple convention exactly as `?x.(_1, _2)`
  // does. It used to be exempt because it collapsed to the plain access `?x._1`.
  //
  // CONTROL: FAILS on a back-out — the pre-change parser skips `validateProjectionLabels`
  // at arity one, so this source parses clean.
  test("WI-YQB1Y: a `_`-prefixed key is refused at arity one as well") {
    assertProjectionRejected("fact ?x.(_1)", "prefixed")
  }

  test("WI-639: a name receiver `Rec.(x, y)` uses field_access accessors") {
    val (pf, t) = factTerm("fact Rec.(x, y)")
    t match
      case fn: Term.Fn =>
        assertEquals(pf.symbols.name(fn.functor), "TupleLiteral")
        for (_, v) <- fn.namedArgs do assertEquals(functorName(pf, v), "field_access")
      case other => fail(s"expected TupleLiteral, got $other")
  }

  test("WI-639: chaining `?x.(a, b).a` reads a column off the projection tuple") {
    // The projection is a value (a TupleLiteral), so `.a` on it is a value dot.
    val (pf, t) = factTerm("fact ?x.(a, b).a")
    t match
      case fn: Term.Fn => assertEquals(pf.symbols.name(fn.functor), "dot_apply")
      case other => fail(s"expected outer dot_apply, got $other")
  }

  test("WI-639: a duplicate projection key is a loud parse error (not silent drop)") {
    assertProjectionRejected("fact ?x.(a, a)", "duplicate")
    assertProjectionRejected("fact ?x.(k: a, k: b)", "duplicate")
  }

  test("WI-639: a `_`-prefixed projection key is a loud parse error") {
    assertProjectionRejected("fact ?x.(_1, _2)", "prefixed")
  }

  test("WI-639: a malformed member list after `.(` is a loud parse error (cut)") {
    // The `.(` opener cuts, so `x.()` (no member) / `x.(1)` (non-identifier
    // member) fail loudly rather than silently backtracking and leaving `.(…)`
    // unconsumed. (A fastparse failure, not one of our `ParseError`s — assert on Left.)
    for src <- Seq("fact ?x.()", "fact ?x.(1)") do
      assert(Parser.parse(src, "<wi639-malformed>").isLeft,
        s"malformed projection must not parse: $src")
  }

  // Visibility precedes the `operation` keyword (`internal operation foo`,
  // WI-369) — previously scaland only accepted a visibility AFTER `operation`,
  // so `internal operation reverseOnto` in stdlib list.anthill failed to parse.
  test("stdlib fix: `internal operation …` (visibility before the keyword) parses + records it") {
    val (_, op) = parseDemoOp("  internal operation worker(x: Int) -> Int")
    assertEquals(op.visibility, Some(Visibility.Internal))
  }

  test("stdlib fix: a plain `operation …` (no visibility) still has none") {
    val (_, op) = parseDemoOp("  operation worker(x: Int) -> Int")
    assertEquals(op.visibility, None)
  }

  // ── Rust parser resync, WI-639 → WI-889 ──────────────────────────
  //   Each test below fails on the pre-resync parser; that is what makes it a
  //   test of the port and not of the surrounding grammar.

  /** WI-890 lexer gap: a string literal is ESCAPE-AWARE (rustland's token regex is
    * `/"([^"\\]|\\.)*"/`). Before this, `"#include \"hdr.hpp\""` ended at the inner
    * quote and the rest of the line was a syntax error — which is exactly how the
    * whole of stdlib `realization/cpp_std.anthill` failed to parse. */
  test("string escapes: `\\\"` does not close the literal, and decodes to a quote") {
    val (pf, term) = factTerm("""fact F(x: "#include \"hdr.hpp\"")""")
    val named = term match
      case fn: Term.Fn => fn.namedArgs.head._2
      case other => fail(s"expected Fn, got $other")
    pf.terms.get(named) match
      case Term.Const(Literal.StringLit(s)) =>
        assertEquals(s, "#include \"hdr.hpp\"")
      case other => fail(s"expected StringLit, got $other")
  }

  test("string escapes: `\\n` `\\t` `\\\\` decode, an unknown escape passes through") {
    val (pf, term) = factTerm("""fact F(x: "a\nb\tc\\d\qe")""")
    val named = term match
      case fn: Term.Fn => fn.namedArgs.head._2
      case other => fail(s"expected Fn, got $other")
    pf.terms.get(named) match
      case Term.Const(Literal.StringLit(s)) => assertEquals(s, "a\nb\tc\\dqe")
      case other => fail(s"expected StringLit, got $other")
  }

  test("string escapes: an ordinary literal is unchanged") {
    val (pf, term) = factTerm("""fact F(x: "plain")""")
    val named = term match
      case fn: Term.Fn => fn.namedArgs.head._2
      case other => fail(s"expected Fn, got $other")
    pf.terms.get(named) match
      case Term.Const(Literal.StringLit(s)) => assertEquals(s, "plain")
      case other => fail(s"expected StringLit, got $other")
  }

  /** WI-727 (proposal 056): the `...` variadic-capture marker. Drives the FLAG, not
    * just the parse — a port that dropped `rest` would still parse `relation.anthill`
    * and leave the loader's "at most one, trailing" check unable to fire. */
  test("WI-727: `...args: R` marks the parameter as a variadic capture") {
    val (pf, op) = parseDemoOp("  operation fix(p: Term, ...args: Map) -> Term")
    assertEquals(op.params.map(p => pf.symbols.name(p.name)), IndexedSeq("p", "args"))
    assertEquals(op.params.map(_.rest), IndexedSeq(false, true))
  }

  test("WI-727: an ordinary parameter list carries no capture") {
    val (_, op) = parseDemoOp("  operation f(p: Term, q: Map) -> Term")
    assertEquals(op.params.map(_.rest), IndexedSeq(false, false))
  }

  /** WI-853: a file's TOP LEVEL admits an `import`. */
  test("WI-853: a top-level `import` parses as its own item") {
    val pf = Parser.parse("import anthill.prelude.List\nfact F(x: 1)", "<wi853>")
      .toOption.getOrElse(fail("parse failed"))
    val imports = pf.items.collect { case Item.ImportItem(i) => i }
    assertEquals(imports.length, 1)
    assertEquals(imports.head.path.segments.map(pf.symbols.name).mkString("."),
                 "anthill.prelude.List")
    assertEquals(pf.items.collect { case Item.FactItem(f) => f }.length, 1,
      "the declaration after the import still parses")
  }

  test("WI-853: a selective top-level import keeps its selection") {
    val pf = Parser.parse("import anthill.prelude.Bool.{ite}", "<wi853-sel>")
      .toOption.getOrElse(fail("parse failed"))
    pf.items.collect { case Item.ImportItem(i) => i }.head.kind match
      case ImportKind.Selective(names) =>
        assertEquals(names.map(n => n.segments.map(pf.symbols.name).mkString(".")).toList,
                     List("ite"))
      case other => fail(s"expected Selective, got $other")
  }

  /** WI-763: a named-tuple type COMPONENT may be a constant standing in type
    * position — the shape a projection's keep spec is written in. */
  test("WI-763: `(person: \"name\")` is a denoted named-tuple component") {
    val (pf, te) = parseReturnType("""Project[T = Row, Keep = (person: "name", years: "age")]""")
    val keep = te match
      case TypeExpr.Parameterized(_, bindings) => bindings(1).bound
      case other => fail(s"expected Parameterized, got $other")
    keep match
      case TypeExpr.TupleType(members) =>
        assertEquals(members.map { case (n, _) => pf.symbols.name(n) },
                     IndexedSeq("person", "years"))
        members.map(_._2).foreach {
          case TypeExpr.Denoted(v) =>
            pf.terms.get(v) match
              case Term.Const(Literal.StringLit(_)) => ()
              case other => fail(s"expected a string denoted, got $other")
          case other => fail(s"expected Denoted, got $other")
        }
      case other => fail(s"expected TupleType, got $other")
  }

  test("WI-763: an ordinary named-tuple component is still a TYPE, not a denoted") {
    val (_, te) = parseReturnType("(name: Int, age: Int)")
    te match
      case TypeExpr.TupleType(members) =>
        members.map(_._2).foreach {
          case TypeExpr.Simple(_) => ()
          case other => fail(s"expected Simple, got $other")
        }
      case other => fail(s"expected TupleType, got $other")
  }

  /** WI-889: `const_map` — the const-level peer of `operation_map`. */
  test("WI-889: `const_map` in a binding block parses") {
    val src = """
namespace test
  provides Float language rust
    artifact "src/float.rs"
    carrier { Float: "f64" }
    const_map { infinity: "f64::INFINITY", nan: "f64::NAN" }
  end
end
"""
    val pf = Parser.parse(src, "constmap.anthill") match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.message).mkString(", ")}")
    val blocks = pf.items.collect { case Item.NamespaceItem(ns) => ns }
      .head.items.collect { case Item.ProvidesBlockItem(b) => b }
    val maps = blocks.head.items.collect { case ProvidesItem.ConstMapI(es) => es }
    assertEquals(maps.length, 1, "one const_map clause")
    assertEquals(maps.head.map(e => pf.symbols.name(e.constName)).toList,
                 List("infinity", "nan"))
  }

  // ── WI-952: an unterminated block comment is named at its OPENER ─────────
  //   The trivia skipper used to give up ON the comment: its inner scan is guarded
  //   by `index + 1 < length`, so on a file ending mid-comment it stopped one
  //   character short of the end and the parser tried to begin a declaration there
  //   — reporting a syntax error at a position INSIDE text the author meant as a
  //   comment. Worse, when that last character was whitespace the outer loop ate it
  //   and the file parsed CLEAN, comment and all.
  //
  //   WHAT FAILS WITHOUT THE FIX: all five `assertUnterminated` tests — the three
  //   whose file does not end in whitespace report `Parse error at <inside the
  //   comment>`, and the two `trailing newline` ones return `Right`. They are five
  //   separate tests on purpose: as a loop inside one, the first failure hides
  //   whether the silent-swallow case is really the silent one. The two controls
  //   pass either way BY DESIGN: they pin the `index + 1 < length` boundary the fix
  //   has to keep, so a scan that calls every comment closing at end-of-file
  //   unterminated does not pass them.

  private def assertUnterminated(src: String, opener: String): Unit =
    Parser.parse(src, "<wi952>") match
      case Right(_) => fail("expected the unterminated comment to be reported")
      case Left(errs) =>
        val head = errs.head
        assert(head.message.startsWith(s"Unterminated block comment: `$opener`"),
          s"expected the unterminated-comment error first, got: ${errs.map(_.message).mkString("; ")}")
        assertEquals(head.span.start, src.indexOf(opener),
          s"the error must point at the OPENER; got: ${head.message}")

  test("WI-952: `{- ` left open on an incomplete file reports the opener") {
    assertUnterminated("sort Demo\n  sort A = ?\n{- oops, never closed", "{-")
  }

  test("WI-952: `{- ` left open at the end of an otherwise complete file reports the opener") {
    // The last character is a newline, so the pre-WI-952 skipper consumed the whole
    // file and this parsed CLEAN — a silent swallow, not merely a bad message.
    assertUnterminated("sort Demo end\n{- oops, never closed\n", "{-")
  }

  test("WI-952: a nested `{- {- -} ` reports the OUTER opener") {
    // The inner comment closes; the outer one is what the author has to fix.
    assertUnterminated("sort Demo end\n{- outer {- inner -}\n", "{-")
  }

  test("WI-952: `{< ` left open swallowing the rest of the file reports the opener") {
    assertUnterminated("{< a doc comment that never ends\nsort Demo end", "{<")
  }

  test("WI-952: `{< ` left open at the end of a complete file reports the opener") {
    assertUnterminated("sort Demo end\n{< never closed\n", "{<")
  }

  test("WI-952 control: a well-formed nested `{- {- -} -}` still skips as before") {
    probeOk("nested-comment",
      """sort Demo
        |  {- outer {- inner -} still outer -}
        |  sort A = ?
        |end""".stripMargin)
  }

  test("WI-952 control: a comment closed by the file's last two characters is fine") {
    // The closer sits at exactly `length - 2` — one step from where the scan gives
    // up — so this is the case an over-eager unterminated check would misreport.
    probeOk("closer-at-eof", "sort Demo end {- done -}")
    probeOk("doc-closer-at-eof", "sort Demo end {< done >}")
  }

  /** WI-991 made the store a parse builds into an argument of a `private[anthill]` seam,
    * so that a test can count `spanOf` with a subclass instead of the production store
    * carrying a counter. THE ACCEPTANCE HALF: the store handed in is the store the
    * returned `ParsedFile` carries. Nothing else at this layer says so, and the way it
    * breaks is quiet — restore `val terms = SimpleTermStore()` inside the body (a
    * plausible merge or revert) and the parameter is silently shadowed: every other parse
    * test still passes, and the only failure is `ParseSpanGrowthTest`'s count assertion in
    * another package, whose message talks about counting rather than about a discarded
    * argument.
    *
    * BOTH LAYERS, because `Parser.parseInto` has an empty-source arm that returns without
    * ever reaching `AnthillParser` — a seam on the delegate alone would leave that input
    * building into a store the caller never sees.
    *
    * There is no freshness CHECK to drive: the public `parse` mints its own store, so a
    * fresh one per parse holds by construction. The first shape of this WAS a check —
    * `require(terms.size == 0)` on a public parameter — and it was measurably wrong:
    * `namespace d end` allocates no terms, so a store that had already backed a
    * declaration-only parse passed the guard and two files ended up sharing one store. */
  test("WI-991: a parse builds into the store it was given") {
    val store = SimpleTermStore()
    val pf = Parser.parseInto("fact p(1)", "<given>", store) match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.render).mkString("; ")}")
    assert(pf.terms eq store, "the ParsedFile carries a different store than the one supplied")
    assert(store.size > 0, "the parse built no terms into the supplied store")

    // The empty-source arm reaches neither the delegate nor any allocation, so identity
    // is the whole of what it can promise — and the whole of what it dropped before.
    val emptyStore = SimpleTermStore()
    val empty = Parser.parseInto("", "<empty>", emptyStore).toOption
      .getOrElse(fail("an empty source should parse"))
    assert(empty.terms eq emptyStore)

    val direct = SimpleTermStore()
    val viaDelegate = AnthillParser.parseInto("fact q(2)", "<direct>", direct).toOption
      .getOrElse(fail("the delegate should parse"))
    assert(viaDelegate.terms eq direct)
  }

  // ── WI-20260829-BAD3V: where a call-site type-arg bracket may be written ──
  //
  // `nameSuffix` admits `Name[bindings](args)`, so the bracket was accepted exactly
  // where the callee's receiver chain was a pure NAME PATH — which is exactly where the
  // call is NOT a dot call but a qualified one. Every value-receiver dot refused it at
  // the LEXER (`parse error: found "[…"`), including the FIRST hop `?xs.map[T = X](f)`.
  // `fieldSeg` now admits the bracket on a dot callee and `refuseDotTypeArgs` gives the
  // located refusal, so the author is told the applicative spelling instead of being
  // told the bracket is unpronounceable.
  //
  // WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT (`fieldSeg`'s `dotCallSuffix`):
  //   * `a dot call's type-arg bracket is admitted and refused` — RED; every row goes
  //     back to `parse error: found …`.
  //   * `a dot head keeps its meta block` and `a bracket off a call does not parse` —
  //     GREEN EITHER WAY, by design. They are the narrowness controls: the bracket is
  //     admitted only when a `(` follows, which is what leaves `?x.m [simp]` alone.

  private def dotBracketErrors(src: String): IndexedSeq[String] =
    Parser.parse(src, "<bad3v>") match
      case Right(_) => fail(s"expected a refusal for: $src")
      case Left(errs) => errs.map(_.message)

  test("WI-20260829-BAD3V: a dot call's type-arg bracket is admitted and refused") {
    val rows = Seq(
      "fact xs.map(f).map[Dst = Int64](g)",          // chained hop
      "fact (xs.map(f)).map[Dst = Int64](g)",        // parenthesized receiver
      "fact map(xs, f).map[Dst = Int64](g)",         // unqualified-call receiver
      "fact Iterable.map(xs, f).map[Dst = Int64](g)",// qualified-call receiver
      "fact xs.map[Dst = Int64](f).map[Dst = Int64](g)", // bracket on both hops
      "fact ?xs.map[Dst = Int64](f)",                // variable receiver, FIRST hop
      "fact [1, 2].map[Dst = Int64](f)"              // literal receiver
    )
    for src <- rows do
      val msgs = dotBracketErrors(src)
      assertEquals(msgs.length, 1, s"$src: ${msgs.mkString("; ")}")
      assert(msgs.head.contains("call-site type arguments are not supported on a dot call"),
        s"$src: expected the located refusal, got: ${msgs.head}")
      assert(!msgs.head.startsWith("parse error: "),
        s"$src: the parser must ADMIT this shape — a syntax error means `dotCallSuffix` " +
        s"did not fire; got: ${msgs.head}")
      assert(msgs.head.contains("The applicative spelling"),
        s"$src: the refusal must name the move; got: ${msgs.head}")
      // A SHAPE, NOT A POSITION — the peer of rustland's `the_refusal_prescribes_no_position`.
      // An earlier wording said "`Sort.m[…](receiver, …)` in an operation body"; a rule head
      // has no operation body to move into, and the companion receiver has no receiver
      // ARGUMENT (both found by /code-review).
      assert(!msgs.head.contains("operation body") && !msgs.head.contains("receiver, "),
        s"$src: the refusal must prescribe no position and no receiver argument; got: ${msgs.head}")
  }

  test("WI-20260829-BAD3V: a dot head keeps its meta block") {
    // The narrowness control. A `[` after a dotted member is also how a `meta_block`
    // opens; the bracket arm requires the call's `(`, so `[simp]` with nothing after it
    // can only be the meta block. Green against the backed-out parser — it measures the
    // DESIGN, not the feature. MEASURED against the wider arm `instArgsList ~
    // fnArgsList.?` (the shape that does not require the call): this test and its
    // neighbour both fail, `fact ?x.m [simp]` and `fact ?x.field[T = Int]` each drawing
    // the dot refusal. Note the failure mode differs from rustland's, where the same
    // widening EATS the attribute silently into a `sort_binding`: here the refusal fires
    // on `typeArgs.nonEmpty` whatever follows, so a `[simp]` after a dot head would be
    // loudly rejected instead. Loud, but wrong — the attribute is not a type argument.
    for src <- Seq("fact ?x.m [simp]", "rule dr: ?x.m [simp]", "rule dr2: ?x.m(?y) [simp]") do
      val pf = Parser.parse(src, "<bad3v-meta>") match
        case Right(p) => p
        case Left(errs) => fail(s"$src: ${errs.map(_.message).mkString("; ")}")
      val meta = pf.items.collectFirst {
        case Item.FactItem(f) => f.meta
        case Item.RuleItem(r) => r.meta
      }.flatten.getOrElse(fail(s"$src: the `[simp]` must still be the META BLOCK"))
      assertEquals(
        meta.entries.map(e => e.key.segments.map(pf.symbols.name).mkString(".")).toList,
        List("simp"), src)
  }

  test("WI-20260829-BAD3V: a juxtaposed entry's `(` reaches the bracket (divergence, pinned)") {
    // NOT parity with rustland, and pinned so the difference is a decision rather than a
    // surprise (found by /code-review). Rustland declares a GLR conflict biased toward the
    // META reading, so it reads THREE entries here; fastparse is ordered, so the bracket
    // alternative wins and this parses as one bracketed dot call, which is then refused.
    //
    // BOTH IMPLEMENTATIONS REFUSE THIS FILE — rustland at conversion ("a rule head must be
    // an atom, not a bare literal") — so what diverges is which error an already-invalid
    // program draws, and no VALID program is known to reach it (see `refuseDotTypeArgs`).
    // If one is ever found, this row is the one that has to move.
    val src = "sort S\n  rule {\n    ?x.m [simp]\n    (a, b)\n  }\nend\n"
    val msgs = dotBracketErrors(src)
    assert(msgs.head.contains("call-site type arguments are not supported on a dot call"),
      s"expected the dot refusal; got: ${msgs.mkString("; ")}")
  }

  test("WI-20260829-BAD3V: a bracket off a call does not parse") {
    // The other half of the narrowness: `?x.field[T = Int]` has no call after the `]`,
    // so nothing kills the meta-block reading and the bracket stays unpronounceable.
    // Green either way — it says what was deliberately NOT widened.
    val msgs = dotBracketErrors("fact ?x.field[T = Int]")
    assert(msgs.exists(_.startsWith("parse error: ")),
      s"expected a syntax error; got: ${msgs.mkString("; ")}")
    assert(!msgs.exists(_.contains("call-site type arguments")),
      s"it must not reach the refusal at all; got: ${msgs.mkString("; ")}")
  }
