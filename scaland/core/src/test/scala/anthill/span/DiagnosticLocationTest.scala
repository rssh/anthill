package anthill.span

import anthill.kb.KnowledgeBase
import anthill.intern.ResolveResult
import anthill.load.{LoadError, Loader, Prelude}
import anthill.parse.{ParseError, ParsedFile, Parser}

/** WI-947 — what a user actually sees: a scaland diagnostic names `file:line:col`.
  *
  * Every assertion here is on a SPECIFIC row and column, not on "a position was
  * produced". That is the point: before this WI every span in the tree was built
  * with row and col hard-coded to 0, so a test that only checked "an error came
  * back" passed just as well with no location at all — which is how the gap
  * survived.
  *
  * CONTROL, measured, not asserted from the armchair: make `Span.at` hand back a
  * zero START and 23 of the 28 tests in this package fail (16 of 21 before WI-957
  * added the ambiguous-symbol family below and WI-961 added `ParseSpanCoverageTest`) — the survivors being the
  * `LineIndex` units (which never build a span) and the locationless-`Span.empty`
  * case. Revert the `Index` capture in ONE production (`param`) and exactly 3 fail:
  * the two WI-727 ones and the rendering-parity one, which uses a WI-727 error as
  * its load-side sample. The pre-existing tests that assert message TEXT
  * (`ParseTest`'s WI-950 scoping tests, `ParserIntegrationTest`'s WI-727 refusals)
  * pass either way BY DESIGN — they never look at a position, which is exactly why
  * they could not have caught this.
  *
  * Declaration spans that no diagnostic cites are pinned in `DeclarationSpanTest`,
  * one case per shape — testing them only through diagnostics left most of the
  * family unpinned.
  */
class DiagnosticLocationTest extends munit.FunSuite:

  private def parseErrors(src: String, file: String = "demo.anthill"): IndexedSeq[ParseError] =
    Parser.parse(src, file) match
      case Right(_) => fail("expected the parse to report an error")
      case Left(errs) => errs

  /** The KB alongside the errors — for assertions that check a diagnostic's CLAIM against
    * the tree it describes (WI-986), rather than against a fixed string. */
  private def loadInto(src: String, file: String = "demo.anthill")
      : (KnowledgeBase, IndexedSeq[LoadError]) =
    val pf: ParsedFile = Parser.parse(src, file) match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.render).mkString("; ")}")
    val kb = KnowledgeBase()
    Prelude.register(kb)
    (kb, Loader.loadAll(kb, IndexedSeq(pf)).toIndexedSeq)

  private def loadErrors(src: String, file: String = "demo.anthill"): IndexedSeq[LoadError] =
    loadInto(src, file)._2

  private def at(span: Span): (Int, Int) = (span.startRow, span.startCol)

  // ── The parse family ─────────────────────────────────────────

  test("a syntax error is reported at its own line and column") {
    // Line 4 is `  fact p(` — an argument list that is never closed. What the user
    // used to get for this was `Parse error at 39: Position 4:9, found "("`: a raw
    // offset from us, and a position only because fastparse spelled one inside its
    // own message text. Now the position is ours, on the span, rendered by the one
    // renderer both families share.
    val src =
      """namespace demo
        |  sort S
        |  end
        |  fact p(
        |end""".stripMargin
    val errs = parseErrors(src)
    assertEquals(errs.length, 1, s"got: ${errs.map(_.render).mkString("; ")}")
    assertEquals(at(errs.head.span), (4, 9))
    assertEquals(src.split("\n")(3).charAt(8), '(')   // the column really is the `(`
    assertEquals(errs.head.render, s"demo.anthill:4:9: ${errs.head.message}")
    assert(errs.head.message.startsWith("parse error: "), errs.head.message)
  }

  test("a refusal about a well-formed declaration points at the offending token") {
    // WI-850: the type-param default. Line 3, and the column is the `T` — not the
    // `[`, not the whitespace before it.
    val src =
      """namespace demo
        |  sort S
        |    operation g[T = S](x: S) -> S
        |  end
        |end""".stripMargin
    val errs = parseErrors(src)
    val refusal = errs.find(_.message.contains("carries a default"))
      .getOrElse(fail(s"expected the WI-850 refusal, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(refusal.span), (3, 17))
    assertEquals(src.split("\n")(2).charAt(16), 'T')  // the column really is the `T`
    assert(refusal.render.startsWith("demo.anthill:3:17: "), refusal.render)
  }

  test("WI-952: an unterminated block comment is located at its OPENER") {
    // The opener is on line 2; the scan gives up at end of input on line 4. The
    // reported position must be the opener — that is what the author has to fix.
    val src =
      """namespace demo
        |  {- opened here
        |  sort S
        |  end""".stripMargin
    val errs = parseErrors(src)
    val unterminated = errs.find(_.message.contains("Unterminated block comment"))
      .getOrElse(fail(s"expected the WI-952 refusal, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(unterminated.span), (2, 3))
  }

  // ── The load family ──────────────────────────────────────────

  test("WI-727: a misplaced variadic capture is located at the capture") {
    // Line 4, column 19: the `...` of `...args`. The refusal is about the marker's
    // POSITION, so the marker is what it points at.
    val src =
      """namespace v
        |  sort Rel
        |    sort R = ?
        |    operation fix(...args: R, p: Rel) -> Rel
        |  end
        |end""".stripMargin
    val errs = loadErrors(src)
    val (refusal, span) = errs.collectFirst {
      case e @ LoadError.Other(m, s) if m.contains("LAST parameter") => (e, s)
    }.getOrElse(fail(s"expected the WI-727 refusal, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(span), (4, 19))
    assertEquals(src.split("\n")(3).substring(18, 21), "...")
    assert(refusal.render.startsWith("demo.anthill:4:19: "), refusal.render)
  }

  test("WI-727: with TWO captures the refusal points at the SECOND") {
    val src =
      """namespace v
        |  sort Rel
        |    sort R = ?
        |    operation fix(...a: R, ...b: R) -> Rel
        |  end
        |end""".stripMargin
    val errs = loadErrors(src)
    val span = errs.collectFirst { case LoadError.Other(m, s) if m.contains("at most one") => s }
      .getOrElse(fail(s"expected the WI-727 refusal, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(span), (4, 28))
    assertEquals(src.split("\n")(3).substring(27, 30), "...")
  }

  test("an unlabelled multi-head rule is located at the rule") {
    val src =
      """namespace demo
        |  rule p(?x), q(?x) :- r(?x)
        |end""".stripMargin
    val errs = loadErrors(src)
    val span = errs.collectFirst { case LoadError.Other(m, s) if m.contains("multi-head rule requires a label") => s }
      .getOrElse(fail(s"expected the multi-head refusal, got: ${errs.map(_.render).mkString("; ")}"))
    // Column 3 is the `rule` keyword: a declaration spans its own first token, and
    // `ruleDecl` re-stamps the entry it dispatched to so the keyword is included.
    // (A rule written inside a braced `rule { … }` block has no keyword of its own
    // and spans from its label-or-first-head — that difference is the two surface
    // forms differing, not the span rule differing.)
    assertEquals(at(span), (2, 3))
    assertEquals(src.split("\n")(1).substring(2, 6), "rule")
  }

  test("WI-949's missing-scope report is located at the declaration whose body was dropped") {
    // The one way to reach `lookupScope`'s miss: run `Loader.load` WITHOUT
    // `scanDefinitions`, so pass 1 never defined the scope. The span is the
    // declaration's NAME — the missing name has nothing to point at on the symbol-table
    // side, and what the reader needs is the declaration whose contents were dropped.
    val src =
      """namespace demo
        |  sort S
        |  end
        |end""".stripMargin
    val pf = Parser.parse(src, "demo.anthill") match
      case Right(p) => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.render).mkString("; ")}")
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.load(kb, pf).toIndexedSeq
    val span = errs.collectFirst { case LoadError.Other(m, s) if m.contains("was not defined in pass 1") => s }
      .getOrElse(fail(s"expected the WI-949 missing-scope report, got: ${errs.map(_.render).mkString("; ")}"))
    assertEquals(at(span), (1, 11))
    assertEquals(src.split("\n")(0).substring(10), "demo")
  }

  // ── WI-957: the ambiguous-symbol family ──────────────────────
  //
  // CONTROL, measured on both halves of the change rather than asserted:
  //
  //   * revert the RAISE SITE (`Loader.resolveName` back to `Span.empty, ""`) and
  //     exactly these 5 tests fail; the other 304 pass;
  //   * make `SimpleTermStore.allocAt` DISCARD its span — the parser half, so every
  //     name-bearing term is allocated locationless again — and the same 5 fail,
  //     with the same 304 passing.
  //
  // So neither half is dead: threading a span to the diagnostic is worthless if the
  // parser never captured one, and capturing one is worthless if the raise site still
  // hard-codes `Span.empty`. Nothing in the pre-existing suite moves either way —
  // `AmbiguousSymbol` had no position and no scope name to assert on, which is
  // precisely how it survived WI-947.

  /** A scope with TWO required parents that each declare `dup` — the only way a
    * short name resolves to more than one symbol. `body` goes inside a third sort
    * that requires both, so every occurrence in it is ambiguous. */
  private def ambiguousDup(body: String): String =
    s"""namespace demo
       |  sort A
       |    operation dup(x: A) -> A
       |  end
       |  sort B
       |    operation dup(x: B) -> B
       |  end
       |  sort C
       |    requires demo.A
       |    requires demo.B
       |$body
       |  end
       |end""".stripMargin

  private def ambiguities(errs: IndexedSeq[LoadError]): IndexedSeq[LoadError.AmbiguousSymbol] =
    errs.collect { case e: LoadError.AmbiguousSymbol => e }

  private def unresolved(errs: IndexedSeq[LoadError], name: String): LoadError.UnresolvedName =
    errs.collectFirst { case e @ LoadError.UnresolvedName(`name`, _, _) => e }
      .getOrElse(fail(
        s"expected an unresolved-name error for '$name', got: ${errs.map(_.render).mkString("; ")}"))

  test("WI-957: an ambiguous symbol is located at the occurrence, in a named scope") {
    // The last locationless load diagnostic. It reported `ambiguous symbol 'dup' in
    // scope ''` — no position, and a scope name that was never filled in.
    val src = ambiguousDup("    rule uses(?x) :- dup(?x)")
    val errs = ambiguities(loadErrors(src))
    assertEquals(errs.length, 1, s"got: ${errs.map(_.render).mkString("; ")}")
    val e = errs.head
    assertEquals(e.name, "dup")
    assertEquals(at(e.span), (11, 22))
    assertEquals(src.split("\n")(10).substring(21, 24), "dup")   // the column really is the `dup`
    // The scope is the one the resolution was actually attempted in, spelled by its
    // qualified name — not the empty string the field carried before.
    assertEquals(e.scopeName, "demo.C")
    assertEquals(e.candidates.sorted, IndexedSeq("demo.A.dup", "demo.B.dup"))
    assertEquals(e.render,
      "demo.anthill:11:22: ambiguous symbol 'dup' in scope 'demo.C': candidates demo.A.dup, demo.B.dup")
  }

  test("WI-957: TWO occurrences of the same ambiguous name are located separately") {
    // What "per OCCURRENCE" means, and the case a declaration-level or file-level span
    // would pass the test above with: the same name, ambiguous twice, must report two
    // DIFFERENT positions. The parse-time term store does not hash-cons, so each
    // written `dup` is its own `TermId` with its own span — this is what pins that.
    val src = ambiguousDup(
      """    rule uses(?x) :- dup(?x)
        |    rule again(?y) :- dup(?y)""".stripMargin)
    val errs = ambiguities(loadErrors(src))
    assertEquals(errs.length, 2, s"got: ${errs.map(_.render).mkString("; ")}")
    assertEquals(errs.map(e => at(e.span)).toSet, Set((11, 22), (12, 23)))
    assertEquals(src.split("\n")(11).substring(22, 25), "dup")
  }

  test("WI-957: an ambiguous INFIX operator is located at the operator token") {
    // `?a + ?b` desugars to `add(?a, ?b)`, and `add` is what resolves. That functor is
    // written nowhere, so the position has to be the `+` the author typed — the one
    // token that denotes it.
    val src =
      """namespace demo
        |  sort A
        |    operation add(x: A, y: A) -> A
        |  end
        |  sort B
        |    operation add(x: B, y: B) -> B
        |  end
        |  sort C
        |    requires demo.A
        |    requires demo.B
        |    rule uses(?x) :- p(?x + ?x)
        |  end
        |end""".stripMargin
    val errs = ambiguities(loadErrors(src))
    assertEquals(errs.length, 1, s"got: ${errs.map(_.render).mkString("; ")}")
    assertEquals(errs.head.name, "add")
    assertEquals(at(errs.head.span), (11, 27))
    assertEquals(src.split("\n")(10).charAt(26), '+')
  }

  test("WI-957: an ambiguous dot member is located at the member, not the receiver") {
    // `?x.fld` builds `dot_apply(?x, Ident(fld))`; the `Ident` is what resolves, so the
    // position is the member token — a span covering the whole accessor would point at
    // the `?x`, which is not the ambiguous part.
    val src =
      """namespace demo
        |  sort A
        |    operation fld(x: A) -> A
        |  end
        |  sort B
        |    operation fld(x: B) -> B
        |  end
        |  sort C
        |    requires demo.A
        |    requires demo.B
        |    rule uses(?x) :- p(?x.fld)
        |  end
        |end""".stripMargin
    val errs = ambiguities(loadErrors(src))
    assertEquals(errs.length, 1, s"got: ${errs.map(_.render).mkString("; ")}")
    assertEquals(errs.head.name, "fld")
    assertEquals(at(errs.head.span), (11, 27))
    assertEquals(src.split("\n")(10).substring(26, 29), "fld")
  }

  test("WI-957: a SYNTHESIZED marker the loader still resolves is located too") {
    // The trap review caught: "the functor looks synthetic" is NOT a reason a node may
    // claim `Span.empty`. `reallocTerm` resolves the functor of EVERY `Term.Fn` bar the
    // one shape it intercepts first (`typed_var`, WI-582 — WI-1007 removed the other
    // exception). These five are not that shape — they reach `resolveName` exactly like
    // a written call — so a user who declares an operation of the same name gets the
    // locationless report this WI exists to retire. Measured, not reasoned: before the
    // fix all five reported `hasLocation == false`.
    //
    // Each is located at the token that PRODUCED it (the `let`, the applied `?p`, the
    // opening bracket), because the functor itself is written nowhere.
    val cases = Seq(
      ("unify",        "    rule uses(?x) :- let ?y = ?x",            22),
      ("ho_apply",     "    rule uses(?p) :- ?p(1)",                  22),
      ("ListLiteral",  "    rule uses(?x) :- p([?x, ?x])",            24),
      ("SetLiteral",   "    rule uses(?x) :- p({?x})",                24),
      ("TupleLiteral", "    rule uses(?x) :- p((a: ?x, b: ?x))",      24),
    )
    for (marker, body, col) <- cases do
      val src =
        s"""namespace demo
           |  sort A
           |    operation $marker(x: A) -> A
           |  end
           |  sort B
           |    operation $marker(x: B) -> B
           |  end
           |  sort C
           |    requires demo.A
           |    requires demo.B
           |$body
           |  end
           |end""".stripMargin
      val found = ambiguities(loadErrors(src)).filter(_.name == marker)
      assertEquals(found.length, 1, s"$marker: expected one ambiguity, got ${found.map(_.render)}")
      assertEquals(at(found.head.span), (11, col), s"$marker located wrong")
      assertEquals(found.head.scopeName, "demo.C", s"$marker scope wrong")
  }

  test("an unresolved name is located at the name, and names the scope that declared it") {
    // WI-962: the scope half. Asserting only the SPAN is what let this site hard-code the
    // literal `"requires"` through a green suite. The scope is `demo.S`, the sort whose
    // `requires` this is.
    //
    // CONTROL, measured: back the raise site out to `"requires"` and this ONE test fails
    // (330 pass). The two `scopeName` assertions in the WI-957 family above pass either
    // way BY DESIGN — they go through `resolveName`, a different raise site, which is
    // exactly how the requires site drifted unnoticed. Backing out the `scopeDisplayName`
    // move alone is not a behaviour change and fails nothing; it is a one-answer change.
    val src =
      """namespace demo
        |  sort S
        |    requires nosuchspec
        |  end
        |end""".stripMargin
    val e = unresolved(loadErrors(src), "nosuchspec")
    assertEquals(at(e.span), (3, 14))
    assertEquals(src.split("\n")(2).substring(13, 23), "nosuchspec")
    assertEquals(e.scopeName, "demo.S")
    assertEquals(e.render, "demo.anthill:3:14: unresolved name 'nosuchspec' in scope 'demo.S'")
  }

  /** WI-986 — `in scope 'X'` is a claim about a SEARCH, so the search has to be the one
    * the message describes. `processRequires` asked `byQualifiedName` alone — the rung a
    * SHORT name is never answered by — and then named the declaring scope anyway.
    *
    * MEASURED before the fix, on the first case below: `demo.anthill:7:14: unresolved
    * name 'Widget' in scope 'demo.S'`, while `Widget` resolves in `demo.S` perfectly
    * well, having been imported there one line up. The reader was sent to inspect a
    * scope in which the name is present, and the real rule — write it qualified — was
    * never stated. The fix makes the claim true by making it accurate: the requirement
    * now resolves the way every other written name does.
    *
    * CONTROL, MEASURED by restoring the `byQualifiedName`-only lookup: exactly ONE of
    * the two fails, the first, 339 of 340 still passing. The second passes EITHER WAY,
    * and so does the `nosuchspec` test above, for the same reason in both cases — their
    * names miss on both ladders, so both ladders tell the truth about them. That is not
    * a defect in the second case, it is its job: it asserts the claim against the TREE
    * rather than against a fixed string, so it still holds a future filler of
    * `scopeName` to account without being rewritten. Only a name that RESOLVES in the
    * named scope can discriminate the two ladders, and that is the first case. */
  test("WI-986: a `requires` resolves in the scope its diagnostic names") {
    val src =
      """namespace demo
        |  sort Widget
        |    operation spin() -> Widget
        |  end
        |  sort S
        |    import demo.Widget
        |    requires Widget
        |  end
        |end""".stripMargin
    val (kb, errs) = loadInto(src)
    assertEquals(errs.map(_.render), IndexedSeq.empty,
      "an imported spec is a legal requirement — §5.1, an import is a local alias")

    // DRIVEN, not "it loaded clean": §5.1 — a `requires` gives the requiring scope
    // access to the required sort's contents, so `spin` must now resolve in `demo.S`.
    // Without this the test would pass on a `requires` that resolved and then linked
    // nothing.
    val inS = kb.symbols.resolveInScope(
      "spin", kb.symbols.scopeOf(kb.resolveSymbol("demo.S")))
    assertEquals(
      inS match
        case ResolveResult.Found(sym) => kb.qualifiedNameOf(sym)
        case other => s"not found: $other",
      "demo.Widget.spin")
  }

  /** WI-988 — LINKING A PARENT THAT CANNOT HOLD CONTENTS IS A NO-OP, AND IT USED TO BE
    * A SILENT ONE. `scopeOf` is total over a symbol, so "can this name hold contents"
    * is the linking site's question; neither site asked it. `addParent` then created the
    * importing side's record and never the parent's, `resolveRecursive` treated the
    * missing parent as eligible, and the answer was `NotFound` — a name the user wrote
    * doing nothing at all.
    *
    * CONTROL, measured by deleting the `parentScopeOf` gate at both sites: each of these
    * two loads clean, 0 errors, and the probe below shows the import contributing
    * nothing — which is the pre-WI-988 behaviour exactly. Both fail with the gate gone;
    * no other test moves. */
  test("WI-988: a wildcard import of a non-scope is refused, naming what it got") {
    val src =
      """namespace demo
        |  sort Host
        |    operation op1() -> Host
        |  end
        |  sort User
        |    import demo.Host.op1.*
        |  end
        |end""".stripMargin
    val (kb, errs) = loadInto(src)
    val e = errs.collectFirst { case o @ LoadError.Other(m, _) if m.contains("wildcard") => o }
      .getOrElse(fail(s"expected a wildcard-import refusal, got: ${errs.map(_.render).mkString("; ")}"))
    assert(e.message.contains("operation"), s"must name the kind it got: ${e.message}")
    assert(e.message.contains("demo.Host.op1"), s"must name the symbol: ${e.message}")

    // The reason it is worth a diagnostic rather than a shrug: the import contributed
    // NOTHING, which is what the user cannot see. This probe is the pre-fix behaviour
    // and stays true after — the gate refuses the link, it does not repair it.
    assertEquals(
      kb.symbols.resolveInScope("op1", kb.symbols.scopeOf(kb.resolveSymbol("demo.User"))),
      ResolveResult.NotFound)
  }

  test("WI-988: a `requires` naming a non-sort is refused, naming what it got") {
    // A requirement names an algebraic spec, and a spec is a sort (§5.2). `op1` resolves
    // here — it is a sibling in the enclosing namespace — so this is the kind gate
    // firing, not the WI-986 resolution failing.
    val src =
      """namespace demo
        |  sort Thing
        |  end
        |  operation op1() -> Thing
        |  sort User
        |    requires op1
        |  end
        |end""".stripMargin
    val errs = loadErrors(src)
    val e = errs.collectFirst { case o @ LoadError.Other(m, _) if m.contains("requires") => o }
      .getOrElse(fail(s"expected a `requires` refusal, got: ${errs.map(_.render).mkString("; ")}"))
    assert(e.message.contains("operation"), s"must name the kind it got: ${e.message}")
    assert(e.message.contains("sort"), s"must say what it wanted: ${e.message}")
  }

  test("WI-986: the scope an unresolved-name diagnostic names really does not resolve it") {
    // The general property, asserted against the tree rather than against a fixed string:
    // whatever scope the message names, ASK that scope. This is the assertion the old
    // site could not have satisfied for an in-scope name, and it holds for any future
    // filler of `scopeName` without being rewritten.
    // `Widget` EXISTS — as `other.Widget` — and is simply not in scope here, which is
    // the case worth pinning: a name absent from the whole KB (the `nosuchspec` test
    // above) makes the claim true for free. A SIBLING sort would not do either; it
    // resolves through the enclosing namespace, and correctly so.
    val src =
      """namespace other
        |  sort Widget
        |  end
        |end
        |namespace demo
        |  sort S
        |    requires Widget
        |  end
        |end""".stripMargin
    val (kb, errs) = loadInto(src)
    val e = unresolved(errs, "Widget")
    assertEquals(e.scopeName, "demo.S")
    assertEquals(
      kb.symbols.resolveInScope(e.name, kb.symbols.scopeOf(kb.resolveSymbol(e.scopeName))),
      ResolveResult.NotFound,
      s"'${e.name}' must really be unresolvable in '${e.scopeName}' for the message to be true")
  }

  test("WI-962: an unresolved import NAME names the scope it was searched for in") {
    // The third filler of `scopeName` — the WI-295 pass-4 retry — pinned on the reading a
    // reader could misjudge: the scope is `demo.A`, the IMPORTED one, not `demo.B` where
    // the import is written (see `LoadError`'s field doc). Untested until now, which is why
    // "is this even the same meaning?" was open rather than settled. It also holds the
    // retry to deriving the name from its symbol: pass `p.path` here instead of
    // `qualifiedNameOf(p.target)` and this test still passes — the two agree today — so
    // what it pins is the VALUE, and the single-source rule is the comment's job.
    val src =
      """namespace demo
        |  sort A
        |    operation real(x: A) -> A
        |  end
        |  sort B
        |    import demo.A.{nosuchname}
        |  end
        |end""".stripMargin
    val e = unresolved(loadErrors(src), "nosuchname")
    assertEquals(e.scopeName, "demo.A")
    assertEquals(at(e.span), (6, 20))
    assertEquals(src.split("\n")(5).substring(19, 30), "nosuchname}")
  }

  // ── The shared rendering ─────────────────────────────────────

  test("both families render a location the same way") {
    // The property the two `render`s exist for: which STAGE found a fault does not
    // change how its location reads. Same file, same shape, one renderer.
    val parseAt = parseErrors(
      """namespace demo
        |  sort S
        |    operation g[T = S](x: S) -> S
        |  end
        |end""".stripMargin).find(_.message.contains("carries a default")).get
    val loadAt = loadErrors(
      """namespace v
        |  sort Rel
        |    sort R = ?
        |    operation fix(...a: R, p: Rel) -> Rel
        |  end
        |end""".stripMargin).collectFirst { case e @ LoadError.Other(m, _) if m.contains("LAST") => e }.get
    assert(parseAt.render.matches("""demo\.anthill:\d+:\d+: .*"""), parseAt.render)
    assert(loadAt.render.matches("""demo\.anthill:\d+:\d+: .*"""), loadAt.render)
  }

  test("a locationless span renders the bare message, not a position 0") {
    // `Span.empty` is the one span with no location, and it must not print as
    // `0:0` — a fake position is worse than none.
    assertEquals(Span.empty.render("something went wrong"), "something went wrong")
    assertEquals(Span.empty.hasLocation, false)
    assertEquals(LoadError.Other("something went wrong", Span.empty).render, "something went wrong")
  }

end DiagnosticLocationTest
