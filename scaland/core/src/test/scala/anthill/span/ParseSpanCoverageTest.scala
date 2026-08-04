package anthill.span

import anthill.load.{EmbeddedStdlib, FileSourceResolver}
import anthill.parse.{ParsedFile, Parser}
import anthill.term.Term
import java.nio.file.Paths

/** WI-961 — THE PARSER NEVER EMITS A RESOLVABLE NAME WITHOUT A POSITION.
  *
  * WI-957 located the `AmbiguousSymbol` diagnostic by giving parse terms spans, but
  * left the coverage CONVENTIONAL: `alloc` and `allocAt` were equally reachable and
  * equally neutral-looking, so the next production to mint a resolvable functor would
  * compile clean, pass every test, and silently restore the locationless report.
  *
  * TWO mechanisms now, because they fail differently:
  *
  *   1. `SimpleTermStore.alloc` takes a `Term.Nameless`, so a `Fn`/`Ref`/`Ident`
  *      without a span DOES NOT COMPILE. No test has to exercise the new production
  *      for the mistake to surface.
  *   2. This test. A type cannot express "the span you passed is not `Span.empty`", so
  *      mechanism 1 is blind to a span that WAS supplied and came out empty — which
  *      the type lowerings can do, deriving theirs from `typeExprSpan`, which falls
  *      back to `Span.empty` when a whole subtree has no located leaf. That
  *      degradation is silent and its symptom is the original bug.
  *
  * There is NO exemption list. An earlier draft tried to enumerate the "synthesized
  * markers that never resolve"; it was wrong (`unify`, `ho_apply`, `ListLiteral`,
  * `SetLiteral`, `TupleLiteral` all DO reach `resolveName` — measured) and could never
  * have been complete, since pattern binders put arbitrary user identifiers in the
  * same position. Locating everything leaves nothing to keep in sync.
  *
  * CONTROL, measured on each mechanism separately, because they catch different
  * mistakes:
  *
  *   * revert ONE `allocAt` in the parser (`fnOrInstOrIdent`'s bare-name arm) to
  *     `alloc`: the build FAILS — `Found: Term.Ident / Required: Term.Nameless`. There
  *     is no test to run and no coverage question to ask.
  *   * make `typeExprSpan` return `Span.empty`, i.e. supply a span that is present but
  *     useless: mechanism 1 sees NOTHING (a span was passed), and exactly ONE test
  *     fails — the corpus case below. The stdlib case stays GREEN, which is the point
  *     of having both: the stdlib never writes an arrow or tuple type in a term
  *     position, so it exercises none of `typeExprToRef`'s lowerings. An audit over
  *     the corpus we happen to ship would have missed this entirely.
  */
class ParseSpanCoverageTest extends munit.FunSuite:

  private val stdlibDir = sys.env.getOrElse("ANTHILL_STDLIB",
    System.getProperty("user.dir") + "/../stdlib")

  /** Every name-bearing term with no location, rendered as `Kind:name`. */
  private def offenders(pf: ParsedFile): List[String] =
    pf.terms.nameBearingWithoutSpan.map { id =>
      pf.terms.get(id) match
        case f: Term.Fn    => s"Fn:${pf.symbols.name(f.functor)}"
        case Term.Ref(s)   => s"Ref:${pf.symbols.name(s)}"
        case Term.Ident(s) => s"Ident:${pf.symbols.name(s)}"
        case other         => s"?:$other"
    }.toList

  test("WI-961: no stdlib file parses to a resolvable name without a position") {
    val (files, parseErrs) = EmbeddedStdlib.parseFromDir(Paths.get(stdlibDir))
    assert(parseErrs.isEmpty, s"stdlib parse errors: $parseErrs")
    assertEquals(files.length, EmbeddedStdlib.stdlibPaths.length)
    val bad = files.flatMap(offenders).toList
    assertEquals(bad.distinct.sorted, Nil,
      s"${bad.length} locationless name-bearing terms across ${files.length} stdlib files")
  }

  /** THE GRAMMAR TOUR. The stdlib is a corpus, not a grammar tour — an audit over it is
    * blind to any production it happens not to use. These are the shapes whose markers
    * were MEASURED to reach `resolveName` (WI-957) plus the binder and type forms whose
    * spans are derived rather than captured, so each one exercises a different way the
    * invariant could break.
    *
    * WI-971 lifted this out of the test below when the span-tightness audit became its
    * second reader — the two audits ask different questions of the same shapes. */
  private val sources: Seq[(String, String)] = Seq(
      // The cut sits mid-body on purpose: a TRAILING `!` is the documented `! atom`
      // ambiguity (`term` is tried before `cutGoal`, so `!` + the next line's keyword
      // parses as `not(...)`), which is a grammar quirk, not what this test is about.
      "cut/unify/ho_apply" ->
        """namespace d
          |  rule a(?x) :- !, p(?x)
          |  rule b(?x) :- let ?y = ?x
          |  rule c(?p) :- ?p(1)
          |end""".stripMargin,
      "collection literals" ->
        """namespace d
          |  rule a(?x) :- p([?x, ?x]), q({?x}), r((m: ?x, n: ?x)), s(())
          |end""".stripMargin,
      "operators + projections" ->
        """namespace d
          |  rule a(?x) :- p(?x + ?x * ?x), q(not ?x), r(-?x), s(?x.f), t(?x.(m, n))
          |end""".stripMargin,
      "expr bodies + patterns" ->
        """namespace d
          |  sort S
          |    operation f(x: S) -> S
          |      = match x
          |          case cons(h, t) -> if h then let y = t in y else lambda z -> z
          |          case nil() -> x
          |          case _ -> x
          |  end
          |end""".stripMargin,
      // These must sit in TERM position (a typed var, an instantiation argument, a
      // `let` annotation) — an operation PARAMETER type is kept as IR and never
      // lowered by the parser, so a corpus that only declares parameters exercises
      // none of `typeExprToRef` and the derived-span path goes untested. Measured:
      // with parameters alone, blanking `typeExprSpan` failed nothing.
      "arrow + tuple + effect types, lowered" ->
        """namespace d
          |  rule a(?f) :- p(?f: (S, S) -> S @ {E})
          |  rule b(?t) :- p(?t: (m: S, n: S))
          |  rule c(?k) :- p(?k: (S) -> S @ {+E, -E})
          |  rule d(?g) :- p(?g: (S) -> S @ {E :- q(?g)})
          |  rule e(?x) :- p(Foo[F = (S) -> S])
          |end""".stripMargin,
      "bounded quantification" ->
        """namespace d
          |  rule a(?xs) :- (forall ?x in ?xs: p(?x)), (some ?y in ?xs: q(?y))
          |end""".stripMargin,
  )

  test("WI-961: the surface forms the stdlib does not exercise are covered too") {
    for (label, src) <- sources do
      Parser.parse(src, s"$label.anthill") match
        case Left(errs) => fail(s"$label: parse failed: ${errs.map(_.render).mkString("; ")}")
        case Right(pf) =>
          assertEquals(offenders(pf).distinct.sorted, Nil, s"$label left names unlocated")
  }

  // ── WI-971: no span ends in trivia ───────────────────────────

  /** Every span the parse produced that ends on a whitespace character, rendered as the
    * text it brackets — declaration spans (walked through `SpanFixture`) and term spans
    * (from the store) together, because the two are captured by different code and have
    * failed differently.
    *
    * A ZERO-WIDTH span passes: it brackets no text, so it has no last character to be
    * wrong about, and `Span`'s doc lists the point diagnostics that are deliberately
    * empty.
    *
    * THERE IS NO EXCLUSION. There was exactly one — the file's LAST top-level
    * declaration, which this audit found running to end of input on its first run and
    * which WI-972 then repaired at `AnthillParserImpl.mkSpanToContent` (fastparse does
    * not rewind a skipped-trivia `~` when the input has nothing left to be reachable).
    * Deleting it is that WI's acceptance, and it is worth noting what the exclusion cost
    * while it stood: `primitives.anthill`, whose top-level braced `sort`s are the one
    * stdlib file whose last declaration does not end in a keyword, was the only file it
    * silenced — one item per file reads like nothing until it is the item that is
    * wrong. */
  private def looseEnds(pf: ParsedFile, src: String): List[String] =
    val decls = SpanFixture.allItems(pf.items).map(SpanFixture.spanOf)
      .filter(sp => sp.hasLocation && sp.end > sp.start && sp.end <= src.length)
      .filter(sp => src.charAt(sp.end - 1).isWhitespace)
      .map(sp => src.slice(sp.start, sp.end))
    decls.toList ++ pf.terms.spansEndingInWhitespace(src).map(_._2)

  test("WI-971: no stdlib file parses to a span that ends in trivia") {
    // THE SECOND MECHANISM, and the reason this file already argues for having two: the
    // `Index` shadow in `AnthillParserImpl` bans a SPELLING, so it is blind to any span
    // that ran long without mentioning `Index`. WI-970's eighth defect was exactly that
    // — fastparse's `flatMap` ran the whitespace skipper before a `Pass` continuation,
    // so EVERY `:-` rule's declaration span ended in the newline before the next
    // declaration. Three greps missed it. This assertion is spelling-blind and would
    // have failed on the first stdlib file that writes a `:-` rule, which is most of
    // them.
    //
    // CONTROL, measured both ways:
    //   * put fastparse's `flatMap` back in `ruleArrowChoice` — the WI-970 defect — and
    //     BOTH cases here fail; the first stdlib file to report is `int64`, with 5 loose
    //     spans (the audit stops at the first bad file, so that is a floor, not a total).
    //     `SpanEndTest`'s rule case catches it too, but only because someone wrote a
    //     fixture for it after the fact; this one needed no fixture at all.
    //   * IT ALREADY EARNED ITS KEEP: on its FIRST run it found WI-972 (see `looseEnds`)
    //     — a ninth site of the same class, present on `HEAD`, that no `~`-vs-`~~`
    //     reading of the productions could reach, because every capture is at the right
    //     offset and only end-of-input behaves differently. Back WI-972's `min` out and
    //     THIS case fails again, on `primitives.anthill`. The grammar-tour case below
    //     does NOT — every entry in `sources` is one `namespace … end`, and a
    //     construct closing on a keyword is tight at end of input anyway. That is the
    //     asymmetry: only a corpus contains a file whose last declaration ends in an
    //     optional, and `SpanEndTest` pins the shape once someone knows to look for it.
    //
    // THE CORPUS IS THE POINT. `DeclarationSpanTest` and `SpanEndTest` pin one span per
    // shape against a fixture someone wrote on purpose; this reads 69 files nobody wrote
    // for a span test, so it covers the combinations a fixture author would not think
    // to write — a declaration followed by a comment, by a blank line, by end-of-file.
    val resolver = FileSourceResolver(IndexedSeq(Paths.get(stdlibDir)))
    var checked = 0
    for modId <- EmbeddedStdlib.stdlibPaths do
      val src = resolver.resolve(modId).getOrElse(fail(s"cannot read stdlib $modId"))
      Parser.parse(src, modId.replace('.', '/') + ".anthill") match
        case Left(errs) => fail(s"$modId: parse failed: ${errs.map(_.render).mkString("; ")}")
        case Right(pf) =>
          checked += 1
          val loose = looseEnds(pf, src)
          assertEquals(loose, Nil, s"$modId: ${loose.length} spans end in trivia")
    // A resolver that silently found nothing would make the loop above assert over an
    // empty corpus and pass — the "it loads clean" failure this file's header names.
    assertEquals(checked, EmbeddedStdlib.stdlibPaths.length)
  }

  test("WI-971: the surface forms the stdlib does not exercise end tight too") {
    // The same audit over the grammar tour above, for the same reason it exists there:
    // the stdlib is a corpus, not a grammar tour, and a production it happens not to use
    // is unmeasured. Trailing trivia is appended to each so the check has something to
    // catch — a source that ends at its last token would pass whatever the parser did.
    for (label, src) <- sources do
      val withTrivia = src + "\n\n{- trailing -}\n"
      Parser.parse(withTrivia, s"$label.anthill") match
        case Left(errs) => fail(s"$label: parse failed: ${errs.map(_.render).mkString("; ")}")
        case Right(pf) =>
          assertEquals(looseEnds(pf, withTrivia), Nil, s"$label left a span ending in trivia")
  }

end ParseSpanCoverageTest
