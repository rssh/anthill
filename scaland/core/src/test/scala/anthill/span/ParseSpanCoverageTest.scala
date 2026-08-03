package anthill.span

import anthill.load.EmbeddedStdlib
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

  test("WI-961: the surface forms the stdlib does not exercise are covered too") {
    // The stdlib is a corpus, not a grammar tour — the audit above is blind to any
    // production it happens not to use. These are the shapes whose markers were
    // MEASURED to reach `resolveName` (WI-957) plus the binder and type forms whose
    // spans are derived rather than captured, so each one exercises a different way
    // the invariant could break.
    val sources = Seq(
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
    for (label, src) <- sources do
      Parser.parse(src, s"$label.anthill") match
        case Left(errs) => fail(s"$label: parse failed: ${errs.map(_.render).mkString("; ")}")
        case Right(pf) =>
          assertEquals(offenders(pf).distinct.sorted, Nil, s"$label left names unlocated")
  }

end ParseSpanCoverageTest
