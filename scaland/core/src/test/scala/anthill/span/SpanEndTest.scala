package anthill.span

import anthill.parse.{Item, Parser, ParsedFile}
import anthill.term.{Term, TermId}

/** WI-970 — A SPAN ENDS WHERE ITS CONSTRUCT ENDS. The first reader of `end`.
  *
  * THE DEFECT THIS PINS, measured before the fix — EIGHT sites, in three shapes:
  *
  *   * FIVE captured their trailing `Index` after a whitespace-SKIPPING `~`, so `end`
  *     sat wherever the trivia after the construct ran out. Not a rounding error —
  *     `import anthill.prelude.List` followed by a blank line reported width 24 for a
  *     20-character path and an `endRow` TWO LINES below its start, and `by auto
  *     {- t -}` reported width 17 for a 4-character `auto`, with the block comment
  *     inside the strategy's span.
  *   * TWO went the other way, `mkSpan(idx, idx)` / `mkSpan(s, s)`: zero width, nothing
  *     to underline, at `operationTypeParam` and the braced-block visibility refusal.
  *   * ONE had neither spelling and could not be grepped for: `ruleArrowChoice` used
  *     fastparse's `flatMap`, which skips trivia before the continuation, and the
  *     continuation for a `:-` rule is `Pass` — so EVERY `:-` rule's declaration span
  *     ran to the start of whatever followed. Found by the declaration-end assertion
  *     this WI added to `DeclarationSpanTest`; three greps had already missed it.
  *
  * WHY IT WAS ARGUABLE AT ALL, and why the argument lost: `Span`'s doc called `end` an
  * upper bound, which costs nothing while `Span.render` prints `formatStart` only. But
  * an end that lands past a comment on a later line is not a loose bound on the
  * construct — it is a position in unrelated source. Two adjacent constructs' spans
  * OVERLAP under it (a name's span reaches to the next token's first character), so
  * the first containment or caret reader to arrive would be wrong, not merely coarse.
  *
  * WHY IT NEEDED A TEST AND NOT JUST A FIX: nothing in the suite read `end`. The
  * WI-965 control measured it — swap the two span combinators' `~~` for `~`, inflicting
  * this defect on ~30 sites at once, and all 311 tests stayed GREEN. `DeclarationSpan
  * Test`'s one width assertion (the `F` of `sort Parameterized[A, F[T]]`) sits where no
  * trivia follows the token, so it cannot see the difference either. Every fixture here
  * therefore writes DELIBERATE trivia after the construct — spaces, a line break, a
  * blank line, a block comment — because a fixture without it measures nothing.
  *
  * ONE PRODUCTION PER TEST, deliberately: munit stops a test at its first failed
  * assertion, so bundling these would let one production's regression hide the rest.
  *
  * CONTROL, both halves measured against the delivered code (321 tests):
  *
  *   * back the whole parser change out — 9 fail: the eight per-site tests below, plus
  *     `DeclarationSpanTest`'s one-line-declaration end assertion. Nothing else moves.
  *   * put a whitespace-skipping `~` back in `located` alone — 8 fail. Everything here
  *     except the rule case, whose end comes from `ruleDecl`'s own capture. Before this
  *     WI that same break failed NOTHING (WI-965's measured control), which is the hole
  *     these assertions exist to close.
  */
class SpanEndTest extends munit.FunSuite:

  private def parse(src: String): ParsedFile = SpanFixture.parse(src, "spans.anthill")

  /** THE INVARIANT: the source text the span brackets IS the construct, with nothing
    * of the trivia around it. Asserted as the TEXT rather than a width so a failure
    * shows what leaked in (`'auto   {- t -}\n'` reads as its own diagnosis, where
    * `17 != 4` does not), and so the assertion pins `start` at the same time. */
  private def assertSpans(src: String, span: Span, expected: String)(using munit.Location): Unit =
    assertEquals(src.slice(span.start, span.end), expected)

  /** The first item matching `f`, or a loud fixture-drift failure — a `collect` that
    * finds nothing would otherwise leave the test asserting over an empty list. */
  private def pick[A](pf: ParsedFile, what: String)(f: PartialFunction[Item, A])(using munit.Location): A =
    SpanFixture.allItems(pf.items).collectFirst(f)
      .getOrElse(fail(s"fixture drift: no $what in the parsed file"))

  /** The span of the first `Term.Fn` built with `functor`, or a loud fixture-drift
    * failure. Parse-time terms carry their span in the store, not in an IR node
    * (WI-957), so a term-level production is reached this way rather than by field. */
  private def termSpan(pf: ParsedFile, functor: String)(using munit.Location): Span =
    (0 until pf.terms.size).view.map(TermId.fromRaw)
      .find(id => pf.terms.get(id) match
        case f: Term.Fn => pf.symbols.name(f.functor) == functor
        case _ => false)
      .map(pf.terms.spanOf)
      .getOrElse(fail(s"fixture drift: no `$functor` term in the parsed file"))

  // ── The five that stretched over trailing trivia ──────────────

  test("WI-970: a dotted `name` ends at its last identifier, not in the line break") {
    // `demo.sub` is at end of line, so the old `~ Index` reached to line 2 col 3.
    val src =
      """namespace demo.sub
        |  fact p(x: 1)
        |end""".stripMargin
    val pf = parse(src)
    val ns = pick(pf, "namespace") { case Item.NamespaceItem(n) => n }
    assertSpans(src, ns.name.span, "demo.sub")
  }

  test("WI-970: a `simpleName` ends at its identifier, not in the space before `:`") {
    // The rule LABEL is the one `simpleName` a fixture can reach. Three spaces before
    // the `:` — the case the ticket measured at width 6 for a 3-character name.
    val src =
      """namespace demo
        |  rule lbl   :   p(?x)
        |end""".stripMargin
    val pf = parse(src)
    val rule = pick(pf, "rule") { case Item.RuleItem(r) => r }
    val label = rule.label.getOrElse(fail("fixture drift: the rule has no label"))
    assertSpans(src, label.span, "lbl")
  }

  test("WI-970: an `importPath` ends at its last segment, not two lines down") {
    // A BLANK line after the import: the old end landed at 4:3, so the path's span
    // covered the newline, the empty line and the next declaration's indent.
    val src =
      """namespace demo
        |  import anthill.prelude.List
        |
        |  fact p(x: 1)
        |end""".stripMargin
    val pf = parse(src)
    val ns = pick(pf, "namespace") { case Item.NamespaceItem(n) => n }
    val imp = ns.imports.headOption.getOrElse(fail("fixture drift: no import"))
    assertSpans(src, imp.path.span, "anthill.prelude.List")
  }

  test("WI-970: a distributive projection ends at its `)`") {
    val src =
      """namespace demo
        |  rule a(?x) :- p(?x.(m, n)   )
        |end""".stripMargin
    val pf = parse(src)
    // The segment's own span rides on the `TupleLiteral` the projection builds.
    val span = termSpan(pf, "TupleLiteral")
    assertSpans(src, span, ".(m, n)")
  }

  test("WI-970: a proof strategy ends at its name, and does not swallow a comment") {
    // THE SHARPEST CASE: the old span ran from `auto` through `{- t -}` and over the
    // line break, so a `by` strategy's span CONTAINED a comment that is not part of it.
    val src =
      """namespace demo
        |  fact p(x: 1)
        |  proof p by auto   {- t -}
        |  end
        |end""".stripMargin
    val pf = parse(src)
    val proof = pick(pf, "proof") { case Item.ProofItem(p) => p }
    val strategy = proof.strategy.getOrElse(fail("fixture drift: the proof has no `by` strategy"))
    assertSpans(src, strategy.span, "auto")
    // The RESOLVED half moves with `end` — this is what "an end two lines down" costs a
    // caret renderer, and the only assertion in the suite that reads `endRow`/`endCol`.
    assertEquals(strategy.span.endRow, strategy.span.startRow)
    assertEquals(strategy.span.endCol - strategy.span.startCol, "auto".length)
  }

  test("WI-970: a rule ends at its last goal, in both arrow directions") {
    // THE EIGHTH SITE, and the one no `~`-vs-`~~` grep could have found: `ruleArrowChoice`
    // used fastparse's `flatMap`, which runs the whitespace skipper before the
    // continuation — and the continuation for a `:-` rule is `Pass`, so the index was
    // left past the rule's text and BOTH `ruleEntry` and `ruleDecl` captured their end
    // from there. Found by the declaration-end assertion this WI added to
    // `DeclarationSpanTest`, not by inspection.
    //
    // BOTH DIRECTIONS, because the fix is `flatMapX` plus an explicit `Pass ~` in the
    // reversed branch: `:-` pins the defect, `-:` pins that asking for the trivia back
    // still works. The reversed form is written across lines, as stdlib
    // `prelude/int64.anthill` writes it — that is the spelling that breaks if the
    // explicit skip is dropped, and the stdlib's own use is a NESTED implication, which
    // is a different production and would not have caught it.
    val src =
      """namespace demo
        |  rule a(?x) :- p(?x)   {- t -}
        |  rule q(?x)
        |    -: r(?x)
        |end""".stripMargin
    val pf = parse(src)
    val rules = SpanFixture.allItems(pf.items).collect { case Item.RuleItem(r) => r }
    assertEquals(rules.length, 2, "fixture drift: expected exactly two rules")
    assertSpans(src, rules.head.span, "rule a(?x) :- p(?x)")
    assertSpans(src, rules(1).span, "rule q(?x)\n    -: r(?x)")
  }

  // ── The one that was zero-width ───────────────────────────────

  test("WI-970: an operation type parameter spans its identifier, not zero characters") {
    // `mkSpan(idx, idx)` before: the WI-850 type-param-default refusal pointed at the
    // right column with nothing under it. The START is unchanged by the fix, which is
    // why this asserts the TEXT — a start-only assertion passes either way.
    val src =
      """namespace demo
        |  sort S
        |    operation f[T   ](x: S) -> S
        |  end
        |end""".stripMargin
    val pf = parse(src)
    val op = pick(pf, "operation") { case Item.OperationItem(o) => o }
    val tp = op.typeParams.headOption.getOrElse(fail("fixture drift: the operation has no type param"))
    assertSpans(src, tp.span, "T")
  }

  test("WI-970: the braced-block visibility refusal spans the modifier it refuses") {
    // The SEVENTH site, found while fixing the six and fixed with them: the refusal
    // reported at `mkSpan(s, s)` — the declaration's start, which is the right column
    // (the modifier is the first token when present) but zero characters wide. It had
    // no test at all, so this drives the refusal as well as its span.
    val src =
      """namespace demo
        |  sort S
        |    internal operation { f(x: S) -> S }
        |  end
        |end""".stripMargin
    Parser.parse(src, "spans.anthill") match
      case Right(_) => fail("a visibility before a braced `operation { … }` block must be refused")
      case Left(errs) =>
        val err = errs.find(_.message.contains("cannot precede a braced"))
          .getOrElse(fail(s"refusal not raised; got ${errs.map(_.render).mkString("; ")}"))
        assertSpans(src, err.span, "internal")
  }

  // ── The ~30 sites that already used the combinators ───────────

  test("WI-970: the `located` / `spanOfToken` combinators keep their spans tight") {
    // WI-965 routed ~30 productions through these two, and its own control found that
    // breaking their `~~` failed NOTHING. This is that missing assertion: `let` is a
    // `spanOfToken` and the pattern binder `y` is a `located`, each written with
    // trailing spaces so a whitespace-skipping `~` would show up here.
    val src =
      """namespace demo
        |  sort S
        |    operation f(x: S) -> S
        |      = let y   = x in y
        |  end
        |end""".stripMargin
    val pf = parse(src)
    assertSpans(src, termSpan(pf, "let_expr"), "let")
    assertSpans(src, termSpan(pf, "pattern_var"), "y")
  }

end SpanEndTest
