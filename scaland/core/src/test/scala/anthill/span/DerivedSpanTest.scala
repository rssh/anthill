package anthill.span

/** WI-989 — WHERE A DERIVED SPAN LANDS, not merely that it landed somewhere.
  *
  * A node with no token of its own — `TypeExtractor.Arrow`, a `NamedTuple` label, the
  * `named_arg` marker — takes a DERIVED span: the first located position its children can
  * offer, else the enclosing construct's. `ParseSpanCoverageTest` audits that such a span
  * is never `Span.empty`, over the stdlib and over a grammar tour, and that audit is
  * necessary. IT IS NOT SUFFICIENT, and this file exists because of the gap:
  *
  *   * A DERIVATION THAT REACHES THE LEAF and one that falls back to the whole enclosing
  *     construct are both non-empty. So locating the `?var` and literal LEAVES — half of
  *     WI-989 — is invisible to the audit: back it out and every offender list stays
  *     empty, because the fallback the other half added catches it. The spans just get
  *     worse, silently, which is the shape of the bug being fixed.
  *   * Conversely the FALLBACK is invisible to a leaf test, since a leaf-bearing type
  *     never needs it.
  *
  * So each case below is written for ONE half, and the two halves were MEASURED
  * separately over the 355-test suite:
  *
  *   * revert `varTermAt` and the four literal productions to the spanless `alloc` — the
  *     leaf half — and
  *     THREE cases here fail (`?f` for `?a`, `Project` for `"name"`, the whole strategy
  *     `tac(k: 3, j: foo)` for `3`) while EVERYTHING ELSE STAYS GREEN, `ParseSpanCoverageTest`
  *     included. That green is the finding: an audit for emptiness cannot see a span that
  *     is merely wrong.
  *   * revert `firstLocated(spans, fallback)` to `getOrElse(Span.empty)` — the fallback
  *     half — and TWO fail: the childless case here, and `ParseSpanCoverageTest`'s
  *     grammar tour. Those spans come out EMPTY rather than wrong, so the audit does see
  *     them, and neither suite subsumes the other.
  *
  * ONE PIECE IS DELIBERATELY UNPINNED, and it is worth naming rather than leaving for
  * someone to discover: `allocNamedArg`'s own fallback. Back it out alone and NOTHING
  * fails — with leaves located, every value that can reach it carries a span, so the
  * fallback is insurance against a value carrier that does not exist yet. It stays for
  * the reason `firstLocated`'s doc gives (a property of the code, not of which leaves
  * happen to be located today); no test can distinguish it until such a carrier is added.
  *
  * THE TEXT, NOT THE OFFSETS (`SpanFixture.assertSpans`): a failure that reads
  * `"?f" != "?a"` names the defect, where `21 != 24` does not.
  */
class DerivedSpanTest extends munit.FunSuite:

  test("WI-989: an arrow whose leaves are ?vars derives from the LEFTMOST leaf") {
    val src =
      """namespace d
        |  rule a(?f) :- p(?f: (?a, ?b) -> ?c)
        |end""".stripMargin
    val pf = SpanFixture.parse(src, "arrow.anthill")

    // The arrow stands for the whole written type and takes the first position that type
    // can offer — `?a`, its leftmost leaf. With `?var`s spanless it was `?f`, the typed
    // binder this type is attached to: non-empty, so the audit passed, and pointing at
    // the wrong token.
    val arrows = SpanFixture.fnSpans(pf, "anthill.prelude.TypeExtractor.Arrow")
    assertEquals(arrows.length, 1)
    SpanFixture.assertSpans(src, arrows.head, "?a")

    // THE SHARPEST FORM of the same claim, and the reason this case uses TWO parameters:
    // the positional labels `_0` and `_1` are built one per field and each takes ITS OWN
    // field's position. They can only differ if the leaves are located — with the
    // fallback alone both collapse onto `?f`, and an assertion that only checked
    // non-emptiness would see two perfectly good spans.
    SpanFixture.assertSpans(src, SpanFixture.refSpan(pf, "_0"), "?a")
    SpanFixture.assertSpans(src, SpanFixture.refSpan(pf, "_1"), "?b")
  }

  test("WI-989: a keep spec's labels derive from the literals they are keyed to") {
    // WI-763's motivating shape, and the one that made this more than tidiness: every
    // leaf is a STRING, so before literals were located the whole lowering derived from
    // nothing — including `Ref:person` and `Ref:years`, which are user-written names the
    // loader resolves by name. That is a locationless `AmbiguousSymbol` on ordinary
    // source.
    val src =
      """namespace d
        |  rule a(?x) :- p(Project[T = S, Keep = (person: "name", years: "age")])
        |end""".stripMargin
    val pf = SpanFixture.parse(src, "keep.anthill")

    SpanFixture.assertSpans(src, SpanFixture.refSpan(pf, "person"), "\"name\"")
    SpanFixture.assertSpans(src, SpanFixture.refSpan(pf, "years"), "\"age\"")
    // The tuple itself derives from its first field, transitively the first literal.
    val tuples = SpanFixture.fnSpans(pf, "anthill.prelude.TypeExtractor.NamedTuple")
    assertEquals(tuples.length, 1)
    SpanFixture.assertSpans(src, tuples.head, "\"name\"")
  }

  test("WI-989: a written type with NO child at all lands on its enclosing construct") {
    // The two shapes for which no leaf exists to derive from, so the enclosing span is
    // the only answer there is. `Foo[E = {}]` is enclosed by the NAME it parameterizes
    // (the row is that name's argument); the unit type by the binder it annotates.
    val src =
      """namespace d
        |  rule a(?x) :- p(Foo[E = {}])
        |  rule b(?u) :- p(?u: ())
        |end""".stripMargin
    val pf = SpanFixture.parse(src, "childless.anthill")

    val rows = SpanFixture.fnSpans(pf, "effects_rows")
    assertEquals(rows.length, 1)
    SpanFixture.assertSpans(src, rows.head, "Foo")
    val tuples = SpanFixture.fnSpans(pf, "anthill.prelude.TypeExtractor.NamedTuple")
    assertEquals(tuples.length, 1)
    SpanFixture.assertSpans(src, tuples.head, "?u")
  }

  test("WI-989: a named_arg marker derives from its value, else from its strategy") {
    // The same defect in a builder that has nothing to do with types — `allocNamedArg`
    // reads its VALUE's span back — which is why the fix is two changes and not one
    // change inside `typeExprToRef`.
    val src =
      """namespace d
        |  proof a
        |    by tac(k: 3, j: foo)
        |  end
        |end""".stripMargin
    val pf = SpanFixture.parse(src, "namedarg.anthill")

    val markers = SpanFixture.fnSpans(pf, "named_arg")
    assertEquals(markers.length, 2)
    // In source order: the literal value (spanless before WI-989, so this marker landed
    // at `Span.empty`), then the name value (which carried its own span all along and is
    // the control — it read the same before the fix).
    SpanFixture.assertSpans(src, markers(0), "3")
    SpanFixture.assertSpans(src, markers(1), "foo")
  }

end DerivedSpanTest
