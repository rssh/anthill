package anthill.span

import anthill.parse.ParsedFile

/** WI-964 — A LOWERED TYPE'S SPAN IS DERIVED ONCE PER NODE, NOT ONCE PER ANCESTOR.
  *
  * `AnthillParser.typeExprToRef` gives each structural lowering (`TypeExtractor.Arrow`,
  * `NamedTuple`, an `EffectExpression` chain) a DERIVED span: the first located position
  * the written type can offer. The straightforward way to write that is a recursive walk
  * of the raw `TypeExpr` — and it was written that way, which made every level re-derive
  * what the level below was about to derive again: O(n) + O(n-1) + … down a curried
  * `(A) -> (B) -> (C) -> D`. The fix builds children first and reads their spans back in
  * O(1), the two being equal by induction (see `typeExprToRef`'s doc).
  *
  * WHY A COUNTER AND NOT A CLOCK. The two forms produce IDENTICAL spans — that is the
  * whole difficulty. Nothing in the parse result differs, so the only observable is the
  * work, and `SimpleTermStore.spanReads` is where a read-back derivation's work lands.
  * A stopwatch would measure the same thing with a machine-dependent threshold; this is
  * exact.
  *
  * WHY A RATIO AND NOT A BOUND. `spanReads` counts every caller, and a parse does other
  * span reads that have nothing to do with types. Two parses of the SAME shape at two
  * depths cancel that shared overhead, and the ratio is the actual claim: doubling the
  * depth doubles the work (linear), it does not quadruple it (quadratic).
  *
  * CONTROL, MEASURED. Restore the recursive `typeExprSpan(te)` walk and derive the arrow
  * lowering's span from the raw `TypeExpr` again: the case below fails at ratio 3.90
  * against its 2.5 ceiling (10500 reads at depth 100, 41000 at 200 — where the read-back
  * form does 700 and 1400, exactly 7 per level and exactly doubling).
  * `ParseSpanCoverageTest` passes EITHER WAY — it asks what the spans ARE, and they do
  * not change — which is why this file exists rather than an assertion added there.
  * Conversely, blank the derived span and this file stays green while
  * `ParseSpanCoverageTest`'s grammar-tour case fails: the two tests cover the two ways
  * the derivation can go wrong, and neither subsumes the other.
  *
  * WHAT THIS DOES NOT CLAIM: that anything got faster. Parsing the whole stdlib reaches
  * `typeExprToRef`'s lowerings ZERO times — the corpus writes no arrow or tuple type in
  * term position (measured; the same fact `ParseSpanCoverageTest` records as the reason
  * its grammar tour exists). The quadratic was latent, and what this file buys is the
  * BOUND — a written type that does nest deeply cannot make the parser quadratic — plus
  * the pin that keeps the bound true.
  */
class ParseSpanGrowthTest extends munit.FunSuite:

  /** `rule deep(?f) :- p(?f: (?a0, ?b0) -> (?a1, ?b1) -> … -> S)` — a curried arrow
    * `depth` levels deep.
    *
    * IN TERM POSITION (a typed rule-body argument), because an operation PARAMETER type
    * is kept as IR and never lowered — a declaration corpus reaches no lowering at all
    * (`ParseSpanCoverageTest` records the same trap).
    *
    * The leaves are `?vars` DELIBERATELY: `variableType` allocates its term through the
    * spanless `alloc`, so a var's span can only be had by ASKING the store, which is
    * what the counter sees. A `Simple` leaf carries its span on the `Name` and is read
    * without touching the store, so a chain of those would count zero either way and the
    * control would not fire. The chain still ends in the located `S` so every lowered
    * node comes out with a real position — the `arrows` assertion checks that, and it is
    * what keeps this from measuring the speed of producing garbage.
    *
    * TWO params per level, so each level also exercises the multi-parameter
    * `namedTupleTypeTerm` path, which had the same defect with a further constant on top
    * (it re-derived a field's span once for the label and again inside the recursive
    * lowering of the field's type). */
  private def deepArrowSource(depth: Int): String =
    val chain = (0 until depth).map(i => s"(?a$i, ?b$i) -> ").mkString
    s"""namespace d
       |  rule deep(?f) :- p(?f: ${chain}S)
       |end""".stripMargin

  private def parseDeep(depth: Int)(using munit.Location): ParsedFile =
    SpanFixture.parse(deepArrowSource(depth), s"deep$depth.anthill")

  test("WI-964: a curried arrow chain lowers in one pass — span reads grow linearly") {
    val depth = 100
    val small = parseDeep(depth)
    val large = parseDeep(depth * 2)
    // Both counts BEFORE anything walks either file: `SpanFixture.fnSpans` below reads
    // spans itself, and a walked file's count is no longer the parse's.
    val a = small.terms.spanReads
    val b = large.terms.spanReads

    // The CAPABILITY first: the chain really was lowered, to one `Arrow` per written
    // `->`, and every one of them got a position. Measuring the work of a lowering that
    // did not happen — or that produced `Span.empty` — would prove nothing.
    val arrows = SpanFixture.fnSpans(small, "anthill.prelude.TypeExtractor.Arrow")
    assertEquals(arrows.length, depth)
    assertEquals(arrows.count(!_.hasLocation), 0, "a lowered arrow came out unlocated")

    // FLOOR: at least one read per lowered node, i.e. the span really is being read back
    // from the built children. Without it the ratio is satisfied vacuously by a parser
    // that never asks the store at all — and that is a shape someone could arrive at,
    // by making the lowering RETURN each node's span alongside its term. `typeExprToRef`
    // argues against exactly that (a returned span is a second copy of a position, free
    // to disagree with the store's), so this failing is the intended way to be sent
    // there rather than a false alarm.
    assert(a >= depth, s"only $a span reads at depth $depth — is the counter still wired?")

    // THE CLAIM: doubling the depth doubles the reads. 2.5 leaves room for the constant
    // per-parse overhead the two runs share; quadratic re-derivation lands at 3.90.
    assert(b <= 2.5 * a,
      s"span reads grew from $a to $b when depth doubled ($depth -> ${depth * 2}) — " +
        s"ratio ${b.toDouble / a}, expected ~2 (linear), got ~4 shape (quadratic)")
  }

end ParseSpanGrowthTest
