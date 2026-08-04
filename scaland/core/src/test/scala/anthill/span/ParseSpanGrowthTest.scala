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
  * work, and a read-back derivation's work lands on `SimpleTermStore.spanOf`. A stopwatch
  * would measure the same thing with a machine-dependent threshold; this is exact.
  *
  * WHOSE READS (WI-991). The count belongs to THE PARSE: `SpanFixture.parseCountingSpanReads`
  * parses into a counting subclass and hands the number back with the file, taken before
  * anything else can run. It used to be a counter on `SimpleTermStore` itself, over that
  * store's whole life — so every later reader moved it (`Loader.loadAll` alone does 912
  * on a stdlib file) and the assertions below were a function of statement order. MEASURED
  * on that shape: hoisting the `fnSpans` walk above the hand-written snapshot left this
  * case GREEN with `a` at 800 rather than 700, the extra 100 being the walk. It did not
  * hide the quadratic by itself (10600 against 41000 is still ratio 3.87, over the
  * ceiling) — what it broke is the meaning of the number, and a contaminating reader is
  * free to be much larger than this one.
  *
  * WHY A RATIO AND NOT A BOUND. A parse does span reads that have nothing to do with
  * types. Two parses of the SAME shape at two depths cancel that shared overhead, and the
  * ratio is the actual claim: doubling the depth doubles the work (linear), it does not
  * quadruple it (quadratic).
  *
  * CONTROL, MEASURED — re-measured under WI-991's shape, with the walk running FIRST, and
  * unchanged by it. Restore the recursive `typeExprSpan(te)` walk and derive the arrow
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
    * The leaves are `?vars` DELIBERATELY: a `TypeExpr.Variable` carries a `TermId`, so
    * its span can only be had by ASKING the store, which is what the counter sees. A
    * `Simple` leaf carries its span on the `Name` and is read without touching the store,
    * so a chain of those would count zero either way and the control would not fire.
    * (WI-989 gave those `?var` terms a real span; it did not change WHERE the span is
    * kept, so the counter reads the same `7 * depth` — verified, not assumed.) The chain
    * still ends in the located `S`, and the `arrows` assertion checks every lowered node
    * came out positioned, which keeps this from measuring the speed of producing garbage.
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

  /** The parse, and the reads THE PARSE did — the count comes back with the file
    * (WI-991), so this test has no snapshot statement to place correctly. */
  private def parseDeep(depth: Int)(using munit.Location): (ParsedFile, Int) =
    SpanFixture.parseCountingSpanReads(deepArrowSource(depth), s"deep$depth.anthill")

  test("WI-964: a curried arrow chain lowers in one pass — span reads grow linearly") {
    val depth = 100
    val (small, a) = parseDeep(depth)
    val (large, b) = parseDeep(depth * 2)

    // The CAPABILITY first: the chain really was lowered, to one `Arrow` per written
    // `->`, and every one of them got a position. Measuring the work of a lowering that
    // did not happen — or that produced `Span.empty` — would prove nothing. BOTH depths:
    // the ratio below can only catch `b` being too LARGE, so a regression that lowers
    // FEWER nodes at 200 (a depth cutoff, a `typeExprToRef` short-circuit) would send `b`
    // toward zero and satisfy it vacuously while every check on `small` still held.
    //
    // WI-991: these WALKS READ SPANS, and they run BEFORE the assertions on `a` and `b`
    // deliberately — that placement is the ticket's acceptance, and asserting `large` at
    // all is only safe because of it. Under the old shape (a counter on `SimpleTermStore`,
    // snapshotted by hand) this ordering silently changed what was measured.
    for (file, want) <- Seq((small, depth), (large, depth * 2)) do
      val arrows = SpanFixture.fnSpans(file, "anthill.prelude.TypeExtractor.Arrow")
      assertEquals(arrows.length, want)
      assertEquals(arrows.count(!_.hasLocation), 0, "a lowered arrow came out unlocated")

    // THE CLAIM (WI-964): doubling the depth doubles the reads. 2.5 leaves room for the
    // constant per-parse overhead the two runs share; quadratic re-derivation lands at
    // 3.90. FIRST of the two, because the exact counts below would also fail on a
    // quadratic (10500, not 700) and this is the one whose message diagnoses it —
    // measured both ways round.
    assert(b <= 2.5 * a,
      s"span reads grew from $a to $b when depth doubled ($depth -> ${depth * 2}) — " +
        s"ratio ${b.toDouble / a}, expected ~2 (linear), got ~4 shape (quadratic)")

    // THE COUNT IS THE PARSE'S — WI-991's own control, and what fails when its change is
    // backed out while everything above stays green. `7 * depth` is exact: 7 reads per
    // written level (the header's "exactly 7 per level and exactly doubling"), and nothing
    // else in this method may contribute to it. Restore the counter to `SimpleTermStore`
    // and snapshot by hand after the walks above, and `a` is 800 — measured — against a
    // ratio of 1.75 that sails under the ceiling. That gap is how the erosion stayed
    // invisible, and these two lines are what close it.
    //
    // They double as the FLOOR the ratio needs: with no lower bound, `b <= 2.5 * a` is
    // satisfied vacuously by a parser that never asks the store at all — a shape someone
    // could reach by making the lowering RETURN each node's span alongside its term.
    // `typeExprToRef` argues against exactly that (a returned span is a second copy of a
    // position, free to disagree with the store's), so this failing is the intended way
    // to be sent there rather than a false alarm.
    assertEquals(a, 7 * depth, s"span reads at depth $depth are no longer the parse's alone")
    assertEquals(b, 7 * depth * 2, s"span reads at depth ${depth * 2} are no longer the parse's alone")
  }

end ParseSpanGrowthTest
