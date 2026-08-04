package anthill.span

import anthill.parse.{Item, Parser, ParsedFile, SimpleTermStore}
import anthill.term.{Term, TermId}

/** What every span test in this package does before it can assert anything: parse a
  * fixture, walk the items it produced, find the one it is about, and compare a span
  * against the source text.
  *
  * WI-970: extracted when `SpanEndTest` became the SECOND copy of both. `allItems` is
  * the one that had to move — it enumerates the scope-opening `Item` shapes, so a third
  * such shape means updating every copy, and the copy that is missed does not fail: it
  * silently stops descending, and the test that depended on it reports the construct as
  * missing from the fixture. That reads as fixture drift and points nowhere near the
  * stale walker.
  *
  * An OBJECT and not a base trait: these are file-level utilities with no per-suite
  * state, and munit suites in this repo extend `munit.FunSuite` directly (there is no
  * scaland test base class to hang them on, and inventing one for two functions would
  * be the larger change).
  */
private[span] object SpanFixture:

  /** Parse or fail with the rendered errors — a fixture that stopped parsing must say
    * so as a test failure, not as a `None` the caller then asserts over. */
  def parse(src: String, file: String)(using munit.Location): ParsedFile =
    parseInto(src, file, SimpleTermStore())

  private def parseInto(src: String, file: String, terms: SimpleTermStore)
                       (using munit.Location): ParsedFile =
    Parser.parseInto(src, file, terms) match
      case Right(pf) => pf
      case Left(errs) =>
        munit.Assertions.fail(s"parse failed: ${errs.map(_.render).mkString("; ")}")

  /** A store that counts what [[SimpleTermStore.spanOf]] is asked — the observable
    * `ParseSpanGrowthTest` measures, living in the test tree where it belongs (WI-991).
    * The production store keeps no counter, so nothing on the loader's path writes one. */
  private final class CountingTermStore extends SimpleTermStore:
    var spanReads = 0
    override def spanOf(id: TermId): Span =
      spanReads += 1
      super.spanOf(id)

  /** A parse, and the number of span reads THE PARSE did (WI-991).
    *
    * The count is taken HERE, at the one moment it means "the parse's work", and handed
    * back with the file — so no later reader can move it and no statement order in a
    * caller can change what it measures. That is the whole point: the caller is free to
    * walk the file first (this fixture's own [[fnSpans]] reads spans, and so does the
    * loader), and the number it was given still describes the parse.
    *
    * Before this, the counter lived on `SimpleTermStore` over its whole life and the
    * caller snapshotted it by hand. MEASURED on that shape: hoisting the `fnSpans` walk
    * above the snapshot — an ordinary readability edit — left `ParseSpanGrowthTest` green
    * while its `a` moved from 700 to 800, the extra 100 being the walk's own reads.
    *
    * ONLY a reader of THE SAME STORE can do that, which is the rule worth carrying away:
    * the loader reads spans too, but it never touched this test's stores — the growth
    * fixture loads nothing. (For scale, a counting store over the whole stdlib measures
    * 912 loader reads across all 58 files, 97 in the largest single one, and ZERO at
    * parse time — the corpus writes no lowered type in term position.) */
  def parseCountingSpanReads(src: String, file: String)(using munit.Location): (ParsedFile, Int) =
    val terms = CountingTermStore()
    val pf = parseInto(src, file, terms)
    (pf, terms.spanReads)

  /** Every item in the file, flattened through the two scope-opening shapes. */
  def allItems(items: Iterable[Item]): Vector[Item] =
    items.toVector.flatMap { item =>
      item +: (item match
        case Item.NamespaceItem(ns) => allItems(ns.items)
        case Item.SortWithBodyItem(s) => allItems(s.items)
        case _ => Vector.empty)
    }

  /** The first item matching `f`, or a loud fixture-drift failure — a `collect` that
    * finds nothing would otherwise leave the test asserting over an empty list.
    *
    * WI-971 moved this here from `SpanEndTest` for the reason the header gives: it
    * became the THIRD and FOURTH copy when `DeclarationSpanTest` grew cases for the two
    * shapes the line-anchored helpers cannot reach. */
  def pick[A](pf: ParsedFile, what: String)(f: PartialFunction[Item, A])(using munit.Location): A =
    allItems(pf.items).collectFirst(f)
      .getOrElse(munit.Assertions.fail(s"fixture drift: no $what in the parsed file"))

  /** The spans of every `Term.Fn` built with `functor`, in store order.
    *
    * Parse-time terms carry their span in the STORE, not in an IR node (WI-957), so a
    * term-level production is reached this way rather than by field — which is what
    * makes this different from [[spanOf]] above, and why both live here.
    *
    * WI-964 made it the second reader: `SpanEndTest` wants one shape's span, and
    * `ParseSpanGrowthTest` wants every arrow a deep type lowered to. Same reason
    * [[allItems]] moved here.
    *
    * This WALK READS SPANS, and since WI-991 that is no longer a caller's problem: a
    * count from [[parseCountingSpanReads]] was taken when its parse returned, so walking
    * the file here cannot reach it. The warning this doc used to carry — take the count
    * from a file nothing has walked yet — was an instruction the compiler could not
    * enforce, and `ParseSpanGrowthTest` now walks BEFORE it asserts, on purpose. */
  def fnSpans(pf: ParsedFile, functor: String): IndexedSeq[Span] =
    (0 until pf.terms.size).map(TermId.fromRaw).flatMap { id =>
      pf.terms.get(id) match
        case f: Term.Fn if pf.symbols.name(f.functor) == functor => Some(pf.terms.spanOf(id))
        case _                                                   => None
    }

  /** THE INVARIANT every test in this package is about: the source text the span
    * brackets IS the construct, with nothing of the trivia around it.
    *
    * Asserted as the TEXT rather than a width so a failure shows what leaked in
    * (`'auto   {- t -}\n'` reads as its own diagnosis, where `17 != 4` does not), and so
    * the assertion pins `start` at the same time. */
  def assertSpans(src: String, span: Span, expected: String)(using munit.Location): Unit =
    munit.Assertions.assertEquals(src.slice(span.start, span.end), expected)

  /** The span an `Item` was written over.
    *
    * EXHAUSTIVE, and a shape it does not know FAILS — because its second caller is an
    * audit (`ParseSpanCoverageTest`) that walks a whole corpus rather than naming one
    * construct. A `case _ => Span.empty` default would let a new declaration shape opt
    * itself out of that audit silently, which is the failure mode the audit exists for.
    * The shapes below are exactly those `AnthillParserImpl.declaration` can yield; the
    * rest of the `Item` enum belongs to the todo-domain IR this parser does not build.
    *
    * `ImportItem` is the one shape with no span of its own — `Import` carries only its
    * path — so it answers with the path's, which is the span `importPath` captures and
    * WI-970 repaired. */
  def spanOf(item: Item)(using munit.Location): Span = item match
    case Item.NamespaceItem(x)      => x.span
    case Item.SortWithBodyItem(x)   => x.span
    case Item.AbstractSortItem(x)   => x.span
    case Item.EntityItem(x)         => x.span
    case Item.FactItem(x)           => x.span
    case Item.ConstItem(x)          => x.span
    case Item.ConstraintItem(x)     => x.span
    case Item.RuleItem(x)           => x.span
    case Item.RuleBlockItem(x)      => x.span
    case Item.OperationItem(x)      => x.span
    case Item.OperationBlockItem(x) => x.span
    case Item.RequiresDeclItem(x)   => x.span
    case Item.ProvidesClauseItem(x) => x.span
    case Item.ProvidesBlockItem(x)  => x.span
    case Item.ProofItem(x)          => x.span
    case Item.ImportItem(x)         => x.path.span
    case other => munit.Assertions.fail(s"no span reader for $other — add one when the shape is added")

end SpanFixture
