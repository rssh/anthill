package anthill.span

import anthill.parse.{Item, Parser, ParsedFile}

/** The two things every span test in this package does before it can assert anything:
  * parse a fixture, and walk the items it produced.
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
    Parser.parse(src, file) match
      case Right(pf) => pf
      case Left(errs) =>
        munit.Assertions.fail(s"parse failed: ${errs.map(_.render).mkString("; ")}")

  /** Every item in the file, flattened through the two scope-opening shapes. */
  def allItems(items: Iterable[Item]): Vector[Item] =
    items.toVector.flatMap { item =>
      item +: (item match
        case Item.NamespaceItem(ns) => allItems(ns.items)
        case Item.SortWithBodyItem(s) => allItems(s.items)
        case _ => Vector.empty)
    }

end SpanFixture
