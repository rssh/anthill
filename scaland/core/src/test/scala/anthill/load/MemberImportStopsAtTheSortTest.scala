package anthill.load

import anthill.kb.KnowledgeBase
import anthill.parse.{ParsedFile, Parser}

/** WI-20260826-NB88H (rustland's twin, same ticket) — A MEMBER IMPORT DOES NOT WALK OUT
  * OF THE SORT IT NAMES.
  *
  * `import a.b.C.{n}` resolves `n` by, among other rungs, asking the resolver for the
  * short name AT `C`'s scope ([[Loader.resolveSelectiveImport]]). That call started an
  * ORDINARY walk, so it left `C` through the enclosing link and answered out of `a.b` —
  * and out of whatever encloses THAT. Measured on the delivered rustland tree, where the
  * stdlib makes the shape visible:
  *
  *   `import anthill.prelude.Numeric.{List}` -> bound `anthill.prelude.List`, a SIBLING
  *   `import anthill.prelude.Pair.{Pair}`    -> bound `Pair` ITSELF, one level out
  *
  * THIS IS WI-1089'S RULE AT THE ONE SITE THAT NEVER APPLIED IT. `resolveRecursive`'s
  * `enclosingStopped` was applied to the edges the walk CROSSES; the selective import
  * crosses no edge, it calls the resolver AT the base scope, so the walk began unstopped.
  * [[anthill.intern.SymbolTable.resolveBelowImport]] is that same walk entered as if the
  * import edge had already been taken.
  *
  * WHAT IS DELIBERATELY NOT NARROWED is the other half of WI-1089's own sentence: a
  * `requires`, a variant exposure and the imported scope's own imports are contents of
  * the thing imported, and stay reachable. Rustland's
  * `SymbolTable::resolve_below_import` carries why converging the import onto the
  * qualified ADDRESS's population is a separate decision (a 55-site migration there).
  *
  * SCALAND HAS NO STDLIB IN THIS FIXTURE, so every row is built from user sorts — which
  * is also what keeps the rows from passing on a stdlib accident.
  *
  * WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT (put `resolveInScope` back in
  * [[Loader.resolveSelectiveImport]]) — measured over the whole suite, 2 of 515:
  *
  *   `a member import does not reach a sibling of the sort`
  *   `a member import does not rebind the sort itself`
  *
  * The other two PASS EITHER WAY, BY DESIGN. They are the over-reach controls: what
  * fails if the stop is ever applied to an edge that is not the enclosing one.
  */
class MemberImportStopsAtTheSortTest extends munit.FunSuite:

  /** A library whose sort declares its own member and `requires` another — with a
    * SIBLING sort and a sibling operation next door, reachable only by walking out. */
  private val lib =
    """namespace nb88h.lib
      |  sort Sibling
      |    entity sibling(v: Int64)
      |  end
      |  operation sibling_op(x: Int64) -> Int64
      |  sort Constrained
      |    operation constrained(x: Int64) -> Int64
      |  end
      |  sort Host
      |    requires nb88h.lib.Constrained
      |    operation own(x: Int64) -> Int64
      |  end
      |end""".stripMargin

  private def parsed(src: String, label: String)(using munit.Location): ParsedFile =
    Parser.parse(src, label) match
      case Right(p)   => p
      case Left(errs) => fail(s"parse of $label failed: ${errs.map(_.render).mkString("; ")}")

  /** The load errors a reader importing `importLine` produces. NOT `LoadFixture.loaded`,
    * which asserts the load is clean — here a refusal IS the subject. */
  private def loadErrors(importLine: String)(using munit.Location): Seq[String] =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val reader =
      s"""namespace nb88h.reader
         |  $importLine
         |  sort User
         |    entity u(v: Int64)
         |  end
         |end""".stripMargin
    Loader
      .loadAll(kb, IndexedSeq(parsed(lib, "lib.anthill"), parsed(reader, "reader.anthill")))
      .map(_.toString)
      .toSeq

  /** Scaland's refusal for this rung reads `unresolved name 'n' in scope 'a.b.C'` — the
    * NAME and the scope it was asked of, rather than rustland's re-joined path. Both say
    * the same thing; the filter is spelled for the message this implementation emits. */
  private def unresolvedImports(importLine: String)(using munit.Location): Seq[String] =
    loadErrors(importLine).filter(_.contains("unresolved name"))

  // ── THE DEFECT ───────────────────────────────────────────────────────────

  /** `Sibling` and `sibling_op` live in `nb88h.lib`, NOT in `Host`. A line naming `Host`
    * must not deliver them — and must say so at the import line, naming the path the
    * author wrote. */
  test("a member import does not reach a sibling of the sort") {
    for name <- Seq("Sibling", "sibling_op") do
      val errs = unresolvedImports(s"import nb88h.lib.Host.{$name}")
      assertEquals(errs.size, 1,
        s"`Host.{$name}` names a SIBLING of `Host` and must be refused once: $errs")
      assert(errs.head.contains(s"'$name'") && errs.head.contains("'nb88h.lib.Host'"),
        s"the refusal must name BOTH the name and the scope it was asked of: ${errs.head}")
  }

  /** The shape rustland's corpus actually carried (`import anthill.prelude.Pair.{Pair}`):
    * a sort asked for a member of its own name, answered with ITSELF from the namespace
    * one level out. */
  test("a member import does not rebind the sort itself") {
    val errs = unresolvedImports("import nb88h.lib.Host.{Host}")
    assertEquals(errs.size, 1,
      s"`Host` has no member `Host`; the answer must not be `Host` from above: $errs")
  }

  // ── THE CONTROLS (pass either way by design) ─────────────────────────────

  /** A member the sort DECLARES — the row that says the refusals above are not "member
    * imports stopped working". */
  test("control: a declared member still imports") {
    assertEquals(unresolvedImports("import nb88h.lib.Host.{own}"), Seq.empty,
      "`Host` declares `own`")
  }

  /** A member reached by `requires` — an edge this ticket deliberately leaves crossable,
    * on WI-1089's own sentence. Narrowing THAT is a separate decision. */
  test("control: a member reached by requires still imports") {
    assertEquals(unresolvedImports("import nb88h.lib.Host.{constrained}"), Seq.empty,
      "`Host requires Constrained`, so `constrained` is contents of what was imported")
  }
