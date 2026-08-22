package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.intern.ResolveResult

/** WI-M460D (rustland's twin, same ticket) — ADDING AN `entity` TO A SPEC MUST NOT
  * HIDE ITS OPERATIONS FROM A `requires` CALLER.
  *
  * §8.6's `exposed` set is the VARIANT-EXPOSURE link's filter: a sort that declares
  * entity constructors leaks *those names and no others* to its enclosing scope. Both
  * implementations applied it to every non-enclosing link instead — and `requires`,
  * `provides` and a wildcard import are non-enclosing too, so whether a bare member
  * name crossed a `requires` edge depended on whether the target happened to declare
  * a variant. The spec said both things in two paragraphs of one section: step 3(c)
  * filtered every non-enclosing parent, while *Variant exposure* said a sort's
  * operations "are reached via `Sort.op`, `requires`, or wildcard".
  *
  * Only the link KIND tells them apart, and `isEnclosing` cannot say it. Scaland
  * carries the writer ON the link already (WI-1074's `ScopeInclusion.origin`), so the
  * fix is one new `ImportOrigin.Exposure` and a per-INCLUSION test — an edge two
  * clauses justify is two records here, so the reaching clause's admits the name
  * whatever order they were written in.
  *
  * SCALAND HAS NO EVALUATOR, so a row asserts WHICH SYMBOL the bare name reached
  * rather than what the call returned. "It loads clean" would measure nothing: the
  * pre-fix program loads clean too — `Spec.f` simply stops being in scope, and the
  * refusal lands wherever the body is later read.
  *
  * WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT (restore
  * `parent.exposed.isEmpty || parent.exposed.contains(name)` on every non-enclosing
  * inclusion) — measured over the whole suite, 3 of 514:
  *
  *   `a requires caller reaches a variant-bearing spec's operation`
  *   `a wildcard import reaches the sort's operations too`
  *   `a sibling file's wildcard import does not lift the filter for another file`
  *     — its FIRST assertion, the writer's own reach; the two negative assertions in
  *       that row hold either way, which is why the row carries all three states.
  *
  * The other three PASS EITHER WAY, BY DESIGN: the variant-less row is the ticket's
  * other program (the two must AGREE, so a fix that broke it would satisfy the subject
  * and still be wrong), and the two exposure rows are what separate re-keying the
  * filter from deleting it.
  */
class RequiresReachesSpecMembersTest extends munit.FunSuite:

  private def resolvedIn(kb: KnowledgeBase, name: String, scopeQn: String): ResolveResult =
    val owner = kb.tryResolveSymbol(scopeQn)
      .getOrElse(fail(s"scope `$scopeQn` must exist — fixture drift"))
    kb.symbols.resolveInScope(name, kb.symbols.scopeOf(owner))

  private def assertReaches(
    kb: KnowledgeBase, name: String, scopeQn: String, expected: String
  )(using munit.Location): Unit =
    resolvedIn(kb, name, scopeQn) match
      case ResolveResult.Found(sym) =>
        assertEquals(kb.qualifiedNameOf(sym), expected,
          s"bare `$name` in `$scopeQn` must reach $expected")
      case other =>
        fail(s"bare `$name` in `$scopeQn` must resolve to $expected; got $other")

  private def specAndCaller(ns: String, specBody: String): String =
    s"""namespace $ns
       |  sort Spec
       |$specBody  operation f(x: Int64) -> Int64
       |  end
       |  sort User
       |    requires $ns.Spec
       |    entity u(n: Int64)
       |    operation g(y: Int64) -> Int64
       |  end
       |end""".stripMargin

  // ── the ticket's two programs, which must agree ──────────────────────────

  /** CONTROL, and the ticket's first program: a variant-LESS spec's `exposed` set is
    * empty, so the filter never fired. This is the arm that made the defect
    * invisible — every stdlib spec (`PartialEq`, `Ord`, `Numeric`, …) declares no
    * variants. */
  test("control: a requires caller reaches a variant-less spec's operation") {
    val kb = LoadFixture.loaded(specAndCaller("m460d.plain", ""), "plain.anthill")
    assertReaches(kb, "f", "m460d.plain.User", "m460d.plain.Spec.f")
  }

  /** THE SUBJECT. One `entity` line more than the control, nothing else changed. */
  test("a requires caller reaches a variant-bearing spec's operation") {
    val kb = LoadFixture.loaded(
      specAndCaller("m460d.variant", "    entity marker(n: Int64)\n"), "variant.anthill")
    assertReaches(kb, "f", "m460d.variant.User", "m460d.variant.Spec.f")
  }

  /** §8.6: a sort's operations "are reached via `Sort.op`, `requires`, or WILDCARD".
    * The wildcard link is non-enclosing too, so it was filtered by `exposed` exactly
    * as the `requires` link was — importing a variant-bearing sort reached its
    * constructors and hid its operations. */
  test("a wildcard import reaches the sort's operations too") {
    val wild = LoadFixture.parsed(
      """namespace m460d.wild
        |  import m460d.wildlib.Colour.*
        |  sort Reader
        |    entity r(v: Int64)
        |  end
        |end""".stripMargin, "wild.anthill")
    val kb = LoadFixture.loaded(
      IndexedSeq(
        LoadFixture.parsed(
          """namespace m460d.wildlib
            |  sort Colour
            |    entity Red(x: Int64)
            |    operation shade(n: Int64) -> Int64
            |  end
            |end""".stripMargin, "wildlib.anthill"),
        wild))
    // The asking file is NAMED, not inherited from wherever the loader left its
    // cursor: an import resolves only in the file that wrote it (WI-1074), so a row
    // about a wildcard that let the ambient cursor decide would be measuring load
    // ORDER. The other rows here involve no import and are cursor-independent.
    kb.symbols.setAskingFile(Some(kb.symbols.fileIdOf(wild)))
    assertReaches(kb, "shade", "m460d.wild", "m460d.wildlib.Colour.shade")
    kb.symbols.setAskingFile(None)
  }

  // ── the controls that keep the exposure link itself narrow ───────────────

  /** CONTROL — passes either way. §8.6's leak still happens: a bare constructor name
    * resolves in the ENCLOSING namespace. Without this row a change that severed the
    * exposure link entirely would satisfy both subjects above. */
  test("control: exposure still leaks a constructor to the enclosing scope") {
    val kb = LoadFixture.loaded(
      """namespace m460d.leak
        |  sort Colour
        |    entity Red(x: Int64)
        |    operation shade(n: Int64) -> Int64
        |  end
        |end""".stripMargin, "leak.anthill")
    assertReaches(kb, "Red", "m460d.leak", "m460d.leak.Colour.Red")
  }

  /** THE WIDENING IS THE IMPORTING FILE'S, NOT THE ADDRESS'S (WI-995 x WI-M460D).
    *
    * A wildcard import written IN the namespace that declares the variant-bearing sort
    * targets the same `(scope, parent)` pair as the exposure link. Rustland dedups its
    * inclusions into ONE record with two origins, and answering "is this edge exposure
    * only" over the raw list there let one file's import lift the `exposed` filter for
    * every other file at the address — a foreign import GRANTING a name, which is the
    * file-local rule inverted. Found by `/code-review`, and fixed there by answering
    * over the VISIBLE origins.
    *
    * Scaland cannot have that hole and this row is what says so rather than assuming
    * it: `parents` is an append-only per-write list, so the import and the exposure are
    * two records, and `originVisible(p.origin)` has already dropped the foreign one
    * before the `exposed` test runs. Driven through the same resolver seam the loader
    * uses, under an explicitly set asking file — three states, because "no file is
    * asking" must not quietly mean "every file's import is visible" either. */
  test("a sibling file's wildcard import does not lift the filter for another file") {
    val lib =
      """namespace m460d.fl
        |  sort Colour
        |    entity Red(x: Int64)
        |    operation shade(n: Int64) -> Int64
        |  end
        |end""".stripMargin
    val importerSrc =
      """namespace m460d.fl
        |  import m460d.fl.Colour.*
        |end""".stripMargin
    val readerSrc =
      """namespace m460d.fl
        |  fact present(1)
        |end""".stripMargin

    val importer = LoadFixture.parsed(importerSrc, "importer.anthill")
    val reader = LoadFixture.parsed(readerSrc, "reader.anthill")
    val kb = LoadFixture.loaded(
      IndexedSeq(LoadFixture.parsed(lib, "lib.anthill"), importer, reader))

    val ns = kb.symbols.scopeOf(kb.resolveSymbol("m460d.fl"))
    val shade = kb.resolveSymbol("m460d.fl.Colour.shade")

    kb.symbols.setAskingFile(Some(kb.symbols.fileIdOf(importer)))
    assertEquals(kb.symbols.resolveInScope("shade", ns), ResolveResult.Found(shade),
      "the file that WROTE the wildcard reaches the sort's operations")

    kb.symbols.setAskingFile(Some(kb.symbols.fileIdOf(reader)))
    assertEquals(kb.symbols.resolveInScope("shade", ns), ResolveResult.NotFound,
      "another file at the same address wrote no import and must not reach it")

    kb.symbols.setAskingFile(None)
    assertEquals(kb.symbols.resolveInScope("shade", ns), ResolveResult.NotFound,
      "no asking file must not mean every file's import is visible")
  }

  /** CONTROL — passes either way, and the row that separates re-keying the filter
    * from DELETING it. The exposure link leaks constructor names and nothing else, so
    * a bare `shade` does NOT resolve in the enclosing namespace. Delete the `exposed`
    * test rather than key it on the link and this row alone goes green, which would
    * be the defect in the other direction. */
  test("control: exposure still does not leak an operation to the enclosing scope") {
    val kb = LoadFixture.loaded(
      """namespace m460d.noleak
        |  sort Colour
        |    entity Red(x: Int64)
        |    operation shade(n: Int64) -> Int64
        |  end
        |end""".stripMargin, "noleak.anthill")
    assertEquals(
      resolvedIn(kb, "shade", "m460d.noleak"), ResolveResult.NotFound,
      "a sort's operation must not leak as a bare name to its enclosing scope")
  }
