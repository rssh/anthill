package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.intern.ResolveResult

/** WI-1089 (rustland's twin, same ticket) — AN IMPORT OPENS WHAT IT NAMES.
  *
  * `import a.b.C` binds the name `C`: not `a.b`, and not `C`'s members. Scaland
  * already had the first half — `processImports`' `Plain` arm writes an ALIAS and links
  * no parent, which is what §8.6's lead sentence says and what the same line means in
  * Scala, Java and Rust. Rustland spliced the target's scope in and had to be changed
  * to match; this suite is what keeps scaland from drifting back.
  *
  * THE SECOND HALF WAS SCALAND'S TOO, and this is what changed here: the parent walk
  * re-entered an imported scope's ENCLOSING chain, so `import a.b.*` also answered with
  * every name of `a` — the module above the one named. `resolveRecursive`'s
  * `enclosingStopped` stops that, and stays stopped for the rest of the path.
  *
  * WHICH TESTS FAIL WHEN IT IS BACKED OUT (drop the `enclosingStopped` conjunct in
  * `SymbolTable.resolveRecursive`): `a wildcard does not open the module around what it
  * names` — the sibling resolves. The other rows pass either way BY DESIGN: they are
  * the controls that the stop does not close what an import DID name, and does not
  * touch a link a declaration justifies.
  */
class ImportOpensWhatItNamesTest extends munit.FunSuite:

  /** A namespace with a sort that has members, and a SIBLING sort beside it — the two
    * things an import could over-deliver. */
  private val lib =
    """namespace wi1089.lib
      |  sort Neighbour
      |    entity neighbour(v: Int64)
      |  end
      |  sort Host
      |    operation op1(x: Int64) -> Int64
      |  end
      |end""".stripMargin

  private def resolvedIn(kb: KnowledgeBase, name: String, scopeQn: String): ResolveResult =
    val owner = kb.tryResolveSymbol(scopeQn)
      .getOrElse(fail(s"scope `$scopeQn` must exist — fixture drift"))
    kb.symbols.resolveInScope(name, kb.symbols.scopeOf(owner))

  private def load(reader: String)(using munit.Location): KnowledgeBase =
    LoadFixture.loaded(
      IndexedSeq(LoadFixture.parsed(lib, "lib.anthill"), LoadFixture.parsed(reader, "reader.anthill"))
    )

  test("a plain import binds the name it writes and opens nothing") {
    val kb = load(
      """namespace wi1089.plain
        |  import wi1089.lib.Host
        |  sort User
        |    entity user(v: Int64)
        |  end
        |end""".stripMargin
    )
    assert(
      resolvedIn(kb, "Host", "wi1089.plain").isInstanceOf[ResolveResult.Found],
      "the alias is what the line was written for",
    )
    assertEquals(
      resolvedIn(kb, "op1", "wi1089.plain"),
      ResolveResult.NotFound,
      "a member of the imported sort is NOT in scope through a plain import",
    )
  }

  test("a wildcard opens what it names") {
    val kb = load(
      """namespace wi1089.wild
        |  import wi1089.lib.Host.*
        |  sort User
        |    entity user(v: Int64)
        |  end
        |end""".stripMargin
    )
    assert(
      resolvedIn(kb, "op1", "wi1089.wild").isInstanceOf[ResolveResult.Found],
      "the wildcard form is how a scope's contents come in",
    )
  }

  test("a wildcard does not open the module around what it names") {
    val kb = load(
      """namespace wi1089.sibling
        |  import wi1089.lib.Host.*
        |  sort User
        |    entity user(v: Int64)
        |  end
        |end""".stripMargin
    )
    assertEquals(
      resolvedIn(kb, "Neighbour", "wi1089.sibling"),
      ResolveResult.NotFound,
      "`Neighbour` is a SIBLING of `Host` in `wi1089.lib`; the import named neither " +
        "`Neighbour` nor `wi1089.lib`, and reaching it took stepping out through " +
        "`Host`'s enclosing link",
    )
  }

  test("CONTROL: naming the module is how its contents come in") {
    val kb = load(
      """namespace wi1089.module
        |  import wi1089.lib.*
        |  sort User
        |    entity user(v: Int64)
        |  end
        |end""".stripMargin
    )
    assert(
      resolvedIn(kb, "Neighbour", "wi1089.module").isInstanceOf[ResolveResult.Found],
      "same fixture, one import changed — so the row above measures the EDGE and not " +
        "some other absence of `Neighbour`",
    )
  }

  /** An import stops the enclosing chain only where it is the edge's SOLE
    * justification. Here `requires Spec` and `import Spec.*` link the same parent, so
    * the reach `requires` gives must survive the import line beside it — an import is
    * additive, and adding one must not take a name away.
    *
    * AND IT MUST NOT DEPEND ON THE ORDER the two clauses are written in, which is what
    * the second half drives: `visited` admits a parent scope once, so a mode decided
    * from whichever inclusion was traversed first would answer differently for the two
    * spellings of the same program. Both found by `/code-review`.
    */
  test("an import beside a requires takes no name away, in either order") {
    // `Sib` sits in ANOTHER namespace than `User`, so the only route to it is out
    // through `Spec`'s enclosing chain — i.e. through the very link the two clauses
    // share. With `Sib` beside `User` the fixture would prove nothing: `User`'s own
    // enclosing namespace would answer whatever the import did.
    val twoLib =
      """namespace wi1089.two.lib
        |  sort Sib
        |    entity sib(v: Int64)
        |  end
        |  sort Spec
        |    operation op1(x: Int64) -> Int64
        |  end
        |end""".stripMargin

    def app(clauses: String): String =
      s"""namespace wi1089.two.app
         |  sort User
         |$clauses
         |    entity user(v: Int64)
         |  end
         |end""".stripMargin

    for (label, clauses) <- Seq(
           "requires first" -> "    requires wi1089.two.lib.Spec\n    import wi1089.two.lib.Spec.*",
           "import first"   -> "    import wi1089.two.lib.Spec.*\n    requires wi1089.two.lib.Spec",
         )
    do
      val kb = LoadFixture.loaded(
        IndexedSeq(
          LoadFixture.parsed(twoLib, "two-lib.anthill"),
          LoadFixture.parsed(app(clauses), s"two-$label.anthill"),
        )
      )
      assert(
        resolvedIn(kb, "Sib", "wi1089.two.app.User").isInstanceOf[ResolveResult.Found],
        s"[$label] `Sib` is reached through the `requires` link, which the import " +
          "beside it neither adds nor removes",
      )
  }

  test("CONTROL: a sort still sees the namespace it is declared in") {
    val kb = load(
      """namespace wi1089.own
        |  sort Local
        |    entity local(v: Int64)
        |  end
        |  sort User
        |    import wi1089.lib.Host.*
        |    entity user(v: Int64)
        |  end
        |end""".stripMargin
    )
    assert(
      resolvedIn(kb, "Local", "wi1089.own.User").isInstanceOf[ResolveResult.Found],
      "the stop applies BELOW an import edge, never to the asking scope's own " +
        "enclosing chain — a sort that imports something must still see its namespace",
    )
  }
