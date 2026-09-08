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
  * touch a link a non-stopping declaration justifies.
  *
  * THE SAME STOP NOW COVERS A `requires` (WI-20260906-6BX85), which NAMES its target
  * exactly as an import does — the last row here. Backing THAT out is a separate edit:
  * drop `ImportOrigin.Requirement` from `resolveRecursive`'s `namesItsTarget`.
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
    *
    * IT USED TO ASSERT THIS ON `Sib`, a SIBLING of the target — the reach WI-1089 left a
    * `requires` and WI-20260906-6BX85 took away. The row is restated on the spec's own
    * MEMBER; `Sib`'s new answer is the row below.
    *
    * AND THAT REWRITE MADE IT INERT FOR THE `forall`: `op1` is a LOCAL of `Spec`, and
    * since 6BX85 both writers of this edge stop the chain anyway. MEASURED by
    * `/code-review` over the whole suite — flipping `namesItsTarget`'s `forall` to
    * `exists` moved ZERO rows. What this row still says is the ADDITIVE one (an import
    * beside a `requires` takes no name away, in either order); the quantifier is driven
    * by "a requires on the enclosing sort does not stop the chain" below.
    */
  test("an import beside a requires takes no name away, in either order") {
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
        resolvedIn(kb, "op1", "wi1089.two.app.User").isInstanceOf[ResolveResult.Found],
        s"[$label] `op1` is reached through the `requires` link, which the import " +
          "beside it neither adds nor removes",
      )
  }

  /** WI-20260906-6BX85 (rustland's twin, same ticket) — A `requires` OPENS THE SPEC IT
    * NAMES, AND NOT THE MODULE AROUND IT.
    *
    * `Sib` sits in ANOTHER namespace than `User`, so the only route to it is out through
    * `Spec`'s enclosing chain — the hop `requires wi1089.two.lib.Spec` never asked for.
    * The rule is WI-1089's read one clause over: what was NAMED is in scope, the module
    * around it is not. Rustland measured the cost of the old reading — 78 of the 79
    * one-segment `anthill.prelude` names shadowable at a consumer of one prelude spec.
    *
    * FAILS IF `ImportOrigin.Requirement` is dropped from `resolveRecursive`'s
    * `namesItsTarget`, or if `Loader.processRequires` stops passing it: `Sib` is Found
    * again. MEASURED by doing it, over the whole suite: exactly ONE row of 540 moves,
    * this one — every other row here, `MemberImportStopsAtTheSortTest` and
    * `RequiresReachesSpecMembersTest` included, passes either way. (Two rows of the 540
    * are red BEFORE and AFTER: `BootstrapTest`'s cross-package `requires Ring` pair,
    * which is scaland codegen and not name resolution.)
    *
    * The MEMBER arm passes either way BY DESIGN — it is what fails if the stop is
    * widened from the enclosing link to the `requires` edge itself.
    */
  test("a requires does not open the module around the spec it names") {
    val twoLib =
      """namespace bx85.two.lib
        |  sort Sib
        |    entity sib(v: Int64)
        |  end
        |  sort Spec
        |    operation op1(x: Int64) -> Int64
        |  end
        |end""".stripMargin
    val app =
      """namespace bx85.two.app
        |  sort User
        |    requires bx85.two.lib.Spec
        |    entity user(v: Int64)
        |  end
        |end""".stripMargin
    val kb = LoadFixture.loaded(
      IndexedSeq(
        LoadFixture.parsed(twoLib, "bx85-lib.anthill"),
        LoadFixture.parsed(app, "bx85-app.anthill"),
      )
    )
    assertEquals(
      resolvedIn(kb, "Sib", "bx85.two.app.User"),
      ResolveResult.NotFound,
      "`requires bx85.two.lib.Spec` names ONE sort; `Sib` is its sibling and the clause " +
        "named neither it nor the namespace holding both",
    )
    assert(
      resolvedIn(kb, "op1", "bx85.two.app.User").isInstanceOf[ResolveResult.Found],
      "CONTROL: the spec's own member is what a `requires` is for, and is untouched",
    )
  }

  /** WI-20260906-6BX85 — TWO WRITERS ON ONE EDGE MUST NOT CANCEL, and this is the only
    * row that says so.
    *
    * `resolveRecursive`'s `namesItsTarget` asks `forall` over the inclusions reaching one
    * parent: the chain is stopped only where EVERY writer of the edge stops it. The row
    * above used to drive that with `requires Spec` beside `import Spec.*`; since this
    * ticket BOTH of those stop, so that pair answers `forall` and `exists` alike.
    * MEASURED before this row was written: flipping `forall` to `exists` moved ZERO of
    * the 540 tests.
    *
    * THE PAIR THAT STILL DISCRIMINATES is an edge that is the ENCLOSING link and a
    * `requires` at once. `sort Outer { sort Inner { requires Outer } }` appends two
    * `ScopeInclusion`s for one parent — `(Outer, isEnclosing = true, Declaration)` and
    * `(Outer, isEnclosing = false, Requirement)`. Under `forall` the `Declaration` keeps
    * the chain and `Inner` still sees its own namespace; under `exists` the `requires`
    * stops it and `Inner` loses `Shared` and everything above.
    *
    * Rustland's twin is
    * `wi_6bx85_requires_opens_the_spec_test::a_requires_on_the_enclosing_sort_is_not_a_stop`.
    */
  test("a requires on the enclosing sort does not stop the chain") {
    val src =
      """namespace bx85.nested
        |  sort Shared
        |    entity shared(v: Int64)
        |  end
        |  sort Outer
        |    operation outer_op(x: Int64) -> Int64
        |    sort Inner
        |      requires Outer
        |      entity inner(v: Int64)
        |    end
        |  end
        |end""".stripMargin
    val kb = LoadFixture.loaded(IndexedSeq(LoadFixture.parsed(src, "bx85-nested.anthill")))
    assert(
      resolvedIn(kb, "Shared", "bx85.nested.Outer.Inner").isInstanceOf[ResolveResult.Found],
      "the `(Inner, Outer)` edge is the ENCLOSING link AND a `requires`; one writer that " +
        "keeps the chain keeps it, so `Inner` still reaches its own namespace",
    )
    assert(
      resolvedIn(kb, "outer_op", "bx85.nested.Outer.Inner").isInstanceOf[ResolveResult.Found],
      "CONTROL: what the `requires` itself brings is untouched",
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
