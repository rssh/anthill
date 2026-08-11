package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.intern.ResolveResult
import anthill.term.{Term, Literal, Var}
import anthill.resolve.SearchStream

/** WI-1074 (rustland WI-995's twin) — an import is spent in the file that lists it.
  *
  * An import writes into a table keyed by the ADDRESS (`ScopeId`), and two files can
  * write one address (`namespace demo` in each) — `SymbolTable.define` merges by short
  * name, so the second file's block IS the first file's scope. Before this WI, one
  * file's import therefore changed how a bare name resolved in a file it had never
  * seen. The rule (WI-995, user decision 2026-08-04): an import resolves ONLY in the
  * file whose text lists it. Rustland measured the corpus cost of the rule at ZERO and
  * landed it directly; this suite inherits that decision and drives the rule itself —
  * scaland has no counterfactual audit to port.
  *
  * WHICH TESTS FAIL WHEN THE FIX IS BACKED OUT (make `SymbolTable.originVisible`
  * return `true`): the fixture-B, fixture-D, wildcard-D, two-writer and pass-2-seam
  * tests — verified. Fixture A (import and reader in ONE file) and fixture C (import
  * in a nested scope, read from the enclosing one) pass either way BY DESIGN: A is the
  * behaviour the rule preserves, and C names the pre-existing reach of an import — the
  * address, not the enclosing text — which the rule does not widen. The mint-parity
  * test also passes either way, for the pass-ordering reason its own comment states;
  * the recency control inside the two-writer test fails against a variant defect
  * instead (an `addImport` that drops a repeated write rather than moving it last).
  *
  * Every fixture drives RESOLUTION, not loading-clean: the imported name is a
  * rule-introduced predicate (the WI-295 deferred-import path, so the pass-4 retry's
  * provenance is on trial too), and the assertion is the SOLUTION VALUES of a driver
  * rule whose body reads the bare name — which fact answered says which symbol the
  * body goal captured. A miss does not error in scaland (`resolveName` degrades to an
  * unqualified intern), so "0 solutions" is the observable shape of "not yours".
  */
class ImportFileLocalityTest extends munit.FunSuite:

  private def loaded(files: (String, String)*)(using munit.Location): KnowledgeBase =
    LoadFixture.loaded(files.map(LoadFixture.parsed).toIndexedSeq)

  /** All Int solutions of `qualifiedRule(?x)`, sorted. The empty list is a real
    * verdict ("the body goal bound a functor with no clauses"), so the driver symbol
    * itself is asserted separately — a vanished RULE must not read as a proven miss. */
  private def driveValues(kb: KnowledgeBase, qualifiedRule: String)(using munit.Location): List[Long] =
    val driveSym = kb.tryResolveSymbol(qualifiedRule)
      .getOrElse(fail(s"driver `$qualifiedRule` must be registered — fixture drift"))
    val vid = kb.freshVar(kb.intern("x"))
    val query = kb.alloc(Term.Fn(driveSym, IArray(kb.alloc(Term.Var(Var.Global(vid)))), IArray.empty))
    SearchStream.resolve(kb, query).allSolutions(kb).map { sol =>
      sol.subst.resolve(vid).map(kb.getTerm) match
        case Some(Term.Const(Literal.IntLit(v))) => v
        case other => fail(s"expected an Int binding for $qualifiedRule, got $other")
    }.toList.sorted

  /** `lib.f` answers 1, `other.f` answers 2 — the VALUE names the symbol the reader's
    * body goal captured, which is the whole assertion everywhere below. */
  private val lib = """namespace lib
                      |  fact base_l(1)
                      |  rule f(?x) :- base_l(?x)
                      |end""".stripMargin
  private val other = """namespace other
                        |  fact base_o(2)
                        |  rule f(?x) :- base_o(?x)
                        |end""".stripMargin

  /** Fixture A — the CONTROL: import and reader in ONE file. Passes with the fix and
    * without it by design; what it pins is that the rule COSTS this fixture nothing. */
  test("WI-1074 A: an import read in its own file keeps working") {
    val main = """namespace demo
                 |  namespace Rec
                 |    import lib.{f}
                 |    rule drive(?x) :- f(?x)
                 |  end
                 |end""".stripMargin
    val kb = loaded(lib -> "lib.anthill", main -> "main.anthill")
    assertEquals(driveValues(kb, "demo.Rec.drive"), List(1L))
  }

  /** Fixture B — a separate file writes the SAME nested address with its own import.
    * The reader's bare `f` must stay ITS file's `lib.f`; backed out, the last import
    * write wins the address and hands the reader `other.f`, flipping the value to 2. */
  test("WI-1074 B: a foreign file's import at the same address does not re-bind an unedited body") {
    val main = """namespace demo
                 |  namespace Rec
                 |    import lib.{f}
                 |    rule drive(?x) :- f(?x)
                 |  end
                 |end""".stripMargin
    val foreign = """namespace demo
                    |  namespace Rec
                    |    import other.{f}
                    |  end
                    |end""".stripMargin
    val kb = loaded(
      lib -> "lib.anthill", other -> "other.anthill",
      main -> "main.anthill", foreign -> "foreign.anthill")
    assertEquals(driveValues(kb, "demo.Rec.drive"), List(1L))
  }

  /** Fixture C — the ticket's reach-namer, and the second by-design control: an import
    * in a NESTED namespace was never visible to the enclosing scope, in the same file
    * or any other. The rule narrows WHO sees an import, not WHERE it reaches. */
  test("WI-1074 C: an import in a nested scope does not leak outward (unchanged)") {
    val main = """namespace demo2
                 |  namespace Inner
                 |    import lib.{f}
                 |  end
                 |  rule drive2(?x) :- f(?x)
                 |end""".stripMargin
    val kb = loaded(lib -> "lib.anthill", main -> "main.anthill")
    assertEquals(driveValues(kb, "demo2.drive2"), Nil)
  }

  /** Fixture D — the ticket's placing fixture: a SIBLING `namespace demo` block in
    * another file, nothing but an import in it. The reader never wrote an import, so
    * its bare `f` binds nothing; backed out it binds `lib.f` and answers 1. */
  test("WI-1074 D: an import in a sibling file's block at the same address is not the reader's") {
    val reader = """namespace demo
                   |  rule drive(?x) :- f(?x)
                   |end""".stripMargin
    val importer = """namespace demo
                     |  import lib.{f}
                     |end""".stripMargin
    val kb = loaded(lib -> "lib.anthill", reader -> "reader.anthill", importer -> "importer.anthill")
    assertEquals(driveValues(kb, "demo.drive"), Nil)
  }

  /** Fixture D via WILDCARD — the second producer. A wildcard import writes a PARENT
    * LINK, not an alias, and the two are suppressed at different points of the walk
    * (the alias at step 1b, the link at the parent filter); a suite exercising only
    * the alias path would leave half the rule unproven. */
  test("WI-1074 D-wildcard: a foreign file's wildcard import is not the reader's either") {
    val reader = """namespace demo
                   |  rule drive(?x) :- f(?x)
                   |end""".stripMargin
    val importer = """namespace demo
                     |  import lib.*
                     |end""".stripMargin
    val kb = loaded(lib -> "lib.anthill", reader -> "reader.anthill", importer -> "importer.anthill")
    assertEquals(driveValues(kb, "demo.drive"), Nil)
  }

  /** THE HOLE THE RULE IS ABOUT, at its sharpest (rustland's two-writer control): two
    * files import DIFFERENT symbols under ONE name into ONE address. Each file must
    * read its own — which is why the rule is keyed on the SYMBOL, not the name. A
    * name-keyed check ("did some visible origin write an entry under this name?")
    * answers yes for BOTH files and hands each the map's winner, so one file's `g`
    * becomes the other's, decided by load order. Driven in both orders because the
    * defect is load-order dependent: one order alone would pass on the winner's side
    * and prove nothing.
    */
  test("WI-1074 two-writer: two files importing one name each read their own symbol") {
    val libs = """namespace liba
                 |  fact base_a(10)
                 |  rule g(?x) :- base_a(?x)
                 |end
                 |namespace libb
                 |  fact base_b(20)
                 |  rule g(?x) :- base_b(?x)
                 |end""".stripMargin
    val readsA = """namespace demo
                   |  import liba.{g}
                   |  rule drive_a(?x) :- g(?x)
                   |end""".stripMargin
    val readsB = """namespace demo
                   |  import libb.{g}
                   |  rule drive_b(?x) :- g(?x)
                   |end""".stripMargin

    // CONTROL: each file alone reads its own import, so a failure below is about the
    // two COEXISTING, not about either fixture.
    assertEquals(driveValues(loaded(libs -> "libs.anthill", readsA -> "reads_a.anthill"), "demo.drive_a"), List(10L))
    assertEquals(driveValues(loaded(libs -> "libs.anthill", readsB -> "reads_b.anthill"), "demo.drive_b"), List(20L))

    val ab = loaded(libs -> "libs.anthill", readsA -> "reads_a.anthill", readsB -> "reads_b.anthill")
    assertEquals(driveValues(ab, "demo.drive_a"), List(10L), "A then B: file A must read the `g` IT imported")
    assertEquals(driveValues(ab, "demo.drive_b"), List(20L), "A then B: file B must read the `g` IT imported")

    val ba = loaded(libs -> "libs.anthill", readsB -> "reads_b.anthill", readsA -> "reads_a.anthill")
    assertEquals(driveValues(ba, "demo.drive_a"), List(10L), "B then A: file A must read the `g` IT imported")
    assertEquals(driveValues(ba, "demo.drive_b"), List(20L), "B then A: file B must read the `g` IT imported")

    // IN-FILE RECENCY, the WI-1074-review counterexample to a dropped repeat: one file
    // re-imports `g` back to its FIRST target, and the textually last import must win —
    // exactly what the old one-slot map guaranteed. An `addImport` that DROPS the
    // repeated (origin, sym) write instead of moving it last leaves `libb.g` newest and
    // answers 20; the fix and the pre-rule map both answer 10, so this control fails
    // only against that variant defect.
    val reimports = """namespace demo9
                      |  import liba.{g}
                      |  import libb.{g}
                      |  import liba.{g}
                      |  rule drive_r(?x) :- g(?x)
                      |end""".stripMargin
    val re = loaded(libs -> "libs.anthill", reimports -> "reimports.anthill")
    assertEquals(driveValues(re, "demo9.drive_r"), List(10L),
      "the textually LAST import of a name wins within its own file")
  }

  /** WHAT THE MINT MINTS IS ADDRESS-SCOPED — rustland parity pinned, because the
    * composition reads like a leak until the two rules are held apart. File B DECLARES
    * `rule f` at the shared address; pass 3 mints `demo.f`, and that minted functor is
    * a DECLARATION at the address — declarations merge across files by design, so file
    * A's bare `f` binds the local `demo.f` over A's own import, exactly as it would if
    * the rule were written in A's file (locals precede imports; the file-local rule
    * narrows who sees an IMPORT, never what is declared). Rustland answers 3 on these
    * fixtures in both load orders — verified against the delivered WI-995,
    * `anthill query`.
    *
    * PASSES WITH THE FIX AND WITHOUT IT — verified, and for a reason worth keeping:
    * A's `import lib.{f}` names a rule-introduced predicate, so its alias is DEFERRED
    * to pass 4 (WI-295) and does not exist yet when pass 3's mint guard asks whether
    * `f` denotes — the mint happens on pass ordering, before origin visibility gets a
    * say. What this test pins is the SEMANTICS (and its rust parity), against a future
    * where the guard runs late or the deferral disappears and B's head would capture
    * A's import, polluting `lib.f` with B's clause (drive would answer {1, 3}). */
  test("WI-1074 mint parity: a foreign file's rule head does not capture this file's import") {
    val declarer = """namespace demo
                     |  fact base_f(3)
                     |  rule f(?x) :- base_f(?x)
                     |end""".stripMargin
    val importer = """namespace demo
                     |  import lib.{f}
                     |  rule drive(?x) :- f(?x)
                     |end""".stripMargin
    val kb = loaded(lib -> "lib.anthill", importer -> "importer.anthill", declarer -> "declarer.anthill")
    assertEquals(driveValues(kb, "demo.drive"), List(3L),
      "a rule-head declaration at the address is address-scoped and shadows the import — rust parity")
  }

  /** The pass-2 DIRECT path (a sort resolves at scan, no WI-295 deferral), driven
    * through the resolver seam the loader itself uses: `resolveInScope` under an
    * explicitly set asking file. Also pins the cursor's third state — NO asking file
    * sees no file's import, because "nothing is asking" must not quietly mean
    * "everything is visible". */
  test("WI-1074 pass-2 seam: a sort import is visible to its writer, no one else, and no-file sees none") {
    val lib2 = """namespace lib2
                 |  sort Thing
                 |    entity Mk(v: Int64)
                 |  end
                 |end""".stripMargin
    val importerSrc = """namespace demo3
                        |  import lib2.{Thing}
                        |end""".stripMargin
    val readerSrc = """namespace demo3
                      |  fact present(1)
                      |end""".stripMargin

    val importer = LoadFixture.parsed(importerSrc, "importer.anthill")
    val reader = LoadFixture.parsed(readerSrc, "reader.anthill")
    val kb = LoadFixture.loaded(IndexedSeq(LoadFixture.parsed(lib2, "lib2.anthill"), importer, reader))

    val demoScope = kb.symbols.scopeOf(kb.resolveSymbol("demo3"))
    val thing = kb.resolveSymbol("lib2.Thing")

    kb.symbols.setAskingFile(Some(kb.symbols.fileIdOf(importer)))
    assertEquals(kb.symbols.resolveInScope("Thing", demoScope), ResolveResult.Found(thing),
      "the writer's own text must see its import")

    kb.symbols.setAskingFile(Some(kb.symbols.fileIdOf(reader)))
    assertEquals(kb.symbols.resolveInScope("Thing", demoScope), ResolveResult.NotFound,
      "another file at the same address must not")

    kb.symbols.setAskingFile(None)
    assertEquals(kb.symbols.resolveInScope("Thing", demoScope), ResolveResult.NotFound,
      "no asking file must not mean every import is visible")
  }
