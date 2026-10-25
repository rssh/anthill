package anthill.load

import anthill.kb.LoadFixture

/** WI-20261023-GJVVW (rustland's `wi_gjvvw_import_reaches_no_parameter_test`, whose doc
  * has the account) — a name an operation's signature declares is in scope in that
  * operation only, so no import reaches it. In rustland `import lib.{c}` bound the
  * parameter `lib.useIt.c` one scope below, on the nested-scope rung, and the goal `c(?x)`
  * answered nothing. scaland registers no symbol for an operation's parameter, so the rung
  * has nothing to land on there; these rows hold the two loaders to one answer, and pass
  * with no change to scaland's loader — there is nothing to back out. rustland's rows
  * over a sort and an operation of one name have no twin here: scaland refuses that pair
  * as a second declaration of the name.
  */
class ImportReachesNoParameterTest extends munit.FunSuite:

  private val lib = """namespace test.gjvvw.lib
                      |  import anthill.prelude.{Int64}
                      |  operation useIt(c: Int64) -> Int64 = c
                      |  fact c(1)
                      |end""".stripMargin

  private def use(ns: String, imp: String) =
    s"""namespace test.gjvvw.$ns
       |  import $imp
       |  rule r(?x) :- c(?x)
       |end""".stripMargin

  /** Solutions of `<ns>.r(?x)` over `lib` and `user` loaded together. */
  private def answers(ns: String, lib: String, user: String)(using munit.Location): Int =
    val kb = LoadFixture.loaded(IndexedSeq(LoadFixture.parsed(lib, "lib"), LoadFixture.parsed(user, "user")))
    LoadFixture.unaryAnswers(kb, s"test.gjvvw.$ns.r")

  test("GJVVW: a selective import reaches the relation, not the parameter") {
    assertEquals(answers("use", lib, use("use", "test.gjvvw.lib.{c}")), 1)
  }

  test("GJVVW: the plain import and the qualified goal reach the relation") {
    assertEquals(answers("plain", lib, use("plain", "test.gjvvw.lib.c")), 1)
    val qualified = """namespace test.gjvvw.qual
                      |  rule r(?x) :- test.gjvvw.lib.c(?x)
                      |end""".stripMargin
    assertEquals(answers("qual", lib, qualified), 1)
  }

  /** Refused in both spellings, each in the words scaland's loader has for it: a
    * selective name under a base names nothing there, and a plain import names no
    * declaration. */
  test("GJVVW: an import naming an operation's parameter is refused") {
    for (imp, refusal) <- Seq(
        "test.gjvvw.lib.useIt.{c}" -> "unresolved name 'c' in scope 'test.gjvvw.lib.useIt'",
        "test.gjvvw.lib.useIt.c" -> "unresolved import 'test.gjvvw.lib.useIt.c'")
    do
      val user = s"""namespace test.gjvvw.imp
                    |  import $imp
                    |end""".stripMargin
      val errs = LoadFixture.refusal("lib" -> lib, "imp" -> user)
      assert(errs.exists(_.contains(refusal)), s"`import $imp` should be refused with `$refusal`, got $errs")
  }

  test("GJVVW: a path to a parameter from outside its operation is refused") {
    val user = """namespace test.gjvvw.path
                 |  rule r(?x) :- test.gjvvw.lib.useIt.c(?x)
                 |end""".stripMargin
    val errs = LoadFixture.refusal("lib" -> lib, "user" -> user)
    assert(errs.exists(_.contains("unresolved name 'test.gjvvw.lib.useIt.c'")), s"got $errs")
  }
