package anthill.kb

import anthill.load.{Loader, Prelude}
import anthill.parse.Parser
import munit.Assertions.{assert, fail}

/** The parse → register-prelude → loadAll test bootstrap, shared by this package's
  * suites. Extracted when WI-1053's review caught it growing a second verbatim home
  * (ScopeIdentityTest, FactsTest); a change to the load entry points now has one
  * fixture to visit.
  */
object LoadFixture:

  /** `src` loaded into a fresh KB; fails the calling test on parse or load errors. */
  def loaded(src: String, label: String)(using munit.Location): KnowledgeBase =
    val pf = Parser.parse(src, label) match
      case Right(p)   => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.render).mkString("; ")}")
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, IndexedSeq(pf))
    assert(errs.isEmpty, s"load errors: $errs")
    kb
