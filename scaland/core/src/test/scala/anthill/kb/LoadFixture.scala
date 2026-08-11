package anthill.kb

import anthill.load.{Loader, Prelude}
import anthill.parse.{Parser, ParsedFile}
import munit.Assertions.{assert, fail}

/** The parse → register-prelude → loadAll test bootstrap, shared by this package's
  * suites. Extracted when WI-1053's review caught it growing a second verbatim home
  * (ScopeIdentityTest, FactsTest); a change to the load entry points now has one
  * fixture to visit. WI-1074 split it into [[parsed]] + the multi-file [[loaded]], so
  * a suite that needs the `ParsedFile` instances themselves (file identity is the
  * INSTANCE) composes the same two steps instead of growing a third home.
  */
object LoadFixture:

  /** `src` parsed under `label` (the file name spans carry); fails the calling test on
    * parse errors. */
  def parsed(src: String, label: String)(using munit.Location): ParsedFile =
    Parser.parse(src, label) match
      case Right(p)   => p
      case Left(errs) => fail(s"parse of $label failed: ${errs.map(_.render).mkString("; ")}")

  /** The given files loaded, in order, into a fresh KB; fails the calling test on load
    * errors. */
  def loaded(files: IndexedSeq[ParsedFile])(using munit.Location): KnowledgeBase =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, files)
    assert(errs.isEmpty, s"load errors: $errs")
    kb

  /** `src` loaded into a fresh KB; fails the calling test on parse or load errors. */
  def loaded(src: String, label: String)(using munit.Location): KnowledgeBase =
    loaded(IndexedSeq(parsed(src, label)))
