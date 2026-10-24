package anthill.kb

import anthill.load.{Loader, Prelude}
import anthill.parse.{Parser, ParsedFile}
import anthill.resolve.SearchStream
import anthill.term.{Literal, Term, Var}
import munit.Assertions.{assert, fail}

/** The parse → register-prelude → loadAll test bootstrap, shared by this package's
  * suites. Extracted when WI-1053's review caught it growing a second verbatim home
  * (ScopeIdentityTest, FactsTest); a change to the load entry points now has one
  * fixture to visit. WI-1074 split it into [[parsed]] + the multi-file [[loaded]], so
  * a suite that needs the `ParsedFile` instances themselves (file identity is the
  * INSTANCE) composes the same two steps instead of growing a third home.
  */
object LoadFixture:

  /** ERF7T: an absolute operator target must exist; small loader fixtures
    * previously relied on an unresolved bare connective. These declarations supply
    * identities only, without pretending Scala implements their control semantics. */
  def registerKernel(kb: KnowledgeBase)(using munit.Location): Unit =
    val file = parsed("""namespace anthill.kernel
      |operation unify(a: Int64, b: Int64) -> Bool
      |operation struct_eq(a: Int64, b: Int64) -> Bool
      |operation cut() -> Bool
      |operation find_dictionary(spec: Int64) -> Bool
      |end""".stripMargin, "<kernel-fixture>")
    val errors = Loader.loadAll(kb, IndexedSeq(file))
    assert(errors.isEmpty, s"kernel fixture: $errors")

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
    registerKernel(kb)
    val errs = Loader.loadAll(kb, files)
    assert(errs.isEmpty, s"load errors: $errs")
    kb

  /** `src` loaded into a fresh KB; fails the calling test on parse or load errors. */
  def loaded(src: String, label: String)(using munit.Location): KnowledgeBase =
    loaded(IndexedSeq(parsed(src, label)))

  /** The `(label, source)` files loaded, in order, into a fresh KB — the KB, or the
    * load's errors RENDERED. A parse failure fails the calling test. Moved here from
    * `HeadIntroductionCensusTest` and `MultiHeadIntroductionTest` (WI-20260908-NE0E4's
    * review), which carried it verbatim, with the three readers below. */
  def tryLoad(files: (String, String)*)(using munit.Location)
      : Either[Seq[String], KnowledgeBase] =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    registerKernel(kb)
    val errs = Loader.loadAll(kb, files.toIndexedSeq.map((label, src) => parsed(src, label)))
    if errs.isEmpty then Right(kb) else Left(errs.toSeq.map(_.render))

  /** The rendered errors of a load that must be REFUSED; fails the calling test when the
    * program loads. */
  def refusal(files: (String, String)*)(using munit.Location): Seq[String] =
    tryLoad(files*).left.getOrElse(fail("expected a load refusal, the program loaded"))

  /** Solutions of `<qn>(?x)` — the goal built on the SYMBOL the name resolves to, so a
    * clause that landed on another symbol is not counted. */
  def unaryAnswers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("x")))))
    SearchStream.resolve(kb, kb.alloc(Term.Fn(sym, IArray(v), IArray.empty)))
      .allSolutions(kb).length

  /** Solutions of the ground goal `<qn>(value)`. */
  def groundAnswers(kb: KnowledgeBase, qn: String, value: Long)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val arg = kb.alloc(Term.Const(Literal.IntLit(value)))
    SearchStream.resolve(kb, kb.alloc(Term.Fn(sym, IArray(arg), IArray.empty)))
      .allSolutions(kb).length
