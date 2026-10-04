package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.resolve.SearchStream
import anthill.term.{Literal, Term}

/** WI-20260821-HSG31 — A DECLARATION AT `<global>` NO LONGER ABSORBS A NAMESPACE'S RULE
  * HEAD. The scaland port of rustland's `wi_hsg31_global_declaration_test`.
  *
  * WI-980 made `<global>` "never yielded to" for a rule HEAD written there, and only for
  * that. A `<global>` `sort` or `operation` is defined in pass 1, so a namespace's
  * same-spelled head resolved to it through the ordinary ladder and became a clause OF it:
  * the namespace's predicate never existed, on a program that loads clean. The rule now
  * holds over the SCOPE (kernel-language.md §5.3, "`<global>` is not a party to any of
  * it"): a head written inside a namespace does not resolve to a name whose only home is
  * `<global>`.
  *
  * NOT PORTED: rustland's two stdlib rows (these fixtures load no stdlib) and its equation
  * row (it drives a `@[simp]` operation through the interpreter).
  *
  * ── THE BACK-OUT, applied and run ───────────────────────────────────────────
  *
  * In `Loader.ruleHeadLadderAnswer`, replace the guarded re-ask
  * `kb.symbols.resolveRuleHeadInsideNamespace(name, scope)` with `ResolveResult.Found(sym)`.
  * **3 rows fail**: the `operation`, `sort` and staged rows. The DECLARATION row is the
  * same change at its second call site: back out `DeclarePredicatePass`'s
  * `ruleHeadLadderAnswer` to `kb.symbols.resolveInScope` and it alone fails. **3 pass either way by
  * design**: the top-level `rule` spelling, the documented top-level form joining at
  * `<global>`, and a namespace REFERENCE to a top-level name. */
class GlobalDeclarationHeadTest extends munit.FunSuite:

  private def load(kb: KnowledgeBase, files: (String, String)*)(using munit.Location): Unit =
    val errs = Loader.loadAll(kb, files.map((l, s) => LoadFixture.parsed(s, l)).toIndexedSeq)
    assert(errs.isEmpty, s"load errors: ${errs.map(_.render)}")

  private def loaded(files: (String, String)*)(using munit.Location): KnowledgeBase =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    load(kb, files*)
    kb

  /** Clauses under `qn`, or `None` when nothing is named `qn` — the absorbed predicate is
    * ABSENT, not empty, so the distinction is the measurement. */
  private def clauses(kb: KnowledgeBase, qn: String): Option[Int] =
    kb.tryResolveSymbol(qn).map(sym => kb.byFunctor(sym).length)

  private def answers(kb: KnowledgeBase, qn: String, args: Int*)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve"))
    val goal = kb.alloc(Term.Fn(sym,
      IArray.from(args.map(a => kb.alloc(Term.Const(Literal.IntLit(a.toLong))))), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  private val ns = "namespace zdemo\n  rule zqop(2, 7) :- true\nend"

  /** One top-level declaration of `zqop` beside the namespace, as two files and as one —
    * the file boundary is not what the rule is about. */
  private def assertNamespaceKeepsItsPredicate(globalDecl: String)(using munit.Location): Unit =
    for files <- Seq(Seq("g.anthill" -> globalDecl, "n.anthill" -> ns),
                     Seq("one.anthill" -> s"$globalDecl\n$ns")) do
      val kb = loaded(files*)
      assertEquals(clauses(kb, "zdemo.zqop"), Some(1), s"$files")
      assertEquals(clauses(kb, "zqop"), Some(0), s"$files")
      assertEquals(answers(kb, "zdemo.zqop", 2, 7), 1, s"$files")

  test("a global operation does not absorb a namespace head") {
    assertNamespaceKeepsItsPredicate("operation zqop(a: Int64, b: Int64) -> Int64 = 1")
  }

  test("a global sort does not absorb a namespace head") {
    assertNamespaceKeepsItsPredicate("sort zqop\n  entity zq(n: Int64)\nend")
  }

  test("a namespace DECLARATION beside a global operation declares too") {
    // The 061 spelling of the same predicate. The declaration-shadow refusal asked the
    // ordinary ladder, so it refused this pair while the bodied spelling above loaded —
    // found by `/code-review`. Rustland has no such refusal; both spellings load there.
    val kb = loaded(
      "g.anthill" -> "operation zqop(a: Int64, b: Int64) -> Int64 = 1",
      "n.anthill" -> "namespace zdemo\n  rule zqop(?a, ?b)\n  rule zqop(2, 7) :- true\nend")
    assertEquals(clauses(kb, "zdemo.zqop"), Some(1))
    assertEquals(answers(kb, "zdemo.zqop", 2, 7), 1)
  }

  test("a staged load does not yield to an earlier global head") {
    // The second `loadAll` decides its heads against a table holding the first batch's
    // `<global>.zq`, and used to find it through the ordinary ladder.
    val kb = loaded("g.anthill" -> "rule zq(0) :- true")
    load(kb, "n.anthill" -> "namespace zq1\n  rule zq(1) :- true\nend")
    assertEquals(clauses(kb, "zq1.zq"), Some(1))
    assertEquals(clauses(kb, "zq"), Some(1))
    assertEquals(answers(kb, "zq1.zq", 1), 1)
    assertEquals(answers(kb, "zq", 0), 1)
  }

  test("CONTROL: a global rule head never absorbed one") {
    val kb = loaded("g.anthill" -> "rule zqop(1, 1) :- true", "n.anthill" -> ns)
    assertEquals(clauses(kb, "zdemo.zqop"), Some(1))
    assertEquals(clauses(kb, "zqop"), Some(1))
  }

  test("CONTROL: the documented top-level form still joins at global") {
    // A namespace-less file's own sort is not inside a namespace, so its head joins the
    // top-level declaration through the enclosing chain.
    val kb = loaded("top.anthill" ->
      "rule p(?x)\nrule p(1) :- true\nsort Rec\n  entity r(n: Int64)\n  rule p(2) :- true\nend")
    assertEquals(clauses(kb, "p"), Some(2))
    assertEquals(clauses(kb, "Rec.p"), None)
    assertEquals(answers(kb, "p", 2), 1)
  }

  test("CONTROL: a namespace reference still reaches a top-level name") {
    val kb = loaded("g.anthill" -> "rule gq(1) :- true\nnamespace zr\n  rule uses(?x) :- gq(?x)\nend")
    assertEquals(answers(kb, "zr.uses", 1), 1)
  }
