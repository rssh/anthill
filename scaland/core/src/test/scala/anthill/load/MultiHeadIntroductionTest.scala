package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.kb.LoadFixture.{groundAnswers, refusal, unaryAnswers as answers}

/** WI-20260908-NE0E4 (rustland's twin: `wi_ne0e4_multi_head_introduction_test`) — A
  * MULTI-HEAD RULE'S HEADS ARE SCOPED WHERE THEY ARE WRITTEN.
  *
  * `rule law: H1, H2 :- B` is N clauses sharing one body (§5.3, "conjunctive sugar"), so
  * each head introduces exactly what the single-head rule `Hᵢ :- B` would. Before this
  * ticket the rule introduced nothing ([[Loader]]'s `ruleIntroducedFunctor` answered
  * `SeveralHeads`), each head landed its clause under the bare intern — ONE global name —
  * and a reader in one sort answered from another sort's clause, on a program that loaded
  * clean. A multi-head rule the load REFUSES mints nothing: a body-less one (it declares,
  * and a declaration declares one predicate) and an unlabeled one (`severalHeadsRefusal`).
  *
  * ── WHICH ROWS FAIL WHEN WHAT IS BACKED OUT — each applied in `Loader` and run ──
  *
  *  * **THE PER-HEAD MINT** — `headIntroductions` answering
  *    `ruleIntroducedFunctor(rule, …).toOption.toIndexedSeq` for every rule (the
  *    pre-ticket population). **10 ROWS FAIL** over this class, the census,
  *    `ParserIntegrationTest` and `DiagnosticLocationTest` (103 of 113 pass): the
  *    cross-sort row, the two-heads-one-name row, the nullary-spellings row, the collision
  *    row, the two-files row, the selective-import row, the joins-rather-than-shadows row
  *    on its fresh head, `HeadIntroductionCensusTest`'s multi-head row, and
  *    `ParserIntegrationTest`'s two multi-head load rows.
  *  * **MINT A BODY-LESS MULTI-HEAD RULE'S HEADS** — `headIntroductions` returning empty
  *    for every refusal but `SeveralHeadsRefusal.Declaration`. **1 ROW FAILS**: the
  *    body-less row, whose minted head would collide with the sort's `aa`.
  *  * **MINT AN UNLABELED MULTI-HEAD RULE'S HEADS** — returning empty for
  *    `SeveralHeadsRefusal.Declaration` alone. **2 ROWS FAIL**: the unlabeled row (its
  *    minted `aa` collides with the sort's) and the unlabeled two-files row (061 asks for
  *    a declaration of a predicate whose heads store nothing).
  *  * **THE CONNECTIVE REFUSAL BEFORE THE READING** — WI-1090's `===` check asked ahead of
  *    `ruleReading` in `loadRuleHeads`, the order before this ticket. **1 ROW FAILS**: the
  *    connective-head row, refused for its `===` where rustland refuses it for its heads.
  *  * **THE LABEL REFUSAL BEFORE THE CONNECTIVE** — the `Unlabeled` arm asked first, as
  *    before round 3 of the review. **1 ROW FAILS**: the unlabeled empty-bodied connective
  *    row, told about its label where rustland tells it about its `===`.
  *
  * PASS EITHER WAY, BY DESIGN: the single-head and distinct-name controls (what makes the
  * cross-sort row about the head COUNT) and the "joins, does not shadow" half of its row.
  * Every row above was measured, each back-out applied in `Loader` and the four suites run
  * (2026-10-24, after the third `/code-review` round).
  */
class MultiHeadIntroductionTest extends munit.FunSuite:

  private def loaded(src: String)(using munit.Location): KnowledgeBase =
    LoadFixture.loaded(src, "multihead.anthill")

  /** The clauses stored under `qn`, or `None` when nothing is named `qn`. */
  private def clauses(kb: KnowledgeBase, qn: String): Option[Int] =
    kb.tryResolveSymbol(qn).map(kb.byFunctor(_).length)

  /** THE INVERTED PAIR: sort P's clause is FALSE (its body reads a fact that is not
    * there), sort Q's TRUE, and each sort reads through a rule of its own — so a merge
    * is a WRONG ANSWER in P rather than an extra one. */
  private def twoSorts(ns: String, pRule: String, qRule: String, pRead: String, qRead: String) =
    s"""namespace $ns
       |  sort P
       |    fact pbase(0)
       |    $pRule
       |    rule see(?x) :- $pRead(?x)
       |  end
       |  sort Q
       |    $qRule
       |    rule see(?x) :- $qRead(?x)
       |  end
       |end""".stripMargin

  test("two sorts writing one head name each read their own clause") {
    val kb = loaded(twoSorts("zzNE.cs",
      "rule lawP: aa(1), bb(1) :- pbase(1)", "rule lawQ: aa(1), cc(1) :- true", "aa", "aa"))
    assertEquals(answers(kb, "zzNE.cs.P.see"), 0, "P's own `aa` is false — a 1 is Q's clause")
    assertEquals(answers(kb, "zzNE.cs.Q.see"), 1, "and Q's is true")
    val (p, q) = (kb.tryResolveSymbol("zzNE.cs.P.aa"), kb.tryResolveSymbol("zzNE.cs.Q.aa"))
    assert(p.isDefined && q.isDefined && p != q, s"each sort's head is its OWN symbol: $p / $q")
    for qn <- Seq("zzNE.cs.P.bb", "zzNE.cs.Q.cc") do
      assertEquals(clauses(kb, qn), Some(1), s"every head is scoped, not only the first: $qn")
  }

  test("the single-head and distinct-name controls") {
    // PASSES EITHER WAY: the single-head spelling always scoped (WI-894), and two
    // DISTINCT names never shared a symbol.
    for (ns, pRule, qRule, pRead, qRead) <- Seq(
        ("zzNE.cl", "rule aa(1) :- pbase(1)", "rule aa(1) :- true", "aa", "aa"),
        ("zzNE.cd", "rule lawP: pa(1), bb(1) :- pbase(1)", "rule lawQ: qa(1), cc(1) :- true",
          "pa", "qa")) do
      assertEquals(answers(loaded(twoSorts(ns, pRule, qRule, pRead, qRead)), s"$ns.P.see"), 0, ns)
  }

  test("two heads of one name in one rule are one scoped predicate") {
    val kb = loaded("""namespace zzNE.sn
      |  sort S
      |    rule law: pp(1), pp(2) :- true
      |  end
      |end""".stripMargin)
    assertEquals(clauses(kb, "zzNE.sn.S.pp"), Some(2), "two clauses, one predicate")
    assertEquals(groundAnswers(kb, "zzNE.sn.S.pp", 2), 1, "and the second clause answers")
  }

  test("both spellings of a nullary head are one term") {
    // WI-20260902-EQG4F item 4, the multi-head route: `:- aa` answered 1 and `:- aa()`
    // answered 0 while `aa` was an undeclared name.
    val kb = loaded("""namespace zzNE.ns
      |  rule law: aa, bb :- true
      |  rule s1(1) :- aa
      |  rule s2(1) :- aa()
      |end""".stripMargin)
    assertEquals((answers(kb, "zzNE.ns.s1"), answers(kb, "zzNE.ns.s2")), (1, 1))
  }

  test("a head and a single-head rule in visible scopes collide") {
    val errs = refusal("multihead.anthill" -> """namespace zzNE.co
      |  rule law: aa, bb :- true
      |  sort S
      |    rule aa :- true
      |  end
      |end""".stripMargin)
    assert(errs.exists(_.contains("the rule head `aa` introduces that name at 2 scopes")),
      errs.mkString("\n"))
  }

  test("a head that already denotes joins rather than shadows") {
    // PASSES EITHER WAY for `aa` (a declared name denotes); the fresh `zz` is what fails
    // under the per-head back-out.
    val kb = loaded("""namespace zzNE.jn
      |  rule aa
      |  sort S
      |    rule law: aa, zz :- true
      |  end
      |  rule see(1) :- aa
      |end""".stripMargin)
    assertEquals(answers(kb, "zzNE.jn.see"), 1, "the head is a clause of the declared `aa`")
    assert(!kb.hasQualifiedName("zzNE.jn.S.aa"), "and mints no `S.aa` shadowing it")
    assertEquals(clauses(kb, "zzNE.jn.S.zz"), Some(1), "while the fresh head is S's own")
  }

  test("heads in two files at one scope must be declared") {
    val errs = refusal(
      "a.anthill" -> "namespace zzNE.tf\n  rule law1: aa(1), bb :- true\nend",
      "b.anthill" -> "namespace zzNE.tf\n  rule law2: aa(2), cc :- true\nend")
    assert(errs.exists(_.contains("the predicate `aa` has rule heads in 2 files")),
      errs.mkString("\n"))
  }

  test("a selective import reaches a multi-head head") {
    val kb = loaded("""namespace zzNE.im
      |  sort Rec
      |    rule law: freshp(1), other(2) :- true
      |  end
      |end
      |namespace zzNE.side
      |  import zzNE.im.Rec.{freshp}
      |  rule see(1) :- freshp(1)
      |end""".stripMargin)
    assertEquals(answers(kb, "zzNE.side.see"), 1)
  }

  test("a body-less multi-head rule is refused for what it is") {
    // Its heads are not minted, so they cannot collide with the sort's `aa` and send the
    // author to declare a name in the scope whose line was the refused one.
    val errs = refusal("multihead.anthill" -> """namespace zzNE.bl
      |  rule law: aa, bb
      |  sort S
      |    rule aa :- true
      |  end
      |end""".stripMargin)
    assert(errs.exists(_.contains("it writes 2 heads at once, and a declaration declares ONE predicate")),
      errs.mkString("\n"))
    assert(!errs.exists(_.contains("introduces that name at")),
      s"a refused declaration mints nothing to collide with: ${errs.mkString("\n")}")
  }

  test("an unlabeled multi-head rule is refused and mints nothing") {
    // The load refuses it, so it stores nothing — and its heads mint nothing to collide
    // with the sort's `aa` (the refused-rules back-out).
    val errs = refusal("multihead.anthill" -> """namespace zzNE.ul
      |  rule aa, bb :- true
      |  sort S
      |    rule aa :- true
      |  end
      |end""".stripMargin)
    assert(errs.exists(_.contains("multi-head rule requires a label")), errs.mkString("\n"))
    assert(!errs.exists(_.contains("introduces that name at")),
      s"a refused rule mints nothing to collide with: ${errs.mkString("\n")}")
  }

  test("a body-less multi-head rule with a connective head is refused for its heads") {
    // rustland's order: the reading (several heads, where a declaration declares one) is
    // asked before WI-1090's `===` refusal, so the two implementations say one thing.
    // Fails when `loadRuleHeads` asks the connective first (the reading back-out).
    val errs = refusal("multihead.anthill" -> "namespace zzNE.cx\n  rule law: f(1) === 2, g\nend")
    assert(errs.exists(_.contains("it writes 2 heads at once")), errs.mkString("\n"))
  }

  test("an unlabeled empty-bodied rule with a connective head is refused for the connective") {
    // rustland's order: WI-1090's `===` refusal before the label's. One program, one
    // diagnostic, in both implementations. Found by `/code-review`.
    val errs = refusal("multihead.anthill" -> "namespace zzNE.cy\n  rule f(1) === 2, g(1) :- true\nend")
    assert(errs.exists(_.contains("is the structural identity TEST")), errs.mkString("\n"))
    assert(!errs.exists(_.contains("requires a label")), errs.mkString("\n"))
  }

  test("unlabeled heads in two files draw no declare-it") {
    // 061's "declare it" is about heads that store clauses. These store none.
    val errs = refusal(
      "a.anthill" -> "namespace zzNE.u2\n  rule aa(1), bb :- true\nend",
      "b.anthill" -> "namespace zzNE.u2\n  rule aa(2) :- true\nend")
    assert(errs.exists(_.contains("multi-head rule requires a label")), errs.mkString("\n"))
    assert(!errs.exists(_.contains("has rule heads in 2 files")), errs.mkString("\n"))
  }
