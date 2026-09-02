package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, Var}
import anthill.resolve.SearchStream

/** WI-20260902-VNWAW (rustland's twin, same ticket) — WHAT A DOTTED PAREN-LESS GOAL
  * MEANS, ONCE WI-20260901-719FJ HAS SAID WHICH SYMBOL IT SPELLS.
  *
  * THERE IS NO SCALAND MIRROR OF THAT TICKET'S FIX, AND THIS FILE IS THE MEASUREMENT
  * THAT SAYS SO rather than an assumption. Rustland's defect was that a dotted goal took
  * neither of the two readings the ONE-SEGMENT arms of the same walk had gained at
  * WI-20260902-CZJ2N — a fielded ENTITY is §8.3's all-fields-fresh pattern, a nullary
  * OPERATION is its own call — so the dotted column diverged from the one-segment one and
  * `not(ns.flag)` answered 1 over a `flag` whose body is `true`. Here BOTH COLUMNS AGREE
  * AT EVERY CELL, because scaland has NEITHER reading for EITHER spelling:
  *
  *   * an OPERATION BODY is parsed and DROPPED (WI-1007, `Loader`'s `OperationItem` arm:
  *     scaland has no typer and no evaluator to consume one, and the KB no slot to hold
  *     it), so a nullary op goal has nothing to reduce and answers 0 in all four
  *     spellings — as does `not(…)` of it, since a rule-body `not` does not reach NAF here
  *     either (719FJ measured that and this file's own op rows re-measure it); and
  *   * §8.3's PARTIAL ENTITY PATTERNS are absent whole — `KnowledgeBase.entityFieldNames`
  *     is filled and has no reader in the main tree — so `acct` and `acct()` alike match
  *     only a fact spelling them identically, and both answer 0 while `acct(n: 1)`
  *     answers. That is **WI-20260902-T8H1W**, filed with this file; these rows are its
  *     fixture and are the ones that must FLIP when it is closed.
  *
  * SO THE ROWS BELOW PIN A BOUNDARY, and each is written as the PAIR that makes it a
  * boundary and not a verdict about the dotted spelling: the dotted goal beside the
  * one-segment goal of the same program. The PREDICATE test is the control that says the
  * harness, the fixture and 719FJ + CZJ2N's own scaland work are all live — it answers 1
  * in all four spellings, which is what stops the two zero-tables above being read as
  * "nothing works here".
  */
class DottedGoalReadingTest extends munit.FunSuite:

  /** Solutions of `<qn>(?x)`, with the goal built on the resolved SYMBOL so a clause that
    * landed elsewhere counts zero rather than silently matching. */
  private def answers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.freshVar(kb.intern("x"))
    val goal = kb.alloc(Term.Fn(sym, IArray(kb.alloc(Term.Var(Var.Global(v)))), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  /** THE CONTROL, AND IT MUST COME FIRST: a nullary PREDICATE goal answers in all four
    * spellings. 719FJ collapsed the dotted citation to the name and CZJ2N made the two
    * nullary spellings one term; both are live here, so the two zero-tables below are
    * statements about the two MISSING READINGS and not about dotted goals or about this
    * fixture. */
  test("a nullary predicate goal answers in both qualifications and both spellings") {
    val kb = LoadFixture.loaded(
      """fact bvn(1)
        |namespace zzvnPr.inner
        |  rule tgt :- bvn(1)
        |  rule sBare(1)  :- tgt
        |  rule sParen(1) :- tgt()
        |end
        |namespace zzvnPr.outer
        |  rule dBare(1)  :- zzvnPr.inner.tgt
        |  rule dParen(1) :- zzvnPr.inner.tgt()
        |end""".stripMargin,
      "vnwawpred.anthill",
    )
    for q <- Seq("zzvnPr.inner.sBare", "zzvnPr.inner.sParen",
                 "zzvnPr.outer.dBare", "zzvnPr.outer.dParen") do
      assertEquals(
        answers(kb, q), 1,
        s"$q: the predicate holds and every spelling of its goal must reach it — this is " +
          "719FJ's collapse and CZJ2N's one-term canon, both live, and the control for " +
          "the two zero-tables in this file",
      )
  }

  /** A NULLARY OPERATION AS A GOAL — 0 IN ALL FOUR SPELLINGS, because the body is
    * dropped at load (WI-1007) so there is nothing to reduce, and `not(…)` of it is 0 too
    * because a rule-body `not` does not reach NAF here.
    *
    * PAIRED, not absolute: what this ticket owns is that the DOTTED column equals the
    * ONE-SEGMENT column. When scaland grows operation bodies, the two must move together
    * — if the one-segment rows start answering and the dotted ones do not, that is
    * rustland's VNWAW defect arriving here and this row is what reports it. */
  test("a nullary operation goal is inert for every spelling — no body to reduce") {
    val kb = LoadFixture.loaded(
      """namespace zzvnOp.inner
        |  import anthill.prelude.Bool
        |  operation flag() -> Bool = true
        |  rule sBare(1)  :- flag
        |  rule sParen(1) :- flag()
        |  rule sNot(1)   :- not(flag)
        |end
        |namespace zzvnOp.outer
        |  rule dBare(1)  :- zzvnOp.inner.flag
        |  rule dParen(1) :- zzvnOp.inner.flag()
        |  rule dNot(1)   :- not(zzvnOp.inner.flag)
        |end""".stripMargin,
      "vnwawop.anthill",
    )
    for cell <- Seq("Bare", "Paren", "Not") do
      val one = answers(kb, s"zzvnOp.inner.s$cell")
      val dot = answers(kb, s"zzvnOp.outer.d$cell")
      assertEquals(
        dot, one,
        s"d$cell must answer what s$cell answers — the qualification decides NOTHING " +
          "about a goal's reading (rustland's WI-20260902-VNWAW). Both are 0 here " +
          "because an operation BODY is dropped at load (WI-1007)",
      )
      assertEquals(
        one, 0,
        s"s$cell: and the shared answer is 0, not a coincidence of two broken columns — " +
          "when scaland grows operation bodies this row goes red and VNWAW's reading has " +
          "to be ported to `reallocTerm`'s dotted branch",
      )
  }

  /** A BARE FIELDED ENTITY AS A GOAL — 0 in both nullary spellings and both
    * qualifications, while the APPLIED spelling answers. §8.3's partial-entity expansion
    * is absent from scaland whole: **WI-20260902-T8H1W**. */
  test("a bare fielded entity goal is empty for every spelling — no §8.3 expansion") {
    val kb = LoadFixture.loaded(
      """namespace zzvnEn.inner
        |  import anthill.prelude.Int64
        |  entity acct(n: Int64)
        |  fact acct(n: 1)
        |  rule sBare(1)    :- acct
        |  rule sParen(1)   :- acct()
        |  rule sApplied(1) :- acct(n: 1)
        |end
        |namespace zzvnEn.outer
        |  rule dBare(1)    :- zzvnEn.inner.acct
        |  rule dParen(1)   :- zzvnEn.inner.acct()
        |  rule dApplied(1) :- zzvnEn.inner.acct(n: 1)
        |end""".stripMargin,
      "vnwawent.anthill",
    )
    for cell <- Seq("Bare", "Paren", "Applied") do
      assertEquals(
        answers(kb, s"zzvnEn.outer.d$cell"), answers(kb, s"zzvnEn.inner.s$cell"),
        s"d$cell must answer what s$cell answers — the qualification decides nothing",
      )
    // THE APPLIED ROW IS THE CONTROL, and it is what makes the two zeros a statement
    // about the EXPANSION rather than about the entity or the fact.
    assertEquals(
      answers(kb, "zzvnEn.inner.sApplied"), 1,
      "the fully-applied goal matches the fact — so the entity, the fact and the goal " +
        "all work, and the two rows below are about §8.3's expansion alone",
    )
    for q <- Seq("zzvnEn.inner.sBare", "zzvnEn.inner.sParen",
                 "zzvnEn.outer.dBare", "zzvnEn.outer.dParen") do
      assertEquals(
        answers(kb, q), 0,
        s"$q: §8.3 says a bare entity name in a LOGICAL position IS `acct()`, the " +
          "all-fields-fresh pattern, and scaland has no partial-entity expansion at all " +
          "(`entityFieldNames` has no reader) — WI-20260902-T8H1W. rustland answers 1 " +
          "here; this row goes red when that ticket lands",
      )
  }
