package anthill.smtgen

/** WI-20261012-KF2SD — A RULE CALL IS READ BY THE ONE CLAUSE THAT CAN ANSWER IT, AND
  * REFUSED WHERE SEVERAL CAN.
  *
  * A rule call in a proved body is a hypothesis, and a predicate of several clauses holds
  * when any of them does. `translateCalledRule` read it as `find(hasBody)` — the first
  * clause with a body — so a claim over a predicate of two clauses was a claim over the
  * first. rustland read it the same way in three places and is mended in one
  * (`Emitter::answering_clause`, `rustland/anthill-cli/tests/include/
  * wi_kf2sd_several_clauses_test.rs`); this emitter reads a rule call in ONE way, the
  * one-argument form, whose argument is a variable — so every clause of one argument
  * can answer, a fact too.
  *
  * Decided with the user, 2026-10-13: REFUSED now; the disjunction of the clauses'
  * readings is WI-20261013-1KF32.
  *
  * ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
  *
  * Restore `translateCalledRule`'s `find(hasBody)` and drop the count before it:
  *   * `a call two clauses with a body can answer is refused` — fails: a document, with
  *     the FIRST clause's `(+ 2.0 3.0)` for the call.
  *   * `a fact beside a clause with a body is two` — fails the same way: the fact was
  *     never looked at.
  *   * `a fact that answers alone is not read as a definition` — fails on the message:
  *     "v0: called rule '…alone' must have exactly one pos arg in head", the clause of
  *     two arguments taken for the call of one.
  * `a call one clause answers is read by it` and `a clause of another arity is another
  * predicate` pass either way BY DESIGN: they are the control, the documents the change
  * must not move.
  */
class SeveralClausesTest extends munit.FunSuite:

  private def kb = Common.loadKbWith("""
    namespace test.smt.several
      import anthill.prelude.{Float}
      import anthill.prelude.Numeric.{add}

      rule cap(?d) :- ?d = add(2.0, 3.0)
      rule cap(?d) :- ?d = add(50.0, 50.0)
      rule reads(?r) :- cap(?c), ?r = add(?c, 1.0)

      rule lim(?d) :- ?d = add(2.0, 3.0)
      fact lim(100.0)
      rule readsLim(?r) :- lim(?c), ?r = add(?c, 1.0)

      rule one(?d) :- ?d = add(2.0, 3.0)
      rule readsOne(?r) :- one(?c), ?r = add(?c, 1.0)

      rule span(?d) :- ?d = add(2.0, 3.0)
      rule span(?a, ?b) :- gte(?b, ?a)
      rule readsSpan(?r) :- span(?c), ?r = add(?c, 1.0)

      fact alone(5.0)
      rule alone(?a, ?b) :- gte(?b, ?a)
      rule readsAlone(?r) :- alone(?c), ?r = add(?c, 1.0)
    end
  """)

  private def refusedAsSeveral(qn: String, relation: String, facts: Int, bodied: Int)(using
      munit.Location
  ): Unit =
    SmtGen.emitSatisfiabilityCheck(kb, qn) match
      case Right(doc) =>
        fail(s"$qn: a call ${facts + bodied} clauses can answer is not read by one; " +
          s"backed out this is a document with the first clause's body:\n$doc")
      case Left(e) =>
        val howMany = s"the call of `$relation` can be answered by ${facts + bodied} clauses " +
          s"of the predicate ($facts fact(s), $bodied with a body)"
        assert(e.message.contains(howMany), s"expected `$howMany`, got: ${e.message}")
        assert(e.message.contains("WI-20261013-1KF32"), e.message)

  private def readAs(qn: String, fragment: String)(using munit.Location): Unit =
    SmtGen.emitSatisfiabilityCheck(kb, qn) match
      case Right(doc) =>
        assert(doc.contains(fragment), s"$qn: the call is read as `$fragment`:\n$doc")
      case Left(e) => fail(s"$qn: one clause answers, and it is read: ${e.message}")

  test("a call two clauses with a body can answer is refused") {
    refusedAsSeveral("test.smt.several.reads", "test.smt.several.cap/1", facts = 0, bodied = 2)
  }

  test("a fact beside a clause with a body is two") {
    refusedAsSeveral("test.smt.several.readsLim", "test.smt.several.lim/1", facts = 1, bodied = 1)
  }

  test("a call one clause answers is read by it") {
    readAs("test.smt.several.readsOne", "(+ (+ 2.0 3.0) 1.0)")
  }

  test("a clause of another arity is another predicate") {
    readAs("test.smt.several.readsSpan", "(+ (+ 2.0 3.0) 1.0)")
  }

  /** THIS EMITTER READS NO FACT, and a fact that answers alone is refused as a predicate of
    * facts only is — by the tail, naming the predicate. The clause with a body beside it
    * is of two arguments and answers no call of one. (/code-review: the fact was handed
    * to `translateCalledRule`, "rule call '…alone' has no defining clauses" — and before
    * the change the two-argument clause was, "must have exactly one pos arg in head".) */
  test("a fact that answers alone is not read as a definition") {
    SmtGen.emitSatisfiabilityCheck(kb, "test.smt.several.readsAlone") match
      case Right(doc) => fail(s"this emitter reads no fact; got a document:\n$doc")
      case Left(e) =>
        assertEquals(e.message, "v0: unhandled body goal functor 'test.smt.several.alone'")
  }
