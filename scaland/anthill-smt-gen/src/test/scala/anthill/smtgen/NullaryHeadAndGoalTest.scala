package anthill.smtgen

/** WI-20260902-EQG4F item 3 — SMT-GEN READS A NULLARY HEAD AND A NULLARY BODY GOAL.
  *
  * WI-20260902-CZJ2N made `flag` and `flag()` ONE term, stored `Term.Ref`. `classifyHead`
  * and `processBodyGoal` both matched `Term.Fn` only, so:
  *   * a nullary head fell to `HeadShape.Unsupported("rule head must be Fn or Bottom, got
  *     Ref(…)")` — a hard `SmtGenError` for BOTH spellings — and the `posArgs.isEmpty =>
  *     Bottom` arm right below it became dead code at the same moment;
  *   * a rule whose body CITES a nullary predicate died `non-Fn body goal: Ref(…)`, naming
  *     the CARRIER rather than the symbol the author wrote.
  * rustland took the equivalent arm in CZJ2N itself (`Term::Ref(s) | Term::Ident(s)` in
  * `classify_head`); its body goals are `NodeOccurrence`s whose nullary `Expr::Apply`
  * already answers with empty argument lists, so only scaland needed a reader. Both now go
  * through one `goalAsFn`, which is that reader.
  *
  * WHAT THIS DOES AND DOES NOT BUY, measured rather than claimed. The HEAD half is a
  * capability: `emitSatisfiabilityCheck` on a nullary-headed rule went from a hard error to
  * a 9-line document. The BODY half is a DIAGNOSTIC: a 0-ary PREMISE still does not
  * translate — it falls through every arm to the loud `unhandled body goal functor`, which
  * is where rustland's own tail leaves it too — so what changed is that the refusal now
  * names `test.smt.nullary.flag` instead of `Ref(1160)`. That shared v0 limit is not fixed
  * here and the row below says so in its assertion.
  *
  * ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
  *
  * Restore `classifyHead`'s `case f: Term.Fn` match and `processBodyGoal`'s `case f:
  * Term.Fn => f / case other => Left("non-Fn body goal")`:
  *   * `a nullary head classifies as Bottom, in both spellings` — BOTH rows fail. Two rows,
  *     because one spelling passing while the other failed is exactly the split CZJ2N
  *     closed, and a single row could not tell that from a clean fix.
  *   * `a nullary-headed rule emits a document` — both rows fail (`Unsupported`).
  *   * `a nullary body goal is refused BY SYMBOL, not by carrier` — fails on the message.
  * `an applied head still classifies` and `an applied body goal still emits` pass either
  * way BY DESIGN: they are the arity control. Without them a change that merely stopped
  * erroring everywhere would look identical to this one.
  */
class NullaryHeadAndGoalTest extends munit.FunSuite:

  private def kb = Common.loadKbWith("""
    namespace test.smt.nullary
      import anthill.prelude.{Float}
      import anthill.prelude.Numeric.{add}

      entity Params(base: Float)

      rule flag :- gte(1, 0)
      rule entityHead(base: 3.0) :- gte(1, 0)
      rule citesBareEntity(?r) :- Params, ?r = add(1.0, 1.0)
      rule citesPosEntity(?r) :- Params(?b), ?r = add(?b, 1.0)
      rule citesBadIneq(?r) :- Params(base: ?b), lte(?b, weirdo(1.0)), ?r = add(?b, 1.0)
      rule citesNullaryPremise(?r) :- Params(base: ?b), flag, ?r = add(?b, 1.0)
      rule flagParen() :- gte(1, 0)
      rule bound(?r) :- Params(base: ?b), ?r = add(?b, 1.0)
      rule citesNullary(?r) :- Params(base: ?b), ?r = add(?b, 1.0), flag
      rule citesApplied(?r) :- Params(base: ?b), ?r = add(?b, 1.0), bound(?q)

      fact Params(base: 2.0)
    end
  """)

  private def shapeOf(k: anthill.kb.KnowledgeBase, qn: String)(using munit.Location): HeadShape =
    val sym = k.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val rid = k.byFunctor(sym).headOption.getOrElse(fail(s"`$qn` has no clause — fixture drift"))
    Emitter(k).classifyHead(rid)

  test("a nullary head classifies as Bottom, in both spellings") {
    val k = kb
    assertEquals(
      shapeOf(k, "test.smt.nullary.flag"), HeadShape.Bottom,
      "`rule flag :- …` is a 0-arg predicate head — backed out this is Unsupported(Ref)",
    )
    assertEquals(
      shapeOf(k, "test.smt.nullary.flagParen"), HeadShape.Bottom,
      "`rule flagParen() :- …` is the SAME term since CZJ2N, so it must classify alike",
    )
  }

  /** THE ARITY CONTROL for the row above: a 1-arg head was never broken and must not move.
    * The result index is a synthetic sentinel, so the SHAPE is what is asserted — pinning
    * the number would make this a test of `freshVar` numbering instead. */
  test("an applied head still classifies") {
    shapeOf(kb, "test.smt.nullary.bound") match
      case HeadShape.FunctionLike(_) => ()
      case other => fail(s"a 1-arg head must stay FunctionLike, got $other")
  }

  test("a nullary-headed rule emits a document") {
    val k = kb
    for qn <- Seq("test.smt.nullary.flag", "test.smt.nullary.flagParen") do
      SmtGen.emitSatisfiabilityCheck(k, qn) match
        case Right(doc) =>
          assert(doc.contains("(check-sat)"), s"$qn: emitted doc is not well-formed:\n$doc")
        case Left(e) =>
          fail(s"$qn: must emit — backed out this is `${e.message}`")
  }

  /** The 0-ary PREMISE still does not translate in either implementation. What this row
    * pins is WHICH refusal: the symbol the author wrote, not the term carrier. */
  test("a nullary body goal is refused BY SYMBOL, not by carrier") {
    SmtGen.emitSatisfiabilityCheck(kb, "test.smt.nullary.citesNullary") match
      case Right(doc) => fail(s"v0 does not translate a 0-ary premise; got a document:\n$doc")
      case Left(e) =>
        assert(
          e.message.contains("test.smt.nullary.flag"),
          s"the refusal must name the symbol, got: ${e.message}",
        )
        assert(
          !e.message.contains("non-Fn body goal"),
          s"backed out, this is the carrier-level refusal: ${e.message}",
        )
  }

  /** THE CONTROL for the row above: an APPLIED citation emitted before this change and
    * must still, so the row above measures the nullary spelling and not a dead emitter. */
  test("an applied body goal still emits") {
    val out = SmtGen.emitSatisfiabilityCheck(kb, "test.smt.nullary.citesApplied")
    assert(out.isRight, s"an applied citation was never broken, got: $out")
  }

  // ── The two holes reading a nullary carrier newly REACHED (/code-review) ──────
  //
  // Both are silent-failure regressions of the widening above, caught before it shipped,
  // and both are guarded at the place the renderer/arm actually depends on rather than at
  // the carrier. They fail if either guard is removed; the `Right` controls beside them
  // fail if a guard is written too wide.

  /** AN OBLIGATION NEEDS A RESULT VARIABLE. `renderUpperBoundWith` interpolates
    * `resultVar` unguarded, so a head that binds none emitted `(assert (not (<=  5.0)))` —
    * invalid SMT-LIB handed back as `Right`, which `Z3Runner` reports as "not unsat"
    * rather than as an error.
    *
    * THE HOLE IS OLDER THAN THE ARM THAT FOUND IT, so the refusal is keyed on the empty
    * `resultVar` rather than on a head shape, and the three rows are the three shapes that
    * reach it. `Params` is the `HeadShape.Predicate` one — an ENTITY functor is what
    * `classifyHead` reads as `Predicate`, and a rule whose head merely CARRIES a named
    * field (`entityHead(base: 3.0)`) is not one: its functor is ordinary, its positional
    * list is empty, and it classifies `Bottom`. MEASURED, after a first draft of this
    * comment credited `entityHead` with the `Predicate` path it does not take
    * (/code-review): `Bottom`, `Bottom`, `Predicate` for the three below. `entityHead`
    * earns its row anyway — its head is a `Term.Fn`, so it took this path BEFORE the
    * widening and is what says the hole predates it. Remove the guard and all three come
    * back `Right` with a document Z3 cannot parse. */
  test("an obligation on a head that binds no result variable is refused") {
    // COLLECTED, NOT SHORT-CIRCUITED: the comment claims all THREE rows fail on a
    // back-out, and a loop that fails on the first would only ever have measured one.
    val k = kb
    val bad = for
      qn <- Seq(
        "test.smt.nullary.flag",       // Bottom, via the nullary carrier — new reach
        "test.smt.nullary.entityHead", // Bottom, via a named-arg Term.Fn — pre-existing
        "test.smt.nullary.Params",     // Predicate — an entity functor heads it
      )
      msg <- SmtGen.emitObligation(k, Obligation(qn, 5.0)) match
        case Left(e) if e.message.contains("binds no result variable") => None
        case Left(e)    => Some(s"$qn: wrong refusal: ${e.message}")
        case Right(doc) => Some(s"$qn: must be refused; Z3 cannot parse:\n$doc")
    yield msg
    assert(bad.isEmpty, s"${bad.length} of 3 rows wrong:\n${bad.mkString("\n")}")
  }

  /** AN ENTITY PREMISE THAT DESTRUCTURES NOTHING IS REFUSED, NOT DROPPED. A bare `Params`
    * reaches the entity arm through the nullary carrier, where the field loop has no slot
    * to walk and `Right(())` claimed it was encoded — measured, the premise vanished from
    * the document entirely. A lift renders a body as an implication's antecedent, so a
    * dropped premise WEAKENS it and the lemma is stronger than what was proved: the
    * unsoundness WI-897 named in rustland's own `process_body_goal`. */
  test("an entity premise that destructures nothing is refused") {
    SmtGen.emitSatisfiabilityCheck(kb, "test.smt.nullary.citesBareEntity") match
      case Left(e) =>
        assert(
          e.message.contains("binds no field by name"),
          s"expected the destructure refusal, got: ${e.message}",
        )
      case Right(doc) =>
        assert(
          !doc.contains("base"),
          "fixture drift: this row exists because the premise was DROPPED",
        )
        fail(s"a bare entity premise must be refused, not silently dropped:\n$doc")
  }

  /** THE CONTROL for the row above, and the guard's width: a real destructure still emits
    * AND still carries the field it binds. Remove the guard's `namedArgs.isEmpty` half and
    * this row is unaffected; write the guard as "any entity premise" and it fails. */
  test("an entity premise that DOES destructure still emits its field") {
    SmtGen.emitSatisfiabilityCheck(kb, "test.smt.nullary.bound") match
      case Right(doc) =>
        assert(doc.contains("base"), s"the bound field must reach the encoding:\n$doc")
      case Left(e) => fail(s"a real destructure was never broken, got: ${e.message}")
  }

  /** THE INEQUALITY ARM MUST RETURN ITS `Either`. It used to compute the `for` and then
    * `return Right(())` regardless, so a `translateExpr` failure swallowed its error AND
    * skipped the `assertions +=` — the premise vanished and the caller was told it was
    * encoded. Pre-existing, and the same antecedent-weakening class as the entity guard
    * above; found by /code-review inside the hunk this ticket rewrote. Backed out (restore
    * the trailing `return Right(())`), this row gets a `Right` whose document has no `<=`. */
  test("a failed inequality operand is reported, not swallowed") {
    SmtGen.emitSatisfiabilityCheck(kb, "test.smt.nullary.citesBadIneq") match
      case Left(e) =>
        assert(
          e.message.contains("weirdo"),
          s"the refusal must name the operand it could not translate, got: ${e.message}",
        )
      case Right(doc) =>
        assert(!doc.contains("<="), "fixture drift: this row exists because the premise VANISHED")
        fail(s"a failed operand must be reported:\n$doc")
  }

  /** A POSITIONAL ENTITY SLOT IS WORSE THAN A MISSING ONE: the field loop walks `namedArgs`
    * only, so `Params(?b)` bound nothing and left `?b` FREE in the encoding — under-
    * constrained rather than merely omitted. A first draft of the guard read "no arguments
    * at all" and let this through (/code-review). */
  test("a positional entity destructure is refused") {
    SmtGen.emitSatisfiabilityCheck(kb, "test.smt.nullary.citesPosEntity") match
      case Left(e) =>
        assert(
          e.message.contains("binds no field by name") || e.message.contains("positional"),
          s"expected the destructure refusal, got: ${e.message}",
        )
      case Right(doc) => fail(s"a positional entity slot must be refused:\n$doc")
  }

  /** ABSTRACT MODE MAY SKIP A RULE CALL, AND A 0-ARY PREMISE IS NOT ONE. The arm was
    * ungated, so reading a nullary carrier newly routed `:- flag` into it and the premise
    * was silently dropped from the document (/code-review). Skipping a call is safe only
    * because its vars stay FREE and an ambient lift re-states it — an argument that says
    * nothing about a premise with no vars. */
  test("abstract mode does not drop a nullary premise") {
    SmtGen.emitSatisfiabilityCheckWith(
      kb, "test.smt.nullary.citesNullaryPremise", ProofConfig(abstractBody = true)
    ) match
      case Left(e) =>
        assert(
          e.message.contains("test.smt.nullary.flag"),
          s"the refusal must name the dropped premise, got: ${e.message}",
        )
      case Right(doc) =>
        assert(!doc.contains("flag"), "fixture drift: this row exists because it was DROPPED")
        fail(s"abstract mode must not drop a 0-ary premise:\n$doc")
  }

  /** THE CONTROL for the row above: abstract mode still skips a real rule CALL, so the
    * gate is not simply "refuse everything in abstract mode". */
  test("abstract mode still skips an applied rule call") {
    val out = SmtGen.emitSatisfiabilityCheckWith(
      kb, "test.smt.nullary.citesApplied", ProofConfig(abstractBody = true))
    assert(out.isRight, s"an applied rule call is what abstract mode exists to skip, got: $out")
  }
