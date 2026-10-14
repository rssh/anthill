package anthill.smtgen

/** WI-20261014-FHEEK, WI-20261012-BR7P3 — A VARIABLE IS GIVEN A VALUE WHERE THE DOCUMENT
  * HAS WRITTEN IT, AND A RULE READ INLINED HAS VARIABLES OF ITS OWN — rustland's
  * `wi_fheek_inlined_names_test`, for what this emitter reads: an equation, an entity's
  * field read by its constant, and the one-argument form.
  *
  * Each place a variable is given a value substituted, and a goal or a definition read
  * before named the variable undeclared; a second definition overwrote the first; an alias
  * (`?x = ?y`) given a value left `?y` free. And the one-argument form read its rule's own
  * variable by its index, which is the caller's variable of that index: `one_arg`'s two
  * goals were of one variable, and a satisfiable body was unsatisfiable. Now one helper
  * (`bindVariable`) equates where the document wrote the variable, and the rule's own
  * variables are named past the clause's (decided with the user, 2026-10-14, for both
  * implementations).
  *
  * ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
  *
  * Measured, each alone (rustland's `inlined-names-2026-10-14.txt` §4):
  *   * the equation substituting: `every place…` (`eqNamed`, `eqDefinedBy`, `eqTwice`)
  *     and `an alias…` (`aliasEq`);
  *   * the entity's constant substituting: `every place…` (`entNamed`);
  *   * the one-argument result substituting: `every place…` (`oneNamed`, `oneDefinedBy`)
  *     and `an alias…` (`aliasOne`);
  *   * the naming: `the one-argument form's own variable…`, and `every place…`, whose
  *     `oneNamed` result is then never bound;
  *   * the alias: `an alias…`;
  *   * the condition (`?x = ?x + 1.0`): `an equation that names its variable…`.
  * `a caller that writes nothing…` passes either way BY DESIGN: the documents the change
  * must not move.
  */
class InlinedNamesTest extends munit.FunSuite:

  private lazy val kb = Common.loadKbWith("""
    namespace test.smt.fheek
      import anthill.prelude.{Float}
      import anthill.prelude.PartialOrd.{gte, lte, lt}

      rule bound(?r) :- ?r = 3.0
      entity Lim(cap: Float)
      fact Lim(cap: 5.0)
      rule shifted(?r) :- ?r = ?y + 1.0, gte(?y, 0.0)

      rule eqNamed :- lte(?d, 10.0), ?d = 3.0, lt(?d, 0.0)
      rule eqDefinedBy :- ?e = ?d + 1.0, ?d = 3.0, lt(?e, 0.0)
      rule eqTwice :- ?d = 3.0, ?d = 4.0, lt(?d, 5.0)
      rule oneNamed :- lte(?r, 10.0), bound(?r), lt(?r, 0.0)
      rule oneDefinedBy :- ?e = ?r + 1.0, bound(?r), lt(?e, 0.0)
      rule entNamed :- lte(?c, 10.0), Lim(cap: ?c), lt(?c, 0.0)
      rule oneArg :- shifted(?v), lt(?z, 0.0), gte(?v, 0.0)
      rule aliasEq :- ?x = ?y, ?x = 5.0, lt(?y, 0.0)
      rule aliasOne :- ?x = ?y, bound(?x), lt(?y, 0.0)
      rule itself :- ?x = ?x + 1.0, lt(?x, 0.0)
      rule control :- bound(?r), ?e = ?r + 1.0, lt(?e, 0.0)
      rule free :- lte(?d, 1.0), ?e = ?d + 1.0, lt(?e, 0.0)
    end
  """)

  /** What the document of `rule` declares and asserts, in order. */
  private def stated(rule: String)(using munit.Location): Seq[String] =
    SmtGen.emitSatisfiabilityCheck(kb, s"test.smt.fheek.$rule") match
      case Right(doc) =>
        doc.linesIterator
          .filter(l => l.startsWith("(declare") || l.startsWith("(assert") || l.startsWith("(define"))
          .toSeq
      case Left(e) => fail(s"$rule: ${e.message}")

  /** The variable of DeBruijn index `n`, as the document names it. */
  private def v(n: Int): String = s"var_${Int.MaxValue - n}"

  test("every place a variable is given a value asks what was written") {
    val d = v(0)
    def named(value: String) = Seq(
      s"(declare-const $d Real)",
      s"(assert (<= $d 10.0))",
      s"(assert (= $d $value))",
      s"(assert (< $d 0.0))"
    )
    val definedBy = Seq(
      s"(declare-const $d Real)",
      s"(assert (= $d 3.0))",
      s"(assert (< (+ $d 1.0) 0.0))"
    )
    assertEquals(stated("eqNamed"), named("3.0"))
    assertEquals(stated("eqDefinedBy"), definedBy)
    assertEquals(stated("eqTwice"), Seq("(assert (= 3.0 4.0))", "(assert (< 3.0 5.0))"))
    assertEquals(stated("oneNamed"), named("3.0"))
    assertEquals(stated("oneDefinedBy"), definedBy)
    assertEquals(stated("entNamed"), "(define-fun cap () Real 5.0)" +: named("cap"))
  }

  test("the one-argument form's own variable is named apart from the clause's") {
    // `oneArg` has two variables; `shifted`'s `?r` is the third, its `?y` the fourth.
    assertEquals(
      stated("oneArg"),
      Seq(
        s"(declare-const ${v(3)} Real)",
        s"(declare-const ${v(0)} Real)",
        s"(assert (>= ${v(3)} 0.0))",
        s"(assert (< ${v(0)} 0.0))",
        s"(assert (>= (+ ${v(3)} 1.0) 0.0))"
      )
    )
  }

  test("an alias given a value gives it to the variable it stands for") {
    val toY = Seq(
      s"(declare-const ${v(0)} Real)",
      s"(assert (= ${v(0)} %s))",
      s"(assert (< ${v(0)} 0.0))"
    )
    assertEquals(stated("aliasEq"), toY.map(_.replace("%s", "5.0")))
    assertEquals(stated("aliasOne"), toY.map(_.replace("%s", "3.0")))
  }

  test("an equation that names its variable is a condition on it") {
    assertEquals(
      stated("itself"),
      Seq(
        s"(declare-const ${v(0)} Real)",
        s"(assert (= ${v(0)} (+ ${v(0)} 1.0)))",
        s"(assert (< ${v(0)} 0.0))"
      )
    )
  }

  test("a caller that writes nothing it hands on has the document it had") {
    assertEquals(stated("control"), Seq("(assert (< (+ 3.0 1.0) 0.0))"))
    assertEquals(
      stated("free"),
      Seq(
        s"(declare-const ${v(1)} Real)",
        s"(assert (<= ${v(1)} 1.0))",
        s"(assert (< (+ ${v(1)} 1.0) 0.0))"
      )
    )
  }
