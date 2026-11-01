package anthill.smtgen

/** WI-20261014-VVRHJ — AN ENTITY'S FIELD IS THE ENTITY'S — rustland's
  * `wi_vvrhj_field_constant_test`, for what this emitter reads (it lifts no lemma). A field
  * read as a constant of a document is named by the entity's qualified name with the field
  * (`test.smt.vvrhj.A.cap`): it was the field's short name, one constant for every entity
  * with a field so named, set to the fact read last. A field is read off the entity's ONE
  * fact: an entity of no fact, of several facts, and a field the fact gives no number are
  * refused — they were 0.0, the first fact's, and 0.0. And a token of the document is what
  * stands between parentheses and blanks: `var_0` in `test.smt.vvrhj.E.var_0` is no variable.
  *
  * WHAT FAILS WHEN A PART IS BACKED OUT (measured, each alone, by a temporary switch): the
  * field named by its short name — `two entities…` and `a field named like a variable…`
  * (and `CommDelayTest`, `InlinedNamesTest`, which pin the names); the field of no fact read
  * as 0.0 — `an entity of no fact…`; several facts read as the first, and a field of no
  * number read as 0.0 — `an entity of several facts…`; the scan splitting a qualified name —
  * `a field named like a variable…`. None passes either way.
  */
class FieldConstantTest extends munit.FunSuite:

  private lazy val kb = Common.loadKbWith("""
    namespace test.smt.vvrhj
      import anthill.prelude.{Float}
      import anthill.prelude.PartialOrd.{gte, lte}

      entity A(cap: Float)
      entity B(cap: Float)
      fact A(cap: 5.0)
      fact B(cap: 1.0)
      rule small :- A(cap: ?a), B(cap: ?b), gte(?a, 2.0)
      rule twin :- A(cap: ?a), B(cap: ?b), lte(?a, 3.0)

      entity Lim(cap: Float)
      rule noFact :- Lim(cap: ?c), gte(?c, -1.0)

      entity Two(cap: Float)
      fact Two(cap: 5.0)
      fact Two(cap: -1.0)
      rule twoFacts :- Two(cap: ?c), lte(?c, 0.0)

      entity Any(cap: Float)
      fact Any(cap: ?v)
      rule anyValue :- Any(cap: ?c), lte(?c, 0.0)

      entity E(var_0: Float)
      fact E(var_0: 5.0)
      rule varField :- E(var_0: ?v), lte(?v, 9.0)
    end
  """)

  private def document(rule: String)(using munit.Location): String =
    SmtGen.emitSatisfiabilityCheck(kb, s"test.smt.vvrhj.$rule") match
      case Right(doc) => doc
      case Left(e)    => fail(s"$rule: ${e.message}")

  test("two entities with a field of one name are two constants") {
    val small = document("small")
    for line <- Seq(
        "(define-fun test.smt.vvrhj.A.cap () Real 5.0)",
        "(define-fun test.smt.vvrhj.B.cap () Real 1.0)",
        "(assert (>= test.smt.vvrhj.A.cap 2.0))")
    do assert(small.linesIterator.contains(line), s"$line:\n$small")
    assume(Z3Runner.available, "z3 not on PATH")
    // `small`'s body holds at a = 5, and `twin`'s at no a.
    assertEquals(Z3Runner.run("vvrhj_small", small), "sat")
    assertEquals(Z3Runner.run("vvrhj_twin", document("twin")), "unsat")
  }

  private def refusal(rule: String)(using munit.Location): String =
    SmtGen.emitSatisfiabilityCheck(kb, s"test.smt.vvrhj.$rule") match
      case Right(doc) => fail(s"$rule is read:\n$doc")
      case Left(e)    => e.message

  test("an entity of no fact is refused") {
    val said = refusal("noFact")
    assert(
      said.contains(
        "the entity `test.smt.vvrhj.Lim` has no fact, and a premise here reads its fields off one"),
      said)
  }

  // Each was read: `twoFacts` as `cap` = 5.0, the first fact, unsat where -1.0 is a model;
  // `anyValue` as `cap` = 0.0, which the first fact with a number set nothing for.
  test("an entity of several facts, and a field of no number, are refused") {
    val two = refusal("twoFacts")
    assert(two.contains("the entity `test.smt.vvrhj.Two` has 2 facts"), two)
    val any = refusal("anyValue")
    assert(
      any.contains("reads the field `cap` of the entity's fact, whose value there is none or no number"),
      any)
  }

  test("a field named like a variable is no variable of the document") {
    val doc = document("varField")
    assert(doc.linesIterator.contains("(define-fun test.smt.vvrhj.E.var_0 () Real 5.0)"), doc)
    assert(!doc.linesIterator.contains("(declare-const var_0 Real)"), doc)
  }
