package anthill.load

import anthill.kb.LoadFixture

/** WI-20260823-53W12 — A BRACKET ON A CALLABLE BINDS ITS TYPE PARAMETERS, NEVER ITS
  * ARGUMENTS (rustland's `wi_53w12_type_value_in_clause_test` and the head rows of
  * `wi_c7anm_head_parameter_column_test` / `wi_s8jyf_provision_spelling_test`; proposal 060
  * §2.1: a rule is an operation). Written alone on a relation it is refused, in a goal, in
  * data and at a clause's own head; it was read as the argument list, `mine[1, 2]`
  * answering as `mine(1, 2)` and `fact myrel[T = Red]` storing a column `T`.
  *
  * BACKED OUT (the check in `reallocTerm` taken out): the three refusal rows fail. The
  * control passes either way, by design. */
class BracketOnCallableTest extends munit.FunSuite:

  private def program(decl: String): String =
    s"""namespace zzbracket
       |  sort Red
       |    entity red
       |  end
       |  fact seed(1, 2)
       |  rule mine(?a, ?b) :- seed(?a, ?b)
       |  $decl
       |end
       |""".stripMargin

  test("a bracket alone on a relation is refused in a goal and in data") {
    for decl <- Seq("rule r(1) :- mine[1, 2]", "rule r(1) :- not(mine[1, 2])", "fact holds(mine[1, 2])") do
      val errs = LoadFixture.refusal("bracket.anthill" -> program(decl))
      assertEquals(errs.count(_.contains("`mine[…]` is a bracket on an operation or a relation")), 1,
        s"`$decl` is refused, once: $errs")
  }

  test("a bracketed head on a relation is refused in both spellings") {
    for decl <- Seq("fact myrel[T = Red]", "rule myrel[T = Red] :- mine(?a, ?b)") do
      val errs = LoadFixture.refusal("bracket.anthill" -> program(decl))
      assertEquals(errs.count(_.contains("`myrel[…]` declares the relation `myrel` with a bracket")), 1,
        s"`$decl` is refused, once: $errs")
  }

  test("a qualified bracketed head and a bracket on a const are refused") {
    val qualified = LoadFixture.refusal("bracket.anthill" -> program("fact zzbracket.myrel[T = Red]"))
    assertEquals(qualified.count(_.contains("`zzbracket.myrel[…]` declares the relation")), 1, s"$qualified")
    val const = LoadFixture.refusal("bracket.anthill" ->
      program("const seven: anthill.prelude.Int64 = 7\n  fact holds(seven[1])"))
    assertEquals(const.count(_.contains("`seven[…]` writes type arguments of `seven`, which takes none")), 1,
      s"$const")
  }

  test("a call's parentheses and a sort's bracket keep their readings") {
    val kb = LoadFixture.loaded(program(
      "fact myrel(T: Red)\n  rule viaColumn(?t) :- myrel(T: ?t)\n  rule viaCall(?x) :- mine(?x, 2)\n  fact held(red[])"),
      "bracket.anthill")
    assertEquals(LoadFixture.unaryAnswers(kb, "zzbracket.viaColumn"), 1)
    assertEquals(LoadFixture.unaryAnswers(kb, "zzbracket.viaCall"), 1)
  }
