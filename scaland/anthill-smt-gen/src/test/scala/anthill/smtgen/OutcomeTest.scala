package anthill.smtgen

class OutcomeTest extends munit.FunSuite:

  test("parse_unsat_only") {
    val d = Outcome.parseZ3Output("unsat\n")
    assertEquals(d.verdict, "unsat")
    assert(d.modelText.isEmpty)
    assert(d.unsatCore.isEmpty)
  }

  test("parse_sat_with_model") {
    val z3 = "sat\n(\n  (define-fun x () Int 5)\n  (define-fun y () Bool true)\n)\n"
    val d = Outcome.parseZ3Output(z3)
    assertEquals(d.verdict, "sat")
    assert(d.modelText.contains("define-fun x"))
    assertEquals(d.variableAssignments.length, 2)
    assertEquals(d.variableAssignments(0), ("x", "5"))
    assertEquals(d.variableAssignments(1), ("y", "true"))
  }

  test("parse_model_keyword_form") {
    val z3 = "sat\n(model\n  (define-fun x () Int 42)\n)\n"
    val d = Outcome.parseZ3Output(z3)
    assertEquals(d.verdict, "sat")
    assertEquals(d.variableAssignments.length, 1)
    assertEquals(d.variableAssignments(0), ("x", "42"))
  }

  test("parse_unsat_with_core") {
    val z3 = "unsat\n(a1 a2 a3)\n"
    val d = Outcome.parseZ3Output(z3)
    assertEquals(d.verdict, "unsat")
    assertEquals(d.unsatCore, Vector("a1", "a2", "a3"))
  }

  test("parse_unknown") {
    val d = Outcome.parseZ3Output("unknown\n")
    assertEquals(d.verdict, "unknown")
    assert(d.modelText.isEmpty)
    assert(d.unsatCore.isEmpty)
  }

  test("parse_sat_with_model_and_negative_value") {
    val z3 = "sat\n(\n  (define-fun d_next () Real (- 1.5))\n)\n"
    val d = Outcome.parseZ3Output(z3)
    assertEquals(d.verdict, "sat")
    assertEquals(d.variableAssignments.length, 1)
    assertEquals(d.variableAssignments(0)._1, "d_next")
    assert(d.variableAssignments(0)._2.contains("- 1.5"),
      s"expected '- 1.5' to surface in value: ${d.variableAssignments(0)._2}")
  }

  test("malformed_input_doesnt_panic") {
    Outcome.parseZ3Output("")
    Outcome.parseZ3Output("(((((")
    Outcome.parseZ3Output("not even a verdict")
  }
