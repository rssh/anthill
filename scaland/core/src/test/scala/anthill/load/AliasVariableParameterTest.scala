package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.parse.{Item, Parser, TypeExpr}

/** WI-20261003-EK43F — a named variable written in the definition of a type alias member is a
  * parameter of the sort the alias is a member of (kernel-language §8.1, *Type aliases*):
  * `sort Holder  sort P = Pair[?A, ?B]  end` declares `A` and `B` as `sort A = ?` does, and the
  * variable is the parameter's name. rustland's `wi_ek43f_alias_variable_parameter_test`; scaland
  * has no typer, so what it holds to is the declaration: the parameters the sort registers, and
  * the refusal of a variable naming another member.
  *
  * CONTROL: with `declareAliasBindingVariables` edited out, the first two tests fail — `Holder`
  * registers no parameter, and the clash parses clean. The third passes either way by design:
  * it holds the desugar to declaring nothing for `?X` and `?_`. */
class AliasVariableParameterTest extends munit.FunSuite:

  private def holder(members: String): String =
    s"""sort Pair
       |  sort A = ?
       |  sort B = ?
       |  entity pair(a: A, b: B)
       |end
       |sort Holder
       |$members
       |  entity holder(p: P)
       |end""".stripMargin

  private def typeParamsOf(kb: KnowledgeBase, sort: String): Set[String] =
    val sym = kb.symbols.scope(kb.globalScope).flatMap(_.locals.get(sort))
      .getOrElse(fail(s"$sort not defined in global scope"))
    kb.symbols.scope(kb.symbols.scopeOf(sym)).getOrElse(fail(s"no $sort scope")).typeParams.toSet

  test("a named variable in a member's binding is a parameter of the sort") {
    val kb = LoadFixture.loaded(holder("  sort P = Pair[?A, ?B]"), "<ek43f>")
    assertEquals(typeParamsOf(kb, "Holder"), Set("A", "B"))
    val written = LoadFixture.loaded(holder("  sort A = ?\n  sort B = ?\n  sort P = Pair[A, B]"), "<ek43f-w>")
    assertEquals(typeParamsOf(written, "Holder"), Set("A", "B"))
    // The alias names the parameter, as the written twin does.
    val pf = LoadFixture.parsed(holder("  sort P = Pair[?A, ?B]"), "<ek43f-ir>")
    val members = pf.items.collect { case Item.SortWithBodyItem(s) => s }
      .find(s => pf.symbols.name(s.name.last) == "Holder").getOrElse(fail("no Holder")).items
    val p = members.collectFirst {
      case Item.AbstractSortItem(a) if pf.symbols.name(a.name.last) == "P" => a.definition
    }.getOrElse(fail("no P"))
    p match
      case TypeExpr.Parameterized(_, bindings) =>
        assertEquals(bindings.map(_.bound).collect { case TypeExpr.Simple(n) => pf.symbols.name(n.last) }, IndexedSeq("A", "B"))
      case other => fail(s"P should apply Pair, got $other")
  }

  test("a variable naming another member of the sort is refused") {
    for (member, kind) <- Seq(("  entity A(x: Int64)", "an entity"), ("  sort A = Int64", "a type alias")) do
      Parser.parse(holder(s"$member\n  sort P = Pair[?A, ?B]"), "<ek43f-clash>") match
        case Right(_) => fail(s"$kind: expected a refusal, the file parsed")
        case Left(errs) =>
          val joined = errs.map(_.message).mkString(" | ")
          assert(joined.contains(s"writes the sort's parameter `A`, but the sort declares `A` as $kind"), joined)
  }

  test("a variable a parameter is declared with is that parameter, and `?_` declares none") {
    val declared = LoadFixture.loaded(holder("  sort T = ?X\n  sort P = Pair[?X, ?X]"), "<ek43f-d>")
    assertEquals(typeParamsOf(declared, "Holder"), Set("T"))
    val anonymous = LoadFixture.loaded(holder("  sort P = Pair[?_, ?_]"), "<ek43f-u>")
    assertEquals(typeParamsOf(anonymous, "Holder"), Set.empty[String])
  }
