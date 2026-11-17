package anthill.parse

import anthill.term.{Term, Literal}

/** WI-20261109-5VM2G: a literal's type is its spelling. A `BigInt` is written with the
  * suffix `n` (`0n`, `-7n`) and is a `BigInt` whatever its size; an unsuffixed integer is
  * an `Int64`, and one too large for it is refused, naming the suffix. Mirrors rustland's
  * `integer_literal` / `bigint_literal` arms and `grammar.js`'s `bigint_literal`.
  *
  * Backed out (the `bigintLiteral` alternative removed from `literal`), the first row fails
  * at the parse; with the overflow read by `toLong` as before, the second fails on a
  * `NumberFormatException`; with `renderLiteral` printing bare digits, the third fails. */
class BigIntLiteralTest extends munit.FunSuite:

  test("a BigInt literal is a BigInt at any size, signed") {
    val result = Parser.parse("fact big(0n, -7n, 123456789012345678901234567890n)", "big.anthill")
    val pf = result.fold(errs => fail(s"parse failed: ${errs.map(_.message).mkString("; ")}"), identity)
    val fact = pf.items.collect { case Item.FactItem(f) => f }.head
    pf.terms.get(fact.term) match
      case fn: Term.Fn[ParseTermId] =>
        assertEquals(
          fn.posArgs.map(pf.terms.get).toList,
          List(
            Term.Const(Literal.BigIntLit(BigInt(0))),
            Term.Const(Literal.BigIntLit(BigInt(-7))),
            Term.Const(Literal.BigIntLit(BigInt("123456789012345678901234567890")))))
      case other => fail(s"expected Fn, got $other")
  }

  test("an unsuffixed integer too large for Int64 is refused, naming the suffix") {
    Parser.parse("fact big(99999999999999999999)", "over.anthill") match
      case Left(errs) =>
        assert(
          errs.exists(_.message.contains(
            "integer literal 99999999999999999999 overflows Int64; write 99999999999999999999n for a BigInt")),
          errs.map(_.message).mkString("; "))
      case Right(_) => fail("an overflowing Int64 literal parsed")
  }

  test("a BigInt prints with its suffix, so it reads back as a BigInt") {
    assertEquals(Parser.renderLiteral(Literal.BigIntLit(BigInt(5))), "5n")
    assertEquals(Parser.renderLiteral(Literal.IntLit(5)), "5")
  }
