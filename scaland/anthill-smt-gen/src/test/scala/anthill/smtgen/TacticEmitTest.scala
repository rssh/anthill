package anthill.smtgen

import anthill.kb.KnowledgeBase
import anthill.term.{Term, TermId, Literal}

/** Mirrors `rustland/anthill-smt-gen/src/tactic_emit.rs::tests`,
  * adapted to drive the runtime-term walker. The rustland tests
  * exercise the parse-IR walker; scaland's runtime walker covers the
  * CLI dispatch path equivalently.
  */
class TacticEmitTest extends munit.FunSuite:

  /** Build a tactic term at the smt-gen tactic position: a Fn with
    * the given functor name and named-arg pairs. Pos args are
    * sub-tactics; named args are param key/value pairs.
    */
  private def fn(
    kb: KnowledgeBase,
    name: String,
    pos: Seq[TermId] = Nil,
    named: Seq[(String, TermId)] = Nil
  ): TermId =
    val functor = kb.intern(name)
    val namedArr: IArray[(anthill.intern.TermSymbol, TermId)] =
      IArray.from(named.map { case (k, v) => (kb.intern(k), v) })
    val posArr: IArray[TermId] = IArray.from(pos)
    kb.alloc(Term.Fn(functor, posArr, namedArr))

  private def bare(kb: KnowledgeBase, name: String): TermId =
    kb.alloc(Term.Ident(kb.intern(name)))

  private def strLit(kb: KnowledgeBase, s: String): TermId =
    kb.alloc(Term.Const(Literal.StringLit(s)))

  private def intLit(kb: KnowledgeBase, n: Long): TermId =
    kb.alloc(Term.Const(Literal.IntLit(n)))

  test("default_smt_elides_to_none") {
    val kb = KnowledgeBase()
    val t = fn(kb, "smt", named = Seq("logic" -> strLit(kb, "LRA")))
    assertEquals(TacticEmit.emitTacticFromTerm(kb, t), None,
      "smt with only logic/timeout params is the default — caller emits (check-sat)")
  }

  test("bare_simplify_emits_name") {
    val kb = KnowledgeBase()
    val t = bare(kb, "simplify")
    assertEquals(TacticEmit.emitTacticFromTerm(kb, t), Some("simplify"))
  }

  test("then_combinator_serialises_as_sexp") {
    val kb = KnowledgeBase()
    val t = fn(kb, "then", pos = Seq(bare(kb, "simplify"), bare(kb, "smt")))
    assertEquals(TacticEmit.emitTacticFromTerm(kb, t), Some("(then simplify smt)"))
  }

  test("or_else_combinator_uses_dashed_keyword") {
    val kb = KnowledgeBase()
    val t = fn(kb, "or_else", pos = Seq(bare(kb, "smt"), bare(kb, "qe")))
    assertEquals(TacticEmit.emitTacticFromTerm(kb, t), Some("(or-else smt qe)"))
  }

  test("par_combinator_uses_par_or") {
    val kb = KnowledgeBase()
    val t = fn(kb, "par", pos = Seq(bare(kb, "smt"), bare(kb, "qe")))
    assertEquals(TacticEmit.emitTacticFromTerm(kb, t), Some("(par-or smt qe)"))
  }

  test("repeat_with_explicit_times") {
    val kb = KnowledgeBase()
    val t = fn(kb, "repeat",
      pos = Seq(bare(kb, "simplify")),
      named = Seq("times" -> intLit(kb, 5)))
    assertEquals(TacticEmit.emitTacticFromTerm(kb, t), Some("(repeat simplify 5)"))
  }

  test("pass_through_with_random_seed") {
    val kb = KnowledgeBase()
    val t = fn(kb, "smt", named = Seq("random_seed" -> intLit(kb, 42)))
    assertEquals(TacticEmit.emitTacticFromTerm(kb, t),
      Some("(using-params smt :random_seed 42)"))
  }

  test("nested_combinators") {
    val kb = KnowledgeBase()
    val inner = fn(kb, "or_else", pos = Seq(bare(kb, "smt"), bare(kb, "qe")))
    val outer = fn(kb, "then", pos = Seq(bare(kb, "simplify"), inner))
    assertEquals(TacticEmit.emitTacticFromTerm(kb, outer),
      Some("(then simplify (or-else smt qe))"))
  }

  test("raw_passes_through_verbatim") {
    val kb = KnowledgeBase()
    val t = fn(kb, "raw", pos = Seq(strLit(kb, "(then simplify smt)")))
    assertEquals(TacticEmit.emitTacticFromTerm(kb, t), Some("(then simplify smt)"))
  }
