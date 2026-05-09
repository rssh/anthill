package anthill.smtgen

import scala.collection.mutable.ArrayBuffer

import anthill.kb.KnowledgeBase
import anthill.term.{Term, TermId, Literal}
import anthill.intern.TermSymbol

/** Serialise a tactic into the body of a Z3 `(check-sat-using ...)`
  * form. Mirrors the runtime-term walker in
  * `rustland/anthill-smt-gen/src/tactic_emit.rs` (lines 157-318).
  *
  * Trivial-default elision (`smt` with only preamble-routed params
  * `logic` / `timeout`): returns `None` so the caller emits the
  * canonical `(check-sat)` instead. Without this, every legacy
  * `by z3(logic: "LRA")` proof would emit different bytes and miss
  * the cache.
  *
  * The parse-IR walker (rustland's `emit_tactic_expr` + friends) is
  * out of v0 scope — scaland's tactic IR is ad-hoc and the runtime
  * KB walker covers the CLI dispatch path.
  */
object TacticEmit:

  /** Walk a runtime KB term as a tactic expression at the top level.
    * Returns `None` for the trivial-default `smt(logic: ...)` case.
    */
  def emitTacticFromTerm(kb: KnowledgeBase, term: TermId): Option[String] =
    val (name, argPairs) = kb.getTerm(term) match
      case Term.Ident(sym) => (kb.resolveSym(sym), Vector.empty)
      case Term.Ref(sym)   => (kb.resolveSym(sym), Vector.empty)
      case f: Term.Fn =>
        val pairs = collectArgPairs(f.posArgs, f.namedArgs)
        (kb.resolveSym(f.functor), pairs)
      case _ => return None
    if isDefaultSmtTerm(kb, name, argPairs) then None
    else Some(emitTermInner(kb, name, argPairs))

  /** Always-emit form (no elision) — used recursively for combinator
    * children where `smt` must be preserved verbatim.
    */
  private def emitTermForce(kb: KnowledgeBase, term: TermId): String =
    kb.getTerm(term) match
      case Term.Ident(sym) => kb.resolveSym(sym)
      case Term.Ref(sym)   => kb.resolveSym(sym)
      case f: Term.Fn =>
        val pairs = collectArgPairs(f.posArgs, f.namedArgs)
        emitTermInner(kb, kb.resolveSym(f.functor), pairs)
      case _ => "smt"

  private def collectArgPairs(
    posArgs: IArray[TermId],
    namedArgs: IArray[(TermSymbol, TermId)]
  ): IndexedSeq[(Option[TermSymbol], TermId)] =
    val v = ArrayBuffer.empty[(Option[TermSymbol], TermId)]
    var i = 0
    while i < posArgs.length do
      v += ((None, posArgs(i)))
      i += 1
    i = 0
    while i < namedArgs.length do
      val (sym, tid) = namedArgs(i)
      v += ((Some(sym), tid))
      i += 1
    v.toVector

  private def emitTermInner(
    kb: KnowledgeBase,
    name: String,
    argPairs: IndexedSeq[(Option[TermSymbol], TermId)]
  ): String =
    if name == "raw" then
      argPairs.headOption match
        case Some((_, first)) => kb.getTerm(first) match
          case Term.Const(Literal.StringLit(s)) => s
          case _ => "smt"
        case None => "smt"
    else if argPairs.isEmpty then name
    else emitAppTerm(kb, name, argPairs)

  private def isDefaultSmtTerm(
    kb: KnowledgeBase,
    name: String,
    argPairs: IndexedSeq[(Option[TermSymbol], TermId)]
  ): Boolean =
    if name != "smt" then false
    else argPairs.forall {
      case (Some(sym), _) =>
        val key = kb.resolveSym(sym)
        key == "logic" || key == "timeout"
      case (None, _) => false
    }

  private def emitAppTerm(
    kb: KnowledgeBase,
    name: String,
    argPairs: IndexedSeq[(Option[TermSymbol], TermId)]
  ): String = name match
    case "then"    => emitCombinatorTerm(kb, "then", argPairs)
    case "or_else" => emitCombinatorTerm(kb, "or-else", argPairs)
    case "par"     => emitCombinatorTerm(kb, "par-or", argPairs)
    case "repeat"  => emitRepeatTerm(kb, argPairs)
    case _         => emitUsingParamsTerm(kb, name, argPairs)

  private def emitCombinatorTerm(
    kb: KnowledgeBase,
    kw: String,
    argPairs: IndexedSeq[(Option[TermSymbol], TermId)]
  ): String =
    val out = StringBuilder("(")
    out.append(kw)
    for (_, t) <- argPairs do
      out.append(' ')
      out.append(emitTermForce(kb, t))
    out.append(')')
    out.toString

  private def emitRepeatTerm(
    kb: KnowledgeBase,
    argPairs: IndexedSeq[(Option[TermSymbol], TermId)]
  ): String =
    var tacticTerm: Option[TermId] = None
    var times: Option[Long] = None
    for (nameOpt, t) <- argPairs do
      val key = nameOpt.map(s => kb.resolveSym(s))
      (key, kb.getTerm(t)) match
        case (Some("times"), Term.Const(Literal.IntLit(n))) => times = Some(n)
        case (None, _) => tacticTerm = Some(t)
        case _ => ()
    val inner = tacticTerm.map(t => emitTermForce(kb, t)).getOrElse("smt")
    times match
      case Some(n) => s"(repeat $inner $n)"
      case None    => s"(repeat $inner)"

  private def emitUsingParamsTerm(
    kb: KnowledgeBase,
    name: String,
    argPairs: IndexedSeq[(Option[TermSymbol], TermId)]
  ): String =
    val kv = ArrayBuffer.empty[(String, String)]
    for (nameOpt, t) <- argPairs do
      nameOpt.foreach { sym =>
        val key = kb.resolveSym(sym)
        if key != "logic" && key != "timeout" then
          val valOpt = kb.getTerm(t) match
            case Term.Const(Literal.StringLit(s)) => Some(s"\"$s\"")
            case Term.Const(Literal.IntLit(n))    => Some(n.toString)
            case Term.Const(Literal.BoolLit(b))   => Some(b.toString)
            case _ => None
          valOpt.foreach(v => kv += ((key, v)))
      }
    if kv.isEmpty then name
    else
      val out = StringBuilder(s"(using-params $name")
      for (k, v) <- kv do
        out.append(s" :$k $v")
      out.append(')')
      out.toString
