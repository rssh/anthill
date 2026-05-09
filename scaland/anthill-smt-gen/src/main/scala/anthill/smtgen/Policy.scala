package anthill.smtgen

import anthill.kb.KnowledgeBase
import anthill.term.{Term, TermId, Literal}
import anthill.intern.TermSymbol

/** Per-predicate translation policy lookup (proposal 030 phase δ).
  * Mirrors `rustland/anthill-smt-gen/src/policy.rs`.
  *
  * Reads `TranslationPolicy(predicate, backend, policy)` facts from
  * the KB. Per-backend defaults kick in when no fact is present:
  *   - `LiftedAxiom` for predicates appearing in any `using` clause
  *     (mechanical: a citing proof needs the predicate's claim
  *     forall-quantified as a hypothesis).
  *   - `Inline` otherwise.
  */
enum PredicatePolicy:
  case Inline, DefineFun, DeclareFun, LiftedAxiom

object Policy:

  /** Look up the explicit `TranslationPolicy(...)` fact for a
    * predicate-and-backend pair, or fall back to the inferred
    * default. `citedPredicates` is the union of every proof's
    * `using` clause across the project.
    */
  def policyFor(
    kb: KnowledgeBase,
    predicate: String,
    backend: String,
    citedPredicates: Set[String]
  ): PredicatePolicy =
    lookupExplicitPolicy(kb, predicate, backend) match
      case Some(p) => p
      case None =>
        if citedPredicates.contains(predicate) then PredicatePolicy.LiftedAxiom
        else PredicatePolicy.Inline

  /** Walk `TranslationPolicy` facts looking for an exact (predicate,
    * backend) match. Returns the first found policy, or None.
    */
  private def lookupExplicitPolicy(
    kb: KnowledgeBase,
    predicate: String,
    backend: String
  ): Option[PredicatePolicy] =
    val policySym = kb.tryResolveSymbol("anthill.realization.policy.TranslationPolicy") match
      case Some(s) => s
      case None    => return None
    val rids = kb.byFunctor(policySym)
    var i = 0
    while i < rids.length do
      val rid = rids(i)
      i += 1
      if kb.ruleBody(rid).isEmpty then
        kb.getTerm(kb.ruleHead(rid)) match
          case f: Term.Fn =>
            val pred = readStringField(kb, f.namedArgs, "predicate")
            val bk   = readStringField(kb, f.namedArgs, "backend")
            // Skip the synthetic schema-declaration fact (whose
            // `predicate` / `backend` fields are sort references,
            // not string literals) and any other malformed records.
            if pred.contains(predicate) && bk.contains(backend) then
              getNamedArg(kb, f.namedArgs, "policy")
                .flatMap(t => decodePolicyTerm(kb, t)) match
                  case Some(p) => return Some(p)
                  case None    => ()
          case _ => ()
    None

  private def decodePolicyTerm(kb: KnowledgeBase, tid: TermId): Option[PredicatePolicy] =
    val functor: TermSymbol = kb.getTerm(tid) match
      case f: Term.Fn   => f.functor
      case Term.Ref(s)  => s
      case Term.Ident(s)=> s
      case _ => return None
    val qn = kb.qualifiedNameOf(functor)
    val short = qn.split('.').lastOption.getOrElse(qn)
    short match
      case "Inline"      => Some(PredicatePolicy.Inline)
      case "DefineFun"   => Some(PredicatePolicy.DefineFun)
      case "DeclareFun"  => Some(PredicatePolicy.DeclareFun)
      case "LiftedAxiom" => Some(PredicatePolicy.LiftedAxiom)
      case _             => None

  private def readStringField(
    kb: KnowledgeBase,
    named: IArray[(TermSymbol, TermId)],
    key: String
  ): Option[String] =
    getNamedArg(kb, named, key).flatMap { tid =>
      kb.getTerm(tid) match
        case Term.Const(Literal.StringLit(s)) => Some(s)
        case _ => None
    }

  /** Locate a named-arg value by field name. Mirrors
    * `anthill_core::kb::typing::get_named_arg`.
    */
  private[smtgen] def getNamedArg(
    kb: KnowledgeBase,
    named: IArray[(TermSymbol, TermId)],
    key: String
  ): Option[TermId] =
    var i = 0
    while i < named.length do
      val (sym, tid) = named(i)
      if kb.resolveSym(sym) == key then return Some(tid)
      i += 1
    None
