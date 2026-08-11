package anthill.smtgen

import anthill.kb.{Facts, KnowledgeBase}
import anthill.term.{Term, TermId}
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
    * backend) match. Returns the first found policy, or None. A
    * malformed record (non-string `predicate` / `backend` field) fails
    * the string reads and is skipped — see `Facts.getNamedStringArg`.
    */
  private def lookupExplicitPolicy(
    kb: KnowledgeBase,
    predicate: String,
    backend: String
  ): Option[PredicatePolicy] =
    Facts.bodylessFacts(kb, "anthill.realization.policy.TranslationPolicy")
      .flatMap { f =>
        val pred = Facts.getNamedStringArg(kb, f, "predicate")
        val bk   = Facts.getNamedStringArg(kb, f, "backend")
        if pred.contains(predicate) && bk.contains(backend) then
          Facts.getNamedArg(kb, f, "policy").flatMap(t => decodePolicyTerm(kb, t))
        else None
      }
      .nextOption()

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
