package anthill.kb

import anthill.term.{Literal, Term, TermId}

/** Field readers over asserted facts — the peer of rustland's
  * `anthill_core::kb::typing::{get_named_arg, get_named_string_arg, unwrap_option}`.
  *
  * These live in `anthill.kb` and not beside their callers because the callers sit in
  * BOTH directions of the dependency graph: `anthill-smt-gen` and `anthill-scala-gen`
  * each `dependsOn(core)`, so a copy in either is unreachable from the other, and until
  * WI-1053 each reader re-derived them privately (Policy, ScalaProfile, TacticEmit).
  */
object Facts:

  /** The `Term.Fn` heads of the body-less clauses asserted under `functorQn`, in
    * assertion order. `Iterator`, so a caller's `find` stops at its match.
    *
    * FACTS ONLY — a BODIED clause under the same functor is a conditional whose
    * conditions a plain reader cannot discharge, and treating its head as a fact would
    * read a claim that may not hold. cpp-gen resolves those properly (WI-760); until a
    * scaland reader needs to, skipping them is the honest half-answer. Before WI-1053
    * this decision was made independently at each walk site (`smtgen.Policy`,
    * `ScalaProfile`) and documented at only one; this is its single home now.
    *
    * `Fn` HEADS ONLY — a body-less clause whose head is a bare `Ident`/`Ref` (a nullary
    * marker fact) has no fields to read, so this walk, whose callers all read named
    * args, skips it. A caller that must see nullary heads needs `byFunctor` directly.
    */
  def bodylessFacts(kb: KnowledgeBase, functorQn: String): Iterator[Term.Fn] =
    kb.tryResolveSymbol(functorQn) match
      case None => Iterator.empty
      case Some(sym) =>
        kb.byFunctor(sym).iterator
          .filter(rid => kb.ruleBody(rid).isEmpty)
          .map(rid => kb.getTerm(kb.ruleHead(rid)))
          .collect { case fn: Term.Fn => fn }

  /** Locate a named-arg value by field name.
    *
    * Core's other keyed reader is `TermView.namedArg`, which keys on `TermSymbol` and
    * returns `Value`; WI-1053 deliberately did NOT layer this on it (nothing read
    * through it yet, and giving it its first consumer was a bigger decision than the
    * ticket). A change to named-arg semantics must visit both.
    */
  def getNamedArg(kb: KnowledgeBase, fn: Term.Fn, key: String): Option[TermId] =
    var i = 0
    while i < fn.namedArgs.length do
      val (sym, tid) = fn.namedArgs(i)
      if kb.resolveSym(sym) == key then return Some(tid)
      i += 1
    None

  /** [[getNamedArg]] narrowed to a string literal — the field kind the realization and
    * proof facts are mostly made of. `None` for an ABSENT field and for one whose value
    * is not a string literal, so a caller that needs those distinguished must ask
    * separately. The non-string half is what lets a string-equality filter over
    * [[bodylessFacts]] skip malformed records: only facts whose selector fields are
    * actual literals can match. (The synthetic schema-declaration fact that filter also
    * used to exclude is no longer asserted — WI-515.)
    */
  def getNamedStringArg(kb: KnowledgeBase, fn: Term.Fn, key: String): Option[String] =
    getNamedArg(kb, fn, key).flatMap(stringOf(kb, _))

  /** Decode a string-literal term. */
  def stringOf(kb: KnowledgeBase, tid: TermId): Option[String] =
    kb.getTerm(tid) match
      case Term.Const(Literal.StringLit(s)) => Some(s)
      case _ => None

  /** An anthill `Option[T]` value as it sits in the KB.
    *
    * `NotAnOption` is what earns this its own type: folding it into `Absent` is what
    * would let a malformed field read as a deliberate `none`. Rustland's
    * `unwrap_option` is the two-state reading; a caller that wants it composes
    * `optionArg(...).wrapped`.
    */
  enum OptionArg:
    case Wrapped(inner: TermId)
    case Absent
    case NotAnOption

    def wrapped: Option[TermId] = this match
      case Wrapped(t) => Some(t)
      case _          => None

  /** Decode `some(x)` / `none`. A nullary constructor reaches the KB as a bare name
    * (`none`) or as a zero-argument application (`none()`), and the stdlib ships both
    * spellings, so both are accepted; `some` likewise wraps positionally or as a single
    * named arg (`some(value: x)`), matching rustland's `unwrap_option`, which reads
    * whichever slot is filled.
    *
    * NO `Var` ARM, deliberately: rustland's loader pads an omitted `Option` field with
    * an unbound var, which `unwrap_option` folds into "absent"; scaland's loader copies
    * `namedArgs` verbatim and synthesises nothing (see [[anthill.codegen.scala.LanguageVersion]]),
    * so a var here is a WRITTEN unbound value and reads as `NotAnOption`.
    */
  def optionArg(kb: KnowledgeBase, tid: TermId): OptionArg =
    kb.getTerm(tid) match
      case fn: Term.Fn if kb.resolveSym(fn.functor) == "some" =>
        if fn.posArgs.length == 1 then OptionArg.Wrapped(fn.posArgs(0))
        else if fn.posArgs.isEmpty && fn.namedArgs.length == 1 then
          OptionArg.Wrapped(fn.namedArgs(0)._2)
        else OptionArg.NotAnOption
      case fn: Term.Fn if kb.resolveSym(fn.functor) == "none" && fn.arity == 0 =>
        OptionArg.Absent
      case Term.Ident(s) if kb.resolveSym(s) == "none" => OptionArg.Absent
      case Term.Ref(s) if kb.resolveSym(s) == "none"   => OptionArg.Absent
      case _ => OptionArg.NotAnOption

end Facts
