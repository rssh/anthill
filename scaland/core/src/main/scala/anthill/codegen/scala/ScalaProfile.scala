package anthill.codegen.scala

import anthill.intern.TermSymbol
import anthill.kb.KnowledgeBase
import anthill.term.{Literal, Term, TermId}

/** What a `LanguageMapping`'s `language_version` field says.
  *
  * FOUR outcomes rather than `Option[String]`, because three unrelated situations would
  * otherwise collapse into `None` and they warrant different responses: a profile that
  * deliberately emits no manifest is fine, a profile that never loaded is a build fault,
  * and a fact that predates the field is schema drift.
  *
  * The distinction is observable in scaland because an omitted named argument is simply
  * ABSENT from the loaded fact — `Loader.reallocTerm` copies `namedArgs` across verbatim
  * and synthesises nothing — so "no such field" and "a field holding `none`" are
  * genuinely different terms. (Rustland's loader pads an omitted field with an unbound
  * var instead, which `realization.anthill` documents; that padding is NOT this
  * implementation's behaviour, and [[ScalaProfile]] must not be read as relying on it.)
  */
enum LanguageVersion:
  /** `language_version: some("3.8.4")`. */
  case Declared(version: String)
  /** `language_version: none` — this profile writes no versioned manifest. */
  case DeclaredAbsent
  /** The fact does not carry the field at all. */
  case FieldOmitted
  /** No `LanguageMapping` fact matched the requested (language, profile). */
  case NoSuchMapping

/** Reads the Scala realization profile out of the KB.
  *
  * `Bootstrap` deliberately cannot do this itself — it is parse-IR-driven with no KB
  * (proposal 034) — so this is the piece that turns a loaded `scala_std` profile into
  * the plain values an emitter takes as parameters. The split is the point: the profile
  * is the single source of truth, and the emitter stays a pure function of its inputs.
  */
object ScalaProfile:

  /** The Scala version a profile declares as its emission target.
    *
    * A missing MAPPING is a value ([[LanguageVersion.NoSuchMapping]]) while a MALFORMED
    * one throws, and that asymmetry is deliberate: "does cobol have a profile?" is a
    * fair question with `no` for an answer, whereas a `language_version` that is neither
    * `some(<string>)` nor `none` is a broken fact, and no answer this returns would be
    * true. Callers that require a mapping to exist say so themselves.
    */
  def languageVersion(
    kb: KnowledgeBase, language: String = "scala", profile: String = "std"
  ): LanguageVersion =
    findMapping(kb, language, profile) match
      case None     => LanguageVersion.NoSuchMapping
      case Some(fn) => versionOf(kb, fn, language, profile)

  private def versionOf(
    kb: KnowledgeBase, fn: Term.Fn, language: String, profile: String
  ): LanguageVersion =
    getNamedArg(kb, fn, "language_version") match
      case None => LanguageVersion.FieldOmitted
      case Some(tid) =>
        optionArg(kb, tid) match
          case OptionArg.Absent      => LanguageVersion.DeclaredAbsent
          case OptionArg.NotAnOption => malformed(language, profile, "not an Option term")
          case OptionArg.Wrapped(inner) =>
            stringOf(kb, inner) match
              case Some(v) => LanguageVersion.Declared(v)
              case None    => malformed(language, profile, "some(<not a string literal>)")

  private def malformed(language: String, profile: String, what: String): Nothing =
    throw IllegalStateException(
      s"LanguageMapping(language: \"$language\", profile: some(\"$profile\")) " +
      s"has a `language_version` that is $what; the schema declares Option[T = String]")

  /** The `Term.Fn` head of the body-less `LanguageMapping` fact for this
    * (language, profile), if one is loaded.
    */
  private def findMapping(
    kb: KnowledgeBase, language: String, profile: String
  ): Option[Term.Fn] =
    val sym = kb.tryResolveSymbol("anthill.realization.LanguageMapping") match
      case Some(s) => s
      case None    => return None
    val rids = kb.byFunctor(sym)
    var i = 0
    while i < rids.length do
      val rid = rids(i)
      i += 1
      // Facts only. A BODIED `LanguageMapping` rule is a conditional mapping whose
      // conditions this reader cannot discharge, and treating its head as a fact would
      // read a mapping that may not hold. cpp-gen resolves those properly (WI-760);
      // until scala-gen needs to, skipping them is the honest half-answer.
      if kb.ruleBody(rid).isEmpty then
        kb.getTerm(kb.ruleHead(rid)) match
          case fn: Term.Fn =>
            val lang = getNamedArg(kb, fn, "language").flatMap(stringOf(kb, _))
            val prof = getNamedArg(kb, fn, "profile")
              .flatMap(t => optionArg(kb, t).wrapped).flatMap(stringOf(kb, _))
            // The schema-declaration fact the loader synthesises for the entity itself
            // carries sort REFERENCES in these slots, not string literals, so it fails
            // this test and is skipped — the same filter `smtgen.Policy` relies on.
            if lang.contains(language) && prof.contains(profile) then return Some(fn)
          case _ => ()
    None

  /** An anthill `Option[T]` value as it sits in the KB.
    *
    * `NotAnOption` is what earns this its own type: folding it into `Absent` is what
    * would let a malformed field read as a deliberate `none`, and every arm below would
    * then be dead code returning what a catch-all already returns.
    */
  private enum OptionArg:
    case Wrapped(inner: TermId)
    case Absent
    case NotAnOption

    def wrapped: Option[TermId] = this match
      case Wrapped(t) => Some(t)
      case _          => None

  /** Decode `some(x)` / `none`. A nullary constructor reaches the KB as a bare name
    * (`none`) or as a zero-argument application (`none()`), and the stdlib ships both
    * spellings, so both are accepted. */
  private def optionArg(kb: KnowledgeBase, tid: TermId): OptionArg =
    kb.getTerm(tid) match
      case fn: Term.Fn if nameOf(kb, fn.functor) == "some" && fn.posArgs.length == 1 =>
        OptionArg.Wrapped(fn.posArgs(0))
      case fn: Term.Fn if nameOf(kb, fn.functor) == "none" && fn.arity == 0 => OptionArg.Absent
      case Term.Ident(s) if nameOf(kb, s) == "none"                        => OptionArg.Absent
      case Term.Ref(s) if nameOf(kb, s) == "none"                          => OptionArg.Absent
      case _ => OptionArg.NotAnOption

  private def stringOf(kb: KnowledgeBase, tid: TermId): Option[String] =
    kb.getTerm(tid) match
      case Term.Const(Literal.StringLit(s)) => Some(s)
      case _ => None

  /** A symbol's scope-local short name — the same reading `getNamedArg` uses for field
    * names, so this file asks the question one way. */
  private def nameOf(kb: KnowledgeBase, sym: TermSymbol): String = kb.resolveSym(sym)

  private def getNamedArg(kb: KnowledgeBase, fn: Term.Fn, key: String): Option[TermId] =
    var i = 0
    while i < fn.namedArgs.length do
      val (sym, tid) = fn.namedArgs(i)
      if kb.resolveSym(sym) == key then return Some(tid)
      i += 1
    None

end ScalaProfile
