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

/** What a `LanguageMapping`'s `type_map` field says: which host type carries the values
  * of each anthill SCALAR (`docs/scala-forward-mapping.md` §2.1a).
  *
  * THREE outcomes and not [[LanguageVersion]]'s four, because `type_map` is declared
  * `List[T = TypeMapping]` rather than an `Option`: a profile that maps no scalar says so
  * with the EMPTY list, which is a `Declared(Map.empty)` and not a fourth case. The two
  * that remain are the two that also apply to a version — a profile that never loaded, and
  * a fact that predates the field — and they are kept apart for the same reason.
  */
enum HostTypeMap:
  case Declared(entries: Map[String, String])
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
          case OptionArg.NotAnOption =>
            malformed(language, profile, "language_version",
              "not an Option term; the schema declares Option[T = String]")
          case OptionArg.Wrapped(inner) =>
            stringOf(kb, inner) match
              case Some(v) => LanguageVersion.Declared(v)
              case None =>
                malformed(language, profile, "language_version",
                  "some(<not a string literal>); the schema declares Option[T = String]")

  /** The host type each anthill scalar's values ARE, as this profile declares them.
    *
    * The `hostScalars` half of what [[ScalaTypes]] renders a written name against, and the
    * reason `scala_std.anthill`'s claim about itself ("changing it changes generated code
    * without touching the codegen implementation") is now true: before WI-1060 the emitter
    * carried its own copy of this table and nothing read the fact.
    *
    * FULLY QUALIFIED AND `_root_`-ANCHORED IN THE FACT, not anchored here. What a written
    * `String` must emit is `_root_.java.lang.String` and not `String` — `string.anthill`
    * emits `trait String` into `anthill.prelude`, so a bare mention in a sibling emission
    * binds THAT (WI-1021, measured). A reader that prepended the anchor would have to know
    * each entry's PACKAGE to do it, which is the table's own content; so the fact carries
    * the whole host name, and this returns it verbatim. That is also what makes the
    * mutation test possible: an edit to the fact is visible in the emitted text.
    *
    * A MARSHALLED ENTRY IS REFUSED rather than read as a rename. `lift`/`lower` say the
    * host represents the anthill type differently and values convert at the boundary
    * (WI-088); Bootstrap emits no conversion, so reading such an entry as a plain rename
    * would emit code that type-checks and moves the wrong bytes. A `lang`/`key`-QUALIFIED
    * entry is refused for the same reason from the other side: those are WI-089's keys
    * for the flat form, and an overlay's host type read as the base profile's is the same
    * silent misread.
    */
  def typeMap(
    kb: KnowledgeBase, language: String = "scala", profile: String = "std"
  ): HostTypeMap =
    findMapping(kb, language, profile) match
      case None => HostTypeMap.NoSuchMapping
      case Some(fn) =>
        getNamedArg(kb, fn, "type_map") match
          case None      => HostTypeMap.FieldOmitted
          case Some(tid) => HostTypeMap.Declared(entriesOf(kb, tid, language, profile))

  private def entriesOf(
    kb: KnowledgeBase, tid: TermId, language: String, profile: String
  ): Map[String, String] =
    val elems = kb.getTerm(tid) match
      case fn: Term.Fn if nameOf(kb, fn.functor) == "ListLiteral" => fn.posArgs
      case _ => malformed(language, profile, "type_map", "not a list literal")
    var acc = Map.empty[String, String]
    var i = 0
    while i < elems.length do
      val (anthillType, hostType) = entryOf(kb, elems(i), language, profile)
      // Last-wins would make the SECOND entry the live one and the first dead text,
      // which is precisely the drift this ticket removes from the emitter.
      if acc.contains(anthillType) then
        malformed(language, profile, "type_map", s"two entries for `$anthillType`")
      acc += (anthillType -> hostType)
      i += 1
    acc

  private def entryOf(
    kb: KnowledgeBase, tid: TermId, language: String, profile: String
  ): (String, String) =
    def bad(what: String): Nothing = malformed(language, profile, "type_map", what)
    kb.getTerm(tid) match
      case fn: Term.Fn if nameOf(kb, fn.functor) == "TypeMapping" =>
        // FOUR OF `TypeMapping`'S SIX FIELDS MUST BE ABSENT for an entry this reader can
        // honour, and they fail the same two ways, so there is one reader of "an
        // Option-typed field that must not be written" and two messages for it. A junk
        // value read as "no adapter" is how a marshalled entry would slip through as a
        // plain rename, which is the one thing these checks exist to stop — so
        // `NotAnOption` is refused and never folded into `Absent`.
        def mustBeAbsent(field: String, present: TermId => String): Unit =
          getNamedArg(kb, fn, field).map(optionArg(kb, _)).foreach {
            case OptionArg.Wrapped(inner) => bad(present(inner))
            case OptionArg.NotAnOption =>
              bad(s"a `$field` that is not an Option term; the schema declares " +
                  "Option[T = String]")
            case OptionArg.Absent => ()
          }
        // MARSHALLED: the host holds the value differently and converts at the boundary
        // (WI-088). Bootstrap emits no conversion, so a plain rename would type-check
        // and move the wrong bytes.
        IndexedSeq("lift", "lower").foreach(adapter =>
          mustBeAbsent(adapter, _ =>
            s"a MARSHALLED entry (`$adapter` present); scala-gen emits no value-level " +
            "conversion, so it cannot honour one"))
        // QUALIFIED: `lang` and `key` are WI-089's query keys for the FLAT form — a
        // `TypeMapping` asserted on its own, selected by (language, profile-or-binding).
        // Inside a `LanguageMapping`'s nested `type_map` that selection has already
        // happened, so `realization.anthill` documents `none` for both as
        // "legacy/nested entry" and a written key can only DISAGREE with the fact
        // enclosing it: `key: some("webots")` names a binding OVERLAY, and reading it
        // here emits the webots host type everywhere.
        IndexedSeq("lang", "key").foreach(qualifier =>
          mustBeAbsent(qualifier, inner =>
            s"a `$qualifier`-QUALIFIED entry (${stringOf(kb, inner).getOrElse("?")}); " +
            "that is WI-089's flat keyed form, and a nested type_map is already " +
            "selected by its LanguageMapping's own language and profile"))
        val anthillType = getNamedArg(kb, fn, "anthill_type").flatMap(stringOf(kb, _))
          .getOrElse(bad("an entry with no `anthill_type` string literal"))
        val hostType = getNamedArg(kb, fn, "host_type").flatMap(stringOf(kb, _))
          .getOrElse(bad(s"`$anthillType` mapped to no `host_type` string literal"))
        (anthillType, hostType)
      case _ => bad("an element that is not a `TypeMapping` application")

  private def malformed(
    language: String, profile: String, field: String, what: String
  ): Nothing =
    throw IllegalStateException(
      s"LanguageMapping(language: \"$language\", profile: some(\"$profile\")) " +
      s"has a `$field` that is $what")

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
