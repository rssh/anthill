package anthill.smtgen

import scala.collection.mutable.{ArrayBuffer, TreeMap, TreeSet}

import anthill.kb.{Facts, KnowledgeBase, RuleId}
import anthill.term.{Term, TermId, Literal, VarId}
import anthill.intern.TermSymbol

/** Public errors raised by the smt-gen API. Returned via `Either`,
  * never thrown. */
final case class SmtGenError(message: String)

/** Caller-supplied overrides forwarded to the SMT preamble. */
final case class ProofConfig(
  /** SMT-LIB logic, e.g. "QF_LRA". Defaults to the auto-detected one. */
  logic: Option[String] = None,
  /** Emitted as `(set-option :timeout N)` before `(set-logic ...)`. */
  timeoutMs: Option[Int] = None,
  /** Anthill QN → SMT operator/identifier overrides (stored, not yet
    * consulted; default mapping covers lf1). */
  mapping: Map[String, String] = Map.empty,
  /** Optional Z3 tactic expression. When `Some`, the emitted document
    * closes with `(check-sat-using <expr>)`; when `None`, with the
    * canonical `(check-sat)`. */
  tacticExpr: Option[String] = None,
  /** Emit `(set-option :produce-models true)` + `(get-model)`. */
  produceModels: Boolean = false,
  /** Emit `(set-option :produce-unsat-cores true)` + `(get-unsat-core)`. */
  produceUnsatCores: Boolean = false,
  /** Reserved — wires the option through but `(get-interpolants)` is
    * not yet emitted. */
  produceInterpolants: Boolean = false,
  /** Pre-rendered SMT-LIB clauses (raw S-expr content, without the
    * surrounding `(assert …)`) spliced into the preamble. */
  assumptions: IndexedSeq[String] = Vector.empty,
  /** AbstractLift mode: when true, `processBodyGoal` does NOT chase
    * rule-call goals into their bodies. */
  abstractBody: Boolean = false
)

/** One obligation to discharge: prove `<rule>(?result) ≤ <bound>` for
  * every binding of the rule's body. Translates to
  * `(assert (not (<= rule_result bound)))` + `(check-sat)` — Z3
  * should answer `unsat`.
  *
  * Matched against rules whose head is `<ruleQn>(?result)` — exactly
  * one logic-variable arg, captured as the rule's "result".
  */
final case class Obligation(ruleQn: String, upperBound: Double)

object SmtGen:

  /** Emit a self-contained SMT-LIB document for one obligation. KB
    * must already have the rule and any facts it depends on loaded.
    * Logic is `QF_LRA` by default — decidable, fast.
    */
  def emitObligation(kb: KnowledgeBase, obligation: Obligation): Either[SmtGenError, String] =
    emitObligationWith(kb, obligation, ProofConfig())

  def emitObligationWith(
    kb: KnowledgeBase,
    obligation: Obligation,
    config: ProofConfig
  ): Either[SmtGenError, String] =
    val emitter = Emitter(kb)
    emitter.collectRule(obligation.ruleQn) match
      case Left(err) => Left(err)
      case Right(_) if emitter.resultVar.isEmpty =>
        // AN OBLIGATION IS `<rule>(?result) <= bound`, so a head with no result variable
        // has nothing to bound. `renderUpperBoundWith` interpolates `resultVar` unguarded
        // and emitted `(assert (not (<=  5.0)))` — invalid SMT-LIB returned as `Right`,
        // which `Z3Runner` then reports as "not unsat" rather than as an error.
        //
        // THE HOLE IS OLDER THAN THE ARM THAT FOUND IT (/code-review on
        // WI-20260902-EQG4F item 3, measured both ways). `HeadShape.Predicate` — an
        // entity- or comparison-headed rule — has always left `resultVar` empty and
        // always produced that document; widening `classifyHead` to read a nullary head
        // as `Bottom` merely added a second way in. Refusing on the empty `resultVar`
        // rather than on a head shape covers both, and is the condition the renderer
        // actually depends on.
        Left(SmtGenError(
          s"obligation on '${obligation.ruleQn}': its head binds no result variable " +
            "(only a function-like head `rule f(?r) :- …` can carry an upper bound)"))
      case Right(_) =>
        emitter.collectFactsForReferencedEntities()
        Right(emitter.renderUpperBoundWith(obligation, config))

  /** Emit a satisfiability check for a rule's body, framed as a proof
    * obligation: `unsat` ⇒ body has no solution ⇒ encoded property
    * holds.
    */
  def emitSatisfiabilityCheck(kb: KnowledgeBase, ruleQn: String): Either[SmtGenError, String] =
    emitSatisfiabilityCheckWith(kb, ruleQn, ProofConfig())

  def emitSatisfiabilityCheckWith(
    kb: KnowledgeBase,
    ruleQn: String,
    config: ProofConfig
  ): Either[SmtGenError, String] =
    val emitter = Emitter(kb)
    emitter.abstractMode = config.abstractBody
    emitter.collectRule(ruleQn) match
      case Left(err) => Left(err)
      case Right(_) =>
        emitter.collectFactsForReferencedEntities()
        Right(emitter.renderSatisfiabilityWith(ruleQn, config))

  // ── Helpers (package-private) ─────────────────────────────────────

  /** Splice cited-lemma assumptions into the preamble. */
  private[smtgen] def emitAssumptions(out: StringBuilder, config: ProofConfig): Unit =
    if config.assumptions.isEmpty then return
    out.append("; Cited-lemma assumptions (from `using` clause).\n")
    val seenDecls = scala.collection.mutable.HashSet.empty[String]
    for clause <- config.assumptions do
      for line <- clause.split('\n') do
        if line.trim.nonEmpty then
          if line.startsWith("(declare-const ") && !seenDecls.add(line) then ()
          else
            out.append(line)
            out.append('\n')
    out.append('\n')

  /** Emit the `anthill_abs` prelude when needed. */
  private[smtgen] def emitAbsPrelude(out: StringBuilder, usesAbs: Boolean, config: ProofConfig): Unit =
    val needs = usesAbs || config.assumptions.exists(_.contains("anthill_abs "))
    if needs then
      out.append("(define-fun anthill_abs ((x Real)) Real (ite (< x 0) (- x) x))\n\n")

  private[smtgen] def emitOutcomeOptions(out: StringBuilder, config: ProofConfig): Unit =
    if config.produceModels then out.append("(set-option :produce-models true)\n")
    if config.produceUnsatCores then out.append("(set-option :produce-unsat-cores true)\n")
    if config.produceInterpolants then out.append("(set-option :produce-interpolants true)\n")

  private[smtgen] def emitOutcomeGetters(out: StringBuilder, config: ProofConfig): Unit =
    if config.produceModels then out.append("(get-model)\n")
    if config.produceUnsatCores then out.append("(get-unsat-core)\n")

  private[smtgen] def parseSyntheticVarName(s: String): Option[Int] =
    if s.startsWith("var_") then s.drop(4).toIntOption else None

  /** The number an SMT text is, where it is a numeral as `formatReal` writes one. */
  private[smtgen] def numeral(text: String): Option[Double] =
    if text.startsWith("(- ") && text.endsWith(")") then
      numeral(text.substring(3, text.length - 1)).map(-_)
    else if text.nonEmpty && text.forall(c => c.isDigit || c == '.') then text.toDoubleOption
    else None

  /** Map anthill arithmetic functor QNs to SMT-LIB ops. */
  private[smtgen] def mapArithOp(qn: String): Option[String] = stripAbsolute(qn) match
    // WI-20260825-1WBZT — the SYNTAX CATEGORY declares each of these now (`Additive`,
    // `Multiplicative`; `stdlib/anthill/prelude/arithmetic.anthill`), and `Numeric`
    // reaches them by `provides`. The FULLY-QUALIFIED arm is the only one the move could
    // invalidate, and a stale one does not error — it silently lowers `+` as an
    // uninterpreted function and just weakens the discharge — so that is the arm added.
    //
    // NO `"Additive.add"` / `"Multiplicative.mul"` SORT-QUALIFIED ARM, deliberately. A
    // user's own top-level `sort Additive` with an `add` qualifies its member as exactly
    // `Additive.add`, so a bare arm would lower THAT to SMT `+` and make a discharge
    // silently unsound — the failure rustland's WI-897 keyed `SMT_BUILTINS` on `Symbol`
    // to refuse (`wi897_symbol_identity_test`, "a user's `Numeric.add` is NOT SMT
    // addition"). The `"Numeric.add"` / `"add"` arms below carry that defect already and
    // are left alone as scaland's own WI-897 work; this ticket must not enlarge the
    // population it applies to.
    case "anthill.prelude.Additive.add" | "anthill.prelude.Numeric.add" | "Numeric.add" |
        "add" =>
      Some("+")
    case "anthill.prelude.Additive.sub" | "anthill.prelude.Numeric.sub" | "Numeric.sub" |
        "sub" =>
      Some("-")
    case "anthill.prelude.Multiplicative.mul" | "anthill.prelude.Numeric.mul" |
        "Numeric.mul" | "mul" =>
      Some("*")
    case "anthill.prelude.Divisible.div" | "anthill.prelude.Float.div" | "Float.div" | "div" => Some("/")
    case "anthill.prelude.Int64.div"     | "Int64.div"             => Some("div")
    case _ => None

  /** WI-20260825-KD9SW — a MINTED operator carries an ADDRESS
    * (`..anthill.prelude.Additive.add`), so every arm here would miss it. The marker is
    * stripped ONCE rather than by adding a `..`-prefixed twin to each arm: these are the
    * same names the arms already list, wearing the spelling `parse.Pratt` now mints.
    * Read through `anthill.intern.absolutePathTarget`, the marker's one reader. */
  private[smtgen] def stripAbsolute(qn: String): String =
    anthill.intern.absolutePathTarget(qn).getOrElse(qn)

  private[smtgen] def mapUnaryOp(qn: String): Option[String] = stripAbsolute(qn) match
    case "anthill.prelude.Float.abs" | "Float.abs" | "abs" => Some("anthill_abs")
    case "anthill.prelude.Int64.abs" => Some("anthill_abs")
    case "anthill.prelude.Additive.neg" | "anthill.prelude.Numeric.neg" => Some("-")
    case "anthill.prelude.Float.neg" | "Float.neg" => Some("-")
    case "anthill.prelude.Int64.neg" | "Int64.neg" => Some("-")
    case _ => None

  private[smtgen] def mapInequalityOp(qn: String): Option[String] = stripAbsolute(qn) match
    case "anthill.prelude.PartialOrd.lte" | "anthill.prelude.Ord.lte" | "Ord.lte" | "lte" => Some("<=")
    case "anthill.prelude.PartialOrd.lt"  | "anthill.prelude.Ord.lt"  | "Ord.lt"  | "lt"  => Some("<")
    case "anthill.prelude.PartialOrd.gte" | "anthill.prelude.Ord.gte" | "Ord.gte" | "gte" => Some(">=")
    case "anthill.prelude.PartialOrd.gt"  | "anthill.prelude.Ord.gt"  | "Ord.gt"  | "gt"  => Some(">")
    case _ => None

  /** Loader desugars `=` to `anthill.prelude.Eq.eq` in goal position;
    * Term.Fn may also carry the unqualified short form during
    * construction.
    */
  private[smtgen] def isEqFunctor(kb: KnowledgeBase, sym: TermSymbol): Boolean =
    val qn = stripAbsolute(kb.qualifiedNameOf(sym))
    if qn == "=" || qn == "anthill.prelude.Eq.eq" || qn == "anthill.prelude.PartialEq.eq"
    then true
    else
      val short = kb.resolveSym(sym)
      short == "=" || short == "eq"

  private[smtgen] def literalAsReal(term: Term): Option[Double] = term match
    case Term.Const(Literal.FloatLit(f)) => Some(f.value)
    case Term.Const(Literal.IntLit(i))   => Some(i.toDouble)
    case _ => None

  /** SMT-LIB number formatter. Uses `(- x)` for negatives because
    * SMT-LIB doesn't accept literal `-1.0`.
    */
  private[smtgen] def formatReal(v: Double): String =
    if v < 0.0 then s"(- ${formatReal(-v)})"
    else if v == math.floor(v) && math.abs(v) < 1e15 then f"$v%.1f"
    else v.toString

  /** Keep alphanumerics and `_`; replace anything else with `_`. */
  private[smtgen] def sanitizeSmtId(name: String): String =
    val out = StringBuilder()
    var i = 0
    while i < name.length do
      val c = name.charAt(i)
      if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9') || c == '_'
      then out.append(c)
      else out.append('_')
      i += 1
    out.toString


// ── Implementation ──────────────────────────────────────────────────

/** Outcome of classifying a rule's head for SMT translation. */
private[smtgen] enum HeadShape:
  /** `⊥` denial form — no result var, no conclusion. */
  case Bottom
  /** Predicate / equation / entity destructure. Head IS the
    * conclusion under proposal 032; routed through `processBodyGoal`. */
  case Predicate
  /** `ruleQn(?result)` — single VarId pos_arg as the result variable. */
  case FunctionLike(resultIdx: Int)
  /** Shape the v0 emitter cannot translate; carried message becomes
    * an `SmtGenError`. */
  case Unsupported(msg: String)


private[smtgen] final class Emitter(val kb: KnowledgeBase):
  /** `(field_const, value)` pairs to emit at the top of the document.
    * `TreeMap` for deterministic iteration order. */
  val fieldConsts: TreeMap[String, Double] = TreeMap.empty
  /** Entity QNs seen on rule body LHS that we'll need to materialise. */
  val referencedEntities: TreeSet[String] = TreeSet.empty
  /** Final translated body equation: `(define-fun <result> () Real <expr>)`. */
  var bodySmtlib: String = ""
  /** Name of the rule's result variable. Empty for satisfiability mode. */
  var resultVar: String = ""
  /** Inequality body goals collected as SMT-LIB constraint expressions. */
  val assertions: ArrayBuffer[String] = ArrayBuffer.empty
  /** Conclusion clauses from the unified head-as-conclusion path
    * (proposal 032). For SMT discharge they are negated and conjoined
    * into one `(assert (not (and …)))`; for the lift they are emitted
    * directly inside the implication's right-hand side. */
  var conclusionAssertions: IndexedSeq[String] = Vector.empty
  /** Free SMT vars introduced by body bindings whose definition is
    * missing — must be `(declare-const ... Real)` in satisfiability
    * mode. */
  val freeVars: TreeSet[String] = TreeSet.empty
  /** QNs of every rule visited (top-level + transitive). */
  val visitedRules: TreeSet[String] = TreeSet.empty
  /** Set when an emitted SMT expression uses `anthill_abs`. */
  var usesAbs: Boolean = false
  /** AbstractLift mode: when true, `processBodyGoal` skips rule-call
    * expansion. */
  var abstractMode: Boolean = false
  /** WI-20261012-BR7P3 — THE DE BRUIJN INDEX THE NEXT VARIABLE OF A RULE READ INLINED
    * IS NAMED BY: past the clause's own (`ruleArity`) and every such variable named
    * before it, as rustland's `next_own_variable`. By its own index it would be the
    * clause's variable of that index. `None` until a clause is opened. */
  var nextOwnVariable: Option[Int] = None
  /** The variables `bindVariable` equated with a value, which stay constants of the
    * document: a one-argument rule's result given its value so is given one. */
  val equated: TreeSet[String] = TreeSet.empty
  /** One for each rule read inlined: the name each variable of its frame went by when
    * the frame was opened ([[nameOwnVariables]]). A variable bound to another name
    * since is an ALIAS of that variable. In the clause's own frame a variable goes by
    * its index, and is bound to no name of its own. */
  val inlinedNames: ArrayBuffer[Map[String, String]] = ArrayBuffer.empty

  /** Walk the rule body and produce the SMT-LIB equation that defines
    * the head's result variable.
    */
  def collectRule(ruleQn: String): Either[SmtGenError, Unit] =
    visitedRules += ruleQn
    val rid = kb.tryResolveSymbol(ruleQn).flatMap(sym => kb.byFunctor(sym).headOption) match
      case Some(r) => r
      case None    => return Left(SmtGenError(s"rule '$ruleQn' not found"))

    nextOwnVariable = Some(kb.ruleArity(rid))
    val head = kb.ruleHead(rid)
    val headShape = classifyHead(rid)
    headShape match
      case HeadShape.FunctionLike(idx) => resultVar = syntheticVarName(idx)
      case HeadShape.Unsupported(msg)  => return Left(SmtGenError(msg))
      case _ => ()

    val body = kb.ruleBody(rid)
    val localBindings: TreeMap[String, String] = TreeMap.empty
    var goalErr: Option[SmtGenError] = None
    var i = 0
    while i < body.length && goalErr.isEmpty do
      processBodyGoal(body(i), localBindings) match
        case Left(e)  => goalErr = Some(e)
        case Right(_) => ()
      i += 1
    if goalErr.isDefined then return Left(goalErr.get)

    // Conclusion goals: under the unified encoding the head IS the
    // conclusion (Predicate); routed through processBodyGoal and
    // siphoned into conclusionAssertions.
    val conclusionGoals: IndexedSeq[TermId] = headShape match
      case HeadShape.Predicate => Vector(head)
      case _                   => Vector.empty
    if conclusionGoals.nonEmpty then
      val bodyCount = assertions.length
      var j = 0
      while j < conclusionGoals.length && goalErr.isEmpty do
        processBodyGoal(conclusionGoals(j), localBindings) match
          case Left(e)  => goalErr = Some(e)
          case Right(_) => ()
        j += 1
      if goalErr.isDefined then return Left(goalErr.get)
      conclusionAssertions = assertions.slice(bodyCount, assertions.length).toVector
      assertions.dropRightInPlace(assertions.length - bodyCount)

    // For upper-bound mode the result var must be bound by the body.
    if resultVar.nonEmpty then
      localBindings.get(resultVar) match
        case Some(rhs) =>
          bodySmtlib = s"(define-fun ${SmtGen.sanitizeSmtId(resultVar)} () Real $rhs)"
        case None =>
          return Left(SmtGenError(
            s"rule body never bound the result variable '?$resultVar'"))

    // Free vars: any var_<i> referenced by an assertion expression
    // (body or conclusion) that has no binding entry.
    for assertion <- (assertions.iterator ++ conclusionAssertions.iterator) do
      val tokens = assertion.split("[^a-zA-Z0-9_]+")
      var k = 0
      while k < tokens.length do
        val tok = tokens(k)
        if SmtGen.parseSyntheticVarName(tok).isDefined && !localBindings.contains(tok) then
          freeVars += tok
        k += 1
    Right(())

  /** A goal's or head's FUNCTOR and its argument lists, in either nullary spelling.
    *
    * WI-20260902-CZJ2N stores `f` and `f()` as ONE term, `Term.Ref(f)` — so a `Term.Fn`-only
    * read stopped seeing a nullary head or goal at all. This is rustland's `occ_as_fn`: its
    * body goals are `NodeOccurrence`s whose nullary `Expr::Apply` already answers with empty
    * argument lists, which is why only scaland needed a reader (WI-20260902-EQG4F item 3).
    * `Term.Ident` rides along for the same reason `classifyHead` takes it — an unresolved
    * name is still a 0-ary application, and refusing it here would name the CARRIER where
    * the caller's own "unhandled body goal functor" names the SYMBOL. */
  private def goalAsFn(goal: TermId): Option[(TermSymbol, IArray[TermId], IArray[(TermSymbol, TermId)])] =
    kb.getTerm(goal) match
      case Term.Fn(functor, posArgs, namedArgs) => Some((functor, posArgs, namedArgs))
      case Term.Ref(sym)                        => Some((sym, IArray.empty, IArray.empty))
      case Term.Ident(sym)                      => Some((sym, IArray.empty, IArray.empty))
      case _                                    => None

  /** Process one rule-body goal. */
  def processBodyGoal(
    goal: TermId,
    bindings: TreeMap[String, String]
  ): Either[SmtGenError, Unit] =
    val (functor, posArgs, namedArgs) = goalAsFn(goal) match
      case Some(t) => t
      case None => return Left(SmtGenError(s"non-Fn body goal: ${kb.getTerm(goal)}"))
    val qn = kb.qualifiedNameOf(functor)

    // Equation goal: `?var = <expr>`.
    if SmtGen.isEqFunctor(kb, functor) then
      if posArgs.length != 2 then
        return Left(SmtGenError(s"= goal: expected 2 pos_args, got ${posArgs.length}"))
      val lhsTerm = kb.getTerm(posArgs(0))
      translateExpr(posArgs(1), bindings) match
        case Left(e) => return Left(e)
        case Right(rhsSmt) =>
          lhsTerm match
            // `?x = <a term that names ?x>` defines nothing: it is a CONDITION on `?x`
            // (rustland's WI-20261012-ZZ7PH). Taken for a definition the variable was bound
            // to a term of itself, which named it undeclared.
            case Term.Var(vid) if kb.collectVars(posArgs(1)).exists(_.id == vid.varId.id) =>
              return translateExpr(posArgs(0), bindings).map { itself =>
                assertions += s"(= $itself $rhsSmt)"
                ()
              }
            case Term.Var(vid) =>
              bindVariable(syntheticVarName(vid.varId.id), rhsSmt, bindings)
              return Right(())
            case _ =>
              translateExpr(posArgs(0), bindings) match
                case Left(e) => return Left(e)
                case Right(lhsSmt) =>
                  assertions += s"(= $lhsSmt $rhsSmt)"
                  return Right(())

    // Inequality body goals: lte/lt/gte/gt(a, b).
    SmtGen.mapInequalityOp(qn) match
      case Some(smtOp) =>
        if posArgs.length != 2 then
          return Left(SmtGenError(s"$qn: expected 2 pos_args, got ${posArgs.length}"))
        // RETURN THE `Either`, DO NOT DISCARD IT (/code-review, WI-20260902-EQG4F). This
        // used to compute the `for` and then `return Right(())` regardless: a
        // `translateExpr` failure swallowed its error AND skipped the `assertions +=`, so
        // the premise vanished from the document and the caller was told it was encoded.
        // Measured: `lte(?b, weirdo(1.0))` emitted a document with no `<=` at all. Same
        // antecedent-weakening class as the entity guard two arms below — a lift renders
        // the body as an implication's antecedent, so a dropped premise makes the spliced
        // lemma stronger than what was proved (rustland's WI-897 note).
        return for
          a <- translateExpr(posArgs(0), bindings)
          b <- translateExpr(posArgs(1), bindings)
        yield
          assertions += s"($smtOp $a $b)"
          ()
      case None => ()

    // Entity-destructure goal.
    if isKnownEntity(functor) then
      // A CITATION THAT DESTRUCTURES NOTHING IS REFUSED, NOT DROPPED (/code-review on
      // WI-20260902-EQG4F item 3). Reading a nullary carrier here newly let a BARE entity
      // premise — `:- Params` — reach this arm, where the loop below has no slot to walk
      // and the `Right(())` said "encoded". Measured: the premise vanished from the
      // document with no trace. A lift renders a body as an implication's antecedent, so
      // a dropped premise WEAKENS it and the lemma spliced into the consumer is stronger
      // than anything proved — the unsoundness WI-897 named in rustland's own
      // `process_body_goal`. `Params()` is refused identically, because CZJ2N made the two
      // spellings ONE term. NOT FIXED HERE, and a relative of the same gap: a destructure
      // whose slots are all literals (`Params(base: 2.0)`) also binds nothing, and this
      // arm still accepts it.
      // THE POSITIONAL CHECK COMES FIRST so each message describes its own case. Written
      // the other way round (/code-review), `Params(?b)` — positional-only — took the
      // "binds no field by name" branch and the carefully worded positional message only
      // ever fired for a MIXED citation, a drift the test could not see because it
      // accepted either string.
      if posArgs.nonEmpty then
        // A POSITIONAL SLOT IS WORSE THAN A MISSING ONE. The loop below walks `namedArgs`
        // only, so `Params(?b)` passed a guard written as "no arguments at all" and bound
        // nothing — measured, `?b` stayed a FREE var in the encoding and the premise was
        // gone, which under-constrains rather than merely omits.
        return Left(SmtGenError(
          s"v0: entity premise '$qn' has ${posArgs.length} positional slot(s); an entity " +
            "destructure binds by field name"))
      // A FIELDLESS ENTITY IS NOT A FAILED DESTRUCTURE. `entity heavy_variant` registers
      // with an EMPTY field list, so `isKnownEntity` is true and a blanket
      // `namedArgs.isEmpty` refusal told its author to "write the fields it binds" — advice
      // for fields that cannot exist (/code-review). It falls through to the loop, which
      // walks nothing and registers the entity as REFERENCED, exactly as rustland's arm
      // does: the premise carries no arithmetic, and the fact harvest is what checks it.
      // The refusal below is for a FIELDED entity cited with none of its fields.
      if namedArgs.isEmpty && kb.entityFieldNames(functor).exists(_.nonEmpty) then
        return Left(SmtGenError(
          s"v0: entity premise '$qn' binds no field by name — write the fields it binds"))
      referencedEntities += qn
      var i = 0
      while i < namedArgs.length do
        val (fieldSym, valTerm) = namedArgs(i)
        kb.getTerm(valTerm) match
          case Term.Var(vid) =>
            val fieldName = kb.resolveSym(fieldSym)
            val constName = SmtGen.sanitizeSmtId(fieldName)
            bindVariable(syntheticVarName(vid.varId.id), constName, bindings)
            if !fieldConsts.contains(constName) then fieldConsts(constName) = 0.0
          case _ => () // wildcards / literals
        i += 1
      return Right(())

    // Abstract mode: don't chase rule calls.
    //
    // A RULE CALL IS THE ONLY THING THIS MAY SKIP, and the gate is what says so
    // (/code-review, WI-20260902-EQG4F; rustland's `process_body_goal` gates its twin on
    // `program_clauses_by_functor` for the same WI-897 reason). Ungated, this arm dropped
    // whatever reached it — and reading a nullary carrier newly routed a 0-ary premise
    // here, so `:- flag4` went from a loud `non-Fn body goal` to silently gone.
    //
    // ANY CLAUSE, FACTS INCLUDED — rustland's predicate verbatim, and NOT the `hasBody`
    // one the rule-call arm below uses. A first draft asked for a bodied clause and made
    // this TWO rows stricter instead of one (/code-review): measured, a fact-defined
    // premise (`rule limit(3.0)`) went from skipped-and-`Right` to `unhandled body goal
    // functor`, where rustland still returns `Ok`.
    //
    // THE ONE DELIBERATE DIVERGENCE IS ARITY. Skipping a call is safe because its vars
    // stay FREE and an ambient cited-rule lift re-states it; a 0-ary premise has no vars
    // to leave free and nothing restates it, so it is excluded here even though it names a
    // clause. rustland's gate admits the nullary case its own safety argument does not
    // cover; this is that one row stricter, and no other.
    if abstractMode && posArgs.nonEmpty && kb.byFunctor(functor).nonEmpty then
      visitedRules += qn
      return Right(())

    // Rule call (`<ruleQn>(?result)` — single-arg shorthand).
    //
    // WI-20261012-KF2SD — READ BY THE ONE CLAUSE THAT CAN ANSWER IT, as rustland's
    // `answering_clause` does. The call is a HYPOTHESIS, and a predicate of several
    // clauses holds when any of them does; `find(hasBody)` read it as the first with a
    // body, which is a stronger hypothesis than the rule states — measured, `rule
    // cap(?d) :- ?d = add(2.0, 3.0)` beside `rule cap(?d) :- ?d = add(50.0, 50.0)`
    // emitted `cap(?c)` as `(+ 2.0 3.0)` (`SeveralClausesTest`), and a claim of both was
    // a claim of the first. The argument is a variable (asked below), which rules no
    // clause out, so every clause of ONE argument can answer — a fact too. Several:
    // refused HERE. Rustland reads their disjunction (WI-20261013-1KF32: the body read in
    // a world for each clause, over its fact and inlined readings, which this emitter
    // does not have); this port keeps the refusal (decided with the user, 2026-10-14). A
    // clause of another arity is another predicate.
    //
    // THIS ARM READS A CLAUSE WITH A BODY AND NO FACT (rustland binds the call's variable
    // to a fact's slot; nothing here does). So a fact that answers ALONE is left to the
    // tail's refusal, as a predicate of facts only always was — and is not handed to
    // `translateCalledRule` as if it were a definition (/code-review).
    if posArgs.length == 1 && namedArgs.isEmpty then
      val candidates = kb.byFunctor(functor)
      val answering = candidates.filter { rid =>
        kb.getTerm(kb.ruleHead(rid)) match
          case f: Term.Fn[TermId] => f.posArgs.length + f.namedArgs.length == 1
          case _          => false
      }
      answering.find(rid => kb.ruleBody(rid).nonEmpty) match
        case Some(rid) =>
          val bindIdx = kb.getTerm(posArgs(0)) match
            case Term.Var(vid) => vid.varId.id
            case other => return Left(SmtGenError(
              s"v0: rule call's pos arg must be a Var, got $other"))
          if answering.length > 1 then
            val facts = answering.count(r => kb.ruleBody(r).isEmpty)
            return Left(SmtGenError(
              s"the call of `$qn/1` can be answered by ${answering.length} clauses of the " +
                s"predicate ($facts fact(s), ${answering.length - facts} with a body), and a " +
                "proof reads a call by ONE: the call holds when ANY of them does, which is " +
                "more than the first one says and is not read as their disjunction " +
                "(WI-20261013-1KF32). Give the case this proof is about a predicate of its " +
                "own, or an argument that selects one clause"))
          translateCalledRule(qn, rid) match
            case Left(e)        => return Left(e)
            case Right(inlined) =>
              bindVariable(syntheticVarName(bindIdx), inlined, bindings)
              return Right(())
        // No clause of one argument, and one with a body of another arity: said as it was.
        case None if answering.isEmpty && candidates.exists(r => kb.ruleBody(r).nonEmpty) =>
          return Left(SmtGenError(
            s"v0: called rule '$qn' must have exactly one pos arg in head"))
        case None => ()

    Left(SmtGenError(s"v0: unhandled body goal functor '$qn'"))

  /** Recursively translate a *called* rule's body to a single SMT-LIB
    * expression — the rule's result, fully inlined.
    */
  def translateCalledRule(calleeQn: String, rid: RuleId): Either[SmtGenError, String] =
    visitedRules += calleeQn
    val head = kb.ruleHead(rid)
    val resultIdx = kb.getTerm(head) match
      case f: Term.Fn[TermId] if f.posArgs.length == 1 => kb.getTerm(f.posArgs(0)) match
        case Term.Var(vid) => vid.varId.id
        case _ => return Left(SmtGenError(
          s"v0: called rule '$calleeQn' head must be ?Var"))
      case _ => return Left(SmtGenError(
        s"v0: called rule '$calleeQn' must have exactly one pos arg in head"))

    // WI-20261012-BR7P3 — EVERY VARIABLE OF IT, ITS RESULT TOO, IS ITS OWN: named apart
    // from the document's before the body is read. By its index it was the clause's
    // variable of that index: `shifted(?r) :- ?r = ?y + 1.0, gte(?y, 0.0)` called beside
    // `lt(?z, 0.0)` wrote `shifted`'s `?y` and the caller's `?z` as one variable, and a
    // satisfiable body was unsatisfiable.
    val localBindings: TreeMap[String, String] = TreeMap.empty
    val body = kb.ruleBody(rid)
    val own = nameOwnVariables(head +: body, localBindings) match
      case Left(e)  => return Left(e)
      case Right(o) => o
    inlinedNames += namesOf(localBindings)
    var goalErr: Option[SmtGenError] = None
    var i = 0
    while i < body.length && goalErr.isEmpty do
      processBodyGoal(body(i), localBindings) match
        case Left(e)  => goalErr = Some(e)
        case Right(_) => ()
      i += 1
    inlinedNames.dropRightInPlace(1)
    if goalErr.isDefined then return Left(goalErr.get)
    // The result is what the body gave it: a value, or — given one where the body had
    // written it already — the variable it was named, equated with the value. A body that
    // gives it none defines nothing.
    val result = syntheticVarName(resultIdx)
    val value = localBindings(result)
    if own.get(result).contains(value) && !equated.contains(value) then
      Left(SmtGenError(s"called rule '$calleeQn' never bound its result var"))
    else Right(value)

  /** WI-20261012-BR7P3 — name the variables of a rule read inlined: `frame` gets each
    * `var_<id>` the terms name, in the order they first name them, bound to a name past
    * every name the document has (`nextOwnVariable`). Returned, the names given. */
  private def nameOwnVariables(
    terms: IndexedSeq[TermId],
    frame: TreeMap[String, String]
  ): Either[SmtGenError, Map[String, String]] =
    var next = nextOwnVariable match
      case Some(first) => first
      case None => return Left(SmtGenError(
        "a rule is read inlined before the clause it is read into is opened, so its own " +
          "variables have no names past the clause's"))
    var own = Map.empty[String, String]
    for term <- terms; vid <- kb.collectVars(term) do
      val local = syntheticVarName(vid.id)
      if !frame.contains(local) then
        val named = syntheticVarName(Int.MaxValue - next)
        next += 1
        frame(local) = named
        own += local -> named
    nextOwnVariable = Some(next)
    Right(own)

  /** What each variable of a frame goes by, where it goes by a name — `inlinedNames`. */
  private def namesOf(frame: TreeMap[String, String]): Map[String, String] =
    frame.iterator.filter((_, bound) => SmtGen.parseSyntheticVarName(bound).isDefined).toMap

  /** WI-20261014-FHEEK — `name`, a variable of the frame being read, IS `value`, as
    * rustland's `bind_variable`. Each place a variable is given a value — an equation, an
    * entity's field read by its constant, a one-argument rule's result — substituted, and
    * each left a variable the document had already written undeclared (`lte(?d, 10.0), ?d
    * = 3.0`) or lost what it already was:
    *   * DEFINED as a term: the term is equated with the value — a numeral that is the
    *     value says nothing — where a second definition overwrote the first;
    *   * an ALIAS of another variable (`?x = ?y`, then `?x` given a value): the value is
    *     that variable's, which stays a constant of the document — put in `?x`'s place it
    *     left `?y` free;
    *   * WRITTEN already, in an assertion or in what the frame binds another of its
    *     variables to: the variable stays a constant of the document, and is equated.
    * Otherwise it is bound by substitution, as it always was. */
  private def bindVariable(name: String, value: String, bindings: TreeMap[String, String]): Unit =
    val term = bindings.get(name) match
      case None => name
      case Some(variable) if SmtGen.parseSyntheticVarName(variable).isDefined =>
        if !inlinedNames.lastOption.flatMap(_.get(name)).contains(variable) then
          assertions += s"(= $variable $value)"
          equated += variable
          return
        variable
      case Some(defined) =>
        if !(SmtGen.numeral(defined).isDefined && SmtGen.numeral(defined) == SmtGen.numeral(value))
        then assertions += s"(= $defined $value)"
        return
    if term == value then return
    def names(text: String): Boolean = text.split("[^a-zA-Z0-9_]+").contains(term)
    val written = assertions.exists(names)
      || bindings.exists((other, defined) => other != name && names(defined))
    if written then
      assertions += s"(= $term $value)"
      equated += term
    else bindings(name) = value

  /** Translate an arithmetic expression to an SMT-LIB term. */
  def translateExpr(
    term: TermId,
    bindings: TreeMap[String, String]
  ): Either[SmtGenError, String] =
    kb.getTerm(term) match
      case Term.Const(Literal.FloatLit(f))   => Right(SmtGen.formatReal(f.value))
      case Term.Const(Literal.IntLit(i))     => Right(SmtGen.formatReal(i.toDouble))
      case Term.Const(Literal.BigIntLit(bi)) => Right(SmtGen.formatReal(bi.toDouble))
      // WI-20261012-BR7P3 — a variable nothing binds is the clause's own, and goes by its
      // index. In an inlined rule's frame every variable is named when it is opened.
      case Term.Var(vid) =>
        val synth = syntheticVarName(vid.varId.id)
        bindings.get(synth) match
          case Some(bound)                   => Right(bound)
          case None if inlinedNames.isEmpty => Right(synth)
          case None => Left(SmtGenError(
            s"`?$synth`, read inlined, has no name in the document: every variable of an " +
              "inlined rule is named when its frame is opened"))
      case Term.Ref(s)   => Right(SmtGen.sanitizeSmtId(kb.resolveSym(s)))
      case Term.Ident(s) => Right(SmtGen.sanitizeSmtId(kb.resolveSym(s)))
      case f: Term.Fn[TermId] =>
        val op = kb.qualifiedNameOf(f.functor)
        SmtGen.mapUnaryOp(op) match
          case Some(smtOp) =>
            if f.posArgs.length != 1 then
              Left(SmtGenError(s"$op: expected 1 pos_arg, got ${f.posArgs.length}"))
            else
              translateExpr(f.posArgs(0), bindings).map { a =>
                if smtOp == "anthill_abs" then usesAbs = true
                s"($smtOp $a)"
              }
          case None =>
            SmtGen.mapArithOp(op) match
              case None => Left(SmtGenError(s"v0: unhandled arithmetic op '$op'"))
              case Some(smtOp) =>
                if f.posArgs.length != 2 then
                  Left(SmtGenError(s"$op: expected 2 pos_args, got ${f.posArgs.length}"))
                else
                  for
                    a <- translateExpr(f.posArgs(0), bindings)
                    b <- translateExpr(f.posArgs(1), bindings)
                  yield s"($smtOp $a $b)"
      case other =>
        Left(SmtGenError(s"v0: unhandled term in expression: $other"))

  /** True if an application of the symbol is an entity — its declaration's instance. A
    * constructor's TYPE FACE answers the declaration's fields but builds the type
    * `Foo[…]`, never an instance (WI-20261020-80VNX; rustland's `is_known_entity`). */
  def isKnownEntity(sym: TermSymbol): Boolean =
    !sym.isTypeFace && kb.entityFieldNames(sym).isDefined

  /** Classify the rule's head shape. Mirrors rustland's `classify_head`.
    *
    * WI-20260902-EQG4F item 3 — READ THE NULLARY HEAD THROUGH [[goalAsFn]]. Since
    * WI-20260902-CZJ2N a nullary head is stored `Term.Ref`, so the `Term.Fn`-only match
    * sent BOTH spellings — `rule flag :- …` and `rule flag() :- …` — to `Unsupported`,
    * which the caller turns into a hard `SmtGenError`; the 0-arg arm below became dead
    * code at the same moment. rustland took this arm in CZJ2N itself; scaland did not,
    * and that is the whole of the gap. */
  def classifyHead(rid: RuleId): HeadShape =
    val head = kb.ruleHead(rid)
    kb.getTerm(head) match
      case Term.Bottom => HeadShape.Bottom
      // AN `Ident` HEAD IS REFUSED HERE, though [[goalAsFn]] admits it. Since
      // WI-20260902-CZJ2N `Term.Ident` means exactly "a name nothing in scope answers"
      // (`Loader.reallocTerm`). `processBodyGoal` may read one because it has a loud tail
      // that names the symbol; this has none, so routing it through would classify an
      // unresolved head as `Bottom` and emit a document with the conclusion silently
      // omitted — a new hole of the class this ticket closes (/code-review).
      case Term.Ident(sym) =>
        HeadShape.Unsupported(
          s"rule head `${kb.qualifiedNameOf(sym)}` names nothing in scope")
      case _ =>
        goalAsFn(head) match
          case None =>
            HeadShape.Unsupported(s"rule head must be Fn or Bottom, got ${kb.getTerm(head)}")
          case Some((functor, posArgs, _)) =>
            val qn = kb.qualifiedNameOf(functor)
            if SmtGen.isEqFunctor(kb, functor)
              || SmtGen.mapInequalityOp(qn).isDefined
              || isKnownEntity(functor)
            then HeadShape.Predicate
            else if posArgs.length == 1 then
              kb.getTerm(posArgs(0)) match
                case Term.Var(vid) => HeadShape.FunctionLike(vid.varId.id)
                case other => HeadShape.Unsupported(
                  s"v0: function-like rule head's pos_arg must be Var, got $other")
            else if posArgs.isEmpty then
              // 0-arg predicate head (`rule status_ok :- …`, either spelling), and the
              // synthesized label-functor of a transitional multi-head labeled rule or a
              // denial. Behaves like `Term.Bottom` — empty conclusion path.
              HeadShape.Bottom
            else HeadShape.Unsupported(
              s"v0: rule head shape not supported (functor=$qn, pos_args=${posArgs.length})")

  /** For each entity referenced in the rule body, find its (single)
    * ground fact and resolve every field to a Real value.
    * `Facts.bodylessFacts` (WI-1053) keeps a bodied clause's head from
    * being read as a ground fact — its body is a condition this
    * reader cannot discharge.
    */
  def collectFactsForReferencedEntities(): Unit =
    val snapshot = referencedEntities.toVector
    for entityQn <- snapshot do
      Facts.bodylessFacts(kb, entityQn)
        .find(f => f.namedArgs.exists { case (_, t) =>
          SmtGen.literalAsReal(kb.getTerm(t)).isDefined
        })
        .foreach { f =>
          var j = 0
          while j < f.namedArgs.length do
            val (fieldSym, valTerm) = f.namedArgs(j)
            val fieldName = kb.resolveSym(fieldSym)
            val constName = SmtGen.sanitizeSmtId(fieldName)
            if fieldConsts.contains(constName) then
              SmtGen.literalAsReal(kb.getTerm(valTerm)).foreach { v =>
                fieldConsts(constName) = v
              }
            j += 1
        }

  def renderUpperBoundWith(obligation: Obligation, config: ProofConfig): String =
    val logic = config.logic.getOrElse("QF_LRA")
    val out = StringBuilder()
    out.append(s"; Generated by anthill-smt-gen for obligation ${obligation.ruleQn}.\n")
    out.append(s"; Logic: $logic.\n")
    config.timeoutMs.foreach(t => out.append(s"(set-option :timeout $t)\n"))
    SmtGen.emitOutcomeOptions(out, config)
    out.append(s"(set-logic $logic)\n\n")

    SmtGen.emitAbsPrelude(out, usesAbs, config)

    for (name, value) <- fieldConsts do
      out.append(s"(define-fun $name () Real ${SmtGen.formatReal(value)})\n")
    out.append('\n')

    SmtGen.emitAssumptions(out, config)

    out.append(bodySmtlib)
    out.append("\n\n")

    out.append(s"; Obligation: $resultVar <= ${obligation.upperBound}\n")
    out.append(s"(assert (not (<= ${SmtGen.sanitizeSmtId(resultVar)} ${SmtGen.formatReal(obligation.upperBound)})))\n")
    config.tacticExpr match
      case Some(expr) => out.append(s"(check-sat-using $expr)\n")
      case None       => out.append("(check-sat)\n")
    SmtGen.emitOutcomeGetters(out, config)
    out.toString

  def renderSatisfiabilityWith(ruleQn: String, config: ProofConfig): String =
    val logic = config.logic.getOrElse("LRA")
    val out = StringBuilder()
    out.append(s"; Generated by anthill-smt-gen — satisfiability check for rule $ruleQn.\n")
    out.append("; `unsat` ⇒ rule body has no solution ⇒ encoded property holds.\n")
    config.timeoutMs.foreach(t => out.append(s"(set-option :timeout $t)\n"))
    SmtGen.emitOutcomeOptions(out, config)
    out.append(s"(set-logic $logic)\n\n")

    SmtGen.emitAbsPrelude(out, usesAbs, config)

    for (name, value) <- fieldConsts do
      out.append(s"(define-fun $name () Real ${SmtGen.formatReal(value)})\n")
    out.append('\n')

    for v <- freeVars do
      out.append(s"(declare-const $v Real)\n")
    out.append('\n')

    SmtGen.emitAssumptions(out, config)

    if bodySmtlib.nonEmpty then
      out.append(bodySmtlib)
      out.append("\n\n")

    for assertion <- assertions do
      out.append(s"(assert $assertion)\n")
    if conclusionAssertions.nonEmpty then
      out.append("; Negated conclusion (from `-:` clause).\n")
      val conj = if conclusionAssertions.length == 1 then conclusionAssertions(0)
                 else s"(and ${conclusionAssertions.mkString(" ")})"
      out.append(s"(assert (not $conj))\n")
    config.tacticExpr match
      case Some(expr) => out.append(s"\n(check-sat-using $expr)\n")
      case None       => out.append("\n(check-sat)\n")
    SmtGen.emitOutcomeGetters(out, config)
    out.toString

  private[smtgen] def syntheticVarName(idx: Int): String = s"var_$idx"
end Emitter


