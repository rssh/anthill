package anthill.smtgen

import scala.collection.mutable.{ArrayBuffer, TreeMap, TreeSet}

import anthill.kb.{KnowledgeBase, RuleId}
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

  /** Map anthill arithmetic functor QNs to SMT-LIB ops. */
  private[smtgen] def mapArithOp(qn: String): Option[String] = qn match
    case "anthill.prelude.Numeric.add" | "Numeric.add" | "add" => Some("+")
    case "anthill.prelude.Numeric.sub" | "Numeric.sub" | "sub" => Some("-")
    case "anthill.prelude.Numeric.mul" | "Numeric.mul" | "mul" => Some("*")
    case "anthill.prelude.Float.div"   | "Float.div"   | "div" => Some("/")
    case "anthill.prelude.Int64.div"     | "Int64.div"             => Some("div")
    case _ => None

  private[smtgen] def mapUnaryOp(qn: String): Option[String] = qn match
    case "anthill.prelude.Float.abs" | "Float.abs" | "abs" => Some("anthill_abs")
    case "anthill.prelude.Int64.abs" => Some("anthill_abs")
    case "anthill.prelude.Float.neg" | "Float.neg" => Some("-")
    case "anthill.prelude.Int64.neg" | "Int64.neg" => Some("-")
    case _ => None

  private[smtgen] def mapInequalityOp(qn: String): Option[String] = qn match
    case "anthill.prelude.Ordered.lte" | "Ordered.lte" | "lte" => Some("<=")
    case "anthill.prelude.Ordered.lt"  | "Ordered.lt"  | "lt"  => Some("<")
    case "anthill.prelude.Ordered.gte" | "Ordered.gte" | "gte" => Some(">=")
    case "anthill.prelude.Ordered.gt"  | "Ordered.gt"  | "gt"  => Some(">")
    case _ => None

  /** Loader desugars `=` to `anthill.prelude.Eq.eq` in goal position;
    * Term.Fn may also carry the unqualified short form during
    * construction.
    */
  private[smtgen] def isEqFunctor(kb: KnowledgeBase, sym: TermSymbol): Boolean =
    val qn = kb.qualifiedNameOf(sym)
    if qn == "=" || qn == "anthill.prelude.Eq.eq" then true
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

  /** Walk the rule body and produce the SMT-LIB equation that defines
    * the head's result variable.
    */
  def collectRule(ruleQn: String): Either[SmtGenError, Unit] =
    visitedRules += ruleQn
    val rid = kb.tryResolveSymbol(ruleQn).flatMap(sym => kb.byFunctor(sym).headOption) match
      case Some(r) => r
      case None    => return Left(SmtGenError(s"rule '$ruleQn' not found"))

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

  /** Process one rule-body goal. */
  def processBodyGoal(
    goal: TermId,
    bindings: TreeMap[String, String]
  ): Either[SmtGenError, Unit] =
    val term = kb.getTerm(goal)
    val fn: Term.Fn = term match
      case f: Term.Fn => f
      case other => return Left(SmtGenError(s"non-Fn body goal: $other"))
    val qn = kb.qualifiedNameOf(fn.functor)

    // Equation goal: `?var = <expr>`.
    if SmtGen.isEqFunctor(kb, fn.functor) then
      if fn.posArgs.length != 2 then
        return Left(SmtGenError(s"= goal: expected 2 pos_args, got ${fn.posArgs.length}"))
      val lhsTerm = kb.getTerm(fn.posArgs(0))
      translateExpr(fn.posArgs(1), bindings) match
        case Left(e) => return Left(e)
        case Right(rhsSmt) =>
          lhsTerm match
            case Term.Var(vid) =>
              bindings(syntheticVarName(vid.id)) = rhsSmt
              return Right(())
            case _ =>
              translateExpr(fn.posArgs(0), bindings) match
                case Left(e) => return Left(e)
                case Right(lhsSmt) =>
                  assertions += s"(= $lhsSmt $rhsSmt)"
                  return Right(())

    // Inequality body goals: lte/lt/gte/gt(a, b).
    SmtGen.mapInequalityOp(qn) match
      case Some(smtOp) =>
        if fn.posArgs.length != 2 then
          return Left(SmtGenError(s"$qn: expected 2 pos_args, got ${fn.posArgs.length}"))
        for
          a <- translateExpr(fn.posArgs(0), bindings)
          b <- translateExpr(fn.posArgs(1), bindings)
        yield
          assertions += s"($smtOp $a $b)"
          ()
        return Right(())
      case None => ()

    // Entity-destructure goal.
    if isKnownEntity(fn.functor) then
      referencedEntities += qn
      var i = 0
      while i < fn.namedArgs.length do
        val (fieldSym, valTerm) = fn.namedArgs(i)
        kb.getTerm(valTerm) match
          case Term.Var(vid) =>
            val fieldName = kb.resolveSym(fieldSym)
            val constName = SmtGen.sanitizeSmtId(fieldName)
            bindings(syntheticVarName(vid.id)) = constName
            if !fieldConsts.contains(constName) then fieldConsts(constName) = 0.0
          case _ => () // wildcards / literals
        i += 1
      return Right(())

    // Abstract mode: don't chase rule calls.
    if abstractMode then
      visitedRules += qn
      return Right(())

    // Rule call (`<ruleQn>(?result)` — single-arg shorthand).
    if fn.posArgs.length == 1 && fn.namedArgs.isEmpty then
      val candidates = kb.byFunctor(fn.functor)
      val hasBody = candidates.exists(rid => kb.ruleBody(rid).nonEmpty)
      if hasBody then
        val bindIdx = kb.getTerm(fn.posArgs(0)) match
          case Term.Var(vid) => vid.id
          case other => return Left(SmtGenError(
            s"v0: rule call's pos arg must be a Var, got $other"))
        translateCalledRule(qn) match
          case Left(e)        => return Left(e)
          case Right(inlined) =>
            bindings(syntheticVarName(bindIdx)) = inlined
            return Right(())

    Left(SmtGenError(s"v0: unhandled body goal functor '$qn'"))

  /** Recursively translate a *called* rule's body to a single SMT-LIB
    * expression — the rule's result, fully inlined.
    */
  def translateCalledRule(calleeQn: String): Either[SmtGenError, String] =
    visitedRules += calleeQn
    val sym = kb.tryResolveSymbol(calleeQn) match
      case Some(s) => s
      case None    => return Left(SmtGenError(s"rule call '$calleeQn' not found"))
    val rid = kb.byFunctor(sym).find(r => kb.ruleBody(r).nonEmpty) match
      case Some(r) => r
      case None    => return Left(SmtGenError(s"rule call '$calleeQn' has no defining clauses"))

    val head = kb.ruleHead(rid)
    val resultIdx = kb.getTerm(head) match
      case f: Term.Fn if f.posArgs.length == 1 => kb.getTerm(f.posArgs(0)) match
        case Term.Var(vid) => vid.id
        case _ => return Left(SmtGenError(
          s"v0: called rule '$calleeQn' head must be ?Var"))
      case _ => return Left(SmtGenError(
        s"v0: called rule '$calleeQn' must have exactly one pos arg in head"))

    val localBindings: TreeMap[String, String] = TreeMap.empty
    val body = kb.ruleBody(rid)
    var i = 0
    while i < body.length do
      processBodyGoal(body(i), localBindings) match
        case Left(e) => return Left(e)
        case Right(_) => ()
      i += 1
    localBindings.get(syntheticVarName(resultIdx)) match
      case Some(s) => Right(s)
      case None => Left(SmtGenError(
        s"called rule '$calleeQn' never bound its result var"))

  /** Translate an arithmetic expression to an SMT-LIB term. */
  def translateExpr(
    term: TermId,
    bindings: TreeMap[String, String]
  ): Either[SmtGenError, String] =
    kb.getTerm(term) match
      case Term.Const(Literal.FloatLit(f))   => Right(SmtGen.formatReal(f.value))
      case Term.Const(Literal.IntLit(i))     => Right(SmtGen.formatReal(i.toDouble))
      case Term.Const(Literal.BigIntLit(bi)) => Right(SmtGen.formatReal(bi.toDouble))
      case Term.Var(vid) =>
        val synth = syntheticVarName(vid.id)
        Right(bindings.getOrElse(synth, synth))
      case Term.Ref(s)   => Right(SmtGen.sanitizeSmtId(kb.resolveSym(s)))
      case Term.Ident(s) => Right(SmtGen.sanitizeSmtId(kb.resolveSym(s)))
      case f: Term.Fn =>
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

  /** True if the symbol resolves to an entity declaration. */
  def isKnownEntity(sym: TermSymbol): Boolean =
    kb.entityFieldNames(sym).isDefined

  /** Classify the rule's head shape. Mirrors rustland's `classify_head`. */
  def classifyHead(rid: RuleId): HeadShape =
    kb.getTerm(kb.ruleHead(rid)) match
      case Term.Bottom => HeadShape.Bottom
      case f: Term.Fn =>
        val qn = kb.qualifiedNameOf(f.functor)
        if SmtGen.isEqFunctor(kb, f.functor)
          || SmtGen.mapInequalityOp(qn).isDefined
          || isKnownEntity(f.functor)
        then HeadShape.Predicate
        else if f.posArgs.length == 1 then
          kb.getTerm(f.posArgs(0)) match
            case Term.Var(vid) => HeadShape.FunctionLike(vid.id)
            case other => HeadShape.Unsupported(
              s"v0: function-like rule head's pos_arg must be Var, got $other")
        else if f.posArgs.isEmpty then
          // Synthesized 0-arg label-functor for transitional multi-head
          // labeled rules (or for denials whose head was synthesized).
          // Behaves like `Term::Bottom` — empty conclusion path.
          HeadShape.Bottom
        else HeadShape.Unsupported(
          s"v0: rule head shape not supported (functor=$qn, pos_args=${f.posArgs.length})")
      case other => HeadShape.Unsupported(s"rule head must be Fn or Bottom, got $other")

  /** For each entity referenced in the rule body, find its (single)
    * ground fact and resolve every field to a Real value.
    */
  def collectFactsForReferencedEntities(): Unit =
    val snapshot = referencedEntities.toVector
    for entityQn <- snapshot do
      kb.tryResolveSymbol(entityQn).foreach { sym =>
        val rids = kb.byFunctor(sym)
        var found = false
        var i = 0
        while !found && i < rids.length do
          kb.getTerm(kb.ruleHead(rids(i))) match
            case f: Term.Fn =>
              val anyConcrete = f.namedArgs.exists { case (_, t) =>
                SmtGen.literalAsReal(kb.getTerm(t)).isDefined
              }
              if anyConcrete then
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
                found = true
            case _ => ()
          i += 1
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


