package anthill.resolve

import anthill.kb.{KnowledgeBase, BuiltinTag, RuleId}
import anthill.term.{Term, TermId}
import anthill.subst.Substitution
import scala.collection.mutable.ArrayBuffer

// ── Delay mode ──────────────────────────────────────────────────

private enum DelayMode:
  case Normal
  case Delayed(consecutiveDelays: Int)

  def reset: DelayMode = this match
    case Normal => Normal
    case Delayed(_) => Delayed(0)

// ── Frame state ─────────────────────────────────────────────────

private enum FrameState:
  case Init(delayMode: DelayMode)
  case ChoicePoint(
    delayMode: DelayMode,
    originalGoal: TermId,
    candidates: ArrayBuffer[(RuleId, Substitution)],
    var next: Int,
    var anyDelayed: Boolean,
    var childSolutions: Int
  )

// ── Frame ───────────────────────────────────────────────────────

private class Frame(
  var goals: ArrayBuffer[TermId],
  var subst: Substitution,
  var depth: Int,
  var state: FrameState
)

// ── Step result ─────────────────────────────────────────────────

private enum StepResult:
  case Continue
  case YieldSolution(sol: Solution)

// ── SearchStream ────────────────────────────────────────────────

/** Lazy search stream that yields one solution at a time via splitFirst.
  * Converts recursive DFS into an explicit choice-point stack.
  */
class SearchStream private (
  private val stack: ArrayBuffer[Frame],
  private val config: ResolveConfig
):

  /** Yield the next solution, returning continuation. */
  def splitFirst(kb: KnowledgeBase): Option[(Solution, SearchStream)] =
    while stack.nonEmpty do
      step(kb) match
        case Some(StepResult.Continue) => // keep going
        case Some(StepResult.YieldSolution(sol)) => return Some((sol, this))
        case None => return None
    None

  def isEmpty: Boolean = stack.isEmpty

  /** Collect all solutions (up to maxSolutions). */
  def allSolutions(kb: KnowledgeBase): ArrayBuffer[Solution] =
    val results = ArrayBuffer.empty[Solution]
    var stream = this
    var continue = true
    while continue do
      stream.splitFirst(kb) match
        case Some((sol, next)) =>
          results += sol
          stream = next
          if config.maxSolutions > 0 && results.length >= config.maxSolutions then
            continue = false
        case None =>
          continue = false
    results

  /** Convert to LazyList. */
  def toLazyList(kb: KnowledgeBase): LazyList[Solution] =
    splitFirst(kb) match
      case None => LazyList.empty
      case Some((sol, next)) => sol #:: next.toLazyList(kb)

  private def step(kb: KnowledgeBase): Option[StepResult] =
    if stack.isEmpty then return None
    val frame = stack.last
    frame.state match
      case _: FrameState.Init => stepInit(kb)
      case _: FrameState.ChoicePoint => stepChoicePoint(kb)

  private def stepInit(kb: KnowledgeBase): Option[StepResult] =
    val frame = stack.last
    val depth = frame.depth
    val delayMode = frame.state match
      case FrameState.Init(dm) => dm
      case _ => return Some(StepResult.Continue) // unreachable

    // 1. Depth limit
    if depth > config.maxDepth then
      stack.remove(stack.length - 1)
      return Some(StepResult.Continue)

    // 2. Floundering: all goals delayed
    delayMode match
      case DelayMode.Delayed(cd) if cd >= frame.goals.length =>
        val sol = Solution(frame.subst.snapshot(), frame.goals.toIndexedSeq)
        stack.remove(stack.length - 1)
        recordSolutionInAncestors()
        return Some(StepResult.YieldSolution(sol))
      case _ =>

    // 3. Goals empty → solution
    if frame.goals.isEmpty then
      val sol = Solution(frame.subst.snapshot(), IndexedSeq.empty)
      stack.remove(stack.length - 1)
      recordSolutionInAncestors()
      return Some(StepResult.YieldSolution(sol))

    val goal = frame.goals(0)

    // 4. Builtin
    kb.getBuiltin(goal) match
      case Some(BuiltinTag.Not) =>
        return stepNaf(kb, goal, depth, delayMode)
      case Some(tag) =>
        Builtins.execute(kb, tag, goal, frame.subst) match
          case BuiltinResult.Success =>
            val newGoals = ArrayBuffer.from(frame.goals.drop(1))
            val newDelay = delayMode.reset
            frame.goals = newGoals
            frame.depth = depth + 1
            frame.state = FrameState.Init(newDelay)
            return Some(StepResult.Continue)

          case BuiltinResult.SuccessWithBindings(extra) =>
            val newGoals = ArrayBuffer.from(frame.goals.drop(1))
            frame.subst.bindCompressed(extra.bindings, kb.terms)
            val newDelay = delayMode.reset
            frame.goals = newGoals
            frame.depth = depth + 1
            frame.state = FrameState.Init(newDelay)
            return Some(StepResult.Continue)

          case BuiltinResult.Failure =>
            stack.remove(stack.length - 1)
            return Some(StepResult.Continue)

          case BuiltinResult.Delay =>
            return handleDelay(frame, goal, depth, delayMode)
      case None =>

    // 5. Non-builtin: query discrimination tree
    var candidates = kb.query(goal)

    // Filter equations
    candidates = candidates.filter((rid, _) => !kb.isEquation(rid))

    frame.state = FrameState.ChoicePoint(
      delayMode, goal, candidates, next = 0, anyDelayed = false, childSolutions = 0
    )
    Some(StepResult.Continue)

  private def stepChoicePoint(kb: KnowledgeBase): Option[StepResult] =
    val frame = stack.last
    val cp = frame.state match
      case cp: FrameState.ChoicePoint => cp
      case _ => return Some(StepResult.Continue)

    if cp.next >= cp.candidates.length then
      // All candidates exhausted
      stack.remove(stack.length - 1)
      return Some(StepResult.Continue)

    val (rid, treeSubst) = cp.candidates(cp.next)
    cp.next += 1

    val body = kb.ruleBody(rid)
    if body.isEmpty then
      // Ground fact match — merge tree_subst with path compression
      val newSubst = frame.subst.snapshot()
      newSubst.bindCompressed(treeSubst.bindings, kb.terms)
      if newSubst.isContradiction then
        return Some(StepResult.Continue)

      val newGoals = ArrayBuffer.from(frame.goals.drop(1))
      val appliedGoals = ArrayBuffer.from(newGoals.map(g => kb.applySubst(g, newSubst)))

      val newDelay = cp.delayMode.reset

      stack += Frame(appliedGoals, newSubst, frame.depth + 1, FrameState.Init(newDelay))
    else
      // Rule with body — instantiate with fresh vars
      val (freshBody, answerLinks) = kb.withFreshVars(rid, treeSubst)

      val newSubst = frame.subst.snapshot()
      newSubst.bindCompressed(answerLinks.bindings, kb.terms)
      if newSubst.isContradiction then
        return Some(StepResult.Continue)

      val remainingGoals = ArrayBuffer.from(frame.goals.drop(1))
      val appliedRemaining = ArrayBuffer.from(remainingGoals.map(g => kb.applySubst(g, newSubst)))
      val newGoals = ArrayBuffer.from(freshBody) ++= appliedRemaining

      val newDelay = cp.delayMode.reset

      stack += Frame(newGoals, newSubst, frame.depth + 1, FrameState.Init(newDelay))

    Some(StepResult.Continue)

  private def stepNaf(
    kb: KnowledgeBase, goal: TermId, depth: Int, delayMode: DelayMode
  ): Option[StepResult] =
    val frame = stack.last
    val innerGoal = Builtins.firstArg(kb, goal)
    val reified = kb.reify(innerGoal, frame.subst)

    Builtins.isGround(kb, reified, Substitution()) match
      case GroundCheck.HasVar =>
        handleDelay(frame, goal, depth, delayMode)
      case GroundCheck.Ground =>
        // Run sub-resolution
        val subStream = SearchStream.create(kb, ArrayBuffer(reified), Substitution(), config)
        val hasSolution = subStream.splitFirst(kb).isDefined
        if hasSolution then
          // Inner goal succeeded → not(Goal) fails
          stack.remove(stack.length - 1)
          Some(StepResult.Continue)
        else
          // Inner goal failed → not(Goal) succeeds
          val newGoals = ArrayBuffer.from(frame.goals.drop(1))
          val newDelay = delayMode match
            case DelayMode.Normal => DelayMode.Normal
            case DelayMode.Delayed(_) => DelayMode.Delayed(0)
          frame.goals = newGoals
          frame.depth = depth + 1
          frame.state = FrameState.Init(newDelay)
          Some(StepResult.Continue)

  private def handleDelay(
    frame: Frame, goal: TermId, depth: Int, delayMode: DelayMode
  ): Option[StepResult] =
    delayMode match
      case DelayMode.Normal =>
        if frame.goals.length == 1 then
          val sol = Solution(frame.subst.snapshot(), IndexedSeq(goal))
          stack.remove(stack.length - 1)
          recordSolutionInAncestors()
          Some(StepResult.YieldSolution(sol))
        else
          val rotated = ArrayBuffer.from(frame.goals.drop(1))
          rotated += goal
          frame.goals = rotated
          frame.depth = depth + 1
          frame.state = FrameState.Init(DelayMode.Delayed(1))
          Some(StepResult.Continue)
      case DelayMode.Delayed(cd) =>
        val rotated = ArrayBuffer.from(frame.goals.drop(1))
        rotated += goal
        frame.goals = rotated
        frame.depth = depth + 1
        frame.state = FrameState.Init(DelayMode.Delayed(cd + 1))
        Some(StepResult.Continue)

  private def recordSolutionInAncestors(): Unit =
    if stack.nonEmpty then
      stack.last.state match
        case cp: FrameState.ChoicePoint => cp.childSolutions += 1
        case _ =>

object SearchStream:
  def create(
    kb: KnowledgeBase,
    goals: ArrayBuffer[TermId],
    subst: Substitution,
    config: ResolveConfig = ResolveConfig()
  ): SearchStream =
    val stack = ArrayBuffer.empty[Frame]
    stack += Frame(goals, subst, 0, FrameState.Init(DelayMode.Normal))
    SearchStream(stack, config)

  /** Convenience: resolve a single goal pattern against the KB. */
  def resolve(
    kb: KnowledgeBase,
    goal: TermId,
    config: ResolveConfig = ResolveConfig()
  ): SearchStream =
    create(kb, ArrayBuffer(goal), Substitution(), config)
