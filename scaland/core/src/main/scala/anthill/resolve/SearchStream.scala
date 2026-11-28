package anthill.resolve

import anthill.kb.{KnowledgeBase, BuiltinTag, RuleId}
import anthill.term.{Literal, Term, TermId}
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
    var next: Int
  )

// ── Frame ───────────────────────────────────────────────────────

/** One goal of a frame's resolvent with its NESTING depth (WI-20261115-0WT09): a goal opened
  * from a clause's body is one deeper than the goal the clause answered, and every other goal
  * keeps its own — "depth is depth", rustland's `FrameGoal::depth`. So the steps one goal's
  * proof takes are never charged to its siblings; the work a search does is the fuel,
  * `ResolveConfig.maxSteps`. */
private final case class FrameGoal(goal: TermId, depth: Int)

/** WI-20261127-AGR9S (proposal 076 Stage A) — a branch's CONTINUATION: every goal it still has
  * to prove, the current one first — rustland's `Goals` on this carrier.
  *
  * LINKED, NOT COPIED. A frame is both a branch and a choice point, and every frame on the stack
  * keeps the continuation it was made with. A child frame used to be given `body ++ a copy of its
  * parent's tail`, so a resolvent growing by one goal a level held `n` copies of a tail up to `n`
  * long over its `n` retained frames: quadratic in memory. Here it is a persistent chain of
  * SCOPES: a scope is the goals left of one body, and its caller's scope. Opening a body links a
  * scope in front of what follows the goal it answers and copies nothing; a branch shares its
  * caller's scopes. THE EXIT IS STRUCTURAL: a scope with no goals left continues with its
  * caller's, and no scope in `scopes` is empty.
  *
  * `back` holds the goals that WAITED, rotated behind every other goal, the latest first (a goal
  * that waits goes behind the whole resolvent, as before). `scopes` is empty only when `back` is
  * too: when the last goal in front is taken, the goals that waited come round as a scope of
  * their own, in the order they waited. */
// A plain class, not a case class: a generated `equals` / `hashCode` / `toString` would walk the
// whole caller chain by recursion.
private final class Scope(val goals: List[FrameGoal], val len: Int, val caller: Scope | Null):
  /** The goals of this scope and of every scope it returns to. */
  val frontLen: Int = len + (if caller == null then 0 else caller.frontLen)

private final class Goals private (
  private val scopes: Scope | Null,
  private val back: List[FrameGoal],
  private val backLen: Int
):
  private def frontLen: Int = if scopes == null then 0 else scopes.frontLen

  def length: Int = frontLen + backLen
  def isEmpty: Boolean = scopes == null
  def nonEmpty: Boolean = scopes != null

  /** The goal this branch asks next. The caller knows there is one. */
  def current: FrameGoal = scopes.nn.goals.head

  /** The current goal rewritten in place (its walked form): one cell is new. */
  def withCurrent(goal: FrameGoal): Goals =
    val s = scopes.nn
    Goals(Scope(goal :: s.goals.tail, s.len, s.caller), back, backLen)

  /** What is left once the current goal is answered with nothing to prove. */
  def afterCurrent: Goals =
    val s = scopes.nn
    Goals.settled(Goals.exit(Scope(s.goals.tail, s.len - 1, s.caller)), back, backLen)

  /** The current goal answered by `body`: the body in a scope of its own, in front of what
    * follows the current goal. */
  def open(body: List[FrameGoal]): Goals =
    val s = scopes.nn
    val rest = Goals.exit(Scope(s.goals.tail, s.len - 1, s.caller))
    Goals.settled(Goals.exit(Scope(body, body.length, rest)), back, backLen)

  /** The current goal TURNED INTO `goals`, which take its place in its scope. */
  def replaceCurrent(goals: List[FrameGoal]): Goals =
    if goals.isEmpty then afterCurrent
    else
      val s = scopes.nn
      Goals(Scope(goals ++ s.goals.tail, s.len - 1 + goals.length, s.caller), back, backLen)

  /** The current goal WAITS: it goes behind every other goal as `goal`. */
  def rotateCurrent(goal: FrameGoal): Goals =
    val rest = afterCurrent
    if rest.isEmpty then Goals.of(List(goal))
    else Goals(rest.scopes, goal :: rest.back, rest.backLen + 1)

  /** Every goal left, in order. */
  def toSeq: IndexedSeq[FrameGoal] =
    val front = Iterator.unfold(scopes)(s => if s == null then None else Some((s.goals, s.caller)))
    (front.flatten ++ back.reverseIterator).toIndexedSeq

private object Goals:
  /** The query's goals, in order: the query's scope. */
  def of(goals: List[FrameGoal]): Goals = settled(exit(Scope(goals, goals.length, null)), Nil, 0)

  /** THE EXIT: a scope with no goals left continues with its caller's. */
  @annotation.tailrec
  def exit(s: Scope | Null): Scope | Null =
    if s != null && s.len == 0 then exit(s.caller) else s

  /** With nothing left in front, the goals that waited come round, in the order they waited. */
  def settled(scopes: Scope | Null, back: List[FrameGoal], backLen: Int): Goals =
    if scopes == null && backLen != 0 then Goals(Scope(back.reverse, backLen, null), Nil, 0)
    else Goals(scopes, back, backLen)

private class Frame(
  var goals: Goals,
  var subst: Substitution,
  var state: FrameState
)

// ── Step result ─────────────────────────────────────────────────

private enum StepResult:
  case Continue
  case YieldSolution(sol: Solution)

// ── Resolve telemetry ───────────────────────────────────────────

/** Immutable resolution telemetry snapshot.
  *
  * `goalSelections` counts every visit to the lazy-walk-aware goal
  * selection in `stepInit` (incremented before the σ-empty fast path).
  * Pre-WI-172 the equivalent work was done eagerly in stepChoicePoint
  * via O(remaining-goals) `applySubst` calls per match — the equivalent
  * metric scaled ~n²/2 on an n-body workload. Post-WI-172 the metric
  * scales linearly: roughly one selection per goal consumed.
  *
  * `actualWalks` is the strict subset where σ was non-empty and
  * `goals(0)` was actually walked + memoized. */
case class ResolveStats(
  steps: Long,
  goalSelections: Long,
  actualWalks: Long,
  /** A goal nested past `maxDepth` was not asked, or the fuel ran out: the search is
    * INCOMPLETE (WI-20261115-0WT09). */
  truncated: Boolean = false,
  /** The search took `maxSteps` steps, its fuel, and stopped (implies `truncated`). */
  outOfFuel: Boolean = false
)

// ── SearchStream ────────────────────────────────────────────────

/** Lazy search stream that yields one solution at a time via splitFirst.
  * Converts recursive DFS into an explicit choice-point stack.
  */
class SearchStream private (
  private val stack: ArrayBuffer[Frame],
  private val config: ResolveConfig
):

  private var stepsCount_ : Long = 0L
  private var goalSelections_ : Long = 0L
  private var actualWalks_ : Long = 0L
  private var truncated_ : Boolean = false
  private var outOfFuel_ : Boolean = false

  /** Telemetry snapshot (see [[ResolveStats]]). Returns an immutable
    * value; callers cannot mutate the underlying counters. */
  def stats: ResolveStats =
    ResolveStats(stepsCount_, goalSelections_, actualWalks_, truncated_, outOfFuel_)

  /** WI-20261115-0WT09 — out of fuel: every open branch is abandoned, the search truncated. */
  private def runOutOfFuel(): Unit =
    outOfFuel_ = true
    truncated_ = true
    stack.clear()

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
    // FUEL (WI-20261115-0WT09): the steps of the whole search, against `maxSteps`. Out of
    // it, every open branch is abandoned: a truncation, never a refutation.
    if stepsCount_ >= config.maxSteps then
      runOutOfFuel()
      return None
    val frame = stack.last
    stepsCount_ += 1
    frame.state match
      case _: FrameState.Init => stepInit(kb)
      case _: FrameState.ChoicePoint => stepChoicePoint(kb)

  private def stepInit(kb: KnowledgeBase): Option[StepResult] =
    val frame = stack.last
    // The CURRENT goal's nesting depth (WI-20261115-0WT09); a frame with no goal left is an
    // answer, which no limit cuts.
    val depth = if frame.goals.nonEmpty then frame.goals.current.depth else 0
    val delayMode = frame.state match
      case FrameState.Init(dm) => dm
      case _ => return Some(StepResult.Continue) // unreachable

    // 1. Depth limit: a goal nested past `maxDepth` is not asked, and the search is
    // incomplete (recorded on the stats, as rustland's `truncated`).
    if depth > config.maxDepth then
      truncated_ = true
      stack.remove(stack.length - 1)
      return Some(StepResult.Continue)

    // 2. Floundering: all goals delayed. Not with no goals left: a frame stays `Delayed`
    // once anything in its derivation waited (`reset` keeps the mode, at 0), and a proof
    // with no goals left is step 3's solution, not a floundered branch — rustland's gate
    // reads the same (its answer dedup and `definite_only` tell the two apart).
    delayMode match
      case DelayMode.Delayed(cd) if frame.goals.nonEmpty && cd >= frame.goals.length =>
        val sol = Solution(frame.subst.snapshot(), frame.goals.toSeq.map(_.goal))
        stack.remove(stack.length - 1)
        return Some(StepResult.YieldSolution(sol))
      case _ =>

    // 3. Goals empty → solution
    if frame.goals.isEmpty then
      val sol = Solution(frame.subst.snapshot(), IndexedSeq.empty)
      stack.remove(stack.length - 1)
      return Some(StepResult.YieldSolution(sol))

    // [WI-172] Lazy substitution. σ already carries every binding
    // accumulated up to this point (merged via bindCompressed in
    // stepChoicePoint). Walking goals(0) here — instead of eagerly
    // applying σ to every remaining goal after each match — turns the
    // inherent SLD work from O(n²) into O(n × goal_size). Memoize the
    // walked form back into goals(0) so choice-point retries don't
    // re-walk. Skip the structural walk when σ is empty (no bindings
    // could change anything anyway).
    goalSelections_ += 1
    val goal =
      if frame.subst.isEmpty then frame.goals.current.goal
      else
        actualWalks_ += 1
        val walked = kb.applySubst(frame.goals.current.goal, frame.subst)
        frame.goals = frame.goals.withCurrent(frame.goals.current.copy(goal = walked))
        walked

    // NARC7 / §5.3: boolean goals are searches at every depth, including NAF and
    // binary-control continuations. The loader's top-level true strip only keeps
    // fact-shaped bodies empty; it cannot supply this operational meaning.
    kb.getTerm(goal) match
      case Term.Const(Literal.BoolLit(value)) =>
        if value then
          frame.goals = frame.goals.afterCurrent
          frame.state = FrameState.Init(delayMode.reset)
        else stack.remove(stack.length - 1)
        return Some(StepResult.Continue)
      case _ => ()

    // 4. Builtin
    kb.getBuiltin(goal) match
      case Some(BuiltinTag.Not) =>
        return stepNaf(kb, goal, depth, delayMode)
      case Some(BuiltinTag.PushChoice) =>
        return stepBinaryControl(kb, goal, depth, delayMode, choice = true)
      case Some(BuiltinTag.PushAnd) =>
        return stepBinaryControl(kb, goal, depth, delayMode, choice = false)
      case Some(tag) =>
        Builtins.execute(kb, tag, goal, frame.subst) match
          case BuiltinResult.Success =>
            val newDelay = delayMode.reset
            frame.goals = frame.goals.afterCurrent
            frame.state = FrameState.Init(newDelay)
            return Some(StepResult.Continue)

          case BuiltinResult.SuccessWithBindings(extra) =>
            frame.subst.bindCompressed(extra.bindings, kb.terms)
            val newDelay = delayMode.reset
            frame.goals = frame.goals.afterCurrent
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
      delayMode, goal, candidates, next = 0
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
    if body.isEmpty && kb.ruleArity(rid) == 0 then
      // Ground fact match — merge tree_subst with path compression.
      // A bodyless rule WITH vars (arity > 0) is NOT ground: its head-match
      // tree_subst carries synthetic-DeBruijn entries that must be opened, so
      // it falls to the `withFreshVars` branch below (WI-637), not this raw
      // bind fast path.
      val newSubst = frame.subst.snapshot()
      newSubst.bindCompressed(treeSubst.bindings, kb.terms)
      if newSubst.isContradiction then
        return Some(StepResult.Continue)

      // [WI-172] No eager applySubst-each. Bindings from this match
      // enter newSubst via bindCompressed above; remaining goals are
      // lazily walked at selection time in stepInit.
      // A fact opens no goal: the tail keeps its own depths.
      val newGoals = frame.goals.afterCurrent

      val newDelay = cp.delayMode.reset

      stack += Frame(newGoals, newSubst, FrameState.Init(newDelay))
    else
      // Rule with body (or a bodyless arity>0 rule) — open its DeBruijn vars.
      val (freshBody, answerLinks) = kb.withFreshVars(rid, treeSubst)

      // WI-637/WI-624: `withFreshVars` flags `answerLinks` contradictory when a
      // query-var link is cyclic (occurs-fail). `bindCompressed` copies only the
      // bindings, not the flag, so honor it HERE before merging — else the
      // occurs-fail candidate leaks a spurious solution with the var unbound.
      if answerLinks.isContradiction then
        return Some(StepResult.Continue)

      val newSubst = frame.subst.snapshot()
      newSubst.bindCompressed(answerLinks.bindings, kb.terms)
      if newSubst.isContradiction then
        return Some(StepResult.Continue)

      // [WI-172] No eager applySubst-each. The body is already
      // concretised through withFreshVars; caller-side bindings flow
      // into newSubst via bindCompressed above; remaining goals walk
      // lazily in stepInit.
      // A CLAUSE BODY IS ONE DEEPER than the goal the clause answers (WI-20261115-0WT09) —
      // the one place a goal's depth grows.
      val bodyDepth = frame.goals.current.depth + 1
      val newGoals = frame.goals.open(freshBody.map(FrameGoal(_, bodyDepth)).toList)

      val newDelay = cp.delayMode.reset

      stack += Frame(newGoals, newSubst, FrameState.Init(newDelay))

    Some(StepResult.Continue)

  /** WI-373AW: splice goals before the caller's tail. Choice branches inherit
    * independent snapshots of the incoming substitution; left-branch bindings must
    * never leak into the right branch. `BinaryControlTest` drives both continuations
    * and the shared tail; its comma control passes with this dispatch backed out. */
  private def stepBinaryControl(
    kb: KnowledgeBase, goal: TermId, depth: Int, delayMode: DelayMode, choice: Boolean
  ): Option[StepResult] =
    val frame = stack.last
    kb.getTerm(goal) match
      case fn: Term.Fn[TermId] if fn.posArgs.length == 2 && fn.namedArgs.isEmpty =>
        val nextState = FrameState.Init(delayMode.reset)
        // A SPLIT IS NO CALL (WI-20261115-0WT09): both operands stand at the goal's depth.
        if choice then
          // LIFO: retain the right continuation below the left one so DFS exhausts
          // the left branch (including its tail) before trying the right branch. Each side
          // is a scope of its own (076 Stage A), sharing the tail.
          val leftSubst = frame.subst.snapshot()
          val goals = frame.goals
          frame.goals = goals.open(List(FrameGoal(fn.posArgs(1), depth)))
          frame.state = nextState
          stack += Frame(goals.open(List(FrameGoal(fn.posArgs(0), depth))), leftSubst, nextState)
        else
          frame.goals = frame.goals.replaceCurrent(
            List(FrameGoal(fn.posArgs(0), depth), FrameGoal(fn.posArgs(1), depth)))
          frame.state = nextState
      case _ =>
        throw IllegalArgumentException("binary resolver primitive requires exactly two positional goals")
    Some(StepResult.Continue)

  private def stepNaf(
    kb: KnowledgeBase, goal: TermId, depth: Int, delayMode: DelayMode
  ): Option[StepResult] =
    val frame = stack.last
    // WI-20260902-EQG4F item 2 — NO NEGAND, NO PROOF. A nullary `not` goal (`:- not`,
    // `:- anthill.kernel.not`) carries nothing to negate, so the frame FAILS — rustland's
    // `step_naf` pops its frame on the same `None`. Before this the negand fell back to
    // the `not` goal ITSELF and the sub-stream below re-entered here at depth 0, so both
    // spellings died `StackOverflowError` rather than answering.
    val innerGoal = Builtins.firstArg(kb, goal) match
      case Some(inner) => inner
      case None =>
        stack.remove(stack.length - 1)
        return Some(StepResult.Continue)
    val reified = kb.reify(innerGoal, frame.subst)

    Builtins.isGround(kb, reified, Substitution()) match
      case GroundCheck.HasVar =>
        handleDelay(frame, goal, depth, delayMode)
      case GroundCheck.Ground =>
        // Run sub-resolution, on what is left of this search's depth below the goal and of
        // its fuel (WI-20261115-0WT09, as rustland's `step_naf`), its steps charged back.
        val subConfig = config.copy(
          maxDepth = math.max(0, config.maxDepth - depth),
          maxSteps = math.max(0L, config.maxSteps - stepsCount_)
        )
        val subStream = SearchStream.create(kb, ArrayBuffer(reified), Substitution(), subConfig)
        val hasSolution = subStream.splitFirst(kb).isDefined
        stepsCount_ += subStream.stats.steps
        if subStream.stats.outOfFuel then
          // Its fuel was this search's: this search stops too.
          runOutOfFuel()
          return Some(StepResult.Continue)
        if !hasSolution && subStream.stats.truncated then
          // A CUT SEARCH PROVES NOTHING (rustland's WI-628): `P`'s search was cut at its depth
          // limit, so its empty result is no refutation and `not(P)` is UNDECIDED — it waits
          // and residualizes, and this search is incomplete. Before, `not(P)` succeeded here;
          // the sub-search's budget is `maxDepth - depth` since WI-20261115-0WT09, which made
          // the cut likelier (`/code-review`).
          truncated_ = true
          return handleDelay(frame, goal, depth, delayMode)
        if hasSolution then
          // Inner goal succeeded → not(Goal) fails
          stack.remove(stack.length - 1)
          Some(StepResult.Continue)
        else
          // Inner goal failed → not(Goal) succeeds
          val newGoals = frame.goals.afterCurrent
          val newDelay = delayMode match
            case DelayMode.Normal => DelayMode.Normal
            case DelayMode.Delayed(_) => DelayMode.Delayed(0)
          frame.goals = newGoals
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
          Some(StepResult.YieldSolution(sol))
        else
          // The goal keeps its own depth behind the tail: a rotation is no step deeper.
          frame.goals = frame.goals.rotateCurrent(FrameGoal(goal, depth))
          frame.state = FrameState.Init(DelayMode.Delayed(1))
          Some(StepResult.Continue)
      case DelayMode.Delayed(cd) =>
        frame.goals = frame.goals.rotateCurrent(FrameGoal(goal, depth))
        frame.state = FrameState.Init(DelayMode.Delayed(cd + 1))
        Some(StepResult.Continue)

object SearchStream:
  def create(
    kb: KnowledgeBase,
    goals: ArrayBuffer[TermId],
    subst: Substitution,
    config: ResolveConfig = ResolveConfig()
  ): SearchStream =
    val stack = ArrayBuffer.empty[Frame]
    // The query's goals are at depth 0.
    stack += Frame(Goals.of(goals.map(FrameGoal(_, 0)).toList), subst, FrameState.Init(DelayMode.Normal))
    SearchStream(stack, config)

  /** Convenience: resolve a single goal pattern against the KB. */
  def resolve(
    kb: KnowledgeBase,
    goal: TermId,
    config: ResolveConfig = ResolveConfig()
  ): SearchStream =
    create(kb, ArrayBuffer(goal), Substitution(), config)
