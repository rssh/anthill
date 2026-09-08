package anthill.resolve

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, Var}

/** WI-20260902-EQG4F item 2 — AN ARGUMENT-LESS BUILTIN GOAL FAILS; IT DOES NOT RECURSE.
  *
  * WI-20260902-CZJ2N stores a nullary goal as `Term.Ref`, and `KnowledgeBase.getBuiltin`
  * reads a goal's tag through `headFunctorOf`, so `:- not` and `:- anthill.kernel.not`
  * REACH `SearchStream.stepNaf` where the `Term.Fn`-only read never did. `Builtins.firstArg`
  * then fell back to `case _ => goal`, so the negand was the `not` goal itself and the
  * sub-stream re-entered `stepNaf` at depth 0 — `maxDepth` never bit.
  *
  * ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
  *
  * Restore `firstArg`'s `case _ => goal` (and `stepNaf`'s `None` frame-pop): the two
  * NULLARY rows below die `StackOverflowError` — not a wrong count, a crash, which is why
  * each runs on its own bounded thread rather than inline. Both APPLIED rows pass either
  * way BY DESIGN: they are what the change must not move, and `notAppliedDotted` is the
  * one that shows NAF genuinely works here, so a nullary row's 0 is a REFUSAL and not
  * merely NAF being dead in scaland.
  *
  * PARITY, MEASURED not assumed: rustland answers 0 for `:- anthill.kernel.not` (its
  * `step_naf` pops the frame on the same missing `pos_arg(0)`, and `builtin_nonvar` /
  * `builtin_ground` return `Failure`). Its parser rejects the one-segment `:- not`
  * outright, so the dotted row is the shared one. Neither implementation refuses an
  * argument-less builtin goal at LOAD — that is a shared limit, not a scaland one.
  */
class NullaryBuiltinGoalTest extends munit.FunSuite:

  private def answers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.freshVar(kb.intern("x"))
    val goal = kb.alloc(Term.Fn(sym, IArray(kb.alloc(Term.Var(Var.Global(v)))), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  /** Run `body` on its own thread with a hard cap: backed out, these rows CRASH with
    * `StackOverflowError`, and a crash inside munit's thread would take the suite with it.
    * Reports the throwable so a back-out reads as a named failure rather than a hang. */
  private def bounded(label: String)(body: => Int)(using munit.Location): Int =
    var out: Either[String, Int] = Left("never finished")
    val t = new Thread(() =>
      out =
        try Right(body)
        catch case e: Throwable => Left(s"${e.getClass.getName}: ${String.valueOf(e.getMessage)}")
    )
    t.setDaemon(true)
    t.start()
    t.join(30000)
    if t.isAlive then fail(s"$label: still running after 30s — unbounded recursion")
    out match
      case Right(n) => n
      case Left(msg) => fail(s"$label: $msg")

  private def kbWith(src: String, file: String): KnowledgeBase =
    LoadFixture.loaded(src, file)

  test("a nullary `not` goal fails instead of recursing, in both spellings") {
    // ONE FILE EACH: a body ending in the one-segment `not` parses only at end of input
    // (the next `rule` keyword is swallowed), which is a parser limit orthogonal to this
    // ticket — so the two spellings get their own fixture rather than one shared file
    // whose parse failure would hide the resolver row it exists to measure.
    val bareKb = kbWith("fact bNb(1)\nrule nbBare(1) :- not\n", "nullaryNotBare.anthill")
    assertEquals(
      bounded("bare")(answers(bareKb, "nbBare")), 0,
      "`:- not` has no negand, so the goal fails and its rule answers nothing — " +
        "backed out this dies StackOverflowError",
    )
    val dottedKb =
      kbWith("fact bNb(1)\nrule nbDotted(1) :- anthill.kernel.not\n", "nullaryNotDotted.anthill")
    assertEquals(
      bounded("dotted")(answers(dottedKb, "nbDotted")), 0,
      "`:- anthill.kernel.not` is the same goal by another spelling, and rustland " +
        "answers 0 for it too",
    )
  }

  /** THE CONTROL THE NULLARY ROWS NEED: NAF is not simply dead here. A dotted APPLIED
    * `not` reaches `stepNaf` and answers, so a nullary row's 0 measures the missing
    * negand and not a resolver that never negates. The one-segment applied spelling
    * lands on a different symbol and answers 0 — a separate, pre-existing gap
    * (`DottedParenLessCitationTest` records it), unmoved by this change. */
  test("an APPLIED `not` is untouched: dotted reaches NAF, one-segment does not") {
    val kb = kbWith(
      """fact bNa(1)
        |rule unA(?n) :- bNa(?n)
        |rule naDotted(1) :- anthill.kernel.not(unA(999))
        |rule naBare(1) :- not(unA(999))
        |""".stripMargin,
      "appliedNot.anthill",
    )
    assertEquals(
      answers(kb, "naDotted"), 1,
      "`unA(999)` is empty, so NAF succeeds — this is what makes the nullary 0s a refusal",
    )
    assertEquals(
      answers(kb, "naBare"), 0,
      "the one-segment applied spelling does not reach NAF (pre-existing, unmoved here)",
    )
  }

  /** THE SHAPE THE `None` ALSO CATCHES, censused rather than left to be rediscovered: a
    * goal with only NAMED arguments has no positional argument either, so it takes the
    * same `Failure`. It used to `Delay` (the old fallback walked the whole goal and found
    * `?y`). rustland answers `Failure` here too — its `pos_arg` reads `pos_args` alone. */
  test("a NAMED-ARG-only `ground` goal fails too, as it does in rustland") {
    val kb = kbWith(
      """fact bNn(1)
        |rule nnNamed(1) :- anthill.reflect.ground(x: 1)
        |""".stripMargin,
      "namedOnlyGround.anthill",
    )
    assertEquals(
      answers(kb, "nnNamed"), 0,
      "`ground` is positional; a named-arg spelling names no argument it can read",
    )
  }

  /** `firstArg`'s other two readers take the same `None`. A nullary `ground` / `nonvar`
    * goal used to read the GOAL as its own argument — never a `Term.Var`, so both
    * SUCCEEDED silently. They now fail, which is `builtin_nonvar` / `builtin_ground`'s
    * `BuiltinResult::Failure` in rustland. */
  test("a nullary `ground` / `nonvar` goal fails rather than succeeding on itself") {
    val kb = kbWith(
      """fact bNg(1)
        |rule ngGround(1) :- anthill.reflect.ground
        |rule ngNonVar(1) :- anthill.reflect.nonvar
        |rule ngGroundOk(1) :- anthill.reflect.ground(bNg(1))
        |""".stripMargin,
      "nullaryGround.anthill",
    )
    assertEquals(answers(kb, "ngGround"), 0, "`:- ground` has no argument to judge")
    assertEquals(answers(kb, "ngNonVar"), 0, "`:- nonvar` has no argument to judge")
    assertEquals(
      answers(kb, "ngGroundOk"), 1,
      "the APPLIED spelling still answers — the control that says the arity is the axis",
    )
  }
