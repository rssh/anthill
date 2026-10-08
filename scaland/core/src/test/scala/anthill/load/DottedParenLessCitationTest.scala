package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.parse.Parser
import anthill.term.{Term, TermId, Var}
import anthill.resolve.SearchStream

/** WI-20260901-719FJ (rustland's twin, same ticket) — A DOTTED PAREN-LESS CITATION IS
  * THE NAME IT SPELLS, IN EVERY LOGICAL POSITION.
  *
  * `ns.tgt` written without a trailing `(…)` has no application to hang a functor on, so
  * the parser folds it into a MINTED `field_access(ns, Ref(tgt))` chain (§6.7: a name
  * with no application is dot projection). That chain is what the spelling lowers to
  * EVERYWHERE, and what it MEANS is the POSITION's to say — never the qualification's.
  * Where a term states a PROPOSITION (a rule head, a `fact` head, a rule-body goal) it is
  * the qualified NAME, resolved exactly as the applied spelling `ns.tgt(…)` resolves its
  * functor.
  *
  * SCALAND'S SYMPTOM WAS THE LOUDER ONE, and it is why this port is not cosmetic:
  * `field_access` is a registered builtin whose tag is `BuiltinResult.Delay`, so a dotted
  * paren-less GOAL SUSPENDED and its residual counted as a solution. Measured before the
  * fix — `rule r(1) :- zz.nope.tgt`, naming a namespace that DOES NOT EXIST, loaded clean
  * and ANSWERED 1, and the same goal over an EMPTY predicate answered 1 as well. In head
  * position the clause landed under `field_access` and the rule was dropped: `rule
  * ns.tgt :- b(1)` answered nothing where `rule ns.tgt() :- b(1)` answered. rustland's
  * goal always FAILED instead of always succeeding; same chain, opposite silence.
  *
  * ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
  *
  * FOUR AXES — the collapse itself and the three POSITIONS that ask for it. Each is
  * PRESENT-BUT-WRONG rather than deleted, and each was APPLIED AND RUN over the WHOLE
  * scaland suite (533 rows), so each count is EXHAUSTIVE over that population: every row
  * not named passed.
  *
  *  * **THE COLLAPSE** — in `Loader.reallocTerm`, make its `dottedCitationName` answer
  *    `None`, so an `atGoal` node keeps the chain. **EXACTLY 4 ROWS FAIL**, which is
  *    every position row here: the rule head, the fact head, the body goal, and the goal
  *    naming nothing.
  *  * **THE RULE-HEAD SITE** — `atGoal = false` at `loadRuleHeads`' head call. **EXACTLY
  *    1 ROW FAILS**: `a dotted paren-less rule head joins the predicate it names`.
  *  * **THE BODY-GOAL SITE** — `atGoal = false` at `loadRuleHeads`' body call. **EXACTLY
  *    2 ROWS FAIL**: `a dotted paren-less body goal runs the predicate` and `a dotted
  *    paren-less goal naming nothing answers nothing`.
  *  * **THE FACT-HEAD SITE** — `atGoal = false` at the `Item.FactItem` call. **EXACTLY 1
  *    ROW FAILS**: `a dotted paren-less fact head asserts on the name`.
  *
  * Every back-out leaves the PARENS arm of each pair untouched, which is what makes each
  * pair a measurement of the SPELLING. `a data slot still stores the chain on both sides
  * of a match` passes under ALL FOUR by design — it is what the change must not move.
  *
  * A LATER ROW, `` `not` negates its negand in every spelling, dotted ones included ``
  * (WI-20261008-T290W), is not in those counts. It has a back-out of its own, stated at
  * its site, and it reads the collapse through a GOAL SLOT — so it fails under THE
  * COLLAPSE as well, measured on the suite of that date.
  */
class DottedParenLessCitationTest extends munit.FunSuite:

  /** Solutions of `<qn>(?x)` — the goal built on the SYMBOL, so a clause that landed on
    * a different symbol counts zero rather than silently matching. Every reader below is
    * unary and takes its answer from a NULLARY goal in its body, which is the position
    * under test. */
  private def answers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.freshVar(kb.intern("x"))
    val goal = kb.alloc(Term.Fn(sym, IArray(kb.alloc(Term.Var(Var.Global(v)))), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  /** THE HEAD, INVERTED — the namespace's OWN clause is FALSE, so the reader answers only
    * if the dotted paren-less head's clause landed AND is reached. Asserting a TRUE one
    * would pass against the defect. */
  test("a dotted paren-less rule head joins the predicate it names") {
    for (label, tag, mark) <- Seq(("bare", "719HdBare", ""), ("parens", "719HdParen", "()")) do
      val kb = LoadFixture.loaded(
        s"""fact b719(1)
           |namespace zz$tag
           |  rule tgt$mark :- b719(999)
           |  rule readsIt(1) :- tgt$mark
           |end
           |rule zz$tag.tgt$mark :- b719(1)""".stripMargin,
        s"$tag.anthill",
      )
      assertEquals(
        answers(kb, s"zz$tag.readsIt"), 1,
        s"$label: the dotted head's clause is the only TRUE one, so the reader answers " +
          "from it — pre-fix the bare arm answered 0 and the rule was dropped",
      )
  }

  /** THE FACT HEAD — a DOTTED head REFERENCES, in a fact as in a rule, and the reference
    * was landing under `field_access`. */
  test("a dotted paren-less fact head asserts on the name") {
    for (label, tag, mark) <- Seq(("bare", "719FtBare", ""), ("parens", "719FtParen", "()")) do
      val kb = LoadFixture.loaded(
        s"""fact b719(1)
           |namespace zz$tag
           |  rule tgt$mark :- b719(999)
           |  rule readsIt(1) :- tgt$mark
           |end
           |fact zz$tag.tgt$mark""".stripMargin,
        s"$tag.anthill",
      )
      assertEquals(
        answers(kb, s"zz$tag.readsIt"), 1,
        s"$label: the fact joins the predicate its head names, and the rule's own clause " +
          "is FALSE — so this answers from the fact or not at all",
      )
  }

  /** THE BODY GOAL, and the arm that matters is the EMPTY one: pre-fix the chain
    * SUSPENDED and the residual was counted, so a goal over an empty predicate answered
    * 1. Both arms are asserted, so "it now always fails" cannot pass this row either. */
  test("a dotted paren-less body goal runs the predicate") {
    for (label, tag, mark) <- Seq(("bare", "719GlBare", ""), ("parens", "719GlParen", "()")) do
      val kb = LoadFixture.loaded(
        s"""fact b719(1)
           |namespace zz$tag
           |  rule full$mark :- b719(1)
           |  rule empty$mark :- b719(999)
           |end
           |rule reads$tag(1) :- zz$tag.full$mark
           |rule readsEmpty$tag(1) :- zz$tag.empty$mark""".stripMargin,
        s"$tag.anthill",
      )
      assertEquals(
        answers(kb, s"reads$tag"), 1,
        s"$label: a goal over a PROVABLE predicate answers",
      )
      assertEquals(
        answers(kb, s"readsEmpty$tag"), 0,
        s"$label: and one over an EMPTY predicate does NOT — pre-fix the bare arm " +
          "answered 1, from a suspended `field_access` residual",
      )
  }

  /** THE LOUDEST PRE-FIX ROW — a goal naming a namespace that does not exist. It loaded
    * clean and ANSWERED; now it loads clean (WI-476's bare intern, the same answer the
    * APPLIED spelling gets) and answers nothing. The applied spelling is the control:
    * it behaved this way all along, which is what says the axis is the SPELLING. */
  test("a dotted paren-less goal naming nothing answers nothing") {
    for (label, mark) <- Seq(("bare", ""), ("parens", "()")) do
      val kb = LoadFixture.loaded(
        s"""fact b719(1)
           |rule noSuch719$label(1) :- zz719.nope.tgt$mark""".stripMargin,
        s"nosuch$label.anthill",
      )
      assertEquals(
        answers(kb, s"noSuch719$label"), 0,
        s"$label: a goal that names nothing proves nothing",
      )
  }

  /** A DATA SLOT KEEPS THE CHAIN, ON BOTH SIDES OF A MATCH — the fact stores it and the
    * rule body finds it. A term's spelling is its identity; collapsing one side of a
    * match and not the other is never a repair. GREEN BEFORE AND AFTER. */
  test("a data slot still stores the chain on both sides of a match") {
    val kb = LoadFixture.loaded(
      """fact b719(1)
        |namespace zz719Ds
        |  rule tgt :- b719(1)
        |end
        |fact holds719(zz719Ds.tgt)
        |rule viaBody719(1) :- holds719(zz719Ds.tgt)""".stripMargin,
      "ds.anthill",
    )
    assertEquals(
      answers(kb, "viaBody719"), 1,
      "the fact's data slot and the body's spell one term",
    )
  }

  /** A NEGAND IS A GOAL, SO ITS DOTTED CITATION IS THE NAME TOO. rustland routes `not`'s
    * negand as a goal of its own (`goal_arg_slots`); `reallocTerm`'s `Term.Fn` arm now
    * does, from `KnowledgeBase.goalArgSlots`.
    *
    * THIS ROW RECORDED A BOUNDARY UNTIL WI-20261008-T290W: every spelling answered 0,
    * the one-segment `not` landing on a bare symbol spelled `..anthill.kernel.not` — the
    * address the operator is minted with, which the loader could not resolve
    * (WI-20260902-373AW) — so there was no negand position to route. Resolving the
    * address made NAF live and the descent drivable, and due.
    *
    * EACH NEGAND TWICE, over an EMPTY predicate and over one that HOLDS, so a 1 is NAF
    * and not a goal that answers whatever it is given.
    *
    * BACK-OUT (the descent — `goalSlots` always empty in `reallocTerm`), run over the
    * whole core suite: 2 ROWS FAIL. This one, on its two DOTTED EMPTY cells — `nDot719`
    * and `nAbs719` answer 0 — and on no other: a data-slot negand keeps the
    * `field_access` chain, whose builtin suspends, and the residual counts as a
    * solution of the negand, so its negation fails whatever the predicate holds. And
    * `DottedGoalReadingTest`'s operation row, whose dotted `Not` cell leaves its
    * one-segment twin. The one-segment and applied cells pass either way by design:
    * their terms are the same in a data slot as in a goal slot. */
  test("`not` negates its negand in every spelling, dotted ones included") {
    val kb = LoadFixture.loaded(
      """fact b719(1)
        |namespace zz719Nf
        |  rule un(?n) :- b719(?n)
        |  rule bare :- b719(999)
        |  rule paren() :- b719(999)
        |  rule full :- b719(1)
        |  rule nUnary(1) :- not(un(999))
        |  rule nBare(1) :- not(bare)
        |  rule nParen(1) :- not(paren())
        |  rule nUnaryFull(1) :- not(un(1))
        |  rule nBareFull(1) :- not(full)
        |  rule nParenFull(1) :- not(full())
        |end
        |rule nDot719(1) :- not(zz719Nf.bare)
        |rule nAbs719(1) :- not(..zz719Nf.bare)
        |rule nTwo719(1) :- anthill.kernel.not(zz719Nf.bare, 0)
        |rule nDotFull719(1) :- not(zz719Nf.full)
        |rule nAbsFull719(1) :- not(..zz719Nf.full)""".stripMargin,
      "naf.anthill",
    )
    // ONE COMPARISON OVER EVERY CELL, so a failure shows the whole table and not the
    // first cell to diverge.
    // `nTwo719` IS MALFORMED — `not` takes one argument, and neither implementation
    // refuses the extra one at load. It is here for one thing: the resolver negates the
    // FIRST argument at any arity, so the loader must read that same argument as the
    // goal. BACK-OUT (`goalArgSlots` gated on arity 1): this cell alone answers 0.
    val empty = Seq("zz719Nf.nUnary", "zz719Nf.nBare", "zz719Nf.nParen", "nDot719", "nAbs719",
                    "nTwo719")
    val full = Seq("zz719Nf.nUnaryFull", "zz719Nf.nBareFull", "zz719Nf.nParenFull",
                   "nDotFull719", "nAbsFull719")
    assertEquals(
      (empty ++ full).map(q => q -> answers(kb, q)),
      empty.map(_ -> 1) ++ full.map(_ -> 0),
      "an EMPTY negand's negation holds and a negand that HOLDS has none")
  }
