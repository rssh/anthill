package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, TermId, Var}
import anthill.intern.TermSymbol
import anthill.resolve.SearchStream

/** WI-20260821-P85Z7 (rustland's twin, same ticket) — A PAREN-LESS NULLARY RULE HEAD IS
  * AN APPLICATION OF ARITY 0, AND IS SCOPED WHERE IT IS WRITTEN.
  *
  * `ruleIntroducedFunctor` read only the `Term.Fn` shape, and the parser gives a bare
  * name a `Term.Ident` — so `rule pl :- ba(1)` introduced NOTHING ANYWHERE and fell to
  * the bare intern: ONE GLOBAL NAME two scopes' same-spelled heads then shared, with the
  * loser's clause answering inside the winner's scope, on a program that loaded clean.
  * That is WI-894's defect class, which pass 3 exists to stop; the nullary spelling never
  * entered the fix. The PARENTHESISED twin was always right, which is what made this a
  * defect rather than a design — so every row is written as that PAIR.
  *
  * SCALAND NEEDED TWO FIXES, NOT ONE, AND THE SECOND IS A PARSE BUG rustland's tokenizer
  * never had. `:-` is one token there; here `(simpleName ~ ":")` ate its first character,
  * so `rule pl :- ba(1)` parsed as the LABEL `pl` with `- ba(1)` for a head and NO body.
  * Measured before the lookahead: the symbol table held `Resolved(pl, …, Rule, …)` where
  * a predicate belonged, `pl` carried ZERO clauses, and the goal citing it answered
  * nothing. The loader fix alone would have minted a name no clause ever landed on.
  *
  * ── WHICH ROWS FAIL WHEN EACH IS BACKED OUT — THREE AXES, each APPLIED AND RUN over
  * the whole scaland suite (526 rows) ─────────────────────────────────────────
  *
  *  * **THE LOADER'S NULLARY SHAPE** — drop the `Term.Ident` arm in
  *    `Loader.ruleIntroducedFunctor`. **EXACTLY 1 ROW FAILS** (525 pass): `two scopes
  *    writing one bare nullary head get two predicates`, at its FIRST assertion — the
  *    head is not a scoped symbol of its own namespace.
  *  * **THE LABEL'S COLON** — restore `(simpleName ~ ":").?` in `AnthillParser.
  *    ruleWithSpan`. **EXACTLY 1 ROW FAILS** (525 pass): the same row, at a DIFFERENT
  *    assertion — the symbols exist and the clause does not, so `zzB.seeB` answers 0.
  *    Two axes, two failure points, one row.
  *  * **THE PREDICATE-PATH GATE** — drop the `kind == SymbolKind.Goal` guard from the
  *    same arm, so a bare EQUATION subject is minted too. **EXACTLY 1 ROW FAILS** (525
  *    pass): `a bare equation subject introduces nothing`. Measured, not assumed — the
  *    rustland twin's first draft credited the wrong row for this axis and running it
  *    said so.
  *
  * Every back-out leaves the PARENS arm untouched, which is what makes each pair a
  * measurement of the SPELLING.
  */
class ParenLessNullaryHeadTest extends munit.FunSuite:

  /** The inverted pair: `a`'s clause is FALSE and `b`'s is TRUE, so asserting only one
    * of them would pass against the defect. `$mark` is `` or `()`. */
  private def pair(tag: String, mark: String) =
    s"""namespace zz$tag.a
       |  fact ba(1)
       |  rule pl$mark :- ba(999)
       |  rule seeA(1) :- pl$mark
       |end
       |
       |namespace zz$tag.b
       |  fact bb(1)
       |  rule pl$mark :- bb(1)
       |  rule seeB(1) :- pl$mark
       |end""".stripMargin

  /** Solutions of `<qn>(?x)` — the goal built on the SYMBOL the head carries, so a head
    * that landed on a different symbol counts zero rather than silently matching. */
  private def answers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.freshVar(kb.intern("x"))
    val goal = kb.alloc(Term.Fn(sym, IArray(kb.alloc(Term.Var(Var.Global(v)))), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  test("two scopes writing one bare nullary head get two predicates") {
    for (label, tag, mark) <- Seq(("bare", "P85Bare", ""), ("parens", "P85Paren", "()")) do
      val kb = LoadFixture.loaded(pair(tag, mark), s"$tag.anthill")
      assert(
        kb.hasQualifiedName(s"zz$tag.a.pl"),
        s"$label: the head must be a scoped symbol of its OWN namespace",
      )
      assert(
        kb.hasQualifiedName(s"zz$tag.b.pl"),
        s"$label: and so must the sibling's — two predicates, not one shared name",
      )
      assertEquals(
        answers(kb, s"zz$tag.a.seeA"), 0,
        s"$label: `a`'s own clause is FALSE, so its reader answers nothing — pre-fix it " +
          "answered 1, from `b`'s clause",
      )
      assertEquals(
        answers(kb, s"zz$tag.b.seeB"), 1,
        s"$label: `b`'s own clause is TRUE — the control that says the goal machinery works",
      )
  }

  /** THE LOOKAHEAD'S OWN BOUNDARY — `!":-"` and not `!"-"`. A prefix-minus head is a
    * real production, so a label followed by one must survive the fix; only the two
    * characters TOGETHER are the arrow. Driven because the comment at
    * `AnthillParser.ruleWithSpan` claims it, and a claim about which spellings a
    * lookahead rejects is worth exactly as much as its row.
    *
    * BACKED OUT — and the recipe took THREE tries to find, which is the row's real
    * content. `!"-"` BEFORE the colon fells the OTHER row instead: `~` skips trivia, so
    * the lookahead lands on the `:` of `:-` and passes, and the label eats the arrow
    * again. `":" ~ !"-"` — the check moved AFTER the colon, still trivia-skipping — is
    * the one this row fells: it looks past the space at `-negp` and rejects a label the
    * arrow rule has no business rejecting. Only the two characters TOGETHER are the
    * arrow, which is what `!":-"` says.
    *
    * THE HEAD MUST START WITH THE MINUS. A first fixture wrote `negp(-1)`, where the
    * minus sits in an ARGUMENT, and all three variants passed it — the row measured
    * nothing until the `-` moved to the front. */
  test("a label followed by a prefix-minus head keeps its label") {
    val kb = LoadFixture.loaded(
      """namespace zzP85Lbl
        |  fact base(1)
        |  rule lblq: -negp(1) :- base(1)
        |end""".stripMargin,
      "lbl.anthill",
    )
    assert(
      kb.hasQualifiedName("zzP85Lbl.lblq"),
      "`lblq:` is a rule LABEL — the `:-` lookahead must not reject a colon followed by " +
        "a prefix-minus head",
    )
  }

  test("a bare equation subject introduces nothing") {
    // §5.3: a `[simp]` head is an APPLICATION, so `rule tau <=> …` matches no redex and
    // fires nothing. The one function this ticket changed is read by BOTH paths, and
    // minting a bare equation subject would stamp it `EquationFunctor` for a law that can
    // never run. The PARENTHESISED twin is the control: it DOES introduce.
    for (label, tag, mark, want) <-
      Seq(("bare", "P85EqBare", "", false), ("parens", "P85EqParen", "()", true))
    do
      val kb = LoadFixture.loaded(
        s"""namespace zz$tag
           |  rule tau$mark <=> 7
           |end""".stripMargin,
        s"$tag.anthill",
      )
      assertEquals(
        kb.hasQualifiedName(s"zz$tag.tau"), want,
        s"$label: only the APPLICATION spelling of an equation subject introduces a name",
      )
  }
