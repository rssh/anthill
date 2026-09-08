package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.resolve.SearchStream
import anthill.term.{Literal, Term}

/** WI-20260821-SBZ2A — A RULE HEAD DECLARES ITS PREDICATE AT THE SCOPE IT IS WRITTEN IN,
  * AND TWO SCOPES THAT CAN SEE EACH OTHER MAY NOT BOTH INTRODUCE ONE NAME.
  *
  * The scaland port of rustland's `wi_fqc85_rule_declaration_test` (proposal 061) and
  * `wi980_rule_head_order_test` (WI-980 as WI-20260822-845G7 left it). Both rules are
  * one ticket here because the second SHRINKS the first: 061 makes a predicate DECLARED
  * rather than discovered, minted in the pass that defines every other name, and once it
  * is, the fixpoint WI-980 shipped computes a constant — so what is ported is the
  * three-phase pass and two refusals, not the rounds, the SCC tie-break or the depth
  * bound rustland has since deleted.
  *
  * ── WHAT WAS WRONG HERE BEFORE, MEASURED ────────────────────────────────────
  *
  * TWO DEFECTS, and only the first was written down at its site.
  *
  *  1. ORDER. `scanRuleGoal`'s guard asked whether a head's name ALREADY DENOTES, and
  *     the pass minted as it walked — so the table it read was the one it was filling.
  *     `namespace demo { rule p(1) :- true  sort Rec { rule p(2) :- true } }` loaded as
  *     ONE predicate with two clauses when the namespace-level rule came first and as
  *     TWO when it came second. Both loaded clean, and the split silently decided
  *     whether a rule EXTENDS someone else's predicate.
  *  2. 061'S READING WAS ABSENT, AND ITS ABSENCE WAS SILENT IN THE SHIPPED STDLIB.
  *     `loadRuleHeads` read `rule.body.isEmpty` as a FACT, so
  *     `logic/constructive.anthill`'s eight intuitionistic axioms — DECLARATIONS in the
  *     shipped source since 061 — were asserted here as universally-true facts whose
  *     variable heads match any proposition; and every `:- true` clause (the stdlib
  *     writes them in `reflect/typing.anthill`, `realization/realization.anthill`,
  *     `prelude/set.anthill` and `prelude/lattice.anthill`) loaded as a BODIED rule whose
  *     `true` goal no clause and no builtin resolves, so those predicates answered
  *     NOTHING. The stdlib parses AND loads clean in scaland, which is what kept sbt
  *     green; no row DROVE any of those predicates. The top-level strip closes that; the
  *     GENERAL reading of a boolean goal is WI-20260822-J38JE's resolver arm, which
  *     scaland still lacks — driven as a gap by `J38JE GAP: a boolean constant goal has
  *     no reading below the top level`.
  *
  * ── THE RULE, IN TWO SENTENCES ──────────────────────────────────────────────
  *
  * > A rule head whose functor RESOLVES is a clause of what it resolves to. One that
  * > resolves to NOTHING declares its predicate at the scope it is WRITTEN IN.
  *
  * Nothing is asked about any other head, so no order can enter — order-freedom is a
  * property of the rule rather than a result computed over the finished program. The rows
  * below still run both orders, because a claim that holds in only one order measures
  * nothing, and because the REFUSAL must be order-free too.
  *
  * ── WHY THE SECOND HALF IS A REFUSAL AND NOT A SPLIT ────────────────────────
  *
  * The rule above is total, but it makes a second scope's same-named head a SHADOW
  * rather than a clause — a scope's own name beats what it imports or inherits, because
  * `resolveRecursive` reads `locals` and returns before consulting any import or parent.
  * The SHADOW ITSELF IS NOT THE DEFECT; INVENTING IT IS. An author who WRITES
  * `rule p(?x)` in both scopes gets exactly that and should, so every refusal row below
  * carries a `declare in EACH scope` arm reproducing it.
  *
  * ── THE BACK-OUTS ───────────────────────────────────────────────────────────
  *
  * Each was APPLIED and the whole scaland suite RUN. Baseline: **565 rows, 563 pass**;
  * the two that fail are `BootstrapTest`'s `WI-1066 CORPUS CONTROL` and `WI-1055`, which
  * fail at HEAD for an unrelated reason (`field.anthill`'s cross-package `requires Ring`
  * has no Bootstrap emission) and are excluded from every count below.
  *
  *  * **THE 061 READING** — `case RuleReading.Declaration => ()` in `loadRuleHeads`, so a
  *    body-less rule ASSERTS again. **11 rows fail**: the four `061:` rows about what a
  *    declaration is or is not, all five channels, the named-owner row and the two-FILES
  *    row.
  *  * **THE TOP-LEVEL `true` STRIP** — drop `filterNot(isEmptyConjunctionGoal(…))` from
  *    `loadRuleHeads`' body build. **15 rows fail** — nearly every row, because once
  *    `rule H` declares, `:- true` is how an assertion is spelled, and an unerased `true`
  *    is a constant goal nothing resolves. All three CONTROLs fail here too, which is the
  *    point: they measure that each scope reaches its OWN clause, and there are no
  *    clauses left.
  *
  *    THAT 14 MEASURES A MISSING FEATURE, NOT THE STRIP, and it must be read that way:
  *    the same back-out fells **zero** rows in rustland, because WI-20260822-J38JE's
  *    resolver arm answers every `true` the strip stops seeing, and rustland corrected
  *    `wi_fqc85`'s own back-out list when it shipped. scaland has the strip and not the
  *    arm — see `J38JE GAP: a boolean constant goal has no reading below the top level`.
  *    What the strip is FOR here is the body's SHAPE: only an EMPTY body makes `fact H`
  *    and `rule H :- true` one clause, which is 061 item 5.
  *  * **THE PASS-1b MINT** — `if false then` in `DeclarePredicatePass.declare`. **8 rows
  *    fail**: all five channels, the named-owner row, the equation-subject row and the
  *    two-FILES row. The declaration mints nothing, so the heads it was to collect either
  *    collide or split.
  *  * **THE COLLISION REFUSAL** — `IndexedSeq.empty` in place of the
  *    `headNameCollisions(…)` call. **8 rows fail**: all five channels, the named-owner
  *    row, the equation-subject row and the LIMIT row's second arm. Every DECLARED arm
  *    passes either way, by design — that is what shows the refusal is about the SILENCE
  *    and not about the shape.
  *  * **THE PHASE FREEZE** — ask the ladder inside the mint loop instead of freezing every
  *    answer first (`if !d then scanRuleGoal(kb, h)` in the `denotes` map, with the
  *    separate mint loop deleted). This is the ORDER back-out, and the one this ticket is
  *    named for. **10 rows fail**: all five channels, the named-owner row, the
  *    equation-subject row, the two-FILES row, the LIMIT row and the `<global>` CONTROL —
  *    each of them in ONE of its two text or file orders and not the other, which is the
  *    defect itself. The `<global>` CONTROL is the sharpest: with the mint interleaved,
  *    `nd`'s head finds the top-level `p` already minted and joins it, so `nd.p` ceases to
  *    exist — WI-894's defect class, reached by asking one question too early.
  *  * **THE ASKING FILE** — `setAskingFile(None)` in place of `Some(file)` in
  *    `headNameReach`. **4 rows fail**: channels 4 and 5, the named-owner row and the
  *    LIMIT row. With imports no longer file-local the reach is read against no file at
  *    all, so a wildcard import contributes nothing and two importing siblings stop
  *    colliding.
  *  * **THE NAMED OWNER** — `ordered.find(cand => edges(cand).isEmpty)`, the SINK of the
  *    direct reach graph, in place of "reached by every other member". **3 rows fail**:
  *    channel 3, channel 4 and the named-owner row. This is the one whose failure is
  *    SILENT in the shipped program rather than loud — the named-owner row drives it:
  *    following the sink's advice on `zzA -> zzB -> zzC` makes the refused program LOAD
  *    CLEAN with `zzA.cp` still split off.
  *  * **THE PER-FILE OWNER** — `edges(other).contains(cand)`, the per-SCOPE union of
  *    reach, in place of the per-file `forall`. **exactly 1 row fails**: the named-owner
  *    row, on its reopened-scope arm.
  *  * **THE PER-SCOPE SENTINELS** — one shared sentinel for every scope. **8 rows fail**:
  *    all five channels, the named-owner row, the equation-subject row and the LIMIT row.
  *    A COARSE back-out, and it is worth saying why: the sentinel IS the scope's identity
  *    here, so sharing one destroys both the resolver's dedup (two overlaid scopes
  *    collapse into a single `Found`) and `headNameReach`'s reverse lookup.
  *  * **`<global>` AS A CANDIDATE** — drop `head.scope != kb.globalScope` from the
  *    candidate filter. **exactly 1 row fails**: `a global head is not a party to the
  *    collision`, on its imported-namespace arm. (Its declared arms cannot measure it at
  *    all — their heads denote, so none becomes a candidate.)
  *  * **`DeclaresNothing`** — `case None => RuleReading.Clause`. **exactly 1 row fails**:
  *    `a body-less rule that can declare NOTHING is refused`.
  *  * **THE FILE RULE'S EQUATION EXEMPTION** — drop `head.kind == SymbolKind.Goal` from
  *    its filter. **exactly 1 row fails**: `an EQUATION subject written in two files is
  *    not refused`.
  *  * **THE CONNECTIVE GUARD in `ruleReading`** — `else if false then`. **121 rows fail**,
  *    110 of them `BootstrapTest`'s and 10 `ParserIntegrationTest`'s, because the shipped
  *    stdlib stops loading: its law layer is written `rule Sort.op(…) <=> …`, whose
  *    subject is QUALIFIED and therefore introduces nothing, so every one of those heads
  *    reads as `DeclaresNothing`. NOT ISOLABLE, and said rather than credited to a
  *    neighbour; the row named "a `<=>` head whose subject introduces NOTHING is still a
  *    clause" is the cheapest witness for what the line is FOR.
  *
  * ONE LINE HAS NO TARGETED BACK-OUT EITHER: taking every candidate pair as an edge
  * instead of asking `headNameReach` — the crude way to remove the visibility test — is
  * not isolable for the same reason, because the stdlib writes many head names at scopes
  * that cannot see each other. `two scopes that cannot see each other keep their own` is
  * the cheapest witness for what THAT line is for.
  *
  * Every row DRIVES its goal. A rule head that binds nowhere still loads clean, so "it
  * loads" would keep passing through exactly the regression this suite exists for.
  */
class RuleHeadDeclarationTest extends munit.FunSuite:

  /** The given `(label, source)` files loaded into one fresh KB — the errors, RENDERED,
    * or the KB. */
  private def tryLoad(files: (String, String)*)(using munit.Location)
      : Either[IndexedSeq[String], KnowledgeBase] =
    val parsed = files.map((label, src) => LoadFixture.parsed(src, label)).toIndexedSeq
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, parsed)
    if errs.isEmpty then Right(kb) else Left(errs.map(_.render).toIndexedSeq)

  private def loaded(files: (String, String)*)(using munit.Location): KnowledgeBase =
    tryLoad(files*) match
      case Right(kb) => kb
      case Left(es)  => fail(s"expected a clean load, got:\n${es.mkString("\n")}")

  /** The refusal `want` must be among the load errors — and the fixture must not load. */
  private def refused(want: String, files: (String, String)*)(using munit.Location): Unit =
    refusedAll(Seq(want), files*)

  /** Every one of `wants` must appear in ONE of the load errors. Separate substrings
    * rather than one, where the message's word ORDER is the scan's and not the
    * program's — the file list in the 061 file-rule message is in file-arrival order,
    * as rustland's is, so asserting the joined spelling would measure the argument
    * order of the test instead of the diagnostic. */
  private def refusedAll(wants: Seq[String], files: (String, String)*)(using munit.Location): Unit =
    tryLoad(files*) match
      case Right(_) => fail(s"expected a refusal containing `${wants.mkString("`, `")}`; " +
        "the fixture loaded clean")
      case Left(es) =>
        for want <- wants do
          assert(es.exists(_.contains(want)), s"want `$want`, got:\n${es.mkString("\n")}")

  /** The clauses stored under the symbol `qn` names, or `None` when nothing is named `qn`
    * at all — the PREDICATE IDENTITY half of the claim, which answer counts alone do not
    * pin: a `Rec.p` that exists but is never reached leaves every count unchanged. */
  private def clauses(kb: KnowledgeBase, qn: String): Option[Int] =
    kb.tryResolveSymbol(qn).map(sym => kb.byFunctor(sym).length)

  /** How many solutions `<qn>(<args>)` has, built on the SYMBOL `qn` names — so a head
    * that landed on a different symbol counts zero rather than silently matching. */
  private def answers(kb: KnowledgeBase, qn: String, args: Int*)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val goal = kb.alloc(Term.Fn(sym,
      IArray.from(args.map(a => kb.alloc(Term.Const(Literal.IntLit(a.toLong))))), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  /** The SHARED arm: one declaration at `owner` collects every head, and the inner scope
    * introduces nothing. `innerQn` is asserted ABSENT rather than merely unreached — that
    * is the difference between the two readings, since a split program has a real inner
    * symbol carrying a clause the outer predicate never sees. */
  private def assertShared(kb: KnowledgeBase, owner: String, innerQn: String, total: Int)
      (using munit.Location): Unit =
    assertEquals(clauses(kb, s"$owner.p"), Some(total),
      s"`$owner.p` must be ONE predicate carrying every clause")
    assertEquals(clauses(kb, innerQn), None,
      s"`$innerQn` must not exist — the declaration is what the inner head resolves to")
    for n <- 1 to total do assertEquals(answers(kb, s"$owner.p", n), 1, s"$owner.p($n)")

  // ── Proposal 061: how a rule READS ──────────────────────────────────────────
  /** One shipped stdlib file's text, read from the same directory `StdlibFixture` uses.
    * Only the corpus row needs it — every other fixture here is written inline, so the
    * rows stay readable and only that one claim depends on what the stdlib says today. */
  private def stdlibText(relative: String): String =
    val src = scala.io.Source.fromFile(s"${anthill.codegen.scala.StdlibFixture.dir}/$relative")
    try src.mkString finally src.close()


  test("061: a body-less rule declares and asserts nothing") {
    // THE RULE ITSELF. `rule p(?x)` brings `p` into existence and stores NO clause, so
    // the predicate EXISTS and answers nothing — and the rule that reads it answers
    // nothing either, which is what makes the declaration a declaration rather than a
    // universally-true fact.
    val kb = loaded("decl.anthill" ->
      """namespace sbz.decl
        |  rule p(?x)
        |  rule uses(?y) :- p(?y)
        |end""".stripMargin)
    assertEquals(clauses(kb, "sbz.decl.p"), Some(0),
      "the predicate EXISTS — declared — and holds no clause")
    assertEquals(answers(kb, "sbz.decl.p", 1), 0, "so it answers nothing")
    assertEquals(answers(kb, "sbz.decl.uses", 1), 0, "and neither does its reader")

    // THE CONTROL, one token apart. Without it the arm above would be equally true of a
    // loader that dropped the rule entirely.
    val ctrl = loaded("asrt.anthill" ->
      """namespace sbz.asrt
        |  rule p(?x) :- true
        |  rule uses(?y) :- p(?y)
        |end""".stripMargin)
    assertEquals(clauses(ctrl, "sbz.asrt.p"), Some(1), "CONTROL: `:- true` ASSERTS")
    assertEquals(answers(ctrl, "sbz.asrt.p", 1), 1, "CONTROL")
    assertEquals(answers(ctrl, "sbz.asrt.uses", 1), 1, "CONTROL")
  }

  test("061 §6.1: a top-level `:- true` is ERASED, so it asserts what `fact` does") {
    // WHAT THE STRIP IS FOR is the body's SHAPE, not the meaning of `true`: only an EMPTY
    // body makes `fact H` and `rule H :- true` ONE clause rather than two with equal
    // answers. The MEANING is WI-20260822-J38JE's — a boolean constant in goal position
    // is a SEARCH — and it lives in the resolver, which scaland has not ported; see the
    // gap row below.
    //
    // THE STRIP HAD TO BE MADE REAL HERE, not merely prescribed. MEASURED in scaland
    // before this change: `rule p(1) :- true` loaded clean AND ANSWERED NOTHING — `true`
    // is a boolean literal, so the body carried a constant goal nothing resolves, and
    // every migrated stdlib site was silently empty.
    val kb = loaded("tt.anthill" ->
      """namespace sbz.tt
        |  rule p(1) :- true
        |  fact q(1)
        |  rule readp(?x) :- p(?x)
        |  rule readq(?x) :- q(?x)
        |end""".stripMargin)
    assertEquals(answers(kb, "sbz.tt.readp", 1), 1, "`:- true` asserts")
    assertEquals(answers(kb, "sbz.tt.readq", 1), 1, "and so does `fact`")
    assertEquals(clauses(kb, "sbz.tt.p"), Some(1),
      "one clause — the `true` contributed no goal, it IS the empty body")
    // The one place the two spellings still differ, and it is a KNOWN GAP rather than a
    // consequence of the desugaring: a `fact` head introduces no scoped name, so `q`
    // reaches the bare global intern. rustland records the same gap at the same row.
    assertEquals(clauses(kb, "sbz.tt.q"), None,
      "a `fact` head is NOT scoped where it is written — a separate ticket, not this one")
  }

  test("J38JE GAP: a boolean constant goal has no reading below the top level") {
    // THE LIMIT OF THE STRIP, driven so it is written down rather than discovered. 061
    // introduced the top-level `:- true` erasure under the reading "`true` IS the empty
    // conjunction"; WI-20260822-J38JE then settled the MEANING one rung lower — a boolean
    // constant in GOAL position is a SEARCH, `true` succeeding and `false` failing, at
    // EVERY goal position, which is where §6.6 already puts the boolean OPERATORS. That
    // reading lives in the RESOLVER (rustland's `SearchStream::step_init`) precisely
    // because a loader strip over the body's top-level goal list can never reach a goal
    // nested under `not` or `|`.
    //
    // SCALAND HAS THE STRIP AND NOT THE ARM, so the three rows below diverge from
    // rustland. They are asserted at the values scaland ACTUALLY gives, with the logical
    // answer named, so the row fails the day the arm lands and has to be updated on
    // purpose. J38JE's item 4 — a NON-Bool constant goal — is the same hole: `:- 42`
    // loads clean and never matches, where rustland refuses it, located.
    val kb = loaded("j.anthill" ->
      """namespace jj
        |  fact base(7)
        |  rule ptrue(1) :- true
        |  rule pfalse(1) :- false
        |  rule pint(1) :- 42
        |  rule notfalse(1) :- not(false)
        |  rule ortrue(1) :- base(9) | true
        |end""".stripMargin)
    // THE TWO THE STRIP REACHES, and they are right.
    assertEquals(answers(kb, "jj.ptrue", 1), 1, "a top-level `true` is erased: the clause fires")
    assertEquals(answers(kb, "jj.pfalse", 1), 0,
      "and `false` answers 0 — BY ACCIDENT: a constant names no name, so it resolves to " +
      "no clause and no builtin; it does not FAIL, it never becomes a goal")
    // THE THREE IT DOES NOT.
    assertEquals(answers(kb, "jj.notfalse", 1), 0, "GAP: logic says 1 — `not` of a failing goal")
    assertEquals(answers(kb, "jj.ortrue", 1), 0, "GAP: logic says 1 — `base(9)` fails, `true` succeeds")
    assertEquals(answers(kb, "jj.pint", 1), 0,
      "GAP: rustland REFUSES `:- 42`, located (J38JE item 4); here the clause is silently dead")
  }

  test("061: THE SHIPPED STDLIB — an intuitionistic axiom is a DECLARATION, not a fact") {
    // `logic/constructive.anthill`'s eight axioms are body-less rules, and the file says
    // in its own header what they mean: "they exist as named symbols so a `proof …` hint
    // block can reference them". Before this port scaland asserted them, so
    // `modus_ponens(?p, ?q)` — a head of two free variables — answered ANY goal.
    //
    // THE ONE ROW THAT READS THE SHIPPED CORPUS, deliberately: the fixtures above prove
    // the rule, and this proves the rule reaches the files scaland actually loads.
    val kb = loaded(
      "anthill/logic/minimal.anthill" -> stdlibText("anthill/logic/minimal.anthill"),
      "anthill/logic/constructive.anthill" -> stdlibText("anthill/logic/constructive.anthill"))
    val qn = "anthill.logic.Constructive.Constructive.modus_ponens"
    assertEquals(clauses(kb, qn), Some(0),
      "the axiom is DECLARED — the symbol exists and carries no clause")
    // ARITY 2, matching the axiom's own head. A goal of the wrong arity answers 0 under
    // both readings and would measure nothing; `modus_ponens(?p, ?q)` read as a FACT is
    // two free variables, so this goal answered 1 before the port.
    assertEquals(answers(kb, qn, 7, 8), 0,
      "so it proves nothing; asserted, its two-variable head answered every goal")
  }

  test("061: a body-less rule that can declare NOTHING is refused") {
    // FOUR SHAPES THAT NAME NO PREDICATE, each with the CONTROL that separates "this
    // shape is refused" from "this shape never loaded". Under 061 each would assert
    // nothing AND declare nothing, so the refusal is the loud reading of a silent drop.
    for (label, src) <- Seq(
      ("a `⊥` denial names no predicate",
        "namespace sbz.n0\n  rule base(1) :- true\n  rule ⊥\nend"),
      ("a declaration declares ONE name",
        "namespace sbz.n1\n  rule lawq: aq(1), bq(2)\nend"),
      ("a qualified name REFERENCES, it never introduces",
        "namespace sbz.n2\n  rule sbz.n2.other(1)\nend"),
      ("a bare variable head names no predicate",
        "namespace sbz.n3\n  rule ?x\nend"),
    ) do
      refused("declares nothing", s"$label.anthill" -> src)

    // THE CONTROLS — the same shapes that CAN carry a body, with one. Each loads.
    loaded("c0.anthill" ->
      "namespace sbz.c0\n  rule base(1) :- true\n  rule ⊥ :- base(9)\nend")
    loaded("c1.anthill" -> "namespace sbz.c1\n  rule lawq: aq(1), bq(2) :- true\nend")
  }

  test("061: a declaration carries no clause text") {
    // A declaration stores no clause, so a citation LABEL has nothing to cite and a
    // `[…]` tag has no clause to govern. Refused rather than dropped: both carriers were
    // silently lost the moment this reading stopped asserting.
    refused("A citation label on it has nothing to cite",
      "lbl.anthill" -> "namespace sbz.lbl\n  rule mylaw: p(?x)\nend")
    refused("A `[…]` tag on it has no clause to govern",
      "tag.anthill" -> "namespace sbz.tag\n  rule p(?x) [simp]\nend")
    // THE CONTROLS — the same carriers on a rule that DOES store a clause.
    loaded("lblc.anthill" -> "namespace sbz.lblc\n  rule mylaw: p(?x) :- true\nend")
    loaded("tagc.anthill" -> "namespace sbz.tagc\n  rule p(?x) :- true\nend")
  }

  test("061: a declaration of a name another construct owns is refused") {
    // `SymbolTable.define` MERGES a repeated (name, scope), so `operation has(x) -> Bool`
    // beside `rule has(?x)` declares nothing new AND asserts nothing — a no-op line, and
    // 059 R4 clause 3 refuses exactly that for every other pair of declarations at one
    // address.
    //
    // BOTH ORDERS, AND THAT IS THE ROW THAT DROVE `DeclarePredicatePass` INTO ITS OWN
    // WALK. A scaland symbol carries ONE kind, so minting the declaration inside pass 1
    // let the text order decide it: MEASURED on the first cut of this port, `opfirst` was
    // refused and `rulefirst` LOADED CLEAN with `has` stamped a `Goal`. Deferring every
    // declaration until every other name in every file exists is what makes the pair
    // agree — the WI-321 invariant, applied to the one kind that did not have it.
    for (label, body) <- Seq(
      ("opfirst", "  operation has(x: Int64) -> Bool\n  rule has(?x)\n"),
      ("rulefirst", "  rule has(?x)\n  operation has(x: Int64) -> Bool\n"),
    ) do
      refused("is already declared in this scope (kind: Operation)",
        s"$label.anthill" -> s"namespace sbz.own$label\n${body}end")
  }

  test("061: an equational head is untouched in both spellings") {
    // 061 leaves equations alone: a `<=>` head's clauses index under the CONNECTIVE, so
    // its subject owns none and there is no predicate to declare. It must NOT read as a
    // declaration, and the `=`/`===` refusals must keep firing rather than be swallowed
    // by one.
    val kb = loaded("eq.anthill" -> "namespace sbz.eq\n  rule tau() <=> 7\nend")
    assert(kb.hasQualifiedName("sbz.eq.tau"),
      "the equation subject still introduces its name")
    refused("is the semantic equality TEST",
      "eqbad.anthill" -> "namespace sbz.eqbad\n  rule tau() = 7\nend")
    refused("is the structural identity TEST",
      "eqbad2.anthill" -> "namespace sbz.eqbad2\n  rule tau() === 7\nend")
    // AND `:- true` REACHES THEM, which is what makes the widened emptiness real: the
    // explicit spelling of the same empty body must be refused exactly as the arrow-less
    // form is.
    refused("is the semantic equality TEST",
      "eqbad3.anthill" -> "namespace sbz.eqbad3\n  rule tau() = 7 :- true\nend")
  }

  test("061: a `<=>` head whose subject introduces NOTHING is still a clause") {
    // [[Loader.ruleReading]] reads the equality family WHOLE — before
    // `ruleIntroducedFunctor` is asked — and this is the population that needs it: a
    // `<=>` head whose subject introduces NO NAME (a QUALIFIED one references an existing
    // symbol; a desugared one carries the converter's functor). Asked the other way
    // round, such a head reads as `DeclaresNothing` and the rule is refused.
    //
    // THE STDLIB'S WHOLE LAW LAYER IS WRITTEN THIS WAY, which is why the back-out for
    // this line is not isolable: with the guard removed the shipped stdlib stops loading
    // and 121 rows fail, 110 of them `BootstrapTest`'s. This row is the cheapest witness
    // for what the guard is FOR.
    val kb = loaded("qeq.anthill" ->
      """namespace sbz.qeq
        |  sort S
        |    sort T = ?
        |    operation isEmpty(s: T) -> Bool
        |  end
        |  rule S.isEmpty(?s) <=> true
        |end""".stripMargin)
    val ns = kb.symbols.scopeOf(kb.tryResolveSymbol("sbz.qeq").getOrElse(fail("no `sbz.qeq`")))
    val stored = kb.byDomain(ns)
    assertEquals(stored.length, 1, "the equation stored its clause — it is not a declaration")
    assert(kb.isEquation(stored.head), "and it is stored AS an equation")
    // WI-898, and the reason the clause count above is not asked of the SUBJECT: an
    // equation's clauses index under the `<=>` connective and never under the name it
    // defines.
    assertEquals(clauses(kb, "sbz.qeq.S.isEmpty"), Some(0),
      "the subject owns no clauses — which is why it declares no predicate either")
  }

  // ── 845G7: two scopes that can see each other ───────────────────────────────

  /** Channel 1's fixture — a sort body, reached through the ENCLOSING chain. */
  private def sortBody(ns: String, ruleFirst: Boolean, decl: String): String =
    val outer = s"$decl  rule p(1) :- true\n"
    val inner = "  sort Rec\n    entity rec(n: Int64)\n    rule p(2) :- true\n  end\n"
    val body = if ruleFirst then outer + inner else inner + outer
    s"namespace $ns\n${body}end"

  test("845G7 channel 1: a sort body and its namespace must declare a shared name") {
    // THE SHAPE THE OLD SCALAND COMMENT NAMED, and the one this port changes the answer
    // to. The sort's head sees the namespace's through the ENCLOSING chain, so both
    // introduce `p` and the program does not say which owns it. Refused in BOTH text
    // orders — a refusal that fired in only one would be the order dependence this
    // ticket removes, wearing a different hat.
    for (ns, first) <- Seq(("sbz.body1", true), ("sbz.body2", false)) do
      refused(s"$ns, $ns.Rec", s"$ns.anthill" -> sortBody(ns, first, ""))
    // DECLARED AT THE NAMESPACE — one predicate, both clauses, the sort's clause reached
    // THROUGH it. In BOTH orders, which is the order-freedom claim itself.
    for (ns, first) <- Seq(("sbz.body3", true), ("sbz.body4", false)) do
      assertShared(loaded(s"$ns.anthill" -> sortBody(ns, first, "  rule p(?x)\n")),
        ns, s"$ns.Rec.p", 2)
    // DECLARED IN THE SORT TOO — two predicates, one clause each, which is the SPLIT the
    // rule refuses to invent. It is legal because it is written.
    val kb = loaded("body5.anthill" ->
      """namespace sbz.body5
        |  rule p(?x)
        |  rule p(1) :- true
        |  sort Rec
        |    entity rec(n: Int64)
        |    rule p(?x)
        |    rule p(2) :- true
        |  end
        |end""".stripMargin)
    assertEquals(clauses(kb, "sbz.body5.p"), Some(1))
    assertEquals(clauses(kb, "sbz.body5.Rec.p"), Some(1))
    assertEquals(answers(kb, "sbz.body5.p", 2), 0, "the sort's clause is its own")
    assertEquals(answers(kb, "sbz.body5.Rec.p", 2), 1)
  }

  /** Channel 2's fixture — a nested ordinary namespace. The inner scope is NOT a sort,
    * which is the point: the rule is about the enclosing CHAIN, not about sort-ness, and
    * a guard keyed on sorts would pass channel 1 and miss this. */
  private def nestedNs(ns: String, ruleFirst: Boolean, decl: String): String =
    val outer = s"$decl  rule p(1) :- true\n"
    val inner = "  namespace inner\n    rule p(2) :- true\n  end\n"
    val body = if ruleFirst then outer + inner else inner + outer
    s"namespace $ns\n${body}end"

  test("845G7 channel 2: a nested namespace and its parent must declare a shared name") {
    for (ns, first) <- Seq(("sbz.nest1", true), ("sbz.nest2", false)) do
      refused(s"$ns, $ns.inner", s"$ns.anthill" -> nestedNs(ns, first, ""))
    for (ns, first) <- Seq(("sbz.nest3", true), ("sbz.nest4", false)) do
      assertShared(loaded(s"$ns.anthill" -> nestedNs(ns, first, "  rule p(?x)\n")),
        ns, s"$ns.inner.p", 2)
  }

  test("845G7 channel 3: a facade and its submodule, at two and three levels") {
    // TWO EDGES AT ONCE: `fa1` sees `inner` through the wildcard import and `inner` sees
    // `fa1` through the enclosing chain.
    //
    // THE SUGGESTED OWNER IS THE FACADE, and that is worth driving: the reach is mutual,
    // so a "reaches nothing" sink test would find nothing and name no owner at all.
    val two = "namespace fa1\n  import fa1.inner.*\n  rule p(1) :- true\n" +
      "  namespace inner\n    rule p(2) :- true\n  end\nend"
    refused("fa1, fa1.inner", "fa1.anthill" -> two)
    refused("a body-less `rule p(…)` in 'fa1', with a named import of that predicate",
      "fa1.anthill" -> two)
    // ONE LEVEL DEEPER — the control on the reach being the real one. A rule read off
    // ADDRESS PREFIXES would still pass the two-level arm.
    val three = "namespace fa2\n  import fa2.inner.*\n  rule p(1) :- true\n" +
      "  namespace inner\n    rule p(2) :- true\n    namespace deep\n" +
      "      rule p(3) :- true\n    end\n  end\nend"
    refused("fa2, fa2.inner, fa2.inner.deep", "fa2.anthill" -> three)
    // DECLARED AT THE FACADE — all three clauses, at any depth.
    val threeDecl = "namespace fa3\n  import fa3.inner.*\n  rule p(?x)\n  rule p(1) :- true\n" +
      "  namespace inner\n    rule p(2) :- true\n    namespace deep\n" +
      "      rule p(3) :- true\n    end\n  end\nend"
    val kb = loaded("fa3.anthill" -> threeDecl)
    assertShared(kb, "fa3", "fa3.inner.p", 3)
    assertEquals(clauses(kb, "fa3.inner.deep.p"), None)
  }

  test("845G7 channel 4: a mutual-import cycle must declare a shared name") {
    // Neither member encloses the other and EACH REACHES THE OTHER, so declaring at
    // either collects the whole group — which is what the owner test ("reached by every
    // other member") answers, and what a sink test cannot.
    //
    // ONE FILE AND TWO, both refused, and in BOTH file orders: the hazard here is
    // shadowing, not assembly, so one author writing both in one file is still one
    // author getting a meaning they did not write.
    val a = "namespace mA\n  import mB.*\n  rule p(1) :- true\n  rule usesp(?x) :- p(?x)\nend"
    val b = "namespace mB\n  import mA.*\n  rule p(2) :- true\nend"
    refused("mA, mB", "a.anthill" -> a, "b.anthill" -> b)
    refused("mA, mB", "b.anthill" -> b, "a.anthill" -> a)
    refused("a body-less `rule p(…)` in 'mA', with a named import of that predicate",
      "one.anthill" -> (a + "\n" + b))

    // REMEDY 1 — DECLARE IT ONCE in `mA` and NAME it from `mB`. The selective import is
    // the explicit opt-in to append to someone else's predicate.
    val aDecl = "namespace mA\n  import mB.*\n  rule p(?x)\n  rule p(1) :- true\n" +
      "  rule usesp(?x) :- p(?x)\nend"
    val bSelected = "namespace mB\n  import mA.{p}\n  rule p(2) :- true\nend"
    // BOTH FILE ORDERS, which is the order-freedom claim at the file granularity: the
    // declaration is minted before any head is decided, so which file the scan reaches
    // first cannot move a clause.
    for files <- Seq(Seq("a.anthill" -> aDecl, "b.anthill" -> bSelected),
                     Seq("b.anthill" -> bSelected, "a.anthill" -> aDecl)) do
      val shared = loaded(files*)
      assertEquals(clauses(shared, "mA.p"), Some(2), "one predicate, both clauses")
      assertEquals(clauses(shared, "mB.p"), None, "`mB` introduced nothing")
      assertEquals(answers(shared, "mA.usesp", 1), 1)
      assertEquals(answers(shared, "mA.usesp", 2), 1,
        "the import is LIVE — this is the row that reads 0 under a silent split")

    // REMEDY 2 — DECLARE IT IN EACH, which says they are separate predicates. THE SHADOW
    // IS BACK, and that is the point: it is refused only when nobody wrote it.
    val bOwn = "namespace mB\n  import mA.*\n  rule p(?x)\n  rule p(2) :- true\nend"
    for files <- Seq(Seq("a.anthill" -> aDecl, "b.anthill" -> bOwn),
                     Seq("b.anthill" -> bOwn, "a.anthill" -> aDecl)) do
      val split = loaded(files*)
      assertEquals(clauses(split, "mA.p"), Some(1), "two predicates, one clause each")
      assertEquals(clauses(split, "mB.p"), Some(1))
      assertEquals(answers(split, "mA.usesp", 1), 1, "its own clause is reached")
      assertEquals(answers(split, "mA.usesp", 2), 0,
        "and the imported one is NOT — the declared local shadows the import, as written")
    // THE CONTROL for that 0: the same import with nothing local to shadow it.
    val ctrl = loaded(
      "a.anthill" -> "namespace mA\n  import mB.*\n  rule usesp(?x) :- p(?x)\nend",
      "b.anthill" -> b)
    assertEquals(answers(ctrl, "mA.usesp", 2), 1, "CONTROL: the import works")
    assertEquals(answers(ctrl, "mA.usesp", 1), 0, "CONTROL: nothing local exists")
  }

  test("845G7 channel 5: a one-way import names the imported scope as owner") {
    // ONE EDGE, so the program does name an owner — `mD` is what `mC` imports and reaches
    // nothing itself. That is the difference from the cycle above, driven rather than
    // described: same two scopes, same two heads, one import instead of two.
    val c = "namespace mC\n  import mD.*\n  rule p(1) :- true\n  rule usesp(?x) :- p(?x)\nend"
    val d = "namespace mD\n  rule p(2) :- true\nend"
    for files <- Seq(Seq("c.anthill" -> c, "d.anthill" -> d),
                     Seq("d.anthill" -> d, "c.anthill" -> c)) do
      refused("a body-less `rule p(…)` in 'mD', with a named import of that predicate",
        files*)
    // AND THE OWNER IT NAMES IS THE ONE THAT WORKS.
    val kb = loaded(
      "c.anthill" ->
        "namespace mC\n  import mD.{p}\n  rule p(1) :- true\n  rule usesp(?x) :- p(?x)\nend",
      "d.anthill" -> "namespace mD\n  rule p(?x)\n  rule p(2) :- true\nend")
    assertEquals(clauses(kb, "mD.p"), Some(2), "one predicate, both clauses")
    assertEquals(clauses(kb, "mC.p"), None)
    assertEquals(answers(kb, "mC.usesp", 1), 1)
    assertEquals(answers(kb, "mC.usesp", 2), 1, "the import is live")
  }

  test("845G7: a named owner must be reachable from EVERY other member") {
    // THE MESSAGE'S PROMISE IS PART OF THE MESSAGE. When it names a scope it says
    // declaring there makes every head a clause of it, so the test that picks the scope
    // is "IS REACHED BY EVERY OTHER MEMBER" — not "reaches nothing". The two differ
    // exactly where reach is NOT transitive, which a wildcard import always is not: it is
    // never re-exported.
    //
    // THE CHAIN IS THE WITNESS. `zzA -> zzB -> zzC`: the SINK is `zzC` and `zzA` cannot
    // see it, so no scope may be named.
    val a = "namespace zzA\n  import zzB.*\n  rule cp(1) :- true\nend"
    val b = "namespace zzB\n  import zzC.*\n  rule cp(2) :- true\nend"
    val c = "namespace zzC\n  rule cp(3) :- true\nend"
    refused("No one of them is reachable from all the others",
      "a.anthill" -> a, "b.anthill" -> b, "c.anthill" -> c)
    // AND HERE IS WHAT NAMING THE SINK WOULD HAVE COST, driven rather than described:
    // declaring at `zzC` — the advice a sink test gives — makes the program LOAD CLEAN
    // with `zzA.cp` STILL A SEPARATE PREDICATE and nothing reported. That is the split
    // the refusal exists to prevent, reached by taking its own advice.
    //
    // (rustland refuses this program on a second rule scaland has not ported — C666A's
    // unguarded non-enclosing join. Here it is silent, which makes the row a sharper
    // measurement of the owner test rather than a weaker one.)
    val cDecl = "namespace zzC\n  rule cp(?x)\n  rule cp(3) :- true\nend"
    val absorbed = loaded("a.anthill" -> a, "b.anthill" -> b, "c.anthill" -> cDecl)
    assertEquals(clauses(absorbed, "zzC.cp"), Some(2), "the sink absorbed only `zzB`")
    assertEquals(clauses(absorbed, "zzA.cp"), Some(1), "and `zzA` is still split off")

    // AND THE SAME PROMISE ACROSS FILES, not only across hops. `pwA` is reopened in two
    // files and only ONE carries `import pwB.*`, so `pwB` is reached from one of `pwA`'s
    // files and not the other — and may not be named, or declaring there would leave the
    // import-less head behind.
    val a1 = "namespace pwA\n  import pwB.*\n  rule p(1) :- true\nend"
    val a2 = "namespace pwA\n  rule p(9) :- true\nend"
    val pwb = "namespace pwB\n  rule p(2) :- true\nend"
    refused("No one of them is reachable from all the others",
      "a1.anthill" -> a1, "a2.anthill" -> a2, "b.anthill" -> pwb)
    // ITS CONTROL — the same three files with the import in BOTH of `pwA`'s, so `pwB` is
    // reached from every file and may be named.
    refused("a body-less `rule p(…)` in 'pwB', with a named import of that predicate",
      "a1.anthill" -> a1,
      "a2.anthill" -> "namespace pwA\n  import pwB.*\n  rule p(9) :- true\nend",
      "b.anthill" -> pwb)

    // THE CONTROL FOR THE WHOLE ROW — three scopes where one IS reachable from all:
    // `zzD` and `zzE` both import `zzF` directly. Without it the assertions above would
    // be satisfied by never naming an owner at all.
    val d = "namespace zzD\n  import zzF.*\n  rule cp(1) :- true\nend"
    val e = "namespace zzE\n  import zzF.*\n  rule cp(2) :- true\nend"
    val f = "namespace zzF\n  rule cp(3) :- true\nend"
    refused("a body-less `rule cp(…)` in 'zzF', with a named import of that predicate",
      "d.anthill" -> d, "e.anthill" -> e, "f.anthill" -> f)
    // AND THE OWNER IT NAMES IS THE ONE THAT WORKS — the promise kept.
    val ok = loaded(
      "d.anthill" -> "namespace zzD\n  import zzF.{cp}\n  rule cp(1) :- true\nend",
      "e.anthill" -> "namespace zzE\n  import zzF.{cp}\n  rule cp(2) :- true\nend",
      "f.anthill" -> "namespace zzF\n  rule cp(?x)\n  rule cp(3) :- true\nend")
    assertEquals(clauses(ok, "zzF.cp"), Some(3), "CONTROL: the promise is kept")
    assertEquals(clauses(ok, "zzD.cp"), None, "CONTROL")
    assertEquals(clauses(ok, "zzE.cp"), None, "CONTROL")
    assertEquals(answers(ok, "zzF.cp", 1), 1, "CONTROL")
  }

  test("845G7: an equation subject is a party to the collision too") {
    // 061 PUTS EQUATIONS OUTSIDE THE *DECLARATION* RULE — their clauses index under the
    // connective, so the subject owns none — and reading that as "outside the VISIBILITY
    // rule too" is a silent split: `zeq` and `zeq.Rec` would each mint their own `f`
    // where the language used to give one, with nothing said. That is the exact hazard
    // this refusal exists for, permitted for half the head shapes.
    //
    // AND THE MESSAGE CHANGES ITS PRESCRIPTION for them, because a body-less `rule` does
    // not collect an equation's subject (WI-898). Both remedies it names are driven
    // below.
    val src = "namespace zeq\n  rule f(true) <=> 1\n  sort Rec\n    entity r(n: Int64)\n" +
      "    rule f(false) <=> 2\n  end\nend"
    refused("zeq, zeq.Rec", "e.anthill" -> src)
    refused("an `operation f(…) -> R` in 'zeq'", "e.anthill" -> src)
    // REMEDY 1 — the `operation` in the named owner, which IS the declaration of an
    // equation-defined name.
    val joined = loaded("e.anthill" ->
      ("namespace zeq2\n  operation f(b: Bool) -> Int64\n  rule f(true) <=> 1\n" +
       "  sort Rec\n    entity r(n: Int64)\n    rule f(false) <=> 2\n  end\nend"))
    assert(!joined.hasQualifiedName("zeq2.Rec.f"),
      "the operation collects both subjects — no second symbol at the sort")
    // REMEDY 2 — a declaration in EACH, which says they are separate.
    val split = loaded("e.anthill" ->
      ("namespace zeq3\n  rule f(?x)\n  rule f(true) <=> 1\n  sort Rec\n" +
       "    entity r(n: Int64)\n    rule f(?x)\n    rule f(false) <=> 2\n  end\nend"))
    assert(split.hasQualifiedName("zeq3.f"))
    assert(split.hasQualifiedName("zeq3.Rec.f"), "two symbols, because both are written")
  }

  test("845G7 LIMIT: the reach is asked only from files that WRITE a head") {
    // A LIMIT OF THE SHIPPED RULE, driven so it is written down rather than discovered.
    // `headNameCollisions` asks what a candidate scope can see from the files it WRITES A
    // HEAD IN, and imports are file-local (WI-995) — so a scope re-opened across files
    // with the `import` in one file and the head in another contributes no edge, and the
    // pair is not refused. The same program with the import line moved into the
    // head-writing file IS refused. Whether it loads therefore depends on which file the
    // import was typed in, not on what the program means.
    //
    // IT IS NOT A PORT DEFECT — RUSTLAND ANSWERS IDENTICALLY, MEASURED on these three
    // files through `anthill load`: `loaded: 2848 facts, 182 rules` for the first
    // arrangement and the same `ns.A, ns.B` refusal, at the same head, for the second.
    // Closing it in scaland alone would make the two loaders disagree about which
    // programs load, which is the divergence class this ticket exists to remove; it needs
    // one decision taken for both trees. Found by `/code-review`.
    val b = "namespace ns.B\n  rule p(2) :- true\nend"
    val kb = loaded(
      "g1.anthill" -> b,
      "g2.anthill" -> "namespace ns.A\n  import ns.B.*\n  rule reads(?x) :- p(?x)\nend",
      "g3.anthill" -> "namespace ns.A\n  rule p(1) :- true\nend")
    assertEquals(clauses(kb, "ns.A.p"), Some(1), "two predicates, and nothing said")
    assertEquals(clauses(kb, "ns.B.p"), Some(1))
    assertEquals(answers(kb, "ns.A.reads", 1), 1, "the local head is what the reader sees")
    assertEquals(answers(kb, "ns.A.reads", 2), 0,
      "and the `import ns.B.*` one line above it is SILENTLY SHADOWED — verbatim the " +
      "failure the refusal's own message describes")
    // THE SAME PROGRAM, one line moved into the head-writing file: refused.
    refused("ns.A, ns.B",
      "g1.anthill" -> b,
      "g2.anthill" -> "namespace ns.A\n  rule reads(?x) :- p(?x)\nend",
      "g3.anthill" -> "namespace ns.A\n  import ns.B.*\n  rule p(1) :- true\nend")
  }

  // ── 061's file rule ─────────────────────────────────────────────────────────

  test("061: one scope reopened in two FILES must declare its predicate") {
    // THE ROW THAT SEPARATES THE TWO REFUSALS. Same address, same name, ONE scope: the
    // collision rule is silent and the FILE rule speaks. Channel 1's rows are the mirror
    // — one file, two scopes — and the collision rule speaks there instead.
    val a = "namespace sbz.split\n  rule p(1) :- true\nend"
    val b = "namespace sbz.split\n  rule p(2) :- true\nend"
    for files <- Seq(Seq("a.anthill" -> a, "b.anthill" -> b),
                     Seq("b.anthill" -> b, "a.anthill" -> a)) do
      // NAMING BOTH FILES is part of the message: the fault is that two parties wrote
      // one predicate, so a reader has to be told which two. The file names come off the
      // head SPANS — `ParsedFile` carries no path — which is also what makes the error
      // located at all.
      refusedAll(Seq("has rule heads in 2 files", "a.anthill", "b.anthill",
        "write `rule p(…)` in 'sbz.split'"), files*)
    val aDecl = "namespace sbz.split\n  rule p(?x)\n  rule p(1) :- true\nend"
    for files <- Seq(Seq("a.anthill" -> aDecl, "b.anthill" -> b),
                     Seq("b.anthill" -> b, "a.anthill" -> aDecl)) do
      val kb = loaded(files*)
      assertEquals(clauses(kb, "sbz.split.p"), Some(2),
        "one predicate, one scope, both files")
      assertEquals(answers(kb, "sbz.split.p", 1), 1)
      assertEquals(answers(kb, "sbz.split.p", 2), 1)
  }

  test("061: a single-scope single-file predicate is auto-declared") {
    // THE CONTROL FOR THE FILE RULE — the same shape in ONE file needs no declaration.
    // Without it, a rule that refused every undeclared predicate would look correct.
    val kb = loaded("one.anthill" ->
      "namespace sbz.auto\n  rule p(1) :- true\n  rule p(2) :- true\nend")
    assertEquals(clauses(kb, "sbz.auto.p"), Some(2))
    assertEquals(answers(kb, "sbz.auto.p", 2), 1)
  }

  test("061: an EQUATION subject written in two files is not refused") {
    // The file rule is about a PREDICATE, and an equation's clauses index under the
    // connective — its subject owns none, so there is no predicate to declare. Backed out
    // (drop the `kind == Goal` filter), this row fails and nothing else does.
    val kb = loaded(
      "a.anthill" -> "namespace sbz.eqf\n  rule f(1) <=> 10\nend",
      "b.anthill" -> "namespace sbz.eqf\n  rule f(2) <=> 20\nend")
    assert(kb.hasQualifiedName("sbz.eqf.f"), "the subject is one symbol across both files")
  }

  // ── The controls ────────────────────────────────────────────────────────────

  test("845G7 CONTROL: two scopes that cannot see each other keep their own") {
    // THE CONTROL THE WHOLE RULE RESTS ON, and the one row whose absence would let a
    // refusal keyed on "two scopes share a short name" look correct while refusing most
    // real programs. `uA` and `uB` are siblings with no import, no `requires` and no
    // enclosure between them: two unrelated predicates that happen to share a name.
    //
    // BOTH ORDERS AND BOTH SPELLINGS — one file and two — because the visibility question
    // must not be answered by adjacency in the text or by which file arrived first.
    val a = "namespace uA\n  rule p(1) :- true\n  rule usesp(?x) :- p(?x)\nend"
    val b = "namespace uB\n  rule p(2) :- true\n  rule usesp(?x) :- p(?x)\nend"
    for files <- Seq(Seq("a.anthill" -> a, "b.anthill" -> b),
                     Seq("b.anthill" -> b, "a.anthill" -> a),
                     Seq("one.anthill" -> (a + "\n" + b))) do
      val kb = loaded(files*)
      assertEquals(clauses(kb, "uA.p"), Some(1), "each scope keeps its own")
      assertEquals(clauses(kb, "uB.p"), Some(1))
      assertEquals(answers(kb, "uA.usesp", 1), 1, "and each reaches only its own")
      assertEquals(answers(kb, "uA.usesp", 2), 0)
      assertEquals(answers(kb, "uB.usesp", 2), 1)
      assertEquals(answers(kb, "uB.usesp", 1), 0)
  }

  test("845G7 CONTROL: a global head is not a party to the collision") {
    // `<global>` IS THE ONE SCOPE NOBODY OPTS INTO — every file shares it, so a head
    // written inside a namespace must not collide with a top-level one. Fusing the two
    // questions fails either way round: treat `<global>` as a party and a one-line user
    // file deletes a stdlib predicate; refuse the pair and the language's own documented
    // top-level form stops loading.
    val g = "rule p(0) :- true"
    val nd = "namespace nd\n  rule p(5) :- true\nend"
    for files <- Seq(Seq("g.anthill" -> g, "n.anthill" -> nd),
                     Seq("n.anthill" -> nd, "g.anthill" -> g)) do
      val kb = loaded(files*)
      assertEquals(clauses(kb, "p"), Some(1), "the top-level head keeps its own")
      assertEquals(clauses(kb, "nd.p"), Some(1), "and the namespace head keeps its own")
      assertEquals(answers(kb, "nd.p", 5), 1)
      assertEquals(answers(kb, "nd.p", 0), 0, "two predicates, not one")
      assertEquals(answers(kb, "p", 0), 1)

    // AND THE EXCLUSION HOLDS IN THE OTHER DIRECTION TOO — the one an overlay-only
    // exclusion does NOT give you. The group is the UNDIRECTED closure of reach, so a
    // namespace-less file that writes `import zzns.*` and a head of the same name would
    // pull `zzns` into a group with `<global>`, and the repair such a refusal names
    // DELETES the `<global>` head's predicate.
    //
    // WHAT THAT COSTS IS A NAMED SILENCE, not a repair: the top-level head does shadow
    // `zzns.gp` for its own file, and nothing says so. The two clause counts pin the
    // trade rather than assume it.
    val nsImported = "namespace zzns\n  rule gp(1) :- true\nend"
    val gImports = "import zzns.*\nrule gp(2) :- true"
    for files <- Seq(Seq("n.anthill" -> nsImported, "g.anthill" -> gImports),
                     Seq("g.anthill" -> gImports, "n.anthill" -> nsImported)) do
      val kb = loaded(files*)
      assertEquals(clauses(kb, "gp"), Some(1), "the top-level head keeps its own")
      assertEquals(clauses(kb, "zzns.gp"), Some(1),
        "and so does the namespace it imports")
  }

  test("845G7 CONTROL: the documented top-level form loads") {
    // `kernel-language.md`'s `**Forms:**` block and `examples/classic-mini/ancestor`
    // both teach a NAMESPACE-LESS program, so `<global>` must stay a scope a head can
    // introduce into. PASSES EITHER WAY today; it is here because refusing the
    // `<global>` pair — the other way to fuse the two questions — breaks exactly this
    // shape, and five documentation sites teach it.
    val kb = loaded("forms.anthill" ->
      "rule parent(1, 2) :- true\nrule ancestor(?x, ?z) :- parent(?x, ?z)")
    assertEquals(clauses(kb, "parent"), Some(1))
    assertEquals(clauses(kb, "ancestor"), Some(1))
    assertEquals(answers(kb, "ancestor", 1, 2), 1)
    assertEquals(answers(kb, "ancestor", 2, 1), 0, "CONTROL: and only what follows")
  }

  test("845G7 CONTROL: a head whose name RESOLVES is a clause of what it resolves to") {
    // THE OTHER END OF THE RULE, and what keeps the law layer working: refusing head /
    // import coexistence generally would report the stdlib's own laws as errors. A head
    // naming a DECLARED operation contributes a clause to it and introduces nothing, so
    // it never becomes a candidate for either refusal.
    val kb = loaded("law.anthill" ->
      """namespace sbz.law
        |  sort S
        |    sort T = ?
        |    operation gte(a: T, b: T) -> Bool
        |    rule gte(?x, ?y) :- true
        |  end
        |end""".stripMargin)
    assertEquals(clauses(kb, "sbz.law.S.gte"), Some(1),
      "the law is a clause OF the declared operation — no second symbol was minted")
  }
