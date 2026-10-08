package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.{Term, Var}
import anthill.resolve.SearchStream

/** WI-20260821-RDGQC (rustland's twin: `wi_rdgqc_head_introduction_census_test`) — WHICH
  * HEAD SHAPES INTRODUCE A NAME, STATED ONCE AND DRIVEN ONCE.
  *
  * A head that introduces nothing reaches the bare intern: ONE GLOBAL NAME two scopes
  * then share, with one scope's clause answering inside the other, on a program that
  * loads clean (WI-894's defect class). Every row below is two scopes writing ONE head
  * name, each reading it through a rule of its own, so a merge is a WRONG COUNT.
  *
  * | shape                                 | scoped? | rows                            |
  * |---------------------------------------|---------|---------------------------------|
  * | `rule p(1) :- …` applied              | YES     | A, 0 and 1                      |
  * | `rule p :- …` paren-less              | YES     | A, 0 and 1                      |
  * | `rule f(?x) <=> …` equation subject   | YES     | A, two distinct symbols         |
  * | `fact p(1)`, `fact p`                 | YES     | A, 1 and 1, as `rule … :- true` |
  * | head in `provides … language anthill` | YES     | A, 0 and 1 — see that row       |
  * | `rule l: p(1), q(9) :- …`             | **no**  | B, 2 and 2 (NE0E4)              |
  * | `rule ns.p …`, `fact ns.p(…)`, `..p`  | n/a     | C, D — REFERENCES, by design    |
  * | `rule ?x.m(?y)`                       | n/a     | C — the desugar's functor       |
  *
  * A `provides … language rust` block is not in the table: scaland loads no clause from
  * one, so there is no head to scope (row A pins that, beside the `anthill` block).
  *
  * ── WHICH ROWS FAIL WHEN WHAT IS BACKED OUT — each applied in `Loader` and run ──
  *
  *  * **THE FACT ARM** — `case Item.FactItem(_) =>` with no `collectFact`, in
  *    `RuleHeadCollectPass.atItem`. **5 ROWS FAIL HERE** — `a fact head is scoped
  *    exactly like the rule spelling…`, `a fact head meets the refusals…`, `a fact head
  *    beside a sibling file's imported one…`, `a fact head that already denotes…`, `a
  *    fact head in a namespace does not join…` — and 2 more over the whole scaland suite
  *    (7 of 613): `LoaderTest`'s WI-1007 control and `RuleHeadDeclarationTest`'s §6.1
  *    row, both of which read a fact head by its name.
  *  * **THE BLOCK ARM** — the `Item.ProvidesBlockItem` arm collecting nothing.
  *    **1 ROW FAILS**: `a head in a language-anthill block…`, on its `anthill` half.
  *  * **THE BLOCK GATE** — that arm collecting without asking
  *    `loadsProvidesBlockClauses`. **1 ROW FAILS**: the same row, on its `language rust`
  *    half — heads minted for clauses the load never asserts.
  *  * **THE BARE-NAME ARM** — `case id: Term.Ident => Left(NotAnApplication)` in
  *    `introducedName`. **2 ROWS FAIL**, each on its bare variant only: `a rule head is
  *    scoped where it is written…` and `a fact head is scoped exactly like…`.
  *  * **THE DOT REFUSAL** — `unqualified` answering `Right(name)`. **3 ROWS FAIL**:
  *    both Part C rows, and `a fact head that already denotes…` on its qualified half.
  *  * **TWO `NoIntroduction.detail` ARMS SHARE A SENTENCE** — `NotAnApplication` given
  *    the `DenialHead` text. **1 ROW FAILS**: `every NoIntroduction reason is reachable
  *    and distinct`.
  *
  * THREE ROWS PASS UNDER EVERY ONE OF THOSE, BY DESIGN, and say so at their site: the
  * multi-head row pins NE0E4's defect and fails when that defect is FIXED; `a fact head
  * and a rule head of one name…` is the control a fact arm must not break; and `the
  * repairs those refusals advise…` measures the advice, a declared predicate needing no
  * mint. PART C ALSO PASSES AGAINST THE TWO-WALK CODE — merging the walks moved no
  * sentence (measured: the probe's five were identical before and after); its teeth are
  * the last back-out.
  */
class HeadIntroductionCensusTest extends munit.FunSuite:

  private def tryLoad(files: (String, String)*)(using munit.Location)
      : Either[Seq[String], KnowledgeBase] =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val parsed = files.toIndexedSeq.map((label, src) => LoadFixture.parsed(src, label))
    val errs = Loader.loadAll(kb, parsed)
    if errs.isEmpty then Right(kb) else Left(errs.toSeq.map(_.render))

  private def loaded(src: String)(using munit.Location): KnowledgeBase =
    LoadFixture.loaded(src, "census.anthill")

  private def refusal(files: (String, String)*)(using munit.Location): Seq[String] =
    tryLoad(files*).left.getOrElse(fail("expected a load refusal, the program loaded"))

  /** Solutions of `<qn>(?x)` — the goal built on the SYMBOL the name resolves to, so a
    * clause that landed on another symbol is not counted. */
  private def answers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("x")))))
    SearchStream.resolve(kb, kb.alloc(Term.Fn(sym, IArray(v), IArray.empty)))
      .allSolutions(kb).length

  /** The names the scope `qn` itself declares. */
  private def locals(kb: KnowledgeBase, qn: String)(using munit.Location): Set[String] =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    kb.symbols.scope(kb.symbols.scopeOf(sym)).fold(Set.empty[String])(_.locals.keySet.toSet)

  /** Two sibling namespaces `zzC.<tag>a` / `zzC.<tag>b`, each writing its own head line
    * (`a` / `b`) and reading it through a `see` of its own. */
  private def pair(tag: String, a: String, b: String, read: String): String =
    s"""namespace zzC.${tag}a
       |  fact ba(1)
       |  $a
       |  rule see(1) :- $read
       |end
       |namespace zzC.${tag}b
       |  fact bb(1)
       |  $b
       |  rule see(1) :- $read
       |end""".stripMargin

  private def assertTwoPredicates(kb: KnowledgeBase, tag: String, label: String)(
      using munit.Location): Unit =
    assert(
      kb.hasQualifiedName(s"zzC.${tag}a.pick") && kb.hasQualifiedName(s"zzC.${tag}b.pick"),
      s"$label: each scope's head is CITABLE under its own qualified name")

  // ── PART A — THE ADMITTED SHAPES: two scopes, two predicates ────────────────

  test("a rule head is scoped where it is written, applied or paren-less") {
    // THE INVERTED PAIR: `a`'s clause is FALSE and `b`'s TRUE, so a merge shows as `a`
    // answering 1 from `b`'s clause.
    for (label, tag, mark, read) <- Seq(
        ("applied", "ap", "(1)", "pick(?)"), ("paren-less", "nu", "", "pick")) do
      val kb = loaded(pair(tag, s"rule pick$mark :- ba(999)", s"rule pick$mark :- bb(1)", read))
      assertTwoPredicates(kb, tag, label)
      assertEquals(
        (answers(kb, s"zzC.${tag}a.see"), answers(kb, s"zzC.${tag}b.see")), (0, 1),
        s"$label: the FALSE scope stays false — a 1 there is the other scope's clause")
  }

  test("an equation subject is scoped where it is written") {
    // THE SYMBOL, NOT A CLAUSE COUNT (WI-898): an equation's clause is headed by the
    // `<=>` connective, so it indexes nothing under the subject either way.
    val kb = loaded(
      """namespace zzC.eqa
        |  rule pick(?x) <=> 1
        |end
        |namespace zzC.eqb
        |  rule pick(?x) <=> 2
        |end""".stripMargin)
    val (a, b) = (kb.tryResolveSymbol("zzC.eqa.pick"), kb.tryResolveSymbol("zzC.eqb.pick"))
    assert(a.isDefined && b.isDefined && a != b,
      s"two scopes' equation subjects are TWO symbols, got $a / $b")
  }

  test("a fact head is scoped exactly like the rule spelling of the same clause") {
    // `fact H` IS `rule H :- true` (§6.1), so the two are ONE clause and must be one
    // program. WRITTEN AS THE PAIR: a regression shows as the spellings DISAGREEING.
    //
    // BACK-OUT (the fact arm): both `fact` rows fail, at the NAME assertion — measured
    // before the arm, the applied one also counted (2, 2), each scope reading the
    // other's fact. The `rule` rows are unmoved, which makes the axis the KEYWORD.
    for (label, tag, a, b, read) <- Seq(
        ("fact, applied", "fa", "fact pick(1)", "fact pick(2)", "pick(?)"),
        ("rule, applied", "ra", "rule pick(1) :- true", "rule pick(2) :- true", "pick(?)"),
        ("fact, bare", "fb", "fact pick", "fact pick", "pick"),
        ("rule, bare", "rb", "rule pick :- true", "rule pick :- true", "pick")) do
      val kb = loaded(pair(tag, a, b, read))
      assertTwoPredicates(kb, tag, label)
      assertEquals(
        (answers(kb, s"zzC.${tag}a.see"), answers(kb, s"zzC.${tag}b.see")), (1, 1),
        s"$label: each scope answers from its OWN clause and not from the other's too")
  }

  test("a fact head and a rule head of one name in one scope are one predicate") {
    // THE CONTROL the fact arm must not break, and it PASSES WITH THE ARM BACKED OUT, by
    // design: the rule's head mints `p` either way and the fact's head resolves to it.
    // What it guards is the other direction — a fact arm that minted a second symbol.
    val kb = loaded(
      """namespace zzC.one
        |  fact base(7)
        |  fact p(1)
        |  rule p(?x) :- base(?x)
        |  rule see(?x) :- p(?x)
        |end""".stripMargin)
    val p = kb.tryResolveSymbol("zzC.one.p").getOrElse(fail("`zzC.one.p` must resolve"))
    assertEquals(kb.byFunctor(p).length, 2, "the fact and the rule are two clauses of `p`")
    assertEquals(answers(kb, "zzC.one.see"), 2)
  }

  test("a head in a language-anthill block is scoped where the block's clauses land") {
    // scaland loads a `language anthill` block's rules and facts into the scope the
    // block is WRITTEN in (it opens no scope of its own), and the heads are minted
    // there — `Loader.loadsProvidesBlockClauses` gates both. rustland lands them in the
    // sort the block realizes; that port is not made here.
    //
    // BACK-OUT (the block arm): none of the four names resolves — and, measured before
    // the arm, the FALSE namespace's `see` answered 1, from the other block's clause,
    // and `fsee` answered 2 in both.
    def block(ns: String, base: String, guard: String, n: Int) =
      s"""namespace zzC.$ns
         |  fact $base(1)
         |  sort Rec
         |    entity E(v: Int64)
         |  end
         |  provides Rec language anthill
         |    rule pick(1) :- $guard
         |    fact fpick($n)
         |  end
         |  rule see(1) :- pick(?)
         |  rule fsee(?x) :- fpick(?x)
         |end""".stripMargin
    val kb = loaded(block("bka", "ba", "ba(999)", 1) + "\n" + block("bkb", "bb", "bb(1)", 2))
    for name <- Seq("zzC.bka.pick", "zzC.bkb.pick", "zzC.bka.fpick", "zzC.bkb.fpick") do
      assert(kb.hasQualifiedName(name), s"`$name` is citable where its clause landed")
    assertEquals((answers(kb, "zzC.bka.see"), answers(kb, "zzC.bkb.see")), (0, 1),
      "a rule head in the block: the FALSE namespace stays false")
    assertEquals((answers(kb, "zzC.bka.fsee"), answers(kb, "zzC.bkb.fsee")), (1, 1),
      "a fact head in the block: each namespace reads its own")

    // THE OTHER HALF OF THE SAME ANSWER: a block in any other language loads no clause
    // here, so its heads must mint nothing — a name with no clause behind it would
    // resolve and silently answer nothing.
    val host = loaded(
      """namespace zzC.bkh
        |  sort Rec
        |    entity E(v: Int64)
        |  end
        |  provides Rec language rust
        |    artifact "x.rs"
        |    rule pick(1) :- true
        |    fact fpick(1)
        |  end
        |end""".stripMargin)
    for name <- Seq("zzC.bkh.pick", "zzC.bkh.fpick", "zzC.bkh.Rec.pick", "zzC.bkh.Rec.fpick") do
      assert(!host.hasQualifiedName(name), s"`$name`: no clause was loaded, so no name")
  }

  // ── PART B — THE SHAPE LEFT OUT: the leak, pinned beside a control ──────────

  test("a multi-head rule's functors are unscoped and two scopes share one predicate") {
    // `ruleIntroducedFunctor` answers `SeveralHeads` — the rule names no SINGLE
    // predicate — while each head still lands its own clause, under the bare intern.
    // WI-20260908-NE0E4 owns the fix; closing it makes this (1, 1) and both names
    // resolve.
    //
    // THE BODIES ARE `true`, so the row reads no fact: written `:- base(0)` it moved
    // with the fact arm (a shared `base` doubled every count) and pinned two things.
    def two(ns: String, head: String) =
      s"""namespace zzC.$ns
         |  $head
         |  rule see(?x) :- pick(?x)
         |end""".stripMargin
    val kb = loaded(
      two("ma", "rule law: pick(1), other(9) :- true") + "\n" +
        two("mb", "rule law: pick(2), other(8) :- true"))
    assertEquals((answers(kb, "zzC.ma.see"), answers(kb, "zzC.mb.see")), (2, 2),
      "LIVE (NE0E4): each scope reads the other's head")
    assert(!kb.hasQualifiedName("zzC.ma.pick") && !kb.hasQualifiedName("zzC.mb.pick"),
      "and neither name is citable — the clauses live under one uncitable global")
    // THE CONTROL that isolates the HEAD COUNT: the same clause as a single-head rule.
    val ctl = loaded(
      two("mca", "rule pick(1) :- true") + "\n" + two("mcb", "rule pick(2) :- true"))
    assertEquals((answers(ctl, "zzC.mca.see"), answers(ctl, "zzC.mcb.see")), (1, 1),
      "single-head control must scope — that is what makes the axis the head COUNT")
  }

  // ── PART C — EVERY `NoIntroduction` REASON IS REACHABLE, AND SAYS ITS OWN THING ──

  private def declaresNothing(src: String)(using munit.Location): String =
    val errs = refusal("census.anthill" -> src)
    val hit = errs.find(_.contains("declares nothing"))
      .getOrElse(fail(s"no `declares nothing` refusal in $errs"))
    hit.substring(hit.indexOf("declares nothing"))

  test("every NoIntroduction reason is reachable and distinct") {
    // The five reasons, each driven from source through the one diagnostic that renders
    // them — `QualifiedSpelling` twice, a qualified name having two spellings. A sixth
    // variant with no producer, or without a sentence of its own, shows here as an
    // unreached row or a duplicate.
    //
    // `SeveralHeads` needs the LABEL in scaland: an unlabeled multi-head rule is refused
    // one step earlier, for wanting a citation handle.
    val rows = Seq(
      ("SeveralHeads", "rule law: aa(1), bb(2)",
        "it writes 2 heads at once, and a declaration declares ONE predicate"),
      ("DenialHead", "rule ⊥",
        "a `⊥` denial names no predicate, so there is nothing for it to declare"),
      ("DesugaredSubject", "rule ?x.m(?y)", "its head functor is the DESUGARING's"),
      ("NotAnApplication", "rule ?x",
        "its head is not a functor application, so it names no predicate"),
      ("QualifiedSpelling", "rule nosuch.xyz()", "`nosuch.xyz` is a QUALIFIED name"),
      // THE MARKED ABSOLUTE SPELLING of the same reason, paren-less: one segment, so a
      // bare `Term.Ident` whose NAME carries the dot — the shape rustland's census
      // drives this reason with, and the one that read as `NotAnApplication` there
      // while its applied twin read as this.
      ("QualifiedSpelling, marked", "rule ..nosuchxyz", "`..nosuchxyz` is a QUALIFIED name"))
    val seen = for (reason, head, sentence) <- rows yield
      val got = declaresNothing(s"namespace zzC.c\n  $head\nend")
      assert(got.contains(sentence), s"$reason: expected `$sentence`, got `$got`")
      got
    assertEquals(seen.distinct.length, rows.length,
      "each reason must say its OWN thing — two arms sharing a sentence is the drift " +
        "one walk exists to prevent")
  }

  test("both spellings of a qualified head get one reason") {
    // A dotted head written WITHOUT parentheses folds into a minted `field_access`
    // chain, and written WITH them is an application whose functor carries the dot: two
    // shapes, one head. With the sentence chosen by a second walk the two could be told
    // different things (rustland measured exactly that); one walk cannot.
    //
    // THE MARKED ABSOLUTE HEAD IS THE SAME PAIR ONE SHAPE OVER: paren-less it is a bare
    // `Term.Ident` and not a chain, so it reaches the reason through the `Ident` arm's
    // dot test rather than through `dottedCitationName` — two more routes to one answer.
    for head <- Seq("nosuch.xyz", "..nosuchxyz", "..nosuch.xyz") do
      assertEquals(
        declaresNothing(s"namespace zzC.q1\n  rule $head\nend"),
        declaresNothing(s"namespace zzC.q2\n  rule $head()\nend"),
        s"`$head`: one head, one verdict, one sentence")
  }

  // ── PART D — A FACT HEAD MEETS WHAT ITS RULE SPELLING MEETS ─────────────────

  /** `pick` written in a namespace AND in a sort nested in it — two scopes that can see
    * each other. `decl` lines go at the top of each. */
  private def nested(ns: String, outer: String, inner: String,
                     outerDecl: String = "", innerDecl: String = ""): String =
    s"""namespace zzC.$ns
       |  $outerDecl
       |  $outer
       |  rule nsee(?x) :- pick(?x)
       |  sort Rec
       |    entity E(v: Int64)
       |    $innerDecl
       |    $inner
       |    rule rsee(?x) :- pick(?x)
       |  end
       |end""".stripMargin

  test("a fact head meets the refusals its rule spelling meets") {
    // ONE NAME INTRODUCED AT TWO SCOPES THAT SEE EACH OTHER (845G7), and ONE PREDICATE
    // ASSEMBLED FROM TWO FILES WITH NO DECLARATION (061). Each is asked of both
    // spellings, because the `rule` one was refused all along while the `fact` one
    // loaded clean — the nested pair as ONE global predicate both readers shared.
    //
    // BACK-OUT (the fact arm): both `fact` arms LOAD, so `refusal` fails them.
    for (label, ns, outer, inner) <- Seq(
        ("fact", "nf", "fact pick(1)", "fact pick(2)"),
        ("rule", "nr", "rule pick(1) :- true", "rule pick(2) :- true")) do
      val errs = refusal("census.anthill" -> nested(ns, outer, inner))
      assert(errs.exists(_.contains("`pick` introduces that name at 2 scopes")),
        s"$label: two scopes that see each other may not both introduce `pick`: $errs")
    for (label, ns, head) <- Seq(
        ("fact", "ff", (n: Int) => s"fact p($n)"),
        ("rule", "fr", (n: Int) => s"rule p($n) :- true")) do
      val errs = refusal(
        "a.anthill" -> s"namespace zzC.$ns\n  ${head(1)}\nend",
        "b.anthill" -> s"namespace zzC.$ns\n  ${head(2)}\nend")
      assert(errs.exists(_.contains("the predicate `p` has rule heads in 2 files")),
        s"$label: a predicate assembled from two files must be declared: $errs")
  }

  test("a fact head beside a sibling file's imported one is refused as a capture") {
    // Imports are FILE-local and a declaration is SCOPE-wide, so one file's fact head
    // minting `d.p` would outrank the import the other file's fact head resolved
    // through, and retarget that unchanged fact. Refused before the mint, as for rules.
    //
    // BACK-OUT (the fact arm): this fixture does not reach the refusal — the import of
    // `lib.p` names nothing, no fact head having introduced it.
    val lib = "namespace zzC.lib\n  fact p(1)\nend"
    val importer = "namespace zzC.d\n  import zzC.lib.{p}\n  fact p(2)\nend"
    val local = "namespace zzC.d\n  fact p(3)\nend"
    val errs = refusal("lib.anthill" -> lib, "importer.anthill" -> importer, "local.anthill" -> local)
    val capture = errs.find(e => e.contains("would capture") && e.contains("`p`"))
      .getOrElse(fail(s"expected the capture refusal, got $errs"))
    assert(capture.contains("importer.anthill") && capture.contains("local.anthill"), capture)
    // THE CONTROL: without the sibling file the importer's fact contributes to `lib.p`.
    val kb = tryLoad("lib.anthill" -> lib, "importer.anthill" -> importer)
      .fold(e => fail(s"the one-file contribution must load: $e"), identity)
    val p = kb.tryResolveSymbol("zzC.lib.p").getOrElse(fail("`zzC.lib.p` must resolve"))
    assertEquals(kb.byFunctor(p).length, 2)
  }

  test("the repairs those refusals advise load, with fact heads") {
    // A refusal that advises a rewrite owes a row that RUNS the rewrite. All three pass
    // with the fact arm backed out, by design — a DECLARED predicate needs no mint — so
    // what they measure is the advice, not the arm.
    //
    // 845G7, FIRST REPAIR: one body-less `rule pick(…)` in the enclosing scope makes
    // every head a clause of it.
    val shared = loaded(nested("d1", "fact pick(1)", "fact pick(2)", outerDecl = "rule pick(?x)"))
    assert(!shared.hasQualifiedName("zzC.d1.Rec.pick"), "the sort introduces nothing")
    assertEquals((answers(shared, "zzC.d1.nsee"), answers(shared, "zzC.d1.Rec.rsee")), (2, 2),
      "one predicate, both facts its clauses")
    // 845G7, SECOND REPAIR: one declaration in EACH scope says they are separate.
    val apart = loaded(nested("d2", "fact pick(1)", "fact pick(2)",
      outerDecl = "rule pick(?x)", innerDecl = "rule pick(?x)"))
    assertEquals((answers(apart, "zzC.d2.nsee"), answers(apart, "zzC.d2.Rec.rsee")), (1, 1),
      "two predicates, each reading its own fact")
    // 061: the declaration, written once, in the scope that owns the predicate.
    val kb = tryLoad(
      "a.anthill" -> "namespace zzC.d3\n  rule p(?x)\n  fact p(1)\nend",
      "b.anthill" -> "namespace zzC.d3\n  fact p(2)\n  rule see(?x) :- p(?x)\nend")
      .fold(errs => fail(s"the advised declaration must load: $errs"), identity)
    assertEquals(answers(kb, "zzC.d3.see"), 2)
  }

  test("a fact head that already denotes references, and mints nothing") {
    // AN IMPORTED NAME. `X.freshp` exists only because a FACT head introduces it, so the
    // selective import of it is a deferred one — and `Side`'s own fact head must find
    // that import rather than mint `Side.freshp` and leave the import dead.
    //
    // BACK-OUT (the fact arm): this fixture does not LOAD — `import zzC.X.{freshp}`
    // names nothing, the fact that would have introduced it having minted nothing.
    val imported = loaded(
      """namespace zzC.X
        |  fact freshp(1)
        |  rule see(?x) :- freshp(?x)
        |end
        |namespace zzC.Side
        |  import zzC.X.{freshp}
        |  fact freshp(2)
        |end""".stripMargin)
    assertEquals(locals(imported, "zzC.Side"), Set.empty[String],
      "the importing scope mints nothing")
    assertEquals(answers(imported, "zzC.X.see"), 2, "both facts are clauses of `X.freshp`")

    // A QUALIFIED SPELLING. Passes with the fact arm backed out, by design; what it
    // guards is `introducedName`'s refusal of a dotted name on the FACT path. BACK-OUT
    // (`unqualified` answering `Right(name)`): `Side2` declares a local spelled
    // `zzC.Y.p` — and the count below does not move, the clause still landing on the
    // real `zzC.Y.p`, so the scope's own names are what is asserted.
    val qualified = loaded(
      """namespace zzC.Y
        |  rule p(1) :- true
        |  rule see(?x) :- p(?x)
        |end
        |namespace zzC.Side2
        |  fact zzC.Y.p(2)
        |end""".stripMargin)
    assertEquals(locals(qualified, "zzC.Side2"), Set.empty[String],
      "a qualified head introduces nothing where it is written")
    assertEquals(answers(qualified, "zzC.Y.see"), 2, "the fact is a clause of `zzC.Y.p`")
  }

  test("a fact head in a namespace does not join a top-level predicate of its name") {
    // `<global>` is not a party to a namespace's names (§5.3): a head written inside a
    // namespace declares there even when the top level writes the same name.
    //
    // BACK-OUT (the fact arm): neither name resolves — and, measured before the arm,
    // the counts were (2, 2).
    val kb = loaded(
      """fact gp(1)
        |rule gsee(?x) :- gp(?x)
        |namespace zzC.g
        |  fact gp(2)
        |  rule see(?x) :- gp(?x)
        |end""".stripMargin)
    assert(kb.hasQualifiedName("gp") && kb.hasQualifiedName("zzC.g.gp"))
    assertEquals((answers(kb, "gsee"), answers(kb, "zzC.g.see")), (1, 1))
  }
