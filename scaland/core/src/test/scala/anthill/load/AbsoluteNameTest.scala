package anthill.load

import anthill.codegen.scala.StdlibFixture
import anthill.intern.{ResolveResult, TermSymbol}
import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.parse.Parser
import anthill.term.{Term, Var}
import anthill.resolve.SearchStream

/** WI-20261008-T290W — THE ABSOLUTE SPELLING `..a.b.c` (kernel §2.3, §8.6): a name that
  * is looked up from the root, by the qualified name it writes, whatever is in scope
  * where it is written.
  *
  * scaland's parser had no such spelling — `..x` was a parse error in every position —
  * so a program rustland loads did not parse here, and the one thing only the marker can
  * say (the top-level `top` from inside a scope that declares its own `top`) had no
  * spelling at all.
  *
  * THE LOADER HAD NO READING FOR IT EITHER, AND THAT WAS ALREADY BITING
  * (WI-20260902-373AW): the Pratt table scaland shares with rustland mints fourteen
  * operators with their address, so `not(…)` loaded under a bare symbol spelled
  * `..anthill.kernel.not` and was not NAF. One rung serves both — a written path and a
  * minted address are one kind of name — which is why the operator row is in this file.
  *
  * THE MARKER RIDES THE HEAD SEGMENT'S TEXT, as in rustland: `Tokens.absoluteHeadToken`
  * writes it for a path in source, and `anthill.intern.absolutePathTarget` is its one
  * reader, asked by `Loader.lookupWritten` — the one rung order every written name
  * resolves in — and by the emitter's `TypeScope.placePath` (`BootstrapTest`, `an
  * absolute written path places by the package it spells, from the root`).
  *
  * ── WHICH ROWS FAIL WHEN WHAT IS BACKED OUT — each applied and run over the whole
  *    core suite (628 rows), so each count is exhaustive over it ──
  *
  *  * **THE SPELLING** — `refName` reading `name` alone. **15 ROWS FAIL**: the eleven
  *    here that write the spelling, `HeadIntroductionCensusTest`'s two qualified rows,
  *    `DottedParenLessCitationTest`'s negand row and `BootstrapTest`'s absolute row.
  *    Three here pass either way BY DESIGN: `a declaration cannot be spelled absolutely`
  *    is the refusal the spelling must not lift, and the operator row and the relative
  *    `Ref` row write no `..`.
  *  * **THE ROOT RUNG** — `lookupWritten` without its `absolutePathTarget` arm. **148
  *    ROWS FAIL**, because the stdlib stops loading: its own `not(…)` and `=` goals are
  *    addresses that then name nothing, and the loud miss says so. Before the loud miss
  *    existed this was the silent state the ticket above describes.
  *  * **THE MARKER AS A NO-OP** — the arm stripping the marker and taking the unmarked
  *    ladder. **2 ROWS FAIL**: `nothing in scope shadows an absolute name` (the
  *    namespace's own `top` answers) and `an absolute path that names nothing is
  *    refused`, on its `..q` half (the scope's `q` answers).
  *  * **THE LOUD MISS** — `resolveName` interning a marked miss in silence. **2 ROWS
  *    FAIL**: `an absolute path that names nothing is refused`, and the operator row on
  *    its last arm.
  *  * **`Ref(…)` READING ITS LAST SEGMENT** — `refTerm` allocating `Term.Ref(n.last)`.
  *    **3 ROWS FAIL**: `Ref of an absolute path is the symbol the path names`, the miss
  *    row on its `Ref` line, and the relative `Ref` row, whose pair comes apart.
  *  * **THE PROOF TARGET** — `loadProof` asking nothing of a marked target. **1 ROW
  *    FAILS**: `an absolute proof target that names nothing is refused`.
  *  * **THE EFFECTS ANCHOR** — the exemption comparing the written text alone. **1 ROW
  *    FAILS**: `the effects anchor is one sort in both spellings`.
  *
  * The NEGAND DESCENT the rung made due (`not(ns.flag)` negates the predicate, not a
  * `field_access` chain) is driven and backed out at `DottedParenLessCitationTest`.
  */
class AbsoluteNameTest extends munit.FunSuite:

  private def loaded(src: String)(using munit.Location): KnowledgeBase =
    LoadFixture.loaded(src, "absolute.anthill")

  private def refusal(src: String)(using munit.Location): Seq[String] =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, IndexedSeq(LoadFixture.parsed(src, "absolute.anthill")))
    if errs.isEmpty then fail(s"expected a load refusal, the program loaded:\n$src")
    errs.toSeq.map(_.render)

  /** Solutions of `<qn>(?x)` — the goal built on the SYMBOL the name resolves to, so a
    * clause that landed on another symbol is not counted. */
  private def answers(kb: KnowledgeBase, qn: String)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve — fixture drift"))
    val v = kb.alloc(Term.Var(Var.Global(kb.freshVar(kb.intern("x")))))
    SearchStream.resolve(kb, kb.alloc(Term.Fn(sym, IArray(v), IArray.empty)))
      .allSolutions(kb).length

  private def parses(src: String): Boolean = Parser.parse(src, "absolute.anthill").isRight

  // ── THE ACCEPTANCE ROW ──────────────────────────────────────────────────────

  test("a goal written in another namespace answers from the root") {
    // THE CONTROL IS THE SAME GOAL SPELLED RELATIVELY: nothing shadows `zzAbs` here, so
    // the two spellings name one predicate and must count alike.
    val kb = loaded(
      """namespace zzAbs.n
        |  fact p(1)
        |  fact p(2)
        |end
        |namespace zzAbs.m
        |  rule viaAbs(?x) :- ..zzAbs.n.p(?x)
        |  rule viaRel(?x) :- zzAbs.n.p(?x)
        |end""".stripMargin)
    assertEquals((answers(kb, "zzAbs.m.viaAbs"), answers(kb, "zzAbs.m.viaRel")), (2, 2))
  }

  test("a nullary absolute goal answers in every spelling") {
    // A paren-less dotted citation folds into a minted `field_access` chain and a
    // paren-less single segment is a bare `Term.Ident`: four shapes, and the marker
    // rides the head segment of each.
    val kb = loaded(
      """fact zzAbsBase(1)
        |rule zzAbsTop :- zzAbsBase(1)
        |namespace zzAbs.nu
        |  rule tgt :- zzAbsBase(1)
        |end
        |namespace zzAbs.nv
        |  rule dBare(1)  :- ..zzAbs.nu.tgt
        |  rule dParen(1) :- ..zzAbs.nu.tgt()
        |  rule sBare(1)  :- ..zzAbsTop
        |  rule sParen(1) :- ..zzAbsTop()
        |end""".stripMargin)
    for q <- Seq("dBare", "dParen", "sBare", "sParen") do
      assertEquals(answers(kb, s"zzAbs.nv.$q"), 1, s"$q: the predicate holds")
  }

  // ── WHAT ONLY THE MARKER CAN SAY ────────────────────────────────────────────

  test("nothing in scope shadows an absolute name") {
    // THE TWO SPELLINGS MUST DIFFER HERE, which is what makes this the row about the
    // marker and not about dotted names: the namespace declares its own `top`, the bare
    // name means that one, and `..top` is the only spelling of the top-level one.
    val kb = loaded(
      """fact top(1)
        |namespace zzAbs.s
        |  fact top(2)
        |  fact top(3)
        |  rule bare(?x) :- top(?x)
        |  rule abs(?x)  :- ..top(?x)
        |end""".stripMargin)
    assertEquals((answers(kb, "zzAbs.s.bare"), answers(kb, "zzAbs.s.abs")), (2, 1),
      "bare `top` is the namespace's own; `..top` is the root's")
  }

  test("an absolute head is a reference: a clause of the predicate it names") {
    // A qualified head references and never introduces (§8.3), and the marked spelling
    // is a qualified one. THE CONTROL is the unmarked head beside it.
    val kb = loaded(
      """namespace zzAbs.h
        |  rule p(1) :- true
        |  rule see(?x) :- p(?x)
        |end
        |namespace zzAbs.side
        |  fact ..zzAbs.h.p(2)
        |  rule ..zzAbs.h.p(3) :- true
        |  fact zzAbs.h.p(4)
        |end""".stripMargin)
    assertEquals(answers(kb, "zzAbs.h.see"), 4, "all four clauses are `zzAbs.h.p`'s")
    val side = kb.tryResolveSymbol("zzAbs.side").getOrElse(fail("`zzAbs.side` must resolve"))
    assertEquals(
      kb.symbols.scope(kb.symbols.scopeOf(side)).fold(Set.empty[String])(_.locals.keySet.toSet),
      Set.empty[String], "an absolute head introduces nothing where it is written")
  }

  // ── A MISS ──────────────────────────────────────────────────────────────────

  test("an absolute path that names nothing is refused") {
    // An unmarked name nothing answers is a predicate the program introduces by using
    // it. A marked one names a symbol by its own qualified name, so it has no such
    // reading — rustland says `unresolved name '..nosuchxyz' in scope 'n'`.
    for (label, line, name) <- Seq(
        ("applied goal", "rule r(1) :- ..zzAbsNope.p(1)", "..zzAbsNope.p"),
        ("paren-less goal", "rule r(1) :- ..zzAbsNope.p", "..zzAbsNope.p"),
        ("one segment", "rule r(1) :- ..zzAbsNope", "..zzAbsNope"),
        ("head with a body", "rule ..zzAbsNope.p(1) :- true", "..zzAbsNope.p"),
        ("fact head", "fact ..zzAbsNope.p(1)", "..zzAbsNope.p"),
        ("argument", "fact holds(..zzAbsNope(1))", "..zzAbsNope"),
        // A DATA slot keeps a paren-less path as a chain, whose HEAD is the marked name.
        ("argument chain", "fact holds(..zzAbsNope.p)", "..zzAbsNope"),
        ("Ref", "fact holds(Ref(..zzAbsNope.p))", "..zzAbsNope.p")) do
      val errs = refusal(s"namespace zzAbs.miss\n  $line\nend")
      assert(errs.exists(_.contains(s"unresolved name '$name' in scope 'zzAbs.miss'")),
        s"$label: `$line` must be refused by the name it wrote, got $errs")
    // IT DOES NOT FALL BACK TO THE SCOPE: `q` exists, in this namespace and nowhere at
    // the root, so `..q` names nothing. The control is the bare name, which answers.
    val errs = refusal("namespace zzAbs.r\n  fact q(1)\n  rule abs(?x) :- ..q(?x)\nend")
    assert(errs.exists(_.contains("unresolved name '..q'")), s"$errs")
    val kb = loaded("namespace zzAbs.r\n  fact q(1)\n  rule bare(?x) :- q(?x)\nend")
    assertEquals(answers(kb, "zzAbs.r.bare"), 1)
    // THE CONTROL FOR THE MARKER: the same misses, unmarked, load.
    loaded("namespace zzAbs.miss\n  rule r(1) :- zzAbsNope.p(1)\n  fact holds(zzAbsNope(1))\nend")
  }

  test("an absolute proof target that names nothing is refused") {
    // scaland records a proof's target AS WRITTEN and discharges nothing, so an unmarked
    // target is not resolved at all — the control, which loads naming nothing. A marked
    // one claims a symbol by its own qualified name, and is asked whether it has one.
    def proof(target: String) =
      s"namespace zzAbs.pf\n  rule law(1) :- true\n  proof $target by auto end\nend"
    val errs = refusal(proof("..zzAbs.pf.nolaw"))
    assert(errs.exists(_.contains("unresolved name '..zzAbs.pf.nolaw' in scope 'zzAbs.pf'")),
      s"$errs")
    loaded(proof("..zzAbs.pf.law"))
    loaded(proof("nolaw"))
  }

  test("the effects anchor is one sort in both spellings") {
    // `anthill.prelude.EffectsRuntime` is the `effects E = ?` desugar's anchor, and a
    // provision of it is exempt from the spec-scope link every other provision over the
    // sort's own parameters gets (WI-703). The exemption is by NAME, so it is asked of
    // both spellings of that name. Read off the sort's own scope: the link is one more
    // parent. THE CONTROL is a spec that is not the anchor, which does link.
    def parents(clause: String): Int =
      val kb = StdlibFixture.kbWith(LoadFixture.parsed(
        s"namespace zzAbs.fx\n  sort S\n    sort E = ?\n    $clause\n  end\nend",
        "anchor.anthill"))
      val s = kb.tryResolveSymbol("zzAbs.fx.S").getOrElse(fail("`zzAbs.fx.S` must resolve"))
      kb.symbols.scope(kb.symbols.scopeOf(s)).fold(fail("the sort has a scope"))(_.parents.length)
    val unlinked = parents("")
    assertEquals(parents("provides anthill.prelude.EffectsRuntime[Effects = E]"), unlinked)
    assertEquals(parents("provides ..anthill.prelude.EffectsRuntime[Effects = E]"), unlinked)
    assertEquals(parents("provides ..anthill.prelude.Eq[T = E]"), unlinked + 1,
      "CONTROL: a provision that is not the anchor links its spec's scope")
  }

  // ── THE OTHER REFERENCE POSITIONS ───────────────────────────────────────────

  test("Ref of an absolute path is the symbol the path names") {
    // THE STORED TERM, not a match count: both sides of a match would agree on a wrong
    // symbol too. `Ref(a.b.c)` is the control — one path, one symbol, either spelling.
    val kb = loaded(
      """namespace zzAbs.rf
        |  fact p(1)
        |end
        |namespace zzAbs.rg
        |  fact citesAbs(Ref(..zzAbs.rf.p))
        |  fact citesRel(Ref(zzAbs.rf.p))
        |end""".stripMargin)
    for holder <- Seq("zzAbs.rg.citesAbs", "zzAbs.rg.citesRel") do
      val sym = kb.tryResolveSymbol(holder).getOrElse(fail(s"`$holder` must resolve"))
      val arg = kb.getTerm(kb.factTerm(kb.byFunctor(sym).head)) match
        case fn: Term.Fn => kb.getTerm(fn.posArgs(0))
        case other       => fail(s"`$holder`'s fact is not an application: $other")
      arg match
        case Term.Ref(target) => assertEquals(kb.qualifiedNameOf(target), "zzAbs.rf.p", holder)
        case other            => fail(s"`$holder` holds $other, not a `Ref`")
  }

  test("a RELATIVE path in Ref resolves as the call spelling of it does — not yet") {
    // WHAT `Ref(…)` GAVE UP when it stopped reading its last segment. `Ref(Rec.E)` used
    // to be `Ref(E)`, which the sort's variant exposure happened to resolve; it is the
    // path `Rec.E` now, and scaland has no relative reading of a dotted path
    // (WI-20261008-JRV1T: the head is not resolved by scope). So it resolves to nothing,
    // EXACTLY AS THE CALL `Rec.E(…)` DOES — and that pair is the assertion: one path, one
    // answer in both carriers, so JRV1T moves them together. The old reading agreed with
    // nothing: `Ref(other.ns.p)` took whatever `p` was in scope.
    //
    // THE CONTROLS resolve: the bare leaf, by exposure, and the fully qualified path.
    val kb = loaded(
      """namespace zzAbs.rr
        |  sort Rec
        |    entity E(v: Int64)
        |  end
        |  fact refRel(Ref(Rec.E))
        |  fact callRel(Rec.E(v: 1))
        |  fact refLeaf(Ref(E))
        |  fact refFull(Ref(zzAbs.rr.Rec.E))
        |end""".stripMargin)
    def held(holder: String): Term =
      val sym = kb.tryResolveSymbol(s"zzAbs.rr.$holder").getOrElse(fail(s"`$holder` must resolve"))
      kb.getTerm(kb.factTerm(kb.byFunctor(sym).head)) match
        case fn: Term.Fn => kb.getTerm(fn.posArgs(0))
        case other       => fail(s"`$holder`'s fact is not an application: $other")
    def named(t: Term): (String, Boolean) = t match
      case Term.Ref(sym) => (kb.qualifiedNameOf(sym), kb.symbols.isResolved(sym))
      case fn: Term.Fn   => (kb.qualifiedNameOf(fn.functor), kb.symbols.isResolved(fn.functor))
      case other         => fail(s"unexpected carrier $other")
    assertEquals(named(held("refRel")), named(held("callRel")),
      "`Ref(Rec.E)` and `Rec.E(…)` name one path and must resolve alike")
    assertEquals(named(held("refRel")), ("Rec.E", false),
      "GAP (WI-20261008-JRV1T): logic says `zzAbs.rr.Rec.E` — the head `Rec` is in scope")
    assertEquals(named(held("refLeaf")), ("zzAbs.rr.Rec.E", true))
    assertEquals(named(held("refFull")), ("zzAbs.rr.Rec.E", true))
  }

  test("a data slot holds one term for the marked and the unmarked path") {
    // A paren-less path in a DATA slot stays a `field_access` chain (a fact's slot and
    // the pattern that searches for it must build one term), and the marker rides its
    // head: `..zzAbs` is the root namespace `zzAbs`, which is what the unmarked head
    // resolves to here. So the fact written one way is found by the pattern written
    // the other. THE CONTROL is a pattern naming another member, which is not found.
    val kb = loaded(
      """namespace zzAbs.d
        |  rule tgt :- true
        |  rule other :- true
        |end
        |fact holdsAbs(..zzAbs.d.tgt)
        |rule viaRel(1) :- holdsAbs(zzAbs.d.tgt)
        |rule viaAbs(1) :- holdsAbs(..zzAbs.d.tgt)
        |rule viaOther(1) :- holdsAbs(..zzAbs.d.other)""".stripMargin)
    assertEquals(
      (answers(kb, "viaRel"), answers(kb, "viaAbs"), answers(kb, "viaOther")), (1, 1, 0))
  }

  test("a requires clause names its spec absolutely") {
    // The TYPE position, through the one reader scaland's loader has of a written type
    // name: a `requires` links the spec's scope, so the spec's member is in scope for
    // the sort. THE CONTROL is the unmarked clause; the miss is refused by name.
    def program(clause: String) =
      s"""namespace zzAbs.lib
         |  sort Spec
         |    operation specOp(x: Int64) -> Int64
         |  end
         |end
         |namespace zzAbs.use
         |  sort Holder
         |    $clause
         |  end
         |end""".stripMargin
    for clause <- Seq("requires ..zzAbs.lib.Spec", "requires zzAbs.lib.Spec") do
      val kb = loaded(program(clause))
      val holder = kb.tryResolveSymbol("zzAbs.use.Holder").getOrElse(fail("fixture drift"))
      kb.symbols.resolveInScope("specOp", kb.symbols.scopeOf(holder)) match
        case ResolveResult.Found(sym) =>
          assertEquals(kb.qualifiedNameOf(sym), "zzAbs.lib.Spec.specOp", clause)
        case other => fail(s"`$clause`: `specOp` must be in scope for the sort, got $other")
    val errs = refusal(program("requires ..zzAbs.nolib.Spec"))
    assert(errs.exists(_.contains("unresolved name '..zzAbs.nolib.Spec'")), s"$errs")
  }

  // ── THE ADDRESSES THE OPERATORS ARE MINTED WITH ─────────────────────────────

  test("the address an operator is minted with resolves, or is refused") {
    // WI-20260902-373AW's program. The Pratt table scaland shares with rustland mints
    // fourteen operators with their ADDRESS (`not` is `..anthill.kernel.not`, `+` is
    // `..anthill.prelude.Additive.add`), and before the root rung every one landed on a
    // bare symbol of that spelling: the written `not` was not NAF, on a stdlib that
    // loaded with zero errors.
    val kb = StdlibFixture.kbWith(LoadFixture.parsed(
      """fact bz(1)
        |rule pz(?n) :- bz(?n)
        |rule emptyz(?n) :- bz(9)
        |rule nafEmpty(1)  :- not(emptyz(1))
        |rule nafFull(1)   :- not(pz(1))
        |rule bangEmpty(1) :- !emptyz(1)
        |rule orFirst(1)   :- pz(1) or emptyz(1)
        |rule barFirst(1)  :- pz(1) | emptyz(1)
        |rule andBoth(1)   :- pz(1) and pz(1)
        |rule ampBoth(1)   :- pz(1) & pz(1)
        |rule arith(1)     :- 1 + 2 = 3, 4 - 1 > 2 * 1, 6 / 2 >= 7 mod 4, 1 != 2, 1 < 2, 1 <= 2
        |rule negated(1)   :- -bz(1) = 0
        |rule commaCtl(1)  :- pz(1), bz(1)""".stripMargin, "ops.anthill"))
    // `not` IS NAF: 1 over an empty predicate, 0 over one that holds. THE CONTROL is the
    // comma conjunction — without it a change that broke goal resolution outright would
    // pass the two 0 rows.
    assertEquals(
      (answers(kb, "nafEmpty"), answers(kb, "nafFull"), answers(kb, "bangEmpty"), answers(kb, "commaCtl")),
      (1, 0, 1, 1))
    // THE CENSUS — the assertion a fifteenth address cannot slip past: after a clean
    // load of the stdlib and of every operator above in goal position, NO symbol is
    // named `..…`. A marked name in the table is an address that resolved to nothing
    // and was interned under the text written; before the rung there were fourteen.
    val marked = (0 until kb.symbols.size)
      .map(i => kb.symbols.name(TermSymbol.fromRaw(i))).filter(_.startsWith(".."))
    assertEquals(marked, IndexedSeq.empty[String])
    // GAP, pinned at what scaland gives: `or` / `and` RESOLVE now and still answer
    // nothing, because they are kernel rules over `push_choice` / `push_and`, resolver
    // primitives scaland does not have. Logic says 1 for all four; 373AW owns them.
    for q <- Seq("orFirst", "barFirst", "andBoth", "ampBoth") do
      assertEquals(answers(kb, q), 0, s"GAP (WI-20260902-373AW): $q")
    // AND THE LOUD HALF: in a KB that does not hold the library, the address names
    // nothing and says so, by the operator's own position. It used to load.
    val errs = refusal("rule r(1) :- 1 + 2 = 3")
    assert(errs.exists(_.contains("unresolved name '..anthill.prelude.Additive.add'")), s"$errs")
  }

  // ── THE GRAMMAR ─────────────────────────────────────────────────────────────

  test("every reference position parses the absolute spelling") {
    // The positions `grammar.js` gives `absolute_name` to, less `describe`, which this
    // parser does not read at all. Each beside its unmarked twin, so a row that fails
    // for a reason other than the marker shows as BOTH failing.
    def both(template: String => String)(using munit.Location): Unit =
      for path <- Seq("zzAbs.n.T", "..zzAbs.n.T", "..T") do
        val src = template(path)
        assert(parses(src), s"must parse:\n$src")
    both(p => s"namespace a\n  rule r(1) :- $p(1)\nend")                  // call head
    both(p => s"namespace a\n  rule r(1) :- $p\nend")                     // bare atom
    both(p => s"namespace a\n  rule r(1) :- q($p[T = Int64])\nend")       // application
    both(p => s"namespace a\n  rule r(1) :- q($p[T = Int64](1))\nend")    // typed call
    both(p => s"namespace a\n  fact q(Ref($p))\nend")                     // Ref
    both(p => s"namespace a\n  sort S\n    entity e(x: $p)\n  end\nend")  // simple type
    both(p => s"namespace a\n  sort S\n    entity e(x: $p[V = Int64])\n  end\nend")
    both(p => s"namespace a\n  sort S\n    entity e(x: List[T = $p])\n  end\nend")
    both(p => s"namespace a\n  sort S\n    requires $p\n  end\nend")
    both(p => s"namespace a\n  proof $p by auto end\nend")                // proof target
    both(p => s"namespace a\n  proof zz by z3 query \"q\" mapping { $p -> \"f\" } end\nend")
    both(p => s"namespace a\n  operation f(x: Int64) -> Int64 = proof $p by auto end x\nend")
  }

  test("a declaration cannot be spelled absolutely") {
    // `..` is admitted in REFERENCE positions only (§2.3): a declaration states where
    // it is, and `namespace ..a.b` would be a namespace whose first segment is
    // punctuation. PASSES WITH THE SPELLING BACKED OUT, by design — these are the
    // refusals admitting the spelling must not lift.
    for src <- Seq(
        "namespace ..a.b\nend",
        "namespace a\n  sort ..S\n  end\nend",
        "namespace a\n  sort S\n    entity ..e(x: Int64)\n  end\nend",
        "namespace a\n  operation ..f(x: Int64) -> Int64\nend",
        "namespace a\n  import ..b.{c}\nend",
        "namespace a\n  rule ..lbl: p(1) :- q(1)\nend",
        // The marker and its head segment are ONE token.
        "namespace a\n  rule r(1) :- .. b.p(1)\nend",
        "namespace a\n  rule r(1) :- ..\nend",
        // A binding's parameter NAME is not a reference.
        "namespace a\n  sort S\n    entity e(x: List[..T = Int64])\n  end\nend") do
      assert(!parses(src), s"must NOT parse:\n$src")
  }
