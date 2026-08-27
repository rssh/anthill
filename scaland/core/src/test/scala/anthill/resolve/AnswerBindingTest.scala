package anthill.resolve

import anthill.kb.{BuiltinTag, KnowledgeBase}
import anthill.term.{Literal, Term, Var}

/** WI-20260827-2YHZ3 — the CROSS-IMPLEMENTATION control for rustland's answer-reader
  * defect.
  *
  * In rustland a rule-head variable bound by a rule-body BUILTIN read back as
  * UNBOUND: the fact fast-path binds through `bind_compressed` (which re-points the
  * answer link `?a -> Var(F)` at the value) while a builtin binds through
  * `bind_waking` on the `SuccessWithBindings` merge, which does not compress — so
  * both links stood and a one-hop `resolve_as_value` stopped on `Var(F)`. Rustland
  * now reads answers through `KnowledgeBase::answer_binding` (deep reification).
  *
  * SCALAND ROUTES THAT SAME MERGE THROUGH `bindCompressed` (`SearchStream`,
  * "case BuiltinResult.SuccessWithBindings"), whose doc says "Keeps the substitution
  * always flat" — so the one-hop `Substitution.resolve` here SHOULD land on the
  * value. These tests MEASURE that rather than assuming it: the ticket asked for the
  * measurement precisely because reading the call site is not evidence.
  *
  * The rule shape is rustland's `rule k(?x) :- ?x <=> 6` as closely as scaland can
  * write it. `unify` is not among scaland's `BuiltinTag`s, so the binding builtin
  * here is `qualified_name` — which is the same mechanism where it matters: it
  * answers `SuccessWithBindings`, and the var it binds is the rule's HEAD var.
  *
  * THE CLAIM IS BOUNDED, and the second test is what bounds it. `bindCompressed`
  * re-points answer links by scanning `this.bindings` ONLY, while `resolve` walks
  * the `parent` chain — so flatness is guaranteed for a link written at the same
  * level as the builtin's bind, and is NOT guaranteed for one held in a parent.
  * Test one drives the same-level shape; test two drives a link created one rule
  * deeper, which is where a parent-held link would show up. Reading the call site
  * alone would have missed that distinction entirely — it is why "scaland routes
  * through bindCompressed" is not, by itself, the answer the ticket asked for.
  *
  * WHAT WOULD FAIL: `?n` reading back as a `Term.Var` instead of the name string —
  * i.e. scaland having rustland's defect. Swap that `bindCompressed` for a plain
  * `bind` loop and both tests fail; that is the back-out these pin.
  */
class AnswerBindingTest extends munit.FunSuite:

  test("a head var bound by a rule-body builtin reads back as its value") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Sort")
    val domain = kb.symbols.scopeOf(kb.intern("test"))

    val qnSym = kb.intern("qualified_name")
    kb.registerBuiltinTag(qnSym, BuiltinTag.QualifiedName)
    val target = kb.makeNameTerm("probe.wi2yhz3.Target")

    // rule named(?n) :- qualified_name(Target, ?n)   — `?n` is the HEAD var, and
    // nothing but the builtin ever binds it.
    val namedSym = kb.intern("named")
    val vn = kb.freshVar(kb.intern("n"))
    val varN = kb.alloc(Term.Var(Var.Global(vn)))
    val head = kb.alloc(Term.Fn(namedSym, IArray(varN), IArray.empty))
    val body = kb.alloc(Term.Fn(qnSym, IArray(target, varN), IArray.empty))
    kb.assertRule(head, IndexedSeq(body), sort, domain)

    val va = kb.freshVar(kb.intern("a"))
    val varA = kb.alloc(Term.Var(Var.Global(va)))
    val query = kb.alloc(Term.Fn(namedSym, IArray(varA), IArray.empty))

    val solutions = SearchStream.resolve(kb, query).allSolutions(kb)
    assertEquals(solutions.length, 1, "the rule proves exactly one answer")
    assert(solutions(0).residual.isEmpty, "and it is definite, not a suspension")

    check(kb, solutions(0).subst.resolve(va).map(kb.getTerm))
  }

  test("the same binding survives a second rule layer, where the link is not local") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("Sort")
    val domain = kb.symbols.scopeOf(kb.intern("test"))

    val qnSym = kb.intern("qualified_name")
    kb.registerBuiltinTag(qnSym, BuiltinTag.QualifiedName)
    val target = kb.makeNameTerm("probe.wi2yhz3.Target")

    // inner(?n) :- qualified_name(Target, ?n)
    val innerSym = kb.intern("inner")
    val vn = kb.freshVar(kb.intern("n"))
    val varN = kb.alloc(Term.Var(Var.Global(vn)))
    kb.assertRule(
      kb.alloc(Term.Fn(innerSym, IArray(varN), IArray.empty)),
      IndexedSeq(kb.alloc(Term.Fn(qnSym, IArray(target, varN), IArray.empty))),
      sort,
      domain)

    // outer(?m) :- inner(?m)   — `?m`'s link is written one frame ABOVE the frame
    // whose builtin does the binding, which is the case `bindCompressed`'s
    // this-level-only scan does not cover by construction.
    val outerSym = kb.intern("outer")
    val vm = kb.freshVar(kb.intern("m"))
    val varM = kb.alloc(Term.Var(Var.Global(vm)))
    kb.assertRule(
      kb.alloc(Term.Fn(outerSym, IArray(varM), IArray.empty)),
      IndexedSeq(kb.alloc(Term.Fn(innerSym, IArray(varM), IArray.empty))),
      sort,
      domain)

    val va = kb.freshVar(kb.intern("a"))
    val varA = kb.alloc(Term.Var(Var.Global(va)))
    val query = kb.alloc(Term.Fn(outerSym, IArray(varA), IArray.empty))

    val solutions = SearchStream.resolve(kb, query).allSolutions(kb)
    assertEquals(solutions.length, 1, "the two-layer rule proves exactly one answer")
    assert(solutions(0).residual.isEmpty, "and it is definite, not a suspension")
    check(kb, solutions(0).subst.resolve(va).map(kb.getTerm))
  }

  private def check(kb: KnowledgeBase, bound: Option[Term]): Unit =
    bound match
      case Some(Term.Var(_)) =>
        fail(
          "scaland has rustland's WI-20260827-2YHZ3 defect: the head var reads back " +
            "UNBOUND because the answer link was never compressed. Read answers " +
            "deeply, as rustland's `answer_binding` now does.")
      case Some(Term.Const(Literal.StringLit(name))) =>
        assertEquals(name, "probe.wi2yhz3.Target")
      case other =>
        fail(s"the head var bound to an unexpected shape: $other")
