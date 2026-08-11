package anthill.kb

import anthill.kb.Facts.OptionArg
import anthill.term.{Literal, Term}

/** WI-1053 — the fact-reading primitives (`bodylessFacts`, `getNamedArg`,
  * `getNamedStringArg`, `optionArg`) have ONE home in `anthill.kb`, where both
  * `anthill-smt-gen` and `anthill-scala-gen` can reach them.
  *
  * CONTROL. These cases DRIVE the shared helpers over a loaded KB — they fail if
  * [[Facts]] misreads facts: stop skipping bodied clauses and the bodied-clause case
  * fails; let [[Facts.getNamedStringArg]] accept a non-literal slot and the
  * malformed-record case fails; reorder the walk (the recorded landmine: discrim /
  * solution order ≠ source order) and the first-match case fails; drop any `optionArg`
  * spelling arm and its case fails. A call site quietly REVERTED to a faithful private
  * copy passes this file by design — behaviour is identical by construction. What holds
  * the call sites to the shared implementation is behavioural coverage THROUGH them
  * (`PolicyTest.explicit_policy_overrides_default`, BootstrapTest's `languageVersion` /
  * `buildSbt` cases, TacticEmitTest) plus WI-1053's acceptance sweep that no
  * `resolveSym(sym) == key` loop exists outside `Facts.scala`.
  */
class FactsTest extends munit.FunSuite:

  private def loaded(src: String): KnowledgeBase = LoadFixture.loaded(src, "<facts>")

  // A sort-scoped entity resolves at `test.facts.Mapping.M` (measured; scaland scopes
  // the entity under its sort). The `nested` fact's `language` slot holds an
  // APPLICATION, not a string literal — the malformed-record shape the string read
  // must refuse. The two `dup` facts differ only in `profile`, to pin match order.
  private val src =
    """namespace test.facts
      |  sort Mapping
      |    entity M(language: String, profile: String)
      |  end
      |  fact M(language: "scala", profile: "std")
      |  fact M(language: "rust", profile: "std")
      |  fact M(language: M(language: "x", profile: "y"), profile: "nested")
      |  fact M(language: "dup", profile: "first")
      |  fact M(language: "dup", profile: "second")
      |  rule M(language: "derived", profile: ?p) :- M(language: "scala", profile: ?p)
      |end""".stripMargin

  private val entityQn = "test.facts.Mapping.M"

  test("bodylessFacts + getNamedStringArg resolve a real fact and read its fields") {
    val kb = loaded(src)
    val heads = Facts.bodylessFacts(kb, entityQn).toVector
    val scalaFact = heads
      .find(fn => Facts.getNamedStringArg(kb, fn, "language").contains("scala"))
      .getOrElse(fail(s"no M fact with language \"scala\" among ${heads.length} heads"))
    assertEquals(
      Facts.getNamedStringArg(kb, scalaFact, "profile"), Some("std"),
      "the sibling field of the located fact must read back")
    assertEquals(
      Facts.getNamedArg(kb, scalaFact, "no_such_field"), None,
      "an absent field is None, not a mis-keyed hit")
  }

  test("a BODIED clause under the same functor is not a fact") {
    val kb = loaded(src)
    val languages = Facts.bodylessFacts(kb, entityQn)
      .flatMap(fn => Facts.getNamedStringArg(kb, fn, "language")).toSet
    assertEquals(languages, Set("scala", "rust", "dup"),
      "the rule head (language: \"derived\") must NOT surface in the walk — its body " +
      "is a condition this reader cannot discharge")
  }

  test("a non-literal slot is refused by the string read, not misread") {
    val kb = loaded(src)
    val malformed = Facts.bodylessFacts(kb, entityQn)
      .find(fn => Facts.getNamedStringArg(kb, fn, "profile").contains("nested"))
      .getOrElse(fail("the malformed fact must still be walked — it IS body-less"))
    assert(Facts.getNamedArg(kb, malformed, "language").isDefined,
      "the slot is present as a term")
    assertEquals(Facts.getNamedStringArg(kb, malformed, "language"), None,
      "a non-literal slot must read as None — the refusal Policy and ScalaProfile " +
      "lean on to match only well-formed records")
  }

  test("the FIRST asserted match wins — the walk is assertion-ordered") {
    val kb = loaded(src)
    val winner = Facts.bodylessFacts(kb, entityQn)
      .find(fn => Facts.getNamedStringArg(kb, fn, "language").contains("dup"))
      .flatMap(fn => Facts.getNamedStringArg(kb, fn, "profile"))
    assertEquals(winner, Some("first"),
      "Policy promises 'the first found policy' and findMapping takes the first " +
      "matching LanguageMapping; both ride on this order")
  }

  test("bodylessFacts of an unknown functor is empty, not an error") {
    val kb = loaded(src)
    assertEquals(Facts.bodylessFacts(kb, "test.facts.NoSuch").toVector, Vector.empty)
  }

  test("optionArg decodes every spelling that occurs in the wild") {
    // Terms built directly against the store — optionArg keys on the SHORT name, so no
    // stdlib `Option` is needed to drive it.
    val kb = loaded(src)
    val someSym = kb.intern("some")
    val noneSym = kb.intern("none")
    val inner = kb.alloc(Term.Const(Literal.StringLit("x")))

    assertEquals(
      Facts.optionArg(kb, kb.alloc(Term.Fn(someSym, IArray(inner), IArray.empty))),
      OptionArg.Wrapped(inner), "positional some(x)")
    assertEquals(
      Facts.optionArg(kb,
        kb.alloc(Term.Fn(someSym, IArray.empty, IArray((kb.intern("value"), inner))))),
      OptionArg.Wrapped(inner),
      "named some(value: x) — rustland's unwrap_option reads whichever slot is " +
      "filled, and this spelling occurs in workitems.anthill")
    assertEquals(
      Facts.optionArg(kb, kb.alloc(Term.Fn(noneSym, IArray.empty, IArray.empty))),
      OptionArg.Absent, "nullary application none()")
    assertEquals(
      Facts.optionArg(kb, kb.alloc(Term.Ident(noneSym))),
      OptionArg.Absent, "bare none as Ident")
    assertEquals(
      Facts.optionArg(kb, kb.alloc(Term.Ref(noneSym))),
      OptionArg.Absent, "bare none as Ref")
    assertEquals(
      Facts.optionArg(kb, inner),
      OptionArg.NotAnOption,
      "a non-option term must NOT fold into Absent — that is what keeps a malformed " +
      "field from reading as a deliberate none")
  }
