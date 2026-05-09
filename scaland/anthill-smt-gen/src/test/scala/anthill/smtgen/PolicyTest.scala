package anthill.smtgen

class PolicyTest extends munit.FunSuite:

  test("no_explicit_policy_no_cites_inlines") {
    val kb = Common.loadKbWith("""
      namespace test.policy.inline
        export foo
        rule foo(?x) :- gte(?x, 0)
      end
    """)
    assertEquals(
      Policy.policyFor(kb, "test.policy.inline.foo", "smt-z3", Set.empty),
      PredicatePolicy.Inline,
      "predicate with no explicit policy and no cite-side use must default to Inline"
    )
  }

  test("no_explicit_policy_with_cite_lifts_axiom") {
    // Under proposal 032 the head IS the rule's claim; the rust
    // test's `:- ... -:` dual-arrow shape isn't valid scaland
    // syntax. policyFor's LiftedAxiom default fires purely on the
    // citedPredicates set, independent of the rule's body shape.
    val kb = Common.loadKbWith("""
      namespace test.policy.lifted
        export foo
        rule foo(?x) :- gte(?x, 0)
      end
    """)
    assertEquals(
      Policy.policyFor(kb, "test.policy.lifted.foo", "smt-z3",
        Set("test.policy.lifted.foo")),
      PredicatePolicy.LiftedAxiom,
      "predicate cited via `using` must default to LiftedAxiom"
    )
  }

  test("explicit_policy_overrides_default") {
    val kb = Common.loadKbWith("""
      namespace test.policy.explicit
        import anthill.realization.policy.{TranslationPolicy, DeclareFun}
        export bar

        rule bar(?x) :- gte(?x, 0)

        fact TranslationPolicy(
          predicate: "test.policy.explicit.bar",
          backend: "smt-z3",
          policy: DeclareFun
        )
      end
    """)
    assert(
      kb.tryResolveSymbol("anthill.realization.policy.TranslationPolicy").isDefined,
      "TranslationPolicy schema must be loaded from stdlib"
    )
    assertEquals(
      Policy.policyFor(kb, "test.policy.explicit.bar", "smt-z3", Set.empty),
      PredicatePolicy.DeclareFun,
      "explicit TranslationPolicy fact must override the Inline default"
    )
  }
