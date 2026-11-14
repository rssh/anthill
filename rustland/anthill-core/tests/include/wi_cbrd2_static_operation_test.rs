//! A STATIC OPERATION WITH A BODY IS THE SPEC'S OWN (WI-20261105-CBRD2, decided with the user
//! 2026-11-14). A static operation's signature names no carrier — no parameter, result or effect
//! at the spec or one of its parameters — so nothing at a call of it says which provider is
//! meant. With a body it is the spec's: a provider's own member of it, a `provides` binding of
//! it, and a member of a spec that provides it at a parameter are each refused at load, at the
//! member's line. A value each provider supplies is a static operation with no body, which the
//! call's bracket chooses.
//!
//! A call of a static operation with a body owes no instance where its spec has no body-less
//! member and no `requires`, in an operation body at a type parameter too. Where the spec has a
//! body-less member, the body may call it, and a call at a type parameter owes the instance as a
//! call of that member does, at whichever parameter of the spec the call binds to one.
//!
//! ## What fails with each part backed out
//!
//! Measured with temporary switches in one build, then removed. The control is every switch
//! unset: every row passes.
//!
//! * the refusal of a static member with a body (`check_override_refinement` and
//!   `check_instance_fact_op_signatures` not raising it):
//!   [`each_supply_route_of_a_static_operation_with_a_body_is_refused`], H20YY's
//!   `a_providers_override_of_a_static_operation_is_refused`, WI-1042's
//!   `a_non_parametric_provided_sorts_member_is_refused`, three rows of NR6FJ, one of YM8HD and
//!   three of ZAWX9, whose providers' static members are now refused;
//! * a static operation that owes no instance read as owing one (`static_call_owes_no_instance`
//!   answering `false`): [`a_static_default_at_a_type_parameter_runs_its_body`],
//!   [`a_static_default_runs_where_the_bracket_leaves_a_parameter_open`], the `Desc.dflt()`
//!   half of CBRD2's `a_defaulted_member_at_an_open_carrier_is_refused`, and NR6FJ's
//!   `with_no_slot_declared_the_default_still_runs`;
//! * a call of a defaulted member at a carrier that provides nothing read as owing the instance
//!   only where the spec has a body-less member, as before (`defaulted_call_owes_an_instance`):
//!   [`a_carrier_taking_default_at_a_carrier_that_provides_nothing_is_refused`], WI-1010's
//!   `a_call_at_an_abstract_type_with_no_provision_is_refused` and WI-1012's
//!   `a_tie_behind_an_abstract_type_is_no_tie`;
//! * the defaulted block of `check_apply_call` entered for a static operation that owes no
//!   instance (its filter off): [`a_static_default_at_a_type_parameter_runs_its_body`],
//!   [`a_static_default_runs_where_the_bracket_leaves_a_parameter_open`] and the `Desc.dflt()`
//!   half of CBRD2's `a_defaulted_member_at_an_open_carrier_is_refused`;
//! * the receiver-less refusal asked of it (`receiver_less_call_names_no_instance`'s exemption
//!   off): NR6FJ's `with_no_slot_declared_the_default_still_runs`;
//! * the block's at-a-parameter read taking the carrier parameter alone (`spec_carrier_param`,
//!   as before):
//!   [`a_static_default_over_a_body_less_sibling_owes_the_instance`] and
//!   [`it_owes_it_at_whichever_parameter_the_call_binds`], which loaded clean and left the call
//!   unanswered (a residual) when it ran; and the same read taken at the parameters of a spec
//!   whose value is the instance (its `spec_is_self_representing` exclusion off): WI-601's
//!   `bare_stream_op_on_abstract_finite_stream_defers_and_evals`, refused "missing `requires
//!   Stream[T = …]`" at a receiver that is the instance;
//! * a rule body's call that names no carrier left to run (`open_defaulted_call` answering
//!   nothing): [`an_unbracketed_static_call_over_a_body_less_sibling_is_refused`].
//!
//! [`a_carrier_taking_override_still_answers`] and
//! [`a_static_operation_with_no_body_is_each_providers`] pass under each, by design: they are
//! what the rule leaves as it was.

use anthill_core::kb::KnowledgeBase;

fn ints(kb: &mut KnowledgeBase, pattern: &str) -> Vec<i64> {
    crate::common::pattern_last_ints(kb, pattern)
}

/// `Desc` with a static `dflt` and a carrier-taking `describe`, both with a body, and a free
/// `leafDflt`; `tail` is written at the end of the namespace.
fn desc(tail: &str) -> String {
    format!(
        r#"namespace p.st
  import anthill.prelude.{{Int64}}
  sort Desc
    sort T = ?
    operation dflt() -> Int64 = 2
    operation describe(x: T) -> Int64 = 1
  end
  operation leafDflt() -> Int64 = 8
{tail}end
"#
    )
}

/// Each way a provider supplies a member is refused for a static operation with a body, naming
/// the member, the operation and the line the member is declared at: the provider's own member,
/// a `provides` binding, and a member of a spec that provides `Desc` at its parameter. Each
/// loaded; the own member answered `Desc[T = Leaf].dflt()` with `8`.
#[test]
fn each_supply_route_of_a_static_operation_with_a_body_is_refused() {
    for (route, tail, member, line) in [
        (
            "own member",
            "  sort Leaf\n    entity leaf(n: Int64)\n    provides Desc[T = Leaf]\n    operation dflt() -> Int64 = 8\n  end\n",
            "p.st.Leaf.dflt",
            "12:5: `",
        ),
        (
            "binding",
            "  sort Leaf\n    entity leaf(n: Int64)\n    provides Desc[T = Leaf, dflt = leafDflt]\n  end\n",
            "p.st.leafDflt",
            "8:3: `",
        ),
        (
            "spec at a parameter",
            "  sort Fancy\n    sort U = ?\n    provides Desc[T = U]\n    operation dflt() -> Int64 = 9\n  end\n  \
             sort Leaf\n    entity leaf(n: Int64)\n    provides Fancy[U = Leaf]\n  end\n",
            "p.st.Fancy.dflt",
            "12:5: `",
        ),
    ] {
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&desc(tail)),
            &[
                &format!("`{member}` overrides `p.st.Desc.dflt`"),
                "a static operation with a body",
                "declare `p.st.Desc.dflt` with no body",
                line,
            ],
            route,
        );
    }
}

/// CONTROL, passing either way by design: an override of the carrier-taking `describe` is the
/// provider's, `Desc.describe(leaf(1))` answers it, and `Desc[T = Leaf].dflt()` the spec's `2`.
#[test]
fn a_carrier_taking_override_still_answers() {
    let mut kb = crate::common::load_kb_with(&desc(
        "  sort Leaf\n    entity leaf(n: Int64)\n    provides Desc[T = Leaf]\n    \
         operation describe(x: Leaf) -> Int64 = 5\n  end\n  \
         rule d(?v) :- ?v <=> Desc[T = Leaf].dflt()\n  \
         rule s(?v) :- ?v <=> Desc.describe(leaf(1))\n",
    ));
    assert_eq!(ints(&mut kb, "p.st.d(?v)"), [2]);
    assert_eq!(ints(&mut kb, "p.st.s(?v)"), [5]);
}

/// A member that takes a value of the carrier, at a carrier that provides nothing, owes the
/// instance as its body-less twin does, where something provides the spec: `Desc.describe(van(1))`
/// is refused in a rule body and in an operation body, naming `Van`. The rule loaded and answered
/// nothing; a static member at that carrier runs ([`a_carrier_taking_override_still_answers`]).
#[test]
fn a_carrier_taking_default_at_a_carrier_that_provides_nothing_is_refused() {
    let van = "  sort Leaf\n    entity leaf(n: Int64)\n    provides Desc[T = Leaf]\n  end\n  \
               sort Van\n    entity van(n: Int64)\n  end\n";
    for (site, tail) in [
        ("rule body", "  rule r(?v) :- Desc.describe(van(1), ?v)\n"),
        ("operation body", "  operation o() -> Int64 = Desc.describe(van(1))\n"),
    ] {
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&desc(&format!("{van}{tail}"))),
            &["p.st.Desc.describe.requires", "`p.st.Van` provides no `p.st.Desc`"],
            site,
        );
    }
}

/// CONTROL, passing either way by design: what each provider supplies is a static operation with
/// no body, and the call's bracket chooses it.
#[test]
fn a_static_operation_with_no_body_is_each_providers() {
    let mut kb = crate::common::load_kb_with(
        r#"namespace p.tg
  import anthill.prelude.{Int64}
  sort Tag
    sort T = ?
    operation tag() -> Int64
  end
  sort Leaf
    entity leaf(n: Int64)
    provides Tag[T = Leaf]
    operation tag() -> Int64 = 5
  end
  sort Twig
    entity twig(n: Int64)
    provides Tag[T = Twig]
    operation tag() -> Int64 = 6
  end
  rule leafs(?v) :- ?v <=> Tag[T = Leaf].tag()
  rule twigs(?v) :- ?v <=> Tag[T = Twig].tag()
end
"#,
    );
    assert_eq!(ints(&mut kb, "p.tg.leafs(?v)"), [5]);
    assert_eq!(ints(&mut kb, "p.tg.twigs(?v)"), [6]);
}

/// A static operation with a body, in a spec with no body-less member and no `requires`, runs
/// its body at a type parameter of an operation, as it does with no bracket: `o3[P]() =
/// Desc[T = P].dflt()` answers `2` at `Leaf`, and `twice`, which calls `dflt`, `4`. `o3` was
/// refused, "missing `requires Desc[T = …]`".
#[test]
fn a_static_default_at_a_type_parameter_runs_its_body() {
    let mut kb = crate::common::load_kb_with(&desc(
        "  sort Leaf\n    entity leaf(n: Int64)\n    provides Desc[T = Leaf]\n  end\n  \
         operation o3[P]() -> Int64 = Desc[T = P].dflt()\n  \
         operation o6[P]() -> Int64 = Desc[T = P].dflt() * 2\n  \
         operation at3() -> Int64 = o3[Leaf]()\n  \
         operation at6() -> Int64 = o6[Leaf]()\n  \
         rule r3(?v) :- ?v <=> at3()\n  \
         rule r6(?v) :- ?v <=> at6()\n",
    ));
    assert_eq!(ints(&mut kb, "p.st.r3(?v)"), [2]);
    assert_eq!(ints(&mut kb, "p.st.r6(?v)"), [4]);
}

/// It runs where the call's bracket leaves a parameter open that providers answer apart:
/// `Pc[C = Bag].both()`, beside `WInt` and `WStr` providing `Pc` at `Bag` with `Element` at
/// `Int64` and at `String`, answers `4`. It was refused, the bracket naming no one instance.
#[test]
fn a_static_default_runs_where_the_bracket_leaves_a_parameter_open() {
    let mut kb = crate::common::load_kb_with(
        r#"namespace p.pc
  import anthill.prelude.{Int64, String}
  sort Pc
    sort C = ?
    sort Element = ?
    operation both() -> Int64 = 4
  end
  sort Bag
    entity bag(n: Int64)
  end
  sort WInt
    provides Pc[C = Bag, Element = Int64]
  end
  sort WStr
    provides Pc[C = Bag, Element = String]
  end
  operation o() -> Int64 = Pc[C = Bag].both()
  rule r(?v) :- ?v <=> o()
end
"#,
    );
    assert_eq!(ints(&mut kb, "p.pc.r(?v)"), [4]);
}

/// `Tag` whose static `twice` calls its body-less `tag`, provided by `Leaf`; `q2` is declared
/// with `requires` (written as given, empty or a clause) and calls `twice` at its parameter.
fn tag(requires: &str) -> String {
    format!(
        r#"namespace p.tw
  import anthill.prelude.{{Int64}}
  sort Tag
    sort T = ?
    operation tag() -> Int64
    operation twice() -> Int64 = tag() * 2
  end
  sort Leaf
    entity leaf(n: Int64)
    provides Tag[T = Leaf]
    operation tag() -> Int64 = 5
  end
  operation q2[P]() -> Int64 {requires}= Tag[T = P].twice()
  operation atLeaf() -> Int64 = q2[Leaf]()
  rule r(?v) :- ?v <=> atLeaf()
end
"#
    )
}

/// Where the spec has a body-less member, a static operation's body may call it, so a call at a
/// type parameter owes the instance as the member's own call does: `q2[P]() = Tag[T =
/// P].twice()` is refused naming `requires Tag[T = …]`, and the repair it advises answers `10` at
/// `Leaf`. It loaded clean, and the rule's call was left unanswered when it ran.
#[test]
fn a_static_default_over_a_body_less_sibling_owes_the_instance() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&tag("")),
        &["p.tw.Tag.twice.requires", "missing `requires Tag[T = …]` on `p.tw.q2`"],
        "a static default over a body-less sibling at a type parameter",
    );
    let mut kb = crate::common::load_kb_with(&tag("requires Tag[T = P] "));
    assert_eq!(ints(&mut kb, "p.tw.r(?v)"), [10]);
}

/// A rule body's call of it with no bracket names no instance, and is refused naming the
/// bracket to write, as a call of the body-less member is, as a value and as the goal it is;
/// `Tag[T = Leaf].twice()`, the repair, answers `10`. Unrefused, the rules loaded and were left
/// unanswered when they ran.
#[test]
fn an_unbracketed_static_call_over_a_body_less_sibling_is_refused() {
    let src = |rules: &str| tag("").replace(
        "  operation q2[P]() -> Int64 = Tag[T = P].twice()\n  operation atLeaf() -> Int64 = q2[Leaf]()\n  rule r(?v) :- ?v <=> atLeaf()\n",
        rules,
    );
    for rule in ["  rule t(?v) :- ?v <=> Tag.twice()\n", "  rule g(?v) :- Tag.twice(?v)\n"] {
        let program = src(rule);
        assert!(program.contains(rule), "the fixture's rules were replaced");
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&program),
            &["p.tw.Tag.twice.requires", "`Tag[T = …].twice(…)`"],
            rule,
        );
    }
    let mut kb = crate::common::load_kb_with(&src("  rule b(?v) :- ?v <=> Tag[T = Leaf].twice()\n"));
    assert_eq!(ints(&mut kb, "p.tw.b(?v)"), [10]);
}

/// It owes the instance at whichever parameter of the spec the call binds to a type parameter,
/// not at a carrier parameter alone: over `Pair2[A, B]`, whose members take a value of neither,
/// `Pair2[A = P, B = Int64].twice()` is refused naming `requires Pair2[A = …]`, and the repair
/// answers `10`. It loaded clean, and the rule's call was left unanswered when it ran.
#[test]
fn it_owes_it_at_whichever_parameter_the_call_binds() {
    let src = |requires: &str| {
        format!(
            r#"namespace p.pr
  import anthill.prelude.{{Int64}}
  sort Pair2
    sort A = ?
    sort B = ?
    operation tag() -> Int64
    operation twice() -> Int64 = tag() * 2
  end
  sort Leaf
    entity leaf(n: Int64)
    provides Pair2[A = Leaf, B = Int64]
    operation tag() -> Int64 = 5
  end
  operation q[P]() -> Int64 {requires}= Pair2[A = P, B = Int64].twice()
  operation atLeaf() -> Int64 = q[Leaf]()
  rule r(?v) :- ?v <=> atLeaf()
end
"#
        )
    };
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&src("")),
        &["p.pr.Pair2.twice.requires", "missing `requires Pair2[A = …]` on `p.pr.q`"],
        "a static default at a non-carrier parameter",
    );
    let mut kb = crate::common::load_kb_with(&src("requires Pair2[A = P, B = Int64] "));
    assert_eq!(ints(&mut kb, "p.pr.r(?v)"), [10]);
}
