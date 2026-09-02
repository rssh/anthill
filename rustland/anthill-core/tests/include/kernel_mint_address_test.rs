//! THE TWO CONVERTER-MINTED KERNEL PRIMITIVES CARRY THEIR ADDRESS.
//!
//! WI-909's group-3 pass — one part of that ticket, not its acceptance: WI-909's own
//! subject is the tier's absence from TYPE position (`remap_symbol_strict`), which
//! nothing here touches. This is the tier-shrinking half.
//!
//! `!` and `requires(X)` / `require[X]` name no functor in the source: the CONVERTER
//! supplies one (`anthill.kernel.cut`, `anthill.kernel.find_dictionary`). Until this
//! change it supplied the SHORT name and `PRELUDE_QUALIFIED` — the implicit tier's
//! lowest rung — turned it back into the address. That is WI-20260825-5W3RJ's shape one
//! namespace over.
//!
//! `pratt::UNIFY_FUNCTOR` / `STRUCT_EQ_FUNCTOR` FOLLOWED, in WI-909's group-4 pass, and
//! this file covers both passes because they are one mechanism. `<=>` and `===` name no
//! functor either, so the converter supplied a short one and the tier turned it back
//! into `anthill.kernel.unify` / `.struct_eq`. Their migration additionally DELETED
//! `kb::load::minted_connective_symbol`, a hand-written override that existed only to
//! lift those two mints back above scope resolution at every functor-resolving producer
//! — which the `..` address does by construction. `PRELUDE_QUALIFIED` 17 -> 15.
//!
//! WHAT THE CHANGE BUYS. The tier sits BELOW scope resolution, so a namespace declaring
//! its own `cut` / `find_dictionary` captured the mint — and a captured control
//! primitive does not fail, it answers differently.
//!
//! WHICH ROWS MEASURE WHICH HALF. The diff has two halves and they need separate
//! back-outs; an earlier version of this file measured only the first.
//!   * THE MINT (restore the short strings in `convert.rs`):
//!       `a_minted_cut_carries_its_address`             `["cut"]` for the address
//!       `a_minted_requires_guard_carries_its_address`  `["find_dictionary"]` likewise
//!       `a_local_cut_declaration_does_not_capture_the_operator`     2 solutions, not 1
//!       `a_local_find_dictionary_declaration_does_not_capture_the_guard` 1, not 0
//!   * THE TIER ROWS (re-add them to `PRELUDE_QUALIFIED`, mints untouched):
//!       `a_rule_head_named_cut_introduces_a_local_name` — the head resolves THROUGH the
//!       tier to `anthill.kernel.cut` instead, so no `test.…cut` is minted and the row
//!       fails. It is the only row that sees that half.
//!   * THE PRE-WI-888 STATE — `pratt::UNIFY_FUNCTOR` / `STRUCT_EQ_FUNCTOR` back to short
//!     AND their `PRELUDE_QUALIFIED` rows restored, `minted_connective_symbol` still
//!     gone. That is the back-out that isolates group 4's mechanism, and BOTH halves are
//!     needed: with the rows left out, a short `struct_eq` names nothing and the STDLIB
//!     stops loading, so every row here fails for an unrelated reason.
//!       `a_rival_unify_in_scope_does_not_capture_the_equation` — MEASURED `left: 0,
//!       right: 1`; its no-rival control still passes, which is what says the row saw
//!       the capture rather than a broken fixture.
//!       `pratt::tests::minted_operators_carry_their_spec_op_address` (a unit test, not
//!       here) — MEASURED "`unify` must be an ABSOLUTE address". It is the ONLY row that
//!       catches a short constant; see `a_minted_unify_carries_its_address` for why the
//!       mint rows cannot.
//!   * PASS EITHER WAY, by design — the controls:
//!       `the_cut_operator_still_commits_with_no_rival`
//!       `the_guard_still_blocks_with_no_rival` / `the_guard_fires_for_a_provider`
//!       `every_desugar_target_carries_the_absolute_marker`
//!       `a_minted_unify_carries_its_address` / `a_minted_struct_eq_carries_its_address`
//!       — green in every state above, because the mint site IS the constant they
//!       compare against. What they measure is stated at their own site.
//!
//! THE TWO HALVES LOAD DIFFERENTLY, ON PURPOSE. The cut rows use `common::load_kb_with`
//! (stdlib + Rust host bindings); the guard rows use `common::load_stdlib_kb_with_source`
//! (stdlib only), because with host bindings present the requirement guard stops
//! discriminating by carrier and every guard row answers 1. Measured — see
//! [`load_guard_kb`], which carries the control pair.
//!
//! THE RIVAL MUST BE A DECLARATION, NOT A RULE, and the first cut of this file got that
//! wrong — recorded because the reason is a language rule and the wrong instrument is
//! silent. A rule HEAD is RESOLVED, not declared (WI-896, kernel-language.md §5.3), so
//! with the tier restored `rule cut() :- …` contributes a clause to the kernel primitive
//! instead of introducing a rival, and both capture rows passed backed-out while
//! measuring nothing. An `operation` is defined in pass 1 and shadows the tier, which is
//! why WI-20260825-P9Y67 drove its own six rows that way. That same fact is what
//! `a_rule_head_named_cut_introduces_a_local_name` now turns into a measurement.

use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::parse::desugar_target as dt;
use anthill_core::parse::pratt;
use smallvec::SmallVec;

use crate::common::{definite_unary, load_kb_with, load_kb_with_stdlib_only};

/// Every PARSE-level functor spelling in `src` that is `short` or the address ending in
/// it, in allocation order.
///
/// Read off the parse IR rather than the KB on purpose: the KB stores the RESOLVED
/// symbol, whose local name is the short one either way, so a KB-side assertion would
/// pass with the mint backed out. The spelling only exists before resolution.
///
/// The two accepted spellings are passed EXPLICITLY rather than matched by suffix. A
/// suffix test (`ends_with(".cut")`) also matches any dotted functor a converter might
/// intern whose last segment collides — including this file's own fixture namespace, if
/// one were ever named that way. Raised by `/code-review`.
fn minted_spellings(src: &str, short: &str, address: &str) -> Vec<String> {
    let parsed = parse::parse(src).expect("parses");
    parsed
        .terms
        .iter()
        .filter_map(|(_, term)| match term {
            Term::Fn { functor, .. } => {
                let n = parsed.symbols.local_name(*functor);
                (n == short || n == address).then(|| n.to_owned())
            }
            _ => None,
        })
        .collect()
}

/// A rule body's `!` mints `..anthill.kernel.cut`, not `cut`.
///
/// FAILS ON BACK-OUT of the mint: `dt::CUT` -> `"cut"` at `convert.rs`'s `"cut" =>` arm.
#[test]
fn a_minted_cut_carries_its_address() {
    let spellings = minted_spellings(
        "namespace test.w909.commit\n  \
         fact p909(1)\n  \
         rule a909(?x) :- p909(?x), !\n\
         end\n",
        "cut",
        dt::CUT,
    );
    assert_eq!(
        spellings,
        vec![dt::CUT.to_owned()],
        "the cut control primitive must name its kernel declaration outright, not mint \
         a bare name for the implicit tier to look up"
    );
}

/// Both requirement spellings mint `..anthill.kernel.find_dictionary`. They lower
/// through two different functions (`rewrite_requires_goal` / `lower_require`) and the
/// row holds them together so a fix to one cannot leave the other short.
///
/// FAILS ON BACK-OUT of either `dt::FIND_DICTIONARY` -> `"find_dictionary"`.
#[test]
fn a_minted_requires_guard_carries_its_address() {
    for body in ["requires(PartialEq[T])", "?d = require[PartialEq[T]]"] {
        let src = format!(
            "namespace test.w909.req\n  \
             import anthill.prelude.{{PartialEq}}\n  \
             fact p909(1)\n  \
             rule a909(?x) :- {body}, p909(?x)\n\
             end\n"
        );
        let spellings = minted_spellings(&src, "find_dictionary", dt::FIND_DICTIONARY);
        assert_eq!(
            spellings,
            vec![dt::FIND_DICTIONARY.to_owned()],
            "`{body}` must name the kernel relation outright; got {spellings:?}"
        );
    }
}

/// `<=>` mints `..anthill.kernel.unify`, not `unify`, and mints exactly one functor.
///
/// IT DOES *NOT* CATCH A SHORT CONSTANT, unlike the four cut / find_dictionary rows
/// above, and saying so is the difference between a pin and a tautology. Those mint
/// sites are `convert.rs` arms that name `dt::CUT` independently of the constant, so the
/// two sides move apart on a back-out. Here the mint site IS the constant — pratt's
/// infix table stores `functor: UNIFY_FUNCTOR` — so backing `UNIFY_FUNCTOR` out to
/// `"unify"` moves BOTH sides and this row stays green. MEASURED in that state, together
/// with the two rows that do fail there.
///
/// WHAT IT DOES MEASURE, which is worth its lines: that the `<=>` SURFACE FORM routes
/// through this constant at all (a second lowering path, or a table entry pointing
/// somewhere else, shows up here), and that it mints ONE functor rather than a bare name
/// beside an address.
///
/// THE ROW THAT CATCHES A SHORT CONSTANT is
/// `pratt::tests::minted_operators_carry_their_spec_op_address`, which asserts the `..`
/// marker over `EQUALITY_FAMILY_FUNCTORS`. Driven: it fails with
/// "`unify` must be an ABSOLUTE address".
#[test]
fn a_minted_unify_carries_its_address() {
    let spellings = minted_spellings(
        "namespace test.w909.eqn\n  \
         operation tau909() -> Int64\n  \
         rule tau909() <=> 7 [simp]\n\
         end\n",
        "unify",
        pratt::UNIFY_FUNCTOR,
    );
    assert_eq!(
        spellings,
        vec![pratt::UNIFY_FUNCTOR.to_owned()],
        "`<=>` must name the kernel primitive outright; a bare `unify` is looked up by \
         the implicit tier, which sits BELOW scope"
    );
}

/// `===` mints `..anthill.kernel.struct_eq`, not `struct_eq`. Same claim and the same
/// limit as the row above — read its second paragraph before trusting this one as a
/// back-out detector.
#[test]
fn a_minted_struct_eq_carries_its_address() {
    let spellings = minted_spellings(
        "namespace test.w909.steq\n  \
         fact p909(1)\n  \
         rule a909(?x) :- p909(?x), ?x === 1\n\
         end\n",
        "struct_eq",
        pratt::STRUCT_EQ_FUNCTOR,
    );
    assert_eq!(
        spellings,
        vec![pratt::STRUCT_EQ_FUNCTOR.to_owned()],
        "`===` must name the kernel primitive outright"
    );
}

/// EVERY desugar target carries the `..` marker.
///
/// PASSES EITHER WAY by design — it does not measure this change, it guards the whole
/// class against the mistake WI-20260825-5W3RJ's own first cut shipped. An unmarked
/// `anthill.kernel.cut` resolves identically in a test KB (the orphan row's
/// `unwrap_or(t)` masks it) and is CAPTURED in production by any scope where `anthill`
/// denotes something else. `parse::pratt` has had this row for its two address tables
/// since WI-20260825-P9Y67; `desugar_target` had none. Raised by `/code-review`.
#[test]
fn every_desugar_target_carries_the_absolute_marker() {
    let unmarked: Vec<&str> = dt::ALL
        .iter()
        .copied()
        .filter(|t| !t.starts_with(anthill_core::intern::ABSOLUTE_PATH_MARKER))
        .collect();
    assert!(
        unmarked.is_empty(),
        "an unmarked target takes the relative, head-qualified reading, so its HEAD \
         segment runs scope resolution and a namespace named `anthill` captures the \
         desugaring: {unmarked:?}"
    );
}

/// The cut fixture: two clauses, `!` in the first. `rival` is spliced in as extra
/// namespace-level source.
///
/// A BUILDER, NOT A `str::replace` ON A CONST. The first version of this file injected
/// the rival with `CUT_SRC.replace("      fact first909(c1)", …)`, which returns the
/// input UNCHANGED when the needle stops matching — a re-indent or a rename would have
/// turned the capture row into a byte-identical copy of the control, asserting the same
/// `1` and passing with the change backed out. Found by `/code-review`.
fn cut_src(rival: &str) -> String {
    format!(
        r#"
    namespace test.w909.commit
      sort Tag
        entity c1
        entity c2
      end
{rival}
      fact first909(c1)
      fact second909(c2)
      rule a909(?x) :- first909(?x), !
      rule a909(?x) :- second909(?x)
    end
"#
    )
}

/// THE CONTROL. With no rival in scope the cut commits to clause 1 — one solution, not
/// two. Passes with and without the change, by design: it is what says the row below
/// measures the capture rather than a cut that stopped working.
#[test]
fn the_cut_operator_still_commits_with_no_rival() {
    let mut kb = load_kb_with(&cut_src(""));
    assert_eq!(
        definite_unary(&mut kb, "test.w909.commit.a909").len(),
        1,
        "cut in clause 1 must discard clause 2 (without the cut this is 2)"
    );
}

/// A NAMESPACE DECLARING ITS OWN `cut` DOES NOT CAPTURE THE OPERATOR — the same program
/// as the control plus one rival declaration, which is the only difference between them.
///
/// INVERTS ON BACK-OUT of the mint, MEASURED: **2 solutions, not 1**, loaded clean with
/// no diagnostic. With the short mint the rival is found by `resolve_in_scope` before
/// the tier is consulted, so the `!` goal calls the rival, `BuiltinTag::Cut` never
/// matches and clause 2 survives.
#[test]
fn a_local_cut_declaration_does_not_capture_the_operator() {
    // An OPERATION, not a rule — see this file's header.
    let mut kb = load_kb_with(&cut_src("      operation cut() -> Bool = true\n"));
    assert_eq!(
        definite_unary(&mut kb, "test.w909.commit.a909").len(),
        1,
        "a same-spelled local declaration must not take the cut's meaning"
    );
}

/// THE ROW FOR THE OTHER HALF OF THE DIFF — the two deleted `PRELUDE_QUALIFIED` rows,
/// which every other row here is blind to.
///
/// A rule head is RESOLVED, not declared. While `anthill.kernel.cut` sat on the implicit
/// tier, a head spelled `cut` reached it and the rule contributed a clause to the KERNEL
/// PRIMITIVE — so `test.w909.head.cut` was never minted. With the row gone the ladder
/// finds nothing and the head introduces a local name, which is what this asserts.
///
/// FAILS IF THE TIER ROWS COME BACK, with the mints left alone — the one back-out no
/// other row here detects. `zz909` is the control: an ordinary name that was never on
/// the tier and mints either way, so a failure that takes both arms down is the fixture
/// breaking rather than the tier returning. Raised by `/code-review`.
#[test]
fn a_rule_head_named_cut_introduces_a_local_name() {
    let kb = load_kb_with(
        "namespace test.w909.head\n  \
         fact ok909(1)\n  \
         rule cut(?x) :- ok909(?x)\n  \
         rule zz909(?x) :- ok909(?x)\n\
         end\n",
    );
    assert!(
        kb.try_resolve_symbol("test.w909.head.zz909").is_some(),
        "control: an ordinary rule head always introduces its name"
    );
    assert!(
        kb.try_resolve_symbol("test.w909.head.cut").is_some(),
        "`cut` is off the implicit tier, so a rule head spelled that way must introduce \
         a LOCAL name instead of adding a clause to `anthill.kernel.cut`"
    );
}

/// The equation fixture: a `[simp]` definition plus a probe that forces the rewrite.
/// `rival` is spliced in as an extra namespace-level line.
///
/// THE RIVAL IS A REAL ONE. `anthill.reflect.unify(a: Term, b: Term, kb: KB)` is a
/// declaration the stdlib already ships — proposal 049's term-level face — so this arm
/// is one `import` line, not a synthetic collision. That is what made the hazard sharp
/// enough to migrate: `desugar_target`'s header called `unify` "the sharper case" for
/// exactly this reason.
fn eqn_src(rival: &str) -> String {
    format!(
        r#"
    namespace test.w909.eqn
      import anthill.prelude.{{Int64}}
      import anthill.prelude.PartialEq.{{eq}}
{rival}
      operation tau909() -> Int64

      rule tau909() <=> 7 [simp]

      rule probe909(1) :- eq(7, tau909())
    end
"#
    )
}

/// A RIVAL `unify` IN SCOPE DOES NOT CAPTURE THE EQUATION — the same program as the
/// control plus one import, which is the only difference between them.
///
/// PASSES EITHER WAY against the previous commit, BY DESIGN, and the distinction is the
/// whole reason this row is worth its lines: `kb::load::minted_connective_symbol` used
/// to hold this property by hand, lifting the minted connective above scope at every
/// functor-resolving producer. WI-909 deletes that function, so the row's job is to say
/// the ADDRESS now holds what the override held.
///
/// FAILS IN THE PRE-WI-888 STATE — short mints, `PRELUDE_QUALIFIED` rows restored, no
/// override — which is the back-out that isolates the mechanism. MEASURED there, both
/// arms, loading clean with no diagnostic either way:
///
/// | fixture | pre-WI-888 | with the addresses |
/// |---|---|---|
/// | rival imported | residual `eq(?_, tau909)` — **captured** | `eq(?_, 7)` |
/// | no rival (control) | `eq(?_, 7)` | `eq(?_, 7)` |
///
/// Backing out the constants ALONE is NOT that measurement and must not be mistaken for
/// it: with the tier rows already gone, a short `struct_eq` names nothing, so the STDLIB
/// stops loading (`rule-body goal `struct_eq` names nothing`, plus three
/// `struct_eq.apply` type errors) and every row here fails for an unrelated reason.
#[test]
fn a_rival_unify_in_scope_does_not_capture_the_equation() {
    // The constant rides in the HEAD so the claim DECIDES: `=` is a semantic test that
    // never binds (§8.3), so `rule p(?m) :- …, ?m = 1` suspends and would count a
    // floundered answer as success — `common::definite_unary`'s doc records the four
    // suites that did. Here the body's `eq(7, tau909())` decides only when the equation
    // has rewritten `tau909()` to `7`; under a capture it leaves a residual and the
    // count is 0.
    let mut control = load_kb_with(&eqn_src(""));
    assert_eq!(
        definite_unary(&mut control, "test.w909.eqn.probe909").len(),
        1,
        "control: with no rival the `[simp]` equation rewrites `tau909()` to `7` and the \
         probe decides. If THIS fails the fixture is broken, not the address"
    );
    let mut rivalled = load_kb_with(&eqn_src("      import anthill.reflect.{unify}\n"));
    assert_eq!(
        definite_unary(&mut rivalled, "test.w909.eqn.probe909").len(),
        1,
        "an `import anthill.reflect.{{unify}}` puts a real 3-arg operation in scope; the \
         minted `<=>` must still denote `anthill.kernel.unify`, because its address \
         outranks scope. Under the tier it did not, and the clause was filed under the \
         reflect operation — silently, which is WI-888."
    );
}

/// A GOAL-POSITION `let` REACHES THE KERNEL PRIMITIVE — driven, because nothing else
/// drives it.
///
/// `let ?y = e` is proposal 049 sugar for `?y <=> e` and lowers through a DIFFERENT
/// function from the `<=>` operator (`convert::convert_let_binding`, not pratt's infix
/// table). That second lowering spelled `"unify"` as a string literal of its own, so
/// WI-909's address did not reach it and it began minting a name that resolves through
/// no rung — the goal could never match.
///
/// THE BREAK ITSELF IS LOUD — a `let` lowers to a GOAL, so WI-1034's rule-body-goal
/// check names it. MEASURED by backing `convert_let_binding` out: "rule-body goal
/// `unify` names nothing: … this goal can NEVER match", which is how this row fails.
///
/// WHAT HAD NO INSTRUMENT WAS THE CHANGE, and that is why this row exists rather than a
/// comment. `parse_test::parse_let_binding_desugars_to_unify` compared the lowering to
/// its OWN `"unify(?v, f(?y))"` literal, so both sides were the same stale spelling and
/// it stayed green. And no `.anthill` file in stdlib, examples, or either embedded
/// project writes a goal-position `let` — MEASURED, `grep ':-.*\blet '` over the corpus
/// is 0 — so the suite never reached the loud error. A backstop nothing walks into
/// reports nothing. The parse-side row now asserts the two lowerings against EACH OTHER;
/// this one walks the goal.
#[test]
fn a_goal_position_let_binds_through_the_kernel_primitive() {
    let mut kb = load_kb_with(
        "namespace test.w909.letgoal\n  \
         import anthill.prelude.{Int64}\n  \
         fact src909(3)\n  \
         rule via_let909(?y) :- src909(?x), let ?y = ?x\n  \
         rule via_op909(?y) :- src909(?x), ?y <=> ?x\n\
         end\n",
    );
    // `Value` has no `PartialEq` (WI-486 removed the carrier-blind comparator), so the
    // two lowerings are compared through the KB-aware view head. That is the right
    // currency anyway: what must agree is the VALUE each binds, not a derived count.
    use anthill_core::kb::term_view::TermView;
    let heads = |kb: &mut KnowledgeBase, qn: &str| -> Vec<String> {
        definite_unary(kb, qn)
            .iter()
            .map(|v| format!("{:?}", v.head(kb)))
            .collect()
    };
    let via_op = heads(&mut kb, "test.w909.letgoal.via_op909");
    assert_eq!(
        via_op.len(),
        1,
        "control: the `<=>` operator spelling binds and decides. If THIS fails the \
         fixture is broken, not the `let` lowering"
    );
    assert!(
        via_op[0].contains('3'),
        "control: …and it binds the fact's value; got {via_op:?}"
    );
    assert_eq!(
        heads(&mut kb, "test.w909.letgoal.via_let909"),
        via_op,
        "`let ?y = ?x` is sugar for `?y <=> ?x` (proposal 049), so it must bind the same \
         way. A short `unify` here resolves through nothing since the tier row went, and \
         the goal silently stops matching"
    );
}

/// A `<=>` IN A QUERY PATTERN IS NOT CAPTURED BY AN INVOCATION IMPORT.
///
/// THE POSITION THE DELETED OVERRIDE WAS ADDED FOR, and it had no test. `kb::load`'s
/// query arm called `minted_connective_symbol` directly, with a comment naming this
/// exact scenario — `anthill query -i anthill.reflect.{unify} …` puts that declaration
/// in `<global>`, the very scope a query pattern resolves in — and the comment was the
/// whole coverage. WI-909 removes the override, so the claim needs an instrument.
///
/// A QUERY PATTERN IS THE POSITION WITH NO LOAD-ERROR CHANNEL: an unresolved functor is
/// interned bare and the query simply matches nothing, so a capture here is silent by
/// construction. That is why the row asserts the resolved QUALIFIED NAME rather than a
/// solution count — a count of 0 cannot tell "captured" from "no such fact".
///
/// The `-i` spelling is deliberate (`supply_invocation_imports`): since WI-995 an
/// `import` written in a program FILE is local to that file and never reaches a query
/// pattern, so a file-based rival would make this row vacuous while reading as though it
/// tested something.
#[test]
fn a_query_pattern_connective_is_not_captured_by_an_invocation_import() {
    let mut kb = load_kb_with_stdlib_only(
        "namespace test.w909.qp\n  \
         fact p909(1)\n\
         end\n",
    );
    let target = anthill_core::parse::desugar_target::qualified(pratt::UNIFY_FUNCTOR);
    assert_eq!(
        crate::common::query_pattern_functor_qn(&mut kb, "?x <=> 1"),
        target,
        "control: with nothing in scope the pattern's minted connective denotes the \
         kernel primitive"
    );
    crate::common::supply_invocation_imports(&mut kb, &["anthill.reflect.{unify}"]);
    assert_eq!(
        crate::common::query_pattern_functor_qn(&mut kb, "?x <=> 1"),
        target,
        "`-i anthill.reflect.{{unify}}` puts a real 3-arg operation into `<global>`, \
         which IS the query scope; the address outranks it. Under the tier this rung \
         lost, which is why the arm carried a hand-written override"
    );
}

/// A RULE HEAD NAMED `unify` INTRODUCES A LOCAL NAME — the `unify` twin of
/// `a_rule_head_named_cut_introduces_a_local_name`, and the row for group 4's OTHER
/// half: the two deleted `PRELUDE_QUALIFIED` rows, which every mint row here is blind
/// to.
///
/// A rule head is RESOLVED, not declared (WI-896). While `anthill.kernel.unify` sat on
/// the implicit tier, a head spelled `unify` reached it and the rule contributed a
/// clause to the KERNEL PRIMITIVE — so `test.w909.head2.unify` was never minted. With
/// the row gone the ladder finds nothing and the head introduces a local name.
///
/// IT EXISTS BECAUSE THE CLAIM WAS DOCUMENTED WITHOUT ONE. `kb::load::parse_equation_lhs`
/// states this behaviour change for `unify` and cited only the `cut` row above as
/// evidence — a different name on a different rung. `/code-review` also found the one
/// test that HAD been measuring it (`wi948_written_connective_head_test`) quietly
/// stop: its head fell to a local mint, leaving a `clauses_under` delta that still
/// compared equal for a new reason. That fixture now imports the connective to keep its
/// own subject; this row asserts the unimported behaviour instead of assuming it.
///
/// FAILS IF THE TIER ROWS COME BACK, mints untouched. `zz909b` is the control: an
/// ordinary name that was never on the tier and mints either way, so a failure taking
/// both arms down is the fixture breaking rather than the tier returning.
#[test]
fn a_rule_head_named_unify_introduces_a_local_name() {
    let kb = load_kb_with(
        "namespace test.w909.head2\n  \
         fact ok909(1)\n  \
         rule unify(?x) :- ok909(?x)\n  \
         rule zz909b(?x) :- ok909(?x)\n\
         end\n",
    );
    assert!(
        kb.try_resolve_symbol("test.w909.head2.zz909b").is_some(),
        "control: an ordinary rule head always introduces its name"
    );
    assert!(
        kb.try_resolve_symbol("test.w909.head2.unify").is_some(),
        "`unify` is off the implicit tier, so a rule head spelled that way must \
         introduce a LOCAL name instead of adding a clause to `anthill.kernel.unify`"
    );
}

/// WI-300's fixture, both arms: `Witheq` provides `Eq` and the guard lets the rule
/// through; `Noeq` provides nothing and the guard stops it.
fn guard_src(rival: &str) -> String {
    format!(
        r#"
    namespace test.w909.guard
      import anthill.prelude.{{Int64, PartialEq, Eq}}
      import anthill.prelude.PartialEq.{{eq}}
      sort Witheq
        entity we(v: Int64)
      end
      sort Noeq
        entity ne(v: Int64)
      end
      fact PartialEq[T = Witheq]
      fact Eq[T = Witheq]
{rival}
      rule related909(?x, ?y) :- requires(PartialEq[T]), eq(?x, ?y)
    end
"#
    )
}

/// Load the guard fixture. STDLIB ONLY — not `load_kb_with`, and the difference is
/// measured rather than stylistic.
///
/// `load_kb_with` also loads the Rust host bindings, and with those present this
/// fixture's guard STOPS DISCRIMINATING BY CARRIER: `Noeq`, which provides nothing,
/// answers 1 exactly as `Witheq` does. Measured as a control pair in one suite run —
/// `wi300_rule_body_requires_test::guard_blocks_when_carrier_has_no_provider`, whose
/// fixture this reduces and which loads stdlib only, asserts 0 and passes in the same
/// run where this row asserted 0 and got 1.
///
/// THAT IS NOT THIS CHANGE'S DEFECT and it is not fixed here: these rows are about
/// whether a same-spelled declaration captures the `requires(X)` MINT, and they need a
/// KB where the guard discriminates at all. Filed as `WI-20260831-QF5JT`.
///
/// NOR IS `load_stdlib_kb_with_source` THE ANSWER, though it also drops the bindings:
/// it loads the user file in a SECOND pass, and driven that way this fixture answers 0
/// for EVERY carrier — the positive arm dies too, so the rows go quiet instead of
/// discriminating. One `load_all` over stdlib + source is the recipe that works, which
/// is what `load_kb_with_stdlib_only` is.
fn load_guard_kb(rival: &str) -> KnowledgeBase {
    load_kb_with_stdlib_only(&guard_src(rival))
}

/// `related909(c(v: 1), c(v: 1))` — the DEFINITE solutions only.
fn guard_solutions(kb: &mut KnowledgeBase, ctor: &str) -> usize {
    let arg = {
        let functor = kb
            .try_resolve_symbol(ctor)
            .unwrap_or_else(|| panic!("ctor {ctor} not in KB"));
        let v = kb.intern("v");
        let one = kb.alloc(Term::Const(Literal::Int(1)));
        kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(v, one)]),
        })
    };
    let related = kb
        .try_resolve_symbol("test.w909.guard.related909")
        .expect("related909 in KB");
    let goal: TermId = kb.alloc(Term::Fn {
        functor: related,
        pos_args: SmallVec::from_slice(&[arg, arg]),
        named_args: SmallVec::new(),
    });
    kb.resolve(
        &[goal],
        &anthill_core::kb::resolve::ResolveConfig::default(),
    )
    .iter()
    // `Solution::is_definite`, not a hand-rolled `residual.is_empty()`: WI-20260822-WZX6B
    // found four suites counting floundered answers as decisions.
    .filter(|s| s.is_definite())
    .count()
}

/// THE POSITIVE ARM. `Witheq` provides `Eq`, so the guard lets the rule through and the
/// structurally-equal pair answers.
///
/// PASSES EITHER WAY, and it is the row that makes the two zero-asserting rows below
/// mean something: without it, a fixture that stopped resolving for an unrelated reason
/// would satisfy every guard assertion in this file. Raised by `/code-review`.
#[test]
fn the_guard_fires_for_a_provider() {
    let mut kb = load_guard_kb("");
    assert_eq!(
        guard_solutions(&mut kb, "test.w909.guard.Witheq.we"),
        1,
        "a carrier that provides Eq must pass the requirement guard"
    );
}

/// THE CONTROL for the blocking arm. `Noeq` has no `provides Eq`, so `requires` blocks
/// and the structurally-equal pair yields nothing. Passes either way, by design.
#[test]
fn the_guard_still_blocks_with_no_rival() {
    let mut kb = load_guard_kb("");
    assert_eq!(
        guard_solutions(&mut kb, "test.w909.guard.Noeq.ne"),
        0,
        "the requirement guard alone decides this — body `eq` is structural and would \
         succeed on its own, as the positive arm shows"
    );
}

/// A NAMESPACE DECLARING ITS OWN `find_dictionary` DOES NOT CAPTURE THE GUARD.
///
/// INVERTS ON BACK-OUT of the mint, MEASURED: **1 solution, not 0**. The short mint
/// resolves to the rival, which succeeds for any argument, so the typer sweep never
/// recognises the goal as the kernel relation, an unsatisfiable requirement stops
/// blocking, and the rule fires on a carrier that provides nothing. A guard that
/// silently stops guarding is the worst reading in this family, which is why the row is
/// driven rather than asserted at the parse level alone.
#[test]
fn a_local_find_dictionary_declaration_does_not_capture_the_guard() {
    // An OPERATION, for the reason the cut row states.
    let mut kb = load_guard_kb("      operation find_dictionary(s: Int64) -> Bool = true\n");
    assert_eq!(
        guard_solutions(&mut kb, "test.w909.guard.Noeq.ne"),
        0,
        "a same-spelled local declaration must not take the requirement guard's meaning"
    );
}
