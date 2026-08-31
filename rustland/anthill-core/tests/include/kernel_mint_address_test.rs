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
//! NOT THE LAST OF THE CLASS, and the header says so because a draft of this file
//! claimed otherwise: `pratt::UNIFY_FUNCTOR` / `STRUCT_EQ_FUNCTOR` are short converter
//! mints on the tier too. See `desugar_target`'s module doc.
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
//!   * PASS EITHER WAY, by design — the controls:
//!       `the_cut_operator_still_commits_with_no_rival`
//!       `the_guard_still_blocks_with_no_rival` / `the_guard_fires_for_a_provider`
//!       `every_desugar_target_carries_the_absolute_marker`
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
