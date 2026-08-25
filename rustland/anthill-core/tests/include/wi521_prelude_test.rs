//! WI-521 — the implicit PRELUDE (cons / nil / some / none, the arithmetic and
//! comparison operator targets, the logic operators not / or / push_choice)
//! resolves via a LOWEST-PRECEDENCE fallback (`prelude_qualified`), not a
//! `<global>` import.
//!
//! The distinguishing property vs the old flat `add_import(<global>, …)`: the
//! fallback fires only when scope resolution fails, so a user name in scope wins
//! without the two ever being CANDIDATES together. With the flat injection, an
//! imported `eq` plus the `<global>` `eq` resolved to `Ambiguous` (a load error) —
//! exactly the footgun the WI-476 collision blocklist worked around.
//!
//! THIS HEADER USED TO OVERSTATE THAT as "a user name that clashes with a prelude
//! name is NEVER ambiguous … so the clash cannot happen", which is false one scope
//! over: a namespace-LESS `operation eq(…)` lands in `<global>`, a non-enclosing
//! parent of every scope, and DOES go ambiguous inside the stdlib's own namespaces —
//! driven by `wi_bfb9a_rival_spec_operation_test::a_namespace_less_declaration_is_free_standing_too`.
//! The property is about the FALLBACK's precedence, not a guarantee about every
//! program.
//!
//! AND A FREE-STANDING RIVAL OF A SPEC OPERATION IS NOW REFUSED OUTRIGHT
//! (WI-20260824-BFB9A), so the shadowing this file was written to demonstrate no
//! longer has a legal program to demonstrate it on — see
//! `a_free_standing_eq_rivalling_the_spec_op_is_refused` below, which is the
//! inverted remains of the original row. The rest of `wi_bfb9a_rival_spec_operation_test`
//! holds that rule's own legs.
//!
//! WHERE WI-521'S SHADOWING IS STILL DRIVEN, since the row above no longer can: the
//! deleted test only ever asserted `errs.is_empty()`, which is not evidence that a user
//! name wins anything. `wi_bfb9a_rival_spec_operation_test::a_non_parametric_carriers_operation_is_not_a_spec_op`
//! is: a namespace declaring its own `mod` is what a `%` written in that namespace
//! reaches, ASSERTED BY VALUE (99, not 1). And the refusal takes only ten of the tier's
//! sixty-two names — `the_refusal_population_is_the_ten_spec_operations` declares all
//! sixty-two free-standing in one load and asserts which ten come back.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Load the full stdlib plus `extra`, returning load/type error strings ([] = clean).
fn load_stdlib_errors(extra: &str) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// THIS TEST'S POLARITY WAS INVERTED BY WI-20260824-BFB9A, and the inversion is the
/// point rather than an edit made in passing.
///
/// It used to assert that a free-standing `operation eq` LOADS CLEAN — the property
/// WI-521 bought by making the implicit prelude a lowest-precedence fallback instead of
/// a flat `<global>` import (under which the use site saw both the imported `eq` and the
/// `<global>` one and reported `Ambiguous`, the footgun WI-476's collision blocklist
/// worked around). BFB9A makes that assertion FALSE on purpose: the rival SYMBOL is now
/// the thing refused, so the shadowing the old test measured has nothing left to
/// measure.
///
/// THIS IS THE ROW THAT MEASURES BFB9A, and the control runs the way round this
/// sentence says: back `check_rival_spec_operations` out and `errs` is EMPTY, so the
/// first assertion below FAILS. (Saying it the other way round — "back the refusal out
/// and this test passes again" — would describe the DELETED
/// `user_eq_shadows_prelude_without_ambiguity`, and a maintainer reverting the change
/// would predict green, get red, and conclude the guard was dead.)
///
/// WI-521's own claim is NOT re-asserted here, and that is deliberate. "The prelude is
/// never ambiguous against a user name" is false one scope over — see the header, and
/// the `<global>` row it names — so a `!contains("Ambiguous")` assertion would read as a
/// general property and be wrong. The message-content assertion below is what this row
/// can actually support.
#[test]
fn a_free_standing_eq_rivalling_the_spec_op_is_refused() {
    let src = r#"
namespace test.wi521.mymod
  import anthill.prelude.{Bool, Int64}
  operation eq(x: Int64, y: Int64) -> Bool = true
end
namespace test.wi521.user
  import anthill.prelude.{Bool, Int64}
  import test.wi521.mymod.{eq}
  operation use_eq(x: Int64) -> Bool = eq(x, x)
end
"#;
    let errs = load_stdlib_errors(src);
    assert!(
        errs.iter().any(|e| e
            .contains("would declare a second symbol of that name")
            && e.contains("anthill.prelude.PartialEq.eq")
            && e.contains("anthill.prelude.PartialEq'")),
        "a free-standing `eq` must be refused, naming both the spec OPERATION it rivals \
         and the SPEC that owns it — the message deliberately does NOT prescribe a \
         `provides` recipe, because two earlier wordings each prescribed something that \
         does not load (see `rival_spec_operation_message`); got: {errs:?}"
    );
    assert_eq!(
        errs.len(),
        1,
        "ONE mistake, ONE message — the rule is about the NAME, so a second rival \
         message (or a per-declaration-site duplicate) is a regression; got: {errs:?}"
    );
}

/// Bare prelude operators resolve with NO import line — the fallback supplies them.
#[test]
fn bare_prelude_names_resolve_without_import() {
    let src = r#"
namespace test.wi521.use
  import anthill.prelude.{Int64, Bool}
  operation plus(x: Int64, y: Int64) -> Int64 = add(x, y)
  operation same(x: Int64, y: Int64) -> Bool = eq(x, y)
end
"#;
    let errs = load_stdlib_errors(src);
    assert!(
        errs.is_empty(),
        "bare prelude `add` / `eq` must resolve without importing them; got: {errs:?}"
    );
}
