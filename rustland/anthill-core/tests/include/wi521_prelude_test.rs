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
//! driven by `wi_kd9sw_minted_operator_address_test::a_free_standing_spec_op_name_is_legal_again`
//! (WI-20260825-KD9SW: such a declaration is legal now — it captures nothing).
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
fn a_free_standing_eq_no_longer_rivals_the_spec_op() {
    // INVERTED BY WI-20260825-KD9SW. This row used to assert that a free-standing
    // `operation eq` was REFUSED, because it would silence the implicit tier for a minted
    // `=`. The mint now names `..anthill.prelude.PartialEq.eq` outright, so there is no
    // tier entry left to silence, the capture is unrepresentable rather than refused, and
    // `load::check_rival_spec_operations` — this row's whole subject — is deleted.
    //
    // THE FIXTURE IS UNCHANGED so the inversion is visible: the same program that drew one
    // rival message now loads clean. That the OPERATOR keeps its meaning anyway is
    // `wi_kd9sw_minted_operator_address_test::an_import_can_no_longer_retarget_an_operator`,
    // and that such a declaration is legal is
    // `…::a_free_standing_spec_op_name_is_legal_again`.
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
        errs.is_empty(),
        "a free-standing `eq` contests nothing now that `=` carries its address; \
         got: {errs:?}"
    );
}

/// Bare prelude names resolve with NO import line — the fallback supplies them.
///
/// THE NAMES HERE ARE NOT THE SPEC OPERATIONS ANY MORE (WI-20260825-KD9SW). `add` / `eq`
/// used to be this row's subject and are now the counter-example: the twelve left the
/// implicit tier when a minted operator started naming its target outright, so writing
/// one bare is an ordinary unresolved name. `cons` / `some` / `not` are what the tier
/// still carries, so they are what this row measures — and the arm below pins the split,
/// which is what stops the row from quietly becoming a tautology. Found by
/// `/code-review`: an earlier cut of this ticket left the old fixture in place with
/// imports added, so the test's own name asserted the opposite of what it ran.
#[test]
fn bare_prelude_names_resolve_without_import() {
    let src = r#"
namespace test.wi521.use
  import anthill.prelude.{Int64, List, Option}
  operation one() -> List[T = Int64] = cons(head: 1, tail: nil)
  operation just() -> Option[T = Int64] = some(value: 7)
end
"#;
    let errs = load_stdlib_errors(src);
    assert!(
        errs.is_empty(),
        "`cons` / `nil` / `some` / `none` are still on the tier and must resolve with no \
         import naming them; got: {errs:?}"
    );

    // THE SPLIT, and the half that makes the row above mean something: a spec operation
    // is NOT on the tier, so the byte-identical treatment of `add` is a load error.
    let spec_op = r#"
namespace test.wi521.specop
  import anthill.prelude.{Int64}
  operation plus(x: Int64, y: Int64) -> Int64 = add(x, y)
end
"#;
    let errs = load_stdlib_errors(spec_op);
    assert!(
        errs.iter().any(|e| e.contains("add")),
        "a bare `add` must NOT resolve — the tier no longer carries it, and a minted `+` \
         needs no tier because it names `..anthill.prelude.Additive.add` outright; \
         got: {errs:?}"
    );
}
