//! WI-525 — NAF allowedness / contract-binding discipline for `<=>` (proposal
//! 049, build step 5). Two static load-time checks ("know errors early"):
//!
//!   Part A — a `<=>` (unify) goal under `not(...)` binds, and NAF on a
//!   non-ground goal is unsound. Every variable in a negated unify must be
//!   bound by an EARLIER positive goal, else `UnsafeNegatedUnify`. Anonymous
//!   `?` placeholders are exempt (existentially local — they can never be bound
//!   earlier, so flagging them would reject the legitimate "x is not of shape
//!   f(_)" idiom).
//!
//!   Part B — a binding `<=>` / `let` (both lower to `unify(?v, e)`) in a
//!   contract position (operation `requires` / `ensures`, or a `constraint`
//!   body) is rejected with `BindingInContract`: a contract must TEST (`=`),
//!   never bind. A `unify` under `not(...)` is a test (NAF), not a binding, and
//!   is left alone.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::parse;

fn load_capturing_errors(extra: &str) -> (KnowledgeBase, Vec<LoadError>) {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).unwrap_or_else(|e| panic!("parse extra: {e:?}")));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => (kb, vec![]),
        Err(errs) => (kb, errs),
    }
}

fn errors_text(errs: &[LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

fn naf_errors(errs: &[LoadError]) -> Vec<&LoadError> {
    errs.iter().filter(|e| matches!(e, LoadError::UnsafeNegatedUnify { .. })).collect()
}

fn contract_errors(errs: &[LoadError]) -> Vec<&LoadError> {
    errs.iter().filter(|e| matches!(e, LoadError::BindingInContract { .. })).collect()
}

// ── Part A: negated unify under `not` ───────────────────────────────────

#[test]
fn negated_unify_with_unbound_var_errors() {
    // `?x <=> 5` binds `?x` positively; `not(?y <=> ?x)` then unifies under
    // negation with `?y` never bound by any earlier positive goal → unsound NAF.
    let src = r#"
        namespace wi525.parta_bad
          rule p(?x)
            :- ?x <=> 5, not(?y <=> ?x)
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let naf = naf_errors(&errs);
    assert!(
        !naf.is_empty(),
        "expected an UnsafeNegatedUnify error for the unbound `?y`; got:\n{}",
        errors_text(&errs),
    );
    assert!(
        naf.iter().any(|e| matches!(e, LoadError::UnsafeNegatedUnify { var_name, .. } if var_name == "y")),
        "the offending variable should be named `y`; got:\n{}",
        errors_text(&errs),
    );
}

#[test]
fn negated_unify_all_vars_bound_first_loads() {
    // Both `?x` and `?y` are bound by earlier positive unifies, so the negated
    // `?y <=> ?x` is range-restricted and sound — no NAF error.
    let src = r#"
        namespace wi525.parta_ok
          rule p(?x, ?y)
            :- ?x <=> 5, ?y <=> 6, not(?y <=> ?x)
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(
        naf_errors(&errs).is_empty(),
        "all negated-unify vars are bound earlier — expected no UnsafeNegatedUnify; got:\n{}",
        errors_text(&errs),
    );
}

#[test]
fn negated_unify_anonymous_placeholder_errors() {
    // `?x` is bound, but the second operand is the anonymous `?` — itself an
    // unbound variable. anthill's NAF requires a ground inner goal, so
    // `not(?x <=> ?)` would flounder: the anonymous var is NOT exempt.
    let src = r#"
        namespace wi525.parta_anon
          rule p(?x)
            :- ?x <=> 5, not(?x <=> ?)
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(
        !naf_errors(&errs).is_empty(),
        "an anonymous `?` under a negated unify is itself unbound — expected an \
         UnsafeNegatedUnify; got:\n{}",
        errors_text(&errs),
    );
}

#[test]
fn negated_unify_underscore_named_var_errors() {
    // Regression: `?_` is a NAMED (shared) variable that happens to intern to the
    // same `"_"` string as the anonymous `?`. It must NOT be silently exempted —
    // it is a genuine unbound var under a negated unify, exactly like `?y`.
    let src = r#"
        namespace wi525.parta_underscore
          rule p(?x)
            :- ?x <=> 5, not(?_ <=> ?x)
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(
        !naf_errors(&errs).is_empty(),
        "a named `?_` under a negated unify is unbound — expected an \
         UnsafeNegatedUnify (must not be exempted by the `_` name); got:\n{}",
        errors_text(&errs),
    );
}

#[test]
fn positive_unify_unbound_var_loads() {
    // A POSITIVE `<=>` binds freely — only the negated case is disciplined.
    let src = r#"
        namespace wi525.parta_pos
          rule p(?v)
            :- ?v <=> 7
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(
        naf_errors(&errs).is_empty(),
        "a positive unify is unrestricted — expected no UnsafeNegatedUnify; got:\n{}",
        errors_text(&errs),
    );
}

// ── Part B: binding `<=>` / `let` in a contract ─────────────────────────

#[test]
fn binding_unify_in_ensures_errors() {
    let src = r#"
        namespace wi525.ensures_bad
          sort S
            sort T = ?
            operation op(x: T) -> T ensures result <=> x
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let contract = contract_errors(&errs);
    assert!(
        contract.iter().any(|e| matches!(e, LoadError::BindingInContract { position, .. } if position == "ensures")),
        "expected a BindingInContract(ensures) error for `ensures result <=> x`; got:\n{}",
        errors_text(&errs),
    );
}

#[test]
fn let_in_ensures_errors() {
    // `let ?z = x` is directed sugar for `?z <=> x` — it binds, so it is
    // rejected in a contract exactly like a bare `<=>`.
    let src = r#"
        namespace wi525.let_bad
          sort S
            sort T = ?
            operation op(x: T) -> T ensures let ?z = x
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(
        !contract_errors(&errs).is_empty(),
        "expected a BindingInContract error for `ensures let ?z = x`; got:\n{}",
        errors_text(&errs),
    );
}

#[test]
fn binding_unify_in_requires_errors() {
    let src = r#"
        namespace wi525.requires_bad
          sort S
            sort T = ?
            operation op(x: T) -> T requires ?z <=> x
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(
        contract_errors(&errs).iter().any(|e| matches!(e, LoadError::BindingInContract { position, .. } if position == "requires")),
        "expected a BindingInContract(requires) error for `requires ?z <=> x`; got:\n{}",
        errors_text(&errs),
    );
}

#[test]
fn binding_unify_in_constraint_errors() {
    let src = r#"
        namespace wi525.constraint_bad
          fact thing(id: 1)
          constraint c1 :- thing(id: ?x), ?x <=> 5
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(
        contract_errors(&errs).iter().any(|e| matches!(e, LoadError::BindingInContract { position, .. } if position == "constraint")),
        "expected a BindingInContract(constraint) error for a `<=>` in a constraint body; got:\n{}",
        errors_text(&errs),
    );
}

#[test]
fn eq_test_in_ensures_loads() {
    // `=` is `eq` — a pure TEST, never binds — so it is the correct contract
    // form and must NOT trip the binding check.
    let src = r#"
        namespace wi525.ensures_ok
          sort S
            sort T = ?
            operation op(x: T) -> T ensures result = x
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(
        contract_errors(&errs).is_empty(),
        "an `=` (eq) test in a contract is fine — expected no BindingInContract; got:\n{}",
        errors_text(&errs),
    );
}
