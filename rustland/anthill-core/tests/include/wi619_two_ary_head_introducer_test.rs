//! WI-619 — the WI-582 type-variable-introducer scan (`collect_rule_tvar_names`)
//! must recognize an equational rule head by its connective FUNCTOR
//! (`eq`/`unify`/`struct_eq`), not by `pos_args.len() == 2`.
//!
//! The old arity gate read the head's `[t]` introducer off `pos_args[0]` for
//! ANY 2-positional-arg head — correct for an equational head `keep[T](…) = rhs`
//! (whose LHS operand is `pos_args[0]`), but WRONG for a plain 2-ary PREDICATE
//! head `same_ty[t](?x, ?y)`, whose `pos_args[0]` is the first ARGUMENT `?x`.
//! There the `[t]` introducer was silently dropped: the `:- Spec[t]` guard never
//! folded, the tvar was never bounded, and the rule quietly lost its WI-582
//! desugar. 1-ary and 3-ary heads read off the head node and worked; exactly
//! 2-ary misfired (found empirically during the WI-618 /code-review).
//!
//! These tests pin the 2-ary case to the SAME behavior the WI-618 suite already
//! verifies for 1-ary heads (`same_ty[t](?y)`), plus a guard that the equational
//! 2-ary head — the shape the old arity gate was actually written for — still
//! reads its introducer off the LHS.

use crate::common::LAMBDA_HINT as HINT;

fn load_errors(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

/// A 2-ary predicate head with an UNBOUNDED `[t]` introducer must now get the
/// WI-582 "no bounding guard" diagnostic — proof the introducer is collected.
/// Before the fix this loaded with ZERO errors (the introducer was read off the
/// argument `?x`, found nothing, and the whole WI-582 scan was skipped).
#[test]
fn two_ary_predicate_head_unbounded_introducer_is_diagnosed() {
    let errs = load_errors(
        r#"
namespace test.wi619.unbounded
  import anthill.prelude.{Int64, Eq}
  rule same_ty[t](?x, ?y)
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains("no bounding guard") && e.contains('t')),
        "a 2-ary head's `[t]` introducer must be collected (and, unbounded, \
         diagnosed); got: {errs:?}",
    );
}

/// A 2-ary predicate head with a `[t]` introducer AND its bounding guard
/// `:- Eq[t]` must load clean: the introducer is collected, so the guard folds
/// into `t`'s bound and `t` resolves. Before the fix the guard stayed a body
/// goal and `t` surfaced as `unresolved name 't'`.
#[test]
fn two_ary_predicate_head_bounded_guard_folds_and_loads() {
    let errs = load_errors(
        r#"
namespace test.wi619.bounded
  import anthill.prelude.{Int64, Eq}
  rule same_ty[t](?x, ?y) :- Eq[t]
end
"#,
    );
    assert!(
        errs.is_empty(),
        "a 2-ary head's bounded `[t]` guard must fold and the rule load clean; \
         got: {errs:?}",
    );
}

/// The exact scenario the bug was found under (WI-618 /code-review): a lowercase
/// `[t]` introducer on a 2-ary head, used under a body arrow `?y <=> (t -> t)`.
/// The introducer must be collected so `t` is exempted from the bare-arrow-typo
/// walk (it is a bounded rule type-var, not a lambda binder). Before the fix
/// the uncollected `t` was flagged as a keyword-less-lambda typo. This is the
/// 2-ary analog of WI-618's `lowercase_rule_type_var_arrow_still_loads`.
#[test]
fn two_ary_head_tvar_under_body_arrow_still_loads() {
    let errs = load_errors(
        r#"
namespace test.wi619.tvararrow
  import anthill.prelude.{Int64, Eq}
  rule same_ty[t](?x, ?y)
    :- Eq[t], ?z <=> (t -> t)
end
"#,
    );
    assert!(
        !errs.iter().any(|e| e.contains(HINT)),
        "a bounded lowercase rule type-var on a 2-ary head must be exempt from \
         the bare-arrow typo check; got: {errs:?}",
    );
}

/// Regression guard for the shape the old arity gate was written for: an
/// equational 2-ary head `keep[T](…) = rhs` reads its `[T]` introducer off the
/// LHS operand (`pos_args[0]` of the `eq` node), not the whole `eq(lhs, rhs)`.
/// The functor-based recognition must keep this working — the `[T]` folds via
/// `:- Summable[T]` and installs as the `?x: T` bound on the `[simp]` rule.
#[test]
fn equational_two_ary_head_reads_introducer_off_lhs() {
    let kb = crate::common::load_kb_with(
        r#"
namespace test.wi619.eqhead
  import anthill.prelude.{Int64, Bool, Eq}
  import test.wi619.eqhead.Lib.{keep}

  sort Summable
    sort T = ?
    requires Eq[T]
  end

  fact Summable[T = Int64]

  sort Lib
    sort A = ?
    operation {
      keep(x: A, y: A) -> A
    }
    rule {
      keep_id: keep[T](?x: T, ?y) = ?x :- Summable[T] [simp]
    }
  end
end
"#,
    );
    let rid = kb
        .rule_id_by_qn("test.wi619.eqhead.Lib.keep_id")
        .expect("equational keep_id rule loaded");
    let bounds = kb.rule_type_bounds(rid);
    assert_eq!(
        bounds.len(),
        1,
        "the equational 2-ary head must still fold `[T]` and install the one \
         `?x: T` bound; got {bounds:?}",
    );
    // ?x is the first head variable; the DeBruijn index is arity-1-position = 1.
    assert_eq!(bounds[0].0, 1, "the bound must key ?x's DeBruijn index (1)");
}
