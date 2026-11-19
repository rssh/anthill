//! A PROVISION WRITTEN WITH NO `eq` IS GIVEN THE DERIVED MEMBER (WI-20261105-CBRD2, decided
//! with the user 2026-11-18). A composite whose `PartialEq` the loader derives is given the `eq`
//! a program would write; one whose author wrote `provides PartialEq` (or `Eq`) and no `eq` had
//! none, so a typed `=` at it named no member and was compared by its operands' values at run
//! time, as an equality no type reached is. It is given the same member now (kernel-language
//! §8.3), and every provision of `PartialEq` has one.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch (the written provisions given no member), then removed.
//! The control is the switch unset: every row passes.
//!
//! * [`a_typed_equality_at_a_written_provision_calls_its_member`] fails on the count, its
//!   answers unchanged.
//! * [`a_float_field_is_compared_through_its_eq`] fails on the answer: `fp(v: nan) = fp(v:
//!   nan)` held, compared by structure.
//! * [`a_sort_writing_its_own_eq_keeps_it`] passes either way by design: a sort that writes
//!   its `eq` is given none.
//! * [`a_parametric_written_provision_is_given_its_member_or_refused`] fails on the member and
//!   the count of the `:- PartialEq[T]` provision, and on the unconditional one, which loads.
//!   Its `:- Eq[T]` case passes either way by design: it is given no member.
//! * [`a_field_nothing_decides_refuses_the_provision`] fails: with no member given, the program
//!   loads (its `=` compared by its values). Measured too with the refusal alone backed out
//!   (the member given anyway): the load is refused in the derived members' own text, naming
//!   no file and no field.

use anthill_core::kb::resolve::untyped_equalities_by_this_thread;

use crate::common::{load_errors_of, load_kb_with, load_stdlib_kb, query_pattern_term};

const SRC: &str = r#"
namespace test.cbrd2.wpm
  import anthill.prelude.{Int64, Bool, Float, Eq, PartialEq, Option}
  import anthill.prelude.Option.{some}
  import anthill.prelude.PartialEq.{eq, neq}
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
  end
  sort Fp
    entity fp(v: Float)
    provides PartialEq[T = Fp]
  end
  sort Loose
    entity loose(n: Int64)
    provides PartialEq[T = Loose]
    operation eq(a: Loose, b: Loose) -> Bool = true
  end
  rule eqW() :- Green = Red
  rule neqW() :- neq(Green, Red)
  rule sameW() :- Red = Red
  rule eqOpt() :- some(Green) = some(Red)
  rule nanSame() :- fp(v: Float.div(0.0, 0.0)) = fp(v: Float.div(0.0, 0.0))
  rule oneSame() :- fp(v: 1.0) = fp(v: 1.0)
  rule looseSame() :- loose(n: 1) = loose(n: 2)
end
"#;

/// Whether `pattern` holds and the equalities compared with no member while it ran, the shared
/// base loaded first so its own load is not counted.
fn holds_counting(kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str) -> (bool, usize) {
    drop(load_stdlib_kb());
    let goal = query_pattern_term(kb, &format!("test.cbrd2.wpm.{pattern}"));
    let before = untyped_equalities_by_this_thread();
    let got = kb.resolve(&[goal], &Default::default());
    let untyped = untyped_equalities_by_this_thread() - before;
    (got.iter().any(|s| s.is_definite()), untyped)
}

/// `=`, `neq` and an `Option` over the written `Color`: each calls a member.
#[test]
fn a_typed_equality_at_a_written_provision_calls_its_member() {
    let mut kb = load_kb_with(SRC);
    let mut untyped = Vec::new();
    for (pattern, want) in [("eqW()", false), ("neqW()", true), ("sameW()", true), ("eqOpt()", false)] {
        let (got, n) = holds_counting(&mut kb, pattern);
        assert_eq!(got, want, "`{pattern}`");
        untyped.push((pattern, n));
    }
    assert!(
        untyped.iter().all(|(_, n)| *n == 0),
        "equalities compared with no member: {untyped:?}"
    );
}

/// The member compares a `Float` field through `Float`'s `eq`, IEEE: `nan` is unequal to
/// itself, `1.0` equal.
#[test]
fn a_float_field_is_compared_through_its_eq() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(holds_counting(&mut kb, "nanSame()"), (false, 0), "`fp(v: nan) = fp(v: nan)`");
    assert_eq!(holds_counting(&mut kb, "oneSame()"), (true, 0), "`fp(v: 1.0) = fp(v: 1.0)`");
}

/// A sort that writes its `eq` keeps it: `Loose`'s holds of any two values.
#[test]
fn a_sort_writing_its_own_eq_keeps_it() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(holds_counting(&mut kb, "looseSame()"), (true, 0));
}

/// A parametric composite's written provision. With the condition its field needs, it is given
/// the member, which a typed `=` at it calls; with none, it is refused, naming the condition;
/// with one reaching `PartialEq` through another spec (`:- Eq[T]`), whose slot a member's
/// comparison at the parameter is not read through (as a written member's is not), it is given
/// none, and its `=` is an equality with no member: an error where it runs (kernel-language
/// §8.3, WI-20261105-CBRD2), neither rule answering — the control, counted.
#[test]
fn a_parametric_written_provision_is_given_its_member_or_refused() {
    let src = |ns: &str, cond: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, PartialEq, Eq}}
  import anthill.prelude.PartialEq.{{eq}}
  sort Bx
    sort T = ?
    entity bx(v: T)
    provides PartialEq[T = Bx[T = T]] {cond}
  end
  rule differ() :- bx(v: 1) = bx(v: 2)
  rule same() :- bx(v: 1) = bx(v: 1)
end
"#
        )
    };
    for (ns, cond, with_member) in [
        ("test.cbrd2.wpm.pc", ":- PartialEq[T]", true),
        ("test.cbrd2.wpm.pe", ":- Eq[T]", false),
    ] {
        let mut kb = load_kb_with(&src(ns, cond));
        assert_eq!(
            kb.try_resolve_symbol(&format!("{ns}.Bx.eq")).is_some(),
            with_member,
            "{ns}: the derived member"
        );
        let mut untyped = 0;
        for (rule, want) in [("differ()", false), ("same()", true)] {
            drop(load_stdlib_kb());
            let goal = query_pattern_term(&mut kb, &format!("{ns}.{rule}"));
            let before = untyped_equalities_by_this_thread();
            let (got, stats) = kb.resolve_with_stats(&[goal], &Default::default());
            untyped += untyped_equalities_by_this_thread() - before;
            let errored = stats.errors.iter().any(|e| e.message.contains("with no `eq` member"));
            assert_eq!(errored, !with_member, "{ns}: `{rule}` raises the error: {:?}", stats.errors);
            assert_eq!(got.iter().any(|s| s.is_definite()), want && with_member, "{ns}: `{rule}`");
        }
        assert_eq!(untyped == 0, with_member, "{ns}: {untyped} equalities compared with no member");
    }
    let errors = load_errors_of(&src("test.cbrd2.wpm.pu", ""));
    assert!(
        errors.iter().any(|e| e.contains("`test.cbrd2.wpm.pu.Bx` provides `PartialEq` with no condition")
            && e.contains("Write the provision with `:- PartialEq[T]`")),
        "{errors:?}"
    );
}

/// A written provision whose field has no equality (a function) can be given no member: the
/// load is refused, naming the carrier and the field.
#[test]
fn a_field_nothing_decides_refuses_the_provision() {
    let errors = load_errors_of(
        r#"
namespace test.cbrd2.wpm.fnf
  import anthill.prelude.{Int64, PartialEq}
  sort H
    entity h(f: (x: Int64) -> Int64)
    provides PartialEq[T = H]
  end
end
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("`test.cbrd2.wpm.fnf.H` provides `PartialEq` and writes no `eq`")
            && e.contains("its field `f`")),
        "{errors:?}"
    );
}
