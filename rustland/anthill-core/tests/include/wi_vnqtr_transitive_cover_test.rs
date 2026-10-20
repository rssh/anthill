//! WI-20260911-VNQTR, found on the way — A CALLER'S CLAUSE COVERS A FORWARD THROUGH ITS CHAIN TO
//! ANY DEPTH.
//!
//! `m(a: ?t, b: ?t) -> Bool requires Ord[T = ?t] = same(a, b)`, over `same[B](a: B, b: B)
//! requires PartialEq[T = B]`, hands `same` the caller's own `?t`. `Ord`'s dictionary holds a
//! `PartialEq[T = ?t]` three levels down (`Ord` provides `WeakOrd`, which requires `Eq`, which
//! requires `PartialEq`), and `PartialEq.eq(a, b)` written in the same body reached it. The
//! forward searched one level (`build_dep_projection`'s Strategy 2) and then tried to build the
//! dictionary at a parameter, so the bracketed call was refused, "declares no `requires` that
//! covers it" — and the inline one loaded only because the refusal did not see its variable
//! (`wi_vnqtr_inline_param_forward_test`); with the variable seen, it was refused alike.
//! Strategy 2c asks the resolver's search for a sub-goal (`scope_chain_cover`) under the
//! call's σ, behind the construction a provision answers, and forwards the projection it
//! finds.
//!
//! BACK-OUT, a temporary switch in one build, over the whole `wi_tests` binary (7552 rows) —
//! Strategy 2c off: **2 red**, [`a_clause_covers_a_forward_through_its_chain`] and
//! [`a_cover_two_levels_down_is_read`], and nothing else.
//!
//! PASSES EITHER WAY BY DESIGN, said at its site: [`a_cover_one_level_down_was_always_read`].

use crate::common::load_errors_of;
use crate::wi_vnqtr_inline_param_forward_test::answers;

fn program(ns: &str, clause: &str, sig: &str) -> String {
    format!(
        r#"
namespace test.vnqtr.cover.{ns}
  import anthill.prelude.{{Int64, Bool, PartialEq, Eq, WeakOrd, Ord}}
  operation same[B](a: B, b: B) -> Bool requires PartialEq[T = B] = PartialEq.eq(a, b)
  operation {sig} -> Bool requires {clause} = same(a, b)
  operation yes() -> Bool = m(1, 1)
  operation no() -> Bool = m(1, 2)
end
"#
    )
}

/// The ticket's shape: `requires Ord` covers the forward of `PartialEq`, and the dictionary
/// it forwards answers — in either spelling of the parameter.
#[test]
fn a_clause_covers_a_forward_through_its_chain() {
    for (ns, sig) in [("inline", "m(a: ?t, b: ?t)"), ("bracket", "m[U](a: U, b: U)")] {
        let param = if ns == "inline" { "?t" } else { "U" };
        let src = program(ns, &format!("Ord[T = {param}]"), sig);
        assert_eq!(
            answers(&src, &[&format!("test.vnqtr.cover.{ns}.yes"), &format!("test.vnqtr.cover.{ns}.no")]),
            ["true", "false"],
            "{ns}"
        );
    }
}

/// Two levels down: `WeakOrd` requires `Eq`, which requires `PartialEq`.
#[test]
fn a_cover_two_levels_down_is_read() {
    let src = program("weak", "WeakOrd[T = U]", "m[U](a: U, b: U)");
    assert_eq!(
        answers(&src, &["test.vnqtr.cover.weak.yes", "test.vnqtr.cover.weak.no"]),
        ["true", "false"]
    );
}

/// CONTROL, passes either way: one level down, `Eq` requires `PartialEq`, which Strategy 2
/// always read.
#[test]
fn a_cover_one_level_down_was_always_read() {
    let src = program("eq", "Eq[T = U]", "m[U](a: U, b: U)");
    assert_eq!(load_errors_of(&src), Vec::<String>::new());
    assert_eq!(
        answers(&src, &["test.vnqtr.cover.eq.yes", "test.vnqtr.cover.eq.no"]),
        ["true", "false"]
    );
}
