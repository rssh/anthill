//! Soundness tests for the typer's `match` branch-type handling.
//!
//! `MatchFinal` (kb/typing.rs) sets the match-expression's result type
//! to the FIRST branch's type and ignores the rest:
//!
//! ```ignore
//! let mut result_ty: Option<TermId> = None;
//! for (i, body_r) in branch_results.into_iter().enumerate() {
//!     if result_ty.is_none() {
//!         result_ty = Some(body_r.ty);   // first branch wins
//!     }
//!     ...
//! }
//! ```
//!
//! There is no join (lub) across branches anywhere in the typer. When a
//! `match` is in *synthesis* mode (no expected type — e.g. the value of
//! an unannotated `let`), the non-first branches are type-checked
//! against `expected = None`, i.e. against nothing. So a branch whose
//! body has a type incompatible with the others is never caught.
//!
//! The two branch-clash tests assert the SOUND behavior (the clash must
//! be rejected) and therefore FAIL today — they demonstrate the bug.
//! They are `#[ignore]`d so the default suite stays green; run with
//! `--ignored` to watch them fail, and remove the `#[ignore]` once
//! join/per-branch checking lands. The anchor test passes today.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra source → load errors (empty Vec on clean load).
fn try_load(extra: &str) -> Vec<load::LoadError> {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).err().unwrap_or_default()
}

/// A `match` in synthesis position (value of an unannotated `let`)
/// whose branches return incompatible types — `Int` vs `String`, which
/// have no common supertype in the (top-less) Type lattice. A sound
/// typer MUST reject this. The current typer takes the first branch's
/// type (`Int`) for the whole expression and never checks the `String`
/// branch, so it loads clean — unsound.
///
/// ASSERTS THE SOUND BEHAVIOR — fails today (demonstrates the bug),
/// goes green when join/per-branch checking lands. `#[ignore]` keeps
/// the default suite green; run `--ignored` to see it fail.
#[test]
#[ignore = "known soundness gap: match takes branch-0 type, ignores other branches (no lub)"]
fn match_synthesis_rejects_incompatible_branches() {
    let src = r#"
namespace test.match_cheat.synth
  import anthill.prelude.{Int, String}

  sort Toggle
    entity on
    entity off
  end

  sort Driver
    operation pick(t: Toggle) -> Int =
      let x = match t
        case on  -> 1
        case off -> "hello"
      x
  end
end
"#;
    let errs = try_load(src);

    // SOUND expectation: the Int/String branch clash must be rejected.
    // Fails today because the typer types the match as branch 0 (Int)
    // and never validates the String branch.
    assert!(
        !errs.is_empty(),
        "unsound: match with incompatible branches (Int vs String) loaded clean — \
         the String branch was never type-checked (first-branch-wins)",
    );
}

/// Broader than synthesis mode: even a `match` placed directly as an
/// operation body — where the declared return type `Int` flows into
/// every branch as `body_expected` — does NOT catch the `String`
/// branch. The op-body return-type check only inspects the *synthesized*
/// match type (branch 0, `Int`); `body_expected` reaches the branches
/// as an inference hint, not an enforced check. So the clash leaks here
/// too.
///
/// ASSERTS THE SOUND BEHAVIOR — fails today. `#[ignore]` as above.
#[test]
#[ignore = "known soundness gap: declared return type does not enforce per-branch checks"]
fn match_as_op_body_rejects_incompatible_branches() {
    let src = r#"
namespace test.match_cheat.checked
  import anthill.prelude.{Int, String}

  sort Toggle
    entity on
    entity off
  end

  sort Driver
    operation pick(t: Toggle) -> Int =
      match t
        case on  -> 1
        case off -> "hello"
  end
end
"#;
    let errs = try_load(src);

    // SOUND expectation: the String branch must fail against the
    // declared Int return type. Fails today — the return check only
    // sees branch 0 (Int).
    assert!(
        !errs.is_empty(),
        "unsound: match-as-op-body with a String branch loaded clean against an Int \
         return type — only branch 0 was checked",
    );
}

/// Anchor: the typer DOES enforce return types — a direct `String` body
/// in an `-> Int` operation is rejected. This rules out "nothing is
/// checked" as the explanation for the two tests above: the leak is
/// specifically the `match` first-branch-wins shortcut, not a missing
/// return-type check.
#[test]
fn direct_string_body_in_int_op_is_rejected() {
    let src = r#"
namespace test.match_cheat.anchor
  import anthill.prelude.{Int, String}

  sort Driver
    operation pick() -> Int =
      "hello"
  end
end
"#;
    let errs = try_load(src);
    assert!(
        !errs.is_empty(),
        "expected String body to be rejected against Int return type, but load was clean",
    );
}
