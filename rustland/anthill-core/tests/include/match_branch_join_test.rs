//! Soundness tests for the typer's `match` branch-type handling (WI-287).
//!
//! `MatchFinal` (kb/typing.rs) used to set the match-expression's result
//! type to the FIRST branch's type and ignore the rest — there was no
//! join across branches anywhere in the typer. In *synthesis* mode
//! (no expected type — e.g. the value of an unannotated `let`) the
//! non-first branches were type-checked against `expected = None`, i.e.
//! against nothing, so a branch whose body type was incompatible with
//! the others was never caught.
//!
//! WI-287 made `compute_branch_join_type` account for every branch: in
//! synthesis mode the result is the join (a common supertype — not
//! strictly the lub) of the branch types and a clash with no common
//! supertype is rejected; in checked mode (an expected type flowed in)
//! every branch must conform to it. The two
//! branch-clash tests below assert that sound behavior and now act as
//! regression guards; the anchor test pins down that return-type
//! checking works in general, so the leak was specifically the old
//! first-branch-wins shortcut.

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
/// typer MUST reject this. WI-287 makes synthesis-mode `match` compute
/// the join of its branch types, so the `Int`/`String` clash is now a
/// type error instead of being silently typed as branch 0 (`Int`).
#[test]
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

/// Broader than synthesis mode: a `match` placed directly as an
/// operation body, where the declared return type `Int` flows in as the
/// match's expected type. Before WI-287 the op-body return-type check
/// only inspected the *synthesized* match type (branch 0, `Int`) and
/// `body_expected` reached the branches as a mere inference hint, so the
/// `String` branch leaked. Now `compute_branch_join_type` runs in checked
/// mode and rejects any branch that doesn't conform to the expected `Int`.
#[test]
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
