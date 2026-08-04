//! WI-956 item 4, the DIAGNOSTIC half — `member_owning_sorts_for_bare`'s parent gate.
//!
//! The typer-internal half of this ticket lives in `typing.rs`'s
//! `wi956_kind_gate_tests`: five readers that asked `kind_of(parent) == Some(Sort)`
//! now share one `impl_parent_sort_of_op`, which asks `has_kind`. This file owns the
//! one consequence a USER can see — the WI-565 hint that names the sort owning a bare
//! member call — because that is a MESSAGE, and message content belongs in a test
//! that reads the loader's own words.
//!
//! `kind_of` reports only the first-declared of a symbol's categories, so a sort whose
//! ENTITY role was registered first (the §6.3 `entity X(…)` sugar, then the same name
//! re-declared with a body) does not look like a sort to it — and the scan that
//! collects "which sorts declare a member with this name" dropped it, leaving the
//! author with the terse unknown-functor message instead of the sort they need.
//!
//! STDLIB LOADS: two, one per `#[test]`. The control is a matched pair — same program
//! twice, differing only in which of the two declarations of the owner comes first —
//! and neither row is evidence without the other.

/// The two declaration orders of one sort, and the hint must not depend on which was
/// written. `Wi956Owner` is declared `entity`-first here and `sort`-first in the
/// control below; everything else is identical, down to the member's name.
fn hint_for(owner_first: &str, owner_second: &str) -> String {
    let src = format!(
        r#"
namespace wi956.bare
  import anthill.prelude.Int64
{owner_first}
{owner_second}
  operation wi956Caller(n: Int64) -> Int64 = wi956Peek(n)
end
"#
    );
    let Err(errs) = crate::common::try_load_kb_with(&src) else {
        panic!(
            "a bare `wi956Peek` outside its owning sort must be refused — a member's \
             bare name is in scope only within the sort that declares it"
        );
    };
    errs.join("\n")
}

const SUGAR: &str = "  entity Wi956Owner(n: Int64)";
const BODY: &str = "  sort Wi956Owner\n    sort T = ?\n    operation wi956Peek(x: T) -> T\n  end";

/// THE FIX. With the `entity` sugar first, `Wi956Owner` registers as
/// `[Entity, Sort]` — `has_kind(Sort)` but `kind_of == Some(Entity)` — and under
/// `kind_of` the owner scan skipped it, so the author was told only that the functor
/// is unknown, with no mention of the sort that has the member.
///
/// CONTROL, MEASURED by restoring `kind_of(parent_sym) != Some(Sort)` in
/// `member_owning_sorts_for_bare`: this test fails, and the message it fails on is the
/// terse one (no `Wi956Owner`, no `receiver.` remedy). The sibling below passes either
/// way — it is the same program with the two declarations swapped, which is the whole
/// point: the diagnostic must not turn on source order.
#[test]
fn a_bare_member_of_an_entity_first_sort_still_names_its_owner() {
    let joined = hint_for(SUGAR, BODY);
    assert!(
        joined.contains("Wi956Owner"),
        "the hint must NAME the sort that declares `wi956Peek`; got:\n{joined}"
    );
}

/// The control: the identical program with `sort` written before `entity`, so
/// `kind_of` and `has_kind` agree. Passes on both sides of the fix by design — it is
/// here so that a regression which merely BREAKS the hint fails loudly, instead of
/// letting the pair above agree at "no owner named" for a new reason.
#[test]
fn the_same_sort_declared_sort_first_names_its_owner_too() {
    let joined = hint_for(BODY, SUGAR);
    assert!(
        joined.contains("Wi956Owner"),
        "the sort-first spelling has always named its owner; got:\n{joined}"
    );
}
