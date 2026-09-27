//! WI-20260924-FS8M3 — a `provides` clause in a `namespace` at a type ALIAS's address is
//! refused, naming what the alias stands for.
//!
//! A clause names its provider by where it is written, so `namespace FSAlias provides
//! Store[State = WIS] … end` over `sort FSAlias = FileStore` filed the provision about
//! `FSAlias` — a name dispatch never searches — and `Store.peek(wis(n: 9))` loaded clean and
//! died at run time, "operation has no body". The user's decision (2026-09-27): refuse the
//! clause, not the entry — the entry's operations stay members at the alias's address
//! (kernel-language §5.1), and the clause is not read through to the target, since for an
//! alias that APPLIES its target that would claim the provision for every instantiation.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! MEASURED 2026-09-27, each back-out against this file alone:
//!
//! * Remove the alias arm of `load_provides_clause`: the four refusal rows fail — each
//!   loads clean — [`a_provision_at_a_bare_alias_address_is_refused`],
//!   [`a_provision_at_an_applied_alias_address_is_refused`],
//!   [`a_provision_at_an_alias_of_an_alias_names_the_sort`] and
//!   [`a_provision_in_a_file_loaded_before_its_alias_is_read_the_same`].
//! * Decide "exact" by the alias's FIRST link alone (`alias_heads[alias] == head`, the
//!   first cut's comparison of the written target with the chain's head, found by
//!   `/code-review`): the alias-of-alias row fails on its exact repair, and the applied
//!   and earlier-file rows fail too — a first link that names the head reads as exact
//!   even when it applies it.
//! * Decide "exact" off the per-declaration load record (`alias_targets`) instead of
//!   the scan: every row passes — see the earlier-file row for why.
//!
//! [`a_provision_at_the_sort_address_dispatches`] and
//! [`an_operation_at_an_alias_address_is_still_a_member`] pass under every back-out by
//! design: the refusal must reach neither the sort's own entry nor an entry's members.

use crate::common::{assert_refused_naming, interp_for, try_load_kb_with, try_load_kb_with_files};
use anthill_core::eval::Value;

/// `Store` over `State`, the sort `FileStore`, its alias `FSAlias`, the applied alias
/// `FSBox = Box[E = Int64]`, then a `namespace {entry}` holding `body`.
fn program(entry: &str, body: &str, goal: &str) -> String {
    format!(
        r#"
namespace t
  import anthill.prelude.{{Int64}}
  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end
  sort WIS
    entity wis(n: Int64)
  end
  sort FileStore
    entity fs(n: Int64)
  end
  sort FSAlias = FileStore
  sort Box
    sort E = ?
    entity box(e: E)
  end
  sort FSBox = Box[E = Int64]
  namespace {entry}
{body}
  end
  operation go() -> Int64 = {goal}
end
"#
    )
}

const PROVISION: &str =
    "    provides Store[State = WIS]\n    operation peek(s: WIS) -> Int64 = s.n";

fn run(src: &str) -> i64 {
    match interp_for(src).call("t.go", &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`t.go` must run to an Int64: {other:?}"),
    }
}

/// The control: the same entry at the sort's own address.
#[test]
fn a_provision_at_the_sort_address_dispatches() {
    assert_eq!(
        run(&program("FileStore", PROVISION, "Store.peek(wis(n: 9))")),
        9
    );
}

/// Was: a clean load, then "operation has no body" for `Store.peek`.
#[test]
fn a_provision_at_a_bare_alias_address_is_refused() {
    let errs = try_load_kb_with(&program("FSAlias", PROVISION, "1"))
        .err()
        .unwrap_or_default();
    assert_refused_naming(
        &errs,
        &[
            "a `provides` clause cannot stand in a `namespace` at 't.FSAlias'",
            "a type alias of 'FileStore'",
            "in a `namespace t.FileStore` entry",
        ],
        "provides at a bare alias's address",
    );
}

/// An applied alias is refused too, and the repair says what writing the clause at the
/// head would claim. Was: a clean load, then "operation has no body".
#[test]
fn a_provision_at_an_applied_alias_address_is_refused() {
    let errs = try_load_kb_with(&program("FSBox", PROVISION, "1"))
        .err()
        .unwrap_or_default();
    assert_refused_naming(
        &errs,
        &[
            "at 't.FSBox', a type alias of 'Box[E = Int64]'",
            "a clause there speaks for every 't.Box'",
        ],
        "provides at an applied alias's address",
    );
}

/// An alias OF an alias stands for exactly the sort at the end of the chain, so its repair
/// is the exact one, not the applied one (found by `/code-review`).
#[test]
fn a_provision_at_an_alias_of_an_alias_names_the_sort() {
    let src = program("A2", PROVISION, "1").replace(
        "  sort FSAlias = FileStore\n",
        "  sort FSAlias = FileStore\n  sort A2 = FSAlias\n",
    );
    let errs = try_load_kb_with(&src).err().unwrap_or_default();
    assert_refused_naming(
        &errs,
        &[
            "at 't.A2', a type alias of 'FSAlias'",
            "in a `namespace t.FileStore` entry",
        ],
        "provides at an alias of an alias",
    );
    assert!(
        !errs.join(" ").contains("speaks for every"),
        "an alias of an alias is not an application: {errs:?}"
    );
}

/// The entry itself stays legal: an operation declared there is a member at the alias's
/// address (§5.1), reached as `FSAlias.twice`.
#[test]
fn an_operation_at_an_alias_address_is_still_a_member() {
    let body = "    operation twice(x: FileStore) -> Int64 = 2";
    assert_eq!(run(&program("FSAlias", body, "FSAlias.twice(fs(n: 1))")), 2);
}

/// The entry in a FILE LOADED BEFORE the one declaring the alias it sits at: the refusal
/// and its repair (exact vs applied) are the same as with the entry written after.
///
/// PASSES EITHER WAY TODAY, by design and MEASURED (2026-09-27): `/code-review` suspected
/// the first cut, which read exactness off the per-declaration load record
/// (`alias_targets`), would misread a bare alias as applied when the entry loads first.
/// Backing the fix out to that reading, this test stays green — with the entry above the
/// alias in one file and in an earlier file alike — because every alias declaration is
/// recorded before any `provides` clause loads. The fix reads the scan instead
/// (`alias_chain_applies`), which is order-independent by construction; this row pins
/// that property against a change in load order.
#[test]
fn a_provision_in_a_file_loaded_before_its_alias_is_read_the_same() {
    let cases: [(&str, bool); 3] = [("FSAlias", true), ("A2", true), ("FSBox", false)];
    for (entry, exact) in cases {
        let block = format!("  namespace {entry}\n{PROVISION}\n  end\n");
        let declarations = program(entry, PROVISION, "1").replace(&block, "").replace(
            "  sort FSAlias = FileStore\n",
            "  sort FSAlias = FileStore\n  sort A2 = FSAlias\n",
        );
        let entry_file = format!("namespace t\n  import anthill.prelude.{{Int64}}\n{block}end\n");
        let errs = try_load_kb_with_files(&[&entry_file, &declarations])
            .err()
            .unwrap_or_default();
        assert_refused_naming(
            &errs,
            &[&format!("a `namespace` at 't.{entry}'")],
            &format!("provides at {entry}, in the earlier file"),
        );
        assert_eq!(
            errs.join(" ").contains("speaks for every"),
            !exact,
            "`{entry}` in the earlier file: exact = {exact}; got {errs:?}"
        );
    }
}
