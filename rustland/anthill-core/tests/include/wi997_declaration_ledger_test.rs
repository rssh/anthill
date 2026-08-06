//! WI-997 / proposal 059 R1 — A TYPE IS DEFINED ONCE.
//!
//! WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT: every `*_is_refused` test
//! below. The `*_still_loads` tests pass EITHER WAY BY DESIGN — they are the
//! control for the ledger's KEY, not a measure of the rule.
//!
//! THE KEY'S CONTROL, MEASURED by mutation rather than argued. Two candidate keys
//! are both "as written" and both work: `(scope, local name)` — what ships —
//! and the nested qualified name pass 1 computes (`…Vec3.Vec3` for the eponymous
//! constructor, since the collapse has not happened yet at that point). The key
//! that FAILS is the address the declaration ENDS AT — the qualified name of the
//! symbol pass 1 produces, i.e. after §6.3 collapses the eponymous constructor
//! onto its sort (WI-926). Keyed that way the STDLIB ITSELF STOPS LOADING, at
//! exactly the 4 eponymous sites the proposal predicted:
//!
//! ```text
//! type 'anthill.geometry.Vec3'      declared more than once: `sort` 45:3, `entity` 46:5
//! type 'anthill.prelude.Duration'   declared more than once: `sort`  2:1, `entity`  3:3
//! type 'anthill.prelude.Timestamp'  declared more than once: `sort`  7:1, `entity`  8:3
//! type 'anthill.prelude.TotalFloat' declared more than once: `sort` 27:1, `entity` 30:3
//! ```
//!
//! So `eponymous_sort_still_loads` is not decoration: it is the row that fails
//! first if anyone re-keys this on a symbol.

use anthill_core::eval::Value;

/// §6.3's eponymous constructor — the shape the key exists to protect.
/// 4 real sites in the corpus (Vec3, TotalFloat, Duration, Timestamp).
#[test]
fn eponymous_sort_still_loads() {
    const SRC: &str = r#"
namespace wi997.epo
  import anthill.prelude.Int64
  sort Vec3
    entity Vec3(x: Int64)
  end
  operation drive() -> Int64 = Vec3(x: 7).x
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    assert!(
        matches!(interp.call("wi997.epo.drive", &[]), Ok(Value::Int(7))),
        "the eponymous constructor must stay legal AND keep constructing",
    );
}

/// A sort and a namespace at one address — 059 R2's whole mechanism. The
/// namespace is not a type, so R1 must not see a pair here.
#[test]
fn secondary_entry_still_loads() {
    const SRC: &str = r#"
namespace wi997.sec
  import anthill.prelude.Int64
  sort Rec
    entity Rec(n: Int64)
  end
  namespace Rec
    operation twice(r: Rec) -> Int64 = r.n
  end
  operation drive() -> Int64 = Rec(n: 5).twice()
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    assert!(
        matches!(interp.call("wi997.sec.drive", &[]), Ok(Value::Int(5))),
        "a secondary entry adds members without redefining the type",
    );
}

/// THE HARM R1 EXISTS FOR: before this, the second body silently REOPENED the
/// ADT — both variants constructed and the second body's members dispatched.
#[test]
fn reopening_a_closed_adt_is_refused() {
    const SRC: &str = r#"
namespace wi997.reopen
  import anthill.prelude.Int64
  sort Colour
    entity Red(v: Int64)
  end
  sort Colour
    entity Blue(v: Int64)
  end
end
"#;
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(SRC),
        &["type 'Colour' is declared more than once in scope 'wi997.reopen': `sort` at 4:3, `sort` at 7:3"],
    );
}

/// §6.3 makes these two SPELLINGS OF ONE DECLARATION, so as siblings they are
/// the same error. This is also the shape WI-979 left failing loudly for an
/// unrelated reason (the missing enclosing-scope link); R1 is why that link must
/// NOT be supplied.
#[test]
fn entity_and_sort_siblings_are_refused() {
    const SRC: &str = r#"
namespace wi997.sib
  import anthill.prelude.Int64
  entity Rec(n: Int64)
  sort Rec
    operation peek(r: Rec) -> Int64 = r.n
  end
end
"#;
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(SRC),
        &[
            // The R1 refusal itself, naming BOTH keywords and BOTH lines.
            "type 'Rec' is declared more than once in scope 'wi997.sib': `entity` at 4:3, `sort` at 5:3",
            // …then the three PRE-EXISTING errors of this shape, which R1 does not
            // change and must not be read as caused by it: pass 1 gates the
            // enclosing-scope parent link on the declaration being NEW, and a
            // free-standing `entity` created no scope for the later `sort` body to
            // inherit, so the body resolves nothing from outside itself (WI-979 left
            // this loud deliberately — R1 is why the link must not be supplied).
            "unresolved name 'Int64' in scope 'peek'",
            "unresolved name 'Rec' in scope 'peek'",
            "no such member (dot dispatch)",
        ],
    );
}

/// `enum` + `enum`, and the message must name the keyword ACTUALLY WRITTEN —
/// both spellings load identically, so nothing after the parse can recover it.
#[test]
fn duplicate_enum_is_refused_and_named_as_enum() {
    const SRC: &str = r#"
namespace wi997.enu
  import anthill.prelude.Int64
  enum Colour
    entity Red
  end
  enum Colour
    entity Blue
  end
end
"#;
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(SRC),
        &["type 'Colour' is declared more than once in scope 'wi997.enu': `enum` at 4:3, `enum` at 7:3"],
    );
}

/// ACROSS FILES — the case that makes the rule worth having, and the reason the
/// ledger spans every file and the message pre-renders both locations instead of
/// riding `LoadError::Located` (which can name only one file).
#[test]
fn duplicate_across_two_files_is_refused_naming_both() {
    const A: &str = r#"
namespace wi997.xf
  import anthill.prelude.Int64
  sort Rec
    entity Rec(n: Int64)
  end
end
"#;
    const B: &str = r#"
namespace wi997.xf
  import anthill.prelude.Int64
  sort Rec
    entity Other(n: Int64)
  end
end
"#;
    let errs = match crate::common::try_load_kb_with_files(&[A, B]) {
        Err(e) => e,
        Ok(_) => panic!("a cross-file duplicate type must be refused, but the load succeeded"),
    };
    let joined = errs.join("\n");
    assert!(
        joined.contains("type 'Rec' is declared more than once"),
        "cross-file duplicate must be refused; got:\n{joined}",
    );
    // BOTH sites named — one location would leave the author hunting the other file.
    assert_eq!(
        joined.matches("`sort` at").count(),
        2,
        "both declarations must be named; got:\n{joined}",
    );
}

/// The scope is part of the key, so the SAME local name in two different scopes
/// is not a duplicate. Without this the rule would refuse most of the corpus.
#[test]
fn same_name_in_two_scopes_still_loads() {
    const SRC: &str = r#"
namespace wi997.a
  import anthill.prelude.Int64
  sort Rec
    entity Rec(n: Int64)
  end
end

namespace wi997.b
  import anthill.prelude.Int64
  sort Rec
    entity Rec(n: Int64)
  end
  operation drive() -> Int64 = Rec(n: 3).n
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    assert!(
        matches!(interp.call("wi997.b.drive", &[]), Ok(Value::Int(3))),
        "one name in two scopes is two types, not a duplicate",
    );
}
