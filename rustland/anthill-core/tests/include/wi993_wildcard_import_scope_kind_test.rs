//! WI-993 — A WILDCARD IMPORT OF A NAME THAT IS NOT A SCOPE.
//!
//! `import a.b.op.*` where `op` is an OPERATION used to take the success path:
//! `find_scope_by_name` was a bare `by_qualified_name` hit that asked nothing about
//! the symbol's KIND, and its caller linked whatever scope came back as a resolution
//! parent. §8.6 gives the form one meaning — "include `a.b` as a non-enclosing parent
//! (every visible name)" — and only a namespace (§5.1) or a sort (§5.2) has names to
//! include.
//!
//! THE TWIN, AND THE TWO SHAPES IT TURNS OUT TO HAVE. WI-988 fixed this in scaland,
//! where `addParent` never creates the parent's record, so the link resolved NOTHING
//! and the import was a silent no-op. Rustland has BOTH that shape and a worse one,
//! and which you get is keyed on the target's kind — measured here by backing the
//! change out:
//!   - an OPERATION's scope carries an ENCLOSING link to the sort that declared it
//!     (`scan_operation_params`), and the parent walk is transitive, so naming one
//!     member spliced in the whole chain above it: a sibling member, and the contents
//!     of the namespace above THAT. The import did not do nothing — it brought names
//!     the author never wrote.
//!   - an ENTITY's scope carries no such link, so there the import is exactly the
//!     silent no-op WI-988 describes: the fixture below still fails at its use site
//!     and the import line says nothing at all.
//! One gate covers both, because the question is the same one either way: does this
//! path name a declaration that HAS contents.
//!
//! THE OTHER CLAUSE. WI-993's note said the `requires` half of WI-988 had no twin
//! here, because `load_requires_decl` records a `SortRequiresInfo` fact instead of a
//! link. That reads the LOAD phase. Sub-pass 2 (`ImportPass::at_item`) wires a scope
//! parent from the same declaration and asked nothing about kind either, so the twin
//! exists and is driven below — `requires lib.Host.op1` on an operation loaded clean
//! and made `Host`'s other member resolve bare.
//!
//! WHAT FAILS WHEN EACH LEVEL IS BACKED OUT — run one at a time, not predicted.
//! Level 1, the kind check in `load::find_scope_by_name` plus the wildcard arm's
//! three-way split in `process_imports`:
//!   - `wildcard_import_of_an_operation_is_refused_naming_the_kind` LOADS CLEAN
//!     without it — it drives a name only the bogus link could reach.
//!   - `the_refused_link_reached_the_enclosing_namespace_too` loses its refusal, and
//!     ONLY that: WI-1089's stop now cuts the very chain this row was written to
//!     exhibit (`op1 → Host → lib` is reached through an import-only edge), so with
//!     level 1 backed out `Neighbour` stays unresolved on its own account. The row is
//!     still a refusal test; what it no longer measures is the REACH, which
//!     `wi1089_import_binds_one_name_test` owns. Found by `/code-review`.
//!     (`a_plain_import_keeps_its_alias_and_stops_leaking_the_siblings` was a third
//!     row of this level when the plain form still linked a parent. WI-1089 removed
//!     that link outright — a plain import binds its name and opens nothing — so the
//!     row now holds against BOTH levels, and its subject moved to
//!     `wi1089_import_binds_one_name_test`.)
//!   - `wildcard_import_of_an_entity_names_the_entity_kind` keeps its use-site error
//!     and LOSES the refusal: one error instead of two. That difference is the whole
//!     ticket — an import that contributes nothing must not also say nothing.
//! Level 2, the `parent_scope_of` call at the `requires` site alone (level 1 left
//! in): `requires_naming_an_operation_is_refused_naming_the_kind` and
//! `requires_naming_a_namespace_is_refused` both load CLEAN, and nothing else moves.
//!
//! The five CONTROLS pass either way BY DESIGN. They are what fails if a gate
//! over-fires: a `requires` on a sort, a variant-less sort import, a namespace, a
//! `namespace` nested in a sort body, and §6.3's eponymous constructor — whose
//! `primary_kind` is `Entity` even though it IS a sort, which is why the gate asks
//! `has_kind`. MEASURED: rewriting the gate to `primary_kind` fails that one control
//! and nothing else in this file.

use crate::common::{expect_load_errors, load_kb_with, try_load_kb_with};

/// The gate's sentence, in the two pieces a reader acts on: WHICH path, and WHICH
/// kind it turned out to name.
fn refusal(path: &str, kind: &str) -> String {
    format!("wildcard import '{path}.*': '{path}' is a declaration of kind {kind}")
}

/// `import lib.Host.op1.*` names an operation. Refused — and the second error is the
/// probe: the sibling `op2` the fixture calls was reachable ONLY through the link the
/// gate now refuses, so with the gate backed out this fixture loads CLEAN.
#[test]
fn wildcard_import_of_an_operation_is_refused_naming_the_kind() {
    let src = r#"namespace wi993a.lib
  sort Host
    operation op1(x: Int64) -> Int64
    operation op2(x: Int64) -> Int64
  end
end

namespace wi993a.cli
  sort User
    import wi993a.lib.Host.op1.*
    operation use_it(y: Int64) -> Int64 = op2(y)
  end
end
"#;
    expect_load_errors(
        try_load_kb_with(src),
        &[
            &refusal("wi993a.lib.Host.op1", "Operation"),
            "`op2` is a member of sort Host, not in scope as a bare name here",
        ],
    );
}

/// The reach was not one hop. An operation's scope encloses to its SORT, and that
/// sort's to its NAMESPACE — so the same one-operation import made a sibling SORT of
/// `wi993b.lib` resolve bare, two levels above the name written. Same back-out
/// verdict: clean without the gate.
#[test]
fn the_refused_link_reached_the_enclosing_namespace_too() {
    let src = r#"namespace wi993b.lib
  sort Neighbour
    entity Neighbour(v: Int64)
  end
  sort Host
    operation op1(x: Int64) -> Int64
  end
end

namespace wi993b.cli
  sort User
    import wi993b.lib.Host.op1.*
    entity User(n: Neighbour)
  end
end
"#;
    expect_load_errors(
        try_load_kb_with(src),
        &[
            &refusal("wi993b.lib.Host.op1", "Operation"),
            // WI-977: qualified — the refusal row above already names its operation
            // in full, and this row now agrees.
            "unresolved name 'Neighbour' in scope 'wi993b.cli.User'",
        ],
    );
}

/// An ENTITY declared inside a sort is the other kind an author reaches for here, and
/// this is the shape WI-988 predicted: an entity's scope reaches nothing, so backing
/// the change out leaves the `op1` error below standing ALONE — the import line
/// contributes nothing and, without the gate, says nothing. The diagnostic names the
/// kind because that is what tells the author which of the two repairs they need.
#[test]
fn wildcard_import_of_an_entity_names_the_entity_kind() {
    let src = r#"namespace wi993c.lib
  sort Host
    entity mk(x: Int64)
    operation op1(x: Int64) -> Int64
  end
end

namespace wi993c.cli
  sort User
    import wi993c.lib.Host.mk.*
    operation use_it(y: Int64) -> Int64 = op1(y)
  end
end
"#;
    expect_load_errors(
        try_load_kb_with(src),
        &[
            &refusal("wi993c.lib.Host.mk", "Entity"),
            "`op1` is a member of sort Host, not in scope as a bare name here",
        ],
    );
}

/// A path that names NOTHING keeps its own diagnostic. The two are different
/// findings with different repairs — a typo versus a path that resolved perfectly
/// well — so the kind gate must not swallow the unresolved case.
#[test]
fn a_path_naming_nothing_is_still_an_unresolved_import() {
    expect_load_errors(
        try_load_kb_with(
            r#"namespace wi993d.cli
  import wi993d.nowhere.*
  entity Use(x: Int64)
end
"#,
        ),
        &["unresolved import 'wi993d.nowhere'"],
    );
}

/// The PLAIN form's parent link rode on the same unchecked helper, so it leaked the
/// same chain. Both halves in one fixture: the sibling `op2` is out of reach (this
/// errors; before WI-993 it loaded clean), while the ALIAS the author wrote the
/// import for is untouched — `op1` is still bound, which is the half a blanket
/// refusal would have broken.
///
/// WI-1089 SETTLED THE PLAIN FORM ENTIRELY — it binds its name and links no parent at
/// all, for any target kind — so this row no longer distinguishes the WI-993 gate.
/// It is kept as a control on the pair that still matters here: the alias survives
/// and the sibling does not.
#[test]
fn a_plain_import_keeps_its_alias_and_stops_leaking_the_siblings() {
    let src = r#"namespace wi993e.lib
  sort Host
    operation op1(x: Int64) -> Int64
    operation op2(x: Int64) -> Int64
  end
end

namespace wi993e.cli
  sort User
    import wi993e.lib.Host.op1
    operation calls_the_alias(y: Int64) -> Int64 = op1(y)
    operation calls_the_sibling(y: Int64) -> Int64 = op2(y)
  end
end
"#;
    expect_load_errors(
        try_load_kb_with(src),
        &["`op2` is a member of sort Host, not in scope as a bare name here"],
    );
}

// ── The `requires` half, which the ticket said had no rustland twin ──
// It does. `load_requires_decl` records a `SortRequiresInfo` fact rather than a
// link — that much of the note is right, and it reads the LOAD phase. Sub-pass 2
// (`ImportPass::at_item`) wires a scope parent from the same declaration, and asked
// nothing about kind either.

/// `requires` naming an OPERATION: the same over-import, through the other clause.
/// Backed out, this fixture LOADS CLEAN — the requiring sort could call `Host`'s
/// other member, a name nothing in this file wrote.
#[test]
fn requires_naming_an_operation_is_refused_naming_the_kind() {
    let src = r#"namespace wi993j.lib
  sort Host
    operation op1(x: Int64) -> Int64
    operation op2(x: Int64) -> Int64
  end
end

namespace wi993j.cli
  sort User
    requires wi993j.lib.Host.op1
    operation use_it(y: Int64) -> Int64 = op2(y)
  end
end
"#;
    expect_load_errors(
        try_load_kb_with(src),
        &[
            "`requires wi993j.lib.Host.op1`: 'wi993j.lib.Host.op1' is a declaration of kind Operation",
            "`op2` is a member of sort Host, not in scope as a bare name here",
        ],
    );
}

/// A `requires` admits a SORT and not a namespace, because it names a SPEC (§5.2) —
/// scaland's rule from WI-988, so both implementations refuse the same programs. The
/// namespace here declares an operation, which is exactly the thing the wired parent
/// would have made resolvable.
#[test]
fn requires_naming_a_namespace_is_refused() {
    let src = r#"namespace wi993k.lib
  operation loose(x: Int64) -> Int64 = x
end

namespace wi993k.cli
  sort User
    requires wi993k.lib
    operation use_it(y: Int64) -> Int64 = loose(y)
  end
end
"#;
    expect_load_errors(
        try_load_kb_with(src),
        &[
            "`requires wi993k.lib`: 'wi993k.lib' is a declaration of kind Namespace",
            "type mismatch in loose.apply: expected known operation or arrow-typed \
             variable, got unknown functor",
        ],
    );
}

/// CONTROL for both: a `requires` on a SORT still wires the link, DRIVEN by a bare
/// call to the spec's operation that only that link resolves.
#[test]
fn control_requires_naming_a_sort_still_wires_its_scope() {
    load_kb_with(
        r#"namespace wi993l.lib
  sort Spec
    operation op1(x: Int64) -> Int64
  end
end

namespace wi993l.cli
  sort User
    requires wi993l.lib.Spec
    operation use_it(y: Int64) -> Int64 = op1(y)
  end
end
"#,
    );
}

// ── CONTROLS: what fails if the gate OVER-fires ──────────────────
// Each of these passes with and without the change, by design. They are here
// because the gate's whole risk is refusing a target that does have contents.

/// A variant-less sort (a spec) is a scope, and the wildcard import is how its
/// operations become bare names — DRIVEN, not merely loaded: `use_it`'s body calls
/// the imported `op1`, which only the parent link resolves.
#[test]
fn control_wildcard_of_a_variantless_sort_still_brings_its_operations() {
    load_kb_with(
        r#"namespace wi993f.lib
  sort Host
    operation op1(x: Int64) -> Int64
  end
end

namespace wi993f.cli
  sort User
    import wi993f.lib.Host.*
    operation use_it(y: Int64) -> Int64 = op1(y)
  end
end
"#,
    );
}

/// A namespace is the other §5.1 scope — and a `namespace` nested in a SORT body is
/// one too (the shape `wi369_internal_visibility_test`'s re-export fixture writes).
/// Both are driven by a name that resolves only through the link.
#[test]
fn control_wildcard_of_a_namespace_and_of_a_namespace_inside_a_sort() {
    load_kb_with(
        r#"namespace wi993g.lib
  sort Neighbour
    entity Neighbour(v: Int64)
  end
end

namespace wi993g.cli
  sort User
    import wi993g.lib.*
    entity User(n: Neighbour)
  end
end
"#,
    );

    load_kb_with(
        r#"sort wi993h.Box
  entity mk(v: Int64)
  namespace inner
    import wi993h.Box.mk
  end
end

namespace wi993h.cli
  import wi993h.Box
  sort User
    import wi993h.Box.inner.*
    operation build(v: Int64) -> Box = mk(v: v)
  end
end
"#,
    );
}

/// §6.3's EPONYMOUS CONSTRUCTOR: `entity Point(…)` at top level is one name playing
/// both `Sort` and `Entity`, and `Entity` is the kind that LEADS (asserted below).
/// It is a sort all the same, so its scope is a scope — this is the control that
/// fails if the gate is ever rewritten to ask `primary_kind`, which would refuse
/// this import outright.
///
/// The observable here is the ABSENCE of the refusal, and that is the whole of what
/// a `primary_kind` gate would change. What the admitted link then DELIVERS is a
/// separate question with a measured answer: the eponymous constructor's own name is
/// declared in the ENCLOSING namespace rather than inside the sort (§6.3's collapse),
/// so this import carries nothing citable — which is why the name is ALSO imported
/// plainly here, and why the DRIVEN case is
/// `control_wildcard_of_a_variantless_sort_still_brings_its_operations`.
///
/// SO THIS ADMITS A LINK THAT RESOLVES NOTHING, which is the shape the gate is named
/// for, and it is intended: the gate tests the KIND, never the current contents. An
/// empty namespace and a spec with no operations are admitted for the same reason,
/// spelled out at `load::parent_scope_of` — a content test would answer differently
/// depending on declaration order, since rule-introduced members are registered a
/// sub-pass later and a 059 R2 secondary entry can add members from another file.
#[test]
fn control_an_eponymous_constructors_sort_is_still_a_scope() {
    let kb = load_kb_with(
        r#"namespace wi993i.lib
  entity Point(x: Int64)
end

namespace wi993i.cli
  sort User
    import wi993i.lib.Point
    import wi993i.lib.Point.*
    operation build(v: Int64) -> Point = Point(x: v)
  end
end
"#,
    );
    let point = kb
        .try_resolve_symbol("wi993i.lib.Point")
        .expect("the eponymous name is defined");
    assert_eq!(
        format!("{:?}", kb.kind_of(point)),
        "Some(Entity)",
        "the control only bites while `Entity` is the kind that LEADS here — if this \
         changes, the fixture stops distinguishing `has_kind` from `primary_kind`"
    );
}
