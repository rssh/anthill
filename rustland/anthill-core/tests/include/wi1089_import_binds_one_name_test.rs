//! WI-1089 — AN IMPORT BINDS THE NAME IT WRITES, AND OPENS ONLY WHAT IT NAMES.
//!
//! `import a.b.C` puts `C` in scope. Not `a.b`, and not `C`'s members: the same line
//! means the same thing in Scala, Java and Rust, scaland already implemented it, and
//! §8.6's own lead sentence says it ("`import` introduces visibility into the current
//! scope; it does not by itself add a sort's contents — use `requires` or wildcard for
//! that"). Two rustland behaviours contradicted that text, neither of them chosen:
//!
//!   1. THE PLAIN FORM SPLICED THE TARGET'S SCOPE IN as a resolution parent, so
//!      `import a.b.C` made `C`'s members bare-callable.
//!   2. THE PARENT WALK RE-ENTERED AN IMPORTED SCOPE'S ENCLOSING CHAIN, so any import
//!      — plain or wildcard — also delivered the module around what was imported, and
//!      the module around THAT. This is what made (1) look like §8.6's "include `a.b`":
//!      the reach was right by accident, and vanished the moment `C` had no scope of
//!      its own (WI-993 measured both halves).
//!
//! WHAT REPLACES THEM, both driven below: the forms that bring contents still do.
//! `import a.b.C.*` opens `C`, `import a.b.*` opens `a.b`, `requires Spec` opens the
//! spec, and `C.member` reaches through the bound name without any import at all.
//!
//! WHAT FAILS WHEN EACH HALF IS BACKED OUT — run one at a time.
//!   * Re-add the plain form's `add_import_parent` (load.rs, `ImportKind::Plain`) ⇒
//!     `a_plain_import_does_not_open_the_thing_it_names` and
//!     `importing_a_namespace_does_not_bring_its_contents` fail: both fixtures load
//!     clean, which is the defect.
//!   * Drop the `EnclosingLinks::StoppedByImport` propagation (intern.rs) ⇒
//!     `a_wildcard_opens_what_it_names_and_not_the_module_around_it` fails: the
//!     sibling sort resolves through an import that never named it.
//!   * The four CONTROLS pass either way by design; they are what fails if the rule
//!     over-reaches and stops a name that was never reached through an import edge.

use crate::common::{expect_load_errors, load_kb_with, try_load_kb_with};

/// A library with a sort that has members, and a SIBLING sort next to it — the two
/// things an import could over-deliver.
const LIB: &str = r#"namespace wi1089.lib
  sort Neighbour
    entity neighbour(v: Int64)
  end
  sort Host
    operation op1(x: Int64) -> Int64
    operation op2(x: Int64) -> Int64
  end
end
"#;

/// `import wi1089.lib.Host` binds `Host`. A bare `op1` is not in scope through it —
/// members are reached by qualifying the bound name, which the control drives.
#[test]
fn a_plain_import_does_not_open_the_thing_it_names() {
    expect_load_errors(
        try_load_kb_with(&format!(
            "{LIB}
namespace wi1089.bare
  sort User
    import wi1089.lib.Host
    operation use_it(y: Int64) -> Int64 = op1(y)
  end
end
"
        )),
        &["`op1` is a member of sort Host, not in scope as a bare name here"],
    );
}

/// CONTROL for the row above, and the half a blanket refusal would have broken: the
/// ALIAS is what the line was written for. `Host` denotes, so `Host.op1(…)` calls
/// through it — no wildcard, no `requires`.
#[test]
fn control_the_bound_name_qualifies_what_it_contains() {
    load_kb_with(&format!(
        "{LIB}
namespace wi1089.qualified
  sort User
    import wi1089.lib.Host
    operation use_it(y: Int64) -> Int64 = Host.op1(y)
  end
end
"
    ));
}

/// CONTROL: the form that DOES open a sort still opens it, driven by the same bare
/// call the row above refuses.
#[test]
fn control_a_wildcard_on_the_sort_opens_its_members() {
    load_kb_with(&format!(
        "{LIB}
namespace wi1089.wild
  sort User
    import wi1089.lib.Host.*
    operation use_it(y: Int64) -> Int64 = op1(y)
  end
end
"
    ));
}

/// The second half, and the one no rule ever stated: an import edge does not re-open
/// the module around what was imported. `import wi1089.lib.Host.*` asks for `Host`'s
/// names; `Neighbour` is a SIBLING of `Host` in `wi1089.lib`, reachable before this
/// only because the walk stepped out through `Host`'s enclosing link.
#[test]
fn a_wildcard_opens_what_it_names_and_not_the_module_around_it() {
    expect_load_errors(
        try_load_kb_with(&format!(
            "{LIB}
namespace wi1089.sibling
  sort User
    import wi1089.lib.Host.*
    entity User(n: Neighbour)
  end
end
"
        )),
        &["unresolved name 'Neighbour' in scope 'User'"],
    );
}

/// CONTROL for that stop: naming the module IS how its contents come in. Same
/// fixture, one import changed — so the row above measures the reach of the edge and
/// not some other absence of `Neighbour`.
#[test]
fn control_a_wildcard_on_the_module_brings_the_sibling() {
    load_kb_with(&format!(
        "{LIB}
namespace wi1089.module
  sort User
    import wi1089.lib.*
    entity User(n: Neighbour)
  end
end
"
    ));
}

/// A namespace is not special: `import wi1089.lib` binds `lib`, and `lib.Neighbour`
/// is how one reaches through it. Both halves in one fixture — the refusal, and the
/// qualified spelling that works — so the rule is not read as "namespaces are
/// unimportable".
#[test]
fn importing_a_namespace_does_not_bring_its_contents() {
    expect_load_errors(
        try_load_kb_with(&format!(
            "{LIB}
namespace wi1089.ns
  sort User
    import wi1089.lib
    entity User(n: Neighbour)
  end
end
"
        )),
        &["unresolved name 'Neighbour' in scope 'User'"],
    );

    load_kb_with(&format!(
        "{LIB}
namespace wi1089.nsq
  sort User
    import wi1089.lib
    entity User(n: lib.Neighbour)
  end
end
"
    ));
}

/// THE STOP IS FOR AN EDGE AN IMPORT ALONE JUSTIFIES. Here the pair
/// `(wi1089.top.sub, wi1089.top)` is the ENCLOSING edge and the imported one at once,
/// and an origin list is per `(scope, parent)` — so a stop keyed on "an import is
/// among the writers" cut the chain above `wi1089.top`, taking `_global` and the
/// prelude with it: a bare `Int64` stopped resolving in a namespace that had merely
/// imported its own parent.
///
/// Found by `/code-review` on the first cut, and this is the row that fails when
/// `parent_edge_is_import_only` is weakened back to `parent_edge_is_imported`.
#[test]
fn an_import_of_the_enclosing_namespace_is_not_a_stop() {
    load_kb_with(
        r#"namespace wi1089.top
  sort Shared
    entity shared(v: Int64)
  end
end

namespace wi1089.top.sub
  import wi1089.top.*
  sort User
    entity user(a: Shared, b: Int64)
  end
end
"#,
    );
}

/// The same root, in the shape that makes it a rule and not a corner: one inclusion,
/// TWO writers. `requires Spec` and `import Spec.*` produce the identical
/// `ScopeInclusion`, so they are one edge carrying both origins — and stopping it on
/// the import's account removed what the `requires` reaches. An import line is
/// additive; adding one must not take a name away.
///
/// Also fails when the predicate is weakened, and it is the half that says WHY the
/// weaker one is wrong rather than merely that it breaks something.
#[test]
fn adding_an_import_beside_a_requires_takes_no_name_away() {
    let src = r#"namespace wi1089.two.lib
  sort Sib
    entity sib(v: Int64)
  end
  sort Spec
    operation op1(x: Int64) -> Int64
  end
end

namespace wi1089.two.app
  sort User
    requires wi1089.two.lib.Spec
    import wi1089.two.lib.Spec.*
    entity user(n: Sib)
  end
end
"#;
    load_kb_with(src);

    // The CONTROL that makes the row above a comparison: the same file without the
    // import line loads too, so what is being asserted is that the import CHANGED
    // nothing — not that `Sib` happens to resolve.
    load_kb_with(&src.replace("    import wi1089.two.lib.Spec.*\n", ""));
}

/// CONTROL: `requires` is the other contents-bringing clause and is untouched — it is
/// a declaration about the requiring sort, not one file's import, so neither the
/// plain-form change nor the enclosing stop applies to it. DRIVEN by a bare call to
/// the spec's operation.
#[test]
fn control_requires_still_opens_the_spec() {
    load_kb_with(
        r#"namespace wi1089.spec
  sort Spec
    operation described(x: Int64) -> Int64
  end

  sort User
    requires Spec
    operation use_it(y: Int64) -> Int64 = described(y)
  end
end
"#,
    );
}
