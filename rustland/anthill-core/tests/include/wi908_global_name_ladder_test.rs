//! WI-908 — a HOST-supplied name is read by THE SAME LADDER as source text.
//!
//! `KnowledgeBase::resolve_name_in_global` answers "which functor does this Rust-side
//! string name?" for every extent mount. It spelled its own pre-WI-752 ladder, so the
//! mount could bind a symbol the author of the name never wrote. Driven here through
//! `register_extent_owner`, the live caller, asserting WHICH symbol each mount lands on.
//!
//! ONE STDLIB LOAD, in the last test only: the implicit tier resolves a name only when
//! its target is LOADED (WI-900), so that claim cannot be made in a bare KB. The other
//! three turn on `<global>`'s own inhabitants — top-level imports and the loader's
//! qualified-only kernel registrations — which `register_prelude` alone supplies.

use anthill_core::kb::extent::ExtentRegError;
use anthill_core::kb::KnowledgeBase;

use crate::common::mount_extent as mount;

/// `Member` deliberately collides with a KERNEL META SORT (`load::KERNEL_META_SORTS`),
/// which is registered QUALIFIED-ONLY — reachable as `by_qualified_name["Member"]` and in
/// no scope's locals. WI-423 delocalized those names so a user sort of the same spelling
/// wins; the absolute-first rung resurrected the phantom.
const LIB: &str = "\
namespace wi908.lib
  sort Member
  end
  sort Box
    entity thing(id: Int64)
  end
end
";

/// The import that gives `<global>` a name whose qualified path is not its own spelling —
/// the only way head-qualification and the absolute reading can disagree at this scope.
///
/// WI-995 — supplied through the INVOCATION (`-i wi908.lib`), because the name it feeds
/// is a HOST string and a host has no file. An import written in a program source is
/// local to that source now, so it could not reach `mount(..)` at all, and the ladder
/// this suite is about would have nothing to disagree over.
/// WI-1089: the WILDCARD form. `-i wi908.lib` binds the name `lib` and nothing
/// else — an invocation import reads exactly as the same line in source does — and
/// this fixture is about names `wi908.lib` CONTAINS being mountable at `<global>`.
const IMPORT_LIB_FLAG: &str = "wi908.lib.*";

const HIDDEN: &str = "\
namespace wi908.priv
  sort Vault
    internal entity secret(id: Int64)
  end
end
";

fn fixture() -> KnowledgeBase {
    let mut kb = crate::common::load_kb_bare(&[LIB, HIDDEN]);
    crate::common::supply_invocation_imports(&mut kb, &[IMPORT_LIB_FLAG]);
    kb
}

/// `name` must not denote at `<global>`, so the mount is refused BY NAME RESOLUTION —
/// loudly, though not yet precisely (see the `internal` test).
fn assert_unmountable(kb: &mut KnowledgeBase, name: &str, why: &str) {
    let err = mount(kb, name).expect_err(why);
    assert!(
        matches!(err, ExtentRegError::UnresolvableName(_)),
        "`{name}` must fail by NAME RESOLUTION; got {err:?}",
    );
}

/// THE INVERSION, with both readings live and distinct. `Member` names the imported
/// `wi908.lib.Member` in scope AND is some symbol's whole qualified name; ranking the
/// absolute reading first bound the mount to the loader's meta-sort — a functor the host
/// never named, and the phantom WI-423 delocalized the meta-sorts to banish.
#[test]
fn an_imported_name_outranks_a_same_spelled_qualified_only_registration() {
    let mut kb = fixture();
    let kernel_member = kb.resolve_symbol("Member");
    let user_member = kb.resolve_symbol("wi908.lib.Member");
    assert_ne!(
        kernel_member, user_member,
        "control: the two readings must be DIFFERENT symbols, or this fixture asserts \
         nothing",
    );

    mount(&mut kb, "Member").expect("`Member` resolves — the question is to WHAT");

    // One `owned()` name mounts exactly one functor, so this also says the meta-sort
    // was NOT the one taken.
    assert!(
        kb.extent_owner(user_member).is_some(),
        "a bare `Member` must mount what `-i wi908.lib` puts in scope",
    );
}

/// THE MISSING RUNG. `Box.thing` is nobody's qualified name; it denotes only by
/// qualifying the imported head `Box` — the rung this position did not have, so the mount
/// was refused outright.
#[test]
fn a_name_qualified_by_an_imported_head_mounts() {
    let mut kb = fixture();
    assert!(
        kb.try_resolve_symbol("Box.thing").is_none(),
        "control: `Box.thing` must NOT be anyone's qualified name, or the absolute rung \
         could answer this and the head-qualified rung is untested",
    );

    mount(&mut kb, "Box.thing").expect("`Box.thing` denotes via its imported head");

    assert!(
        kb.extent_owner(kb.resolve_symbol("wi908.lib.Box.thing"))
            .is_some(),
        "the head `Box` resolves to `wi908.lib.Box`, so the tail names its entity",
    );
}

/// THE VISIBILITY GATE, which belongs to the LADDER (WI-752) and therefore to this
/// position too. `internal` is the declaration's statement that outside code has no
/// business naming the member; a host string is outside code.
///
/// The refusal is loud but NOT yet precise: the mount takes only the ladder's
/// `VisibleOnly` half, so a name that exists-and-is-hidden reports as one that does not
/// exist. The diagnostic half (the `Any` re-read in `Loader::resolve_dotted_reported`) is
/// a `Loader` method this seam cannot reach — WI-911. (Its AMBIGUITY half needs no such
/// lift and no longer has one: WI-917 moved that answer into the ladder itself, which is
/// why `an_ambiguous_host_name_is_refused_as_ambiguous_not_absent` can assert precision
/// here while this test cannot.)
#[test]
fn an_internal_member_is_not_mountable_from_global() {
    let mut kb = fixture();
    assert!(
        kb.try_resolve_symbol("wi908.priv.Vault.secret").is_some(),
        "control: the symbol EXISTS — the refusal below must be about visibility, not \
         about a missing declaration",
    );

    assert_unmountable(
        &mut kb,
        "wi908.priv.Vault.secret",
        "an `internal` member is invisible from `<global>`",
    );
}

/// THE ONE CAPABILITY THIS ALIGNMENT DROPS, pinned as the decision it is: the absolute
/// rung is DOTTED-ONLY (WI-476 — a bare name resolves in its environment or not at all),
/// so a short host name outside the implicit tier must be IN SCOPE. `Sort` is a
/// qualified-only kernel registration with no scope presence, and it used to mount.
#[test]
fn a_short_name_outside_the_implicit_tier_no_longer_resolves_absolutely() {
    let mut kb = fixture();
    assert!(
        kb.try_resolve_symbol("Sort").is_some(),
        "control: `Sort` IS a defined symbol — the refusal below is about the ladder, \
         not about absence",
    );

    assert_unmountable(
        &mut kb,
        "Sort",
        "a short name must denote at `<global>` to mount",
    );
}

/// …AND THE HALF THAT SURVIVES, which the test above must not be read as denying: the
/// ladder's LOWEST rung is the implicit tier (`resolve_implicit`), and it is short-name
/// keyed. So a reflection or prelude name still mounts bare, with no scope presence and
/// no import — the capability the pre-WI-908 code kept via its absolute rung, reached now
/// by the rung that is actually meant for it.
///
/// Needs the stdlib: the tier resolves a name only when its target is LOADED (WI-900).
///
/// INVERTED IN WI-909's THIRD PASS, and it took two repointings to get here: this row
/// used `SortView` until the reflection sorts left the tier, then `cons` until the
/// constructors left it too. There is no third name — `PRELUDE_QUALIFIED` is empty — so
/// the claim itself is what changes rather than its subject.
///
/// THE HALF THAT SURVIVES IS STILL THE POINT. WI-908's finding was that a mount name is
/// read through the ordinary ladder (`resolve_name_in_global`) rather than an absolute
/// lookup of its own; that is unchanged and is what the qualified arm below measures.
/// What is gone is the rung the ladder used to END with, so a SHORT name with no scope
/// presence now denotes nothing and cannot be mounted.
///
/// THE REFUSAL IS THE MIGRATION, and it is loud: a host mounting `cons` is told the name
/// resolves to nothing rather than silently taking an extent on a symbol it did not mean.
#[test]
fn a_short_name_with_no_scope_presence_no_longer_mounts() {
    let mut kb = crate::common::load_kb_with("namespace wi908.anchor\n  fact a908(1)\nend\n");

    mount(&mut kb, "cons").expect_err(
        "the implicit tier is empty since WI-909, so a bare `cons` denotes nothing at \
         `<global>` and there is no functor to mount",
    );

    // CONTROL — the ladder itself is intact: the QUALIFIED name still mounts, which is
    // what says the row above measures the missing rung rather than a broken mount.
    mount(&mut kb, "anthill.prelude.List.cons").expect("the qualified name still mounts");
    assert!(
        kb.extent_owner(kb.resolve_symbol("anthill.prelude.List.cons"))
            .is_some(),
        "the mount lands on the qualified target",
    );
}
