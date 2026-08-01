//! WI-908 — a HOST-supplied name is read by THE SAME LADDER as source text.
//!
//! `KnowledgeBase::resolve_name_in_global` answers "which functor does this Rust-side
//! string name?" for every extent mount. It spelled its own pre-WI-752 ladder, so the
//! mount could bind a symbol the author of the name never wrote. Driven here through
//! `register_extent_owner`, the live caller, asserting WHICH symbol each mount lands on.
//!
//! ONE STDLIB LOAD, in the last test only: the implicit tier resolves a name only when
//! its target is LOADED (WI-900), so that claim cannot be made in a bare KB. The other
//! three turn on `_global`'s own inhabitants — top-level imports and the loader's
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

/// A top-level import — the one way `_global` gains a name whose qualified path is not
/// its own spelling, and therefore the only place head-qualification and the absolute
/// reading can disagree at this scope (WI-853).
const IMPORT_LIB: &str = "import wi908.lib\n";

const HIDDEN: &str = "\
namespace wi908.priv
  sort Vault
    internal entity secret(id: Int64)
  end
end
";

fn fixture() -> KnowledgeBase {
    crate::common::load_kb_bare(&[LIB, IMPORT_LIB, HIDDEN])
}

/// `name` must not denote at `_global`, so the mount is refused BY NAME RESOLUTION —
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
        "a bare `Member` must mount what a top-level `import wi908.lib` puts in scope",
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
        kb.extent_owner(kb.resolve_symbol("wi908.lib.Box.thing")).is_some(),
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
        "an `internal` member is invisible from `_global`",
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

    assert_unmountable(&mut kb, "Sort", "a short name must denote at `_global` to mount");
}

/// …AND THE HALF THAT SURVIVES, which the test above must not be read as denying: the
/// ladder's LOWEST rung is the implicit tier (`resolve_implicit`), and it is short-name
/// keyed. So a reflection or prelude name still mounts bare, with no scope presence and
/// no import — the capability the pre-WI-908 code kept via its absolute rung, reached now
/// by the rung that is actually meant for it.
///
/// Needs the stdlib: the tier resolves a name only when its target is LOADED (WI-900).
/// `SortView` is one of the reflection result sorts the tier lists precisely so the
/// anthill-stl bridge / CLI can name them bare, and it carries no resident facts — the
/// sibling `SortInfo` resolves identically but is then refused as a `ResidentCollision`,
/// which is the single-owner rule, not the ladder.
#[test]
fn a_short_implicit_tier_name_still_mounts_with_no_scope_presence() {
    let mut kb = crate::common::load_kb_with("namespace wi908.anchor\n  fact a908(1)\nend\n");

    mount(&mut kb, "SortView").expect("`SortView` is an implicit-tier name");

    assert!(
        kb.extent_owner(kb.resolve_symbol("anthill.reflect.SortView")).is_some(),
        "the implicit tier maps the bare short name to its qualified target",
    );
}
