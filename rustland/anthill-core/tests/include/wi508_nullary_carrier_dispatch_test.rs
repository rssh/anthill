//! WI-508 — a NULLARY spec op `new() -> C` (carrier only in the RESULT, zero
//! params) resolves its carrier from the call context rather than failing
//! dispatch.
//!
//! Value-directed dispatch has no carrier-typed argument to dispatch on, so it
//! returns `NoCandidates` and the WI-325 abstract-binding check used to fire
//! ("missing requires MutableCollection[…]"). The fix (kb/typing.rs,
//! `resolve_nullary_result_carrier`) resolves the carrier, in priority order:
//!   (a) the EXPECTED RETURN TYPE names a concrete carrier  → that carrier's
//!       override (PinNow);
//!   (b) no carrier pinned and exactly ONE provider exists  → use it
//!       (information hiding);
//!   (c) no carrier pinned and 2+ providers                 → loud ambiguity.
//! A `requires`-covered call (a generic consumer over `requires
//! MutableCollection`) keeps taking the existing Deferred / dict-threaded path.

use crate::common::{interp_for, register_modify_handler};

// ── Acceptance: the stdlib MutableCollection.new() pinned by the return type ──

const SRC_STDLIB: &str = r#"
namespace test.wi508
  import anthill.prelude.{Int64, MutableStack, MutableCollection}
  import anthill.prelude.MutableCollection.{new}
  import anthill.prelude.FiniteCollection.{size}

  operation depth(s: MutableStack[T = Int64]) -> Int64 = size(s)
  -- abstract MutableCollection.new(); carrier pinned only by the return type
  operation freshBare() -> MutableStack[T = Int64] effects Modify[result] = new()
end
"#;

#[test]
fn wi508_abstract_new_from_return_type() {
    let mut interp = interp_for(SRC_STDLIB);
    register_modify_handler(&mut interp);
    let s = interp.call("test.wi508.freshBare", &[]).expect("freshBare");
    assert_eq!(
        interp.call("test.wi508.depth", &[s]).unwrap().as_int(),
        Some(0),
        "abstract new() from the return type yields a fresh empty stack",
    );
}

// ── The (a)/(b)/(c) model on a controlled spec `Maker`. `Maker` has a SECOND
//    param `Element` (like MutableCollection's Element/E) that `make() -> C`
//    never pins, so even the ANNOTATED call leaves `Element` open → value-
//    directed dispatch hits `NoCandidates` → the WI-508 helper runs (a
//    single-carrier-param spec would be fully pinned by the annotation and
//    resolved by the pre-existing dispatch, never reaching the helper).

const TWO_PROVIDERS: &str = r#"
namespace test.wi508d
  sort Maker
    sort C = ?
    sort Element = ?
    operation make() -> C
  end
  sort Foo
    entity foo
    operation make() -> Foo = foo()
    provides Maker[C = Foo, Element = Foo]
  end
  sort Bar
    entity bar
    operation make() -> Bar = bar()
    provides Maker[C = Bar, Element = Bar]
  end
  -- (a) annotation pins the carrier -> helper resolves to Foo.make (the return
  --     type names Foo) even with 2 providers; Element stays open
  operation mkFoo() -> Foo = Maker.make()
end
"#;

const ONE_PROVIDER: &str = r#"
namespace test.wi508e
  import anthill.prelude.Bool
  sort Maker
    sort C = ?
    sort Element = ?
    operation make() -> C
  end
  sort Foo
    entity foo
    operation make() -> Foo = foo()
    provides Maker[C = Foo, Element = Foo]
  end
  -- (b) carrier unpinned but a UNIQUE provider exists -> information hiding
  operation mkUnique() -> Bool =
    let x = Maker.make()
    true
end
"#;

const TWO_PROVIDERS_AMBIG: &str = r#"
namespace test.wi508f
  import anthill.prelude.Bool
  sort Maker
    sort C = ?
    sort Element = ?
    operation make() -> C
  end
  sort Foo
    entity foo
    operation make() -> Foo = foo()
    provides Maker[C = Foo, Element = Foo]
  end
  sort Bar
    entity bar
    operation make() -> Bar = bar()
    provides Maker[C = Bar, Element = Bar]
  end
  -- (c) carrier unpinned with 2+ providers -> loud ambiguity at load
  operation mkAmbig() -> Bool =
    let x = Maker.make()
    true
end
"#;

#[test]
fn wi508_annotation_disambiguates_with_two_providers() {
    let _ = interp_for(TWO_PROVIDERS);
}

#[test]
fn wi508_unique_provider_information_hiding() {
    let _ = interp_for(ONE_PROVIDER);
}

#[test]
#[should_panic(expected = "load failed")]
fn wi508_two_providers_unannotated_is_loud() {
    let _ = interp_for(TWO_PROVIDERS_AMBIG);
}

// ── Guards: the CONCRETE carrier constructor `MutableStack.new()` is unchanged.
//    Its element `T` is ordinary inference, not part of WI-508 (the carrier is
//    fixed). Documents that `let x = MutableStack.new()` is valid and `T` is a
//    monomorphic unification var: pinned by a later use, harmless if never used.

const SRC_CONCRETE: &str = r#"
namespace test.wi508g
  import anthill.prelude.{Int64, Bool, MutableStack}
  import anthill.prelude.FiniteCollection.{size}

  -- element T inferred Int64 from the push
  operation useNew() -> Int64 effects Modify[result] =
    let x = MutableStack.new()
    let _ = MutableStack.push(x, 10)
    size(x)

  -- element T never determined; still valid (empty stack of an unknown element)
  operation ambNew() -> Bool effects Modify[result] =
    let x = MutableStack.new()
    true
end
"#;

#[test]
fn wi508_concrete_new_element_inferred_from_use() {
    let mut interp = interp_for(SRC_CONCRETE);
    register_modify_handler(&mut interp);
    let r = interp.call("test.wi508g.useNew", &[]).expect("useNew");
    assert_eq!(r.as_int(), Some(1), "push(x, 10) pins T = Int64; size is 1");
}

#[test]
fn wi508_concrete_new_unpinned_element_loads() {
    let _ = interp_for(SRC_CONCRETE); // ambNew loads with T left free
}
