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
use anthill_core::kb::term_view::TermView;

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
        interp
            .call("test.wi508.depth", &[s])
            .unwrap()
            .literal_int64(interp.kb()),
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

// ── Guards: the CONCRETE carrier constructor `MutableStack.new()`. Its element `T` is
//    not part of WI-508 (the carrier is fixed). `new()` fixes no `T`, so the slot is open
//    in its result — and CLOSED where the stack gets a name (WI-20261001-80ZV8, the user's
//    decision of 2026-10-04): `let x = MutableStack.new()` is a stack of `x.T`. These rows
//    used to document the opposite — "`T` is a monomorphic unification var: pinned by a
//    later use" — which was never what happened: the slot was open at every use, so one
//    stack took an `Int64` and then a `String`
//    (`wi_80zv8_named_open_slot_test::a_writable_value_is_not_read_at_two_types`). A later
//    use really pinning it is WI-20261004-KEGNC.

/// `useNew` over a stack made by `bound`, the `let` that names it.
fn concrete_program(ns: &str, bound: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, MutableStack}}
  import anthill.prelude.FiniteCollection.{{size}}

  operation useNew() -> Int64 effects Modify[result] =
    {bound}
    let _ = MutableStack.push(x, 10)
    size(x)
end
"#
    )
}

/// THE ELEMENT IS SAID WHERE THE STACK IS NAMED — an annotation, or a bracket in either
/// spelling. Each runs: one push, size 1.
#[test]
fn wi508_concrete_new_element_said_at_the_name() {
    for (ns, bound) in [
        ("test.wi508g.ann", "let x: MutableStack[T = Int64] = MutableStack.new()"),
        ("test.wi508g.callee", "let x = MutableStack.new[T = Int64]()"),
        ("test.wi508g.recv", "let x = MutableStack[T = Int64].new()"),
    ] {
        let mut interp = interp_for(&concrete_program(ns, bound));
        register_modify_handler(&mut interp);
        let r = interp
            .call(&format!("{ns}.useNew"), &[])
            .unwrap_or_else(|e| panic!("{bound}: {e:?}"));
        assert_eq!(r.literal_int64(interp.kb()), Some(1), "{bound}");
    }
}

/// … AND NOT BY A LATER USE: with nothing said at the name the push is refused, the stack's
/// own unknown named. Loaded before WI-20261001-80ZV8's naming rule (this file's
/// `wi508_concrete_new_element_inferred_from_use`, which ran to 1).
/// FAILS with the naming rule backed out (`wi_80zv8_named_open_slot_test`'s ledger, part 1);
/// the three spellings above and the unpinned row below pass either way, by design.
#[test]
fn wi508_concrete_new_element_is_not_inferred_from_use() {
    let errs = crate::common::load_errors_of(&concrete_program(
        "test.wi508g.unsaid",
        "let x = MutableStack.new()",
    ));
    crate::common::assert_refused_naming(
        &errs,
        &["push.elem (op-arg): expected x.T, got Int64"],
        "a stack named with no element said, then pushed an Int64",
    );
}

/// A stack nothing reads at an element loads with `T` never said — an empty stack of its own
/// unknown. Passes with or without the naming rule, by design.
#[test]
fn wi508_concrete_new_unpinned_element_loads() {
    let _ = interp_for(
        r#"
namespace test.wi508g.amb
  import anthill.prelude.{Int64, Bool, MutableStack}

  operation ambNew() -> Bool effects Modify[result] =
    let x = MutableStack.new()
    true
end
"#,
    );
}
