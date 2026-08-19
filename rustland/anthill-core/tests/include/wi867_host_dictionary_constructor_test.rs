//! WI-867 — the host-facing dictionary constructor knows the layout.
//!
//! WI-857 gave a requirement dictionary one layout and guarded the host BOUNDARY:
//! `call_with_requirements` validates each supplied chain dictionary against
//! `dict_layout(slot spec, dict provider)`. The CONSTRUCTOR was not guarded — the
//! public `alloc_requirement(functor, subs)` had no spec to check against, so a host
//! could build a dictionary that claims a provider and bundles nothing, and carry it
//! around until a frame push read a slot that was not there. That failure names the
//! CALLEE, not the caller that built the value.
//!
//! `alloc_dictionary(spec, provider, subs)` is the constructor with the pair, and
//! `alloc_dictionary_unchecked` is what the old one became — the value carrier alone,
//! renamed so reaching for it is a decision.
//!
//! WHY IT MATTERS NOW rather than in principle: the one in-tree host was layout-valid
//! only because the chains involved are empty (the chain-free-provider accident WI-857
//! records), and 058 phase 7 gives such specs real chains.

use anthill_core::eval::Value;
use anthill_core::kb::typing::dict_layout;

/// An entry op whose parent sort declares a `requires` — the host-boundary shape.
/// Its body does NOT read the requirement, so a layout-valid dictionary carrying a
/// marker sub-slot is enough to run it: this file is about the SHAPE a host hands
/// over, not about what a body does with the evidence.
const SRC: &str = r#"
namespace wi867.host
  import anthill.prelude.{Int64, Ord}

  sort Entry
    requires Ord[T = Int64]
    operation main(n: Int64) -> Int64 = n
  end
end
"#;

/// THE FIXTURE'S PREMISE, MEASURED rather than assumed — every row below is vacuous if
/// this layout is 0, which is exactly the accident that hid the gap in the real host.
///
/// `Ord`'s own chain is 1 (WI-1110 left it the single `provides WeakOrd` conversion)
/// and `Int64` is a carrier-keyed provider declaring none, so the whole dictionary IS
/// the spec half.
#[test]
fn wi867_the_fixture_has_a_non_empty_layout() {
    let mut interp = crate::common::interp_for(SRC);
    let ord = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Ord")
        .expect("Ord is a stdlib spec");
    let int64 = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Int64")
        .expect("Int64 is a stdlib carrier");
    let layout = dict_layout(interp.kb_mut(), ord, int64);
    assert_eq!(
        layout.arity(),
        1,
        "a dictionary for `Ord` at `Int64` bundles one sub-requirement; without that \
         every refusal row below would pass on an empty layout: {}",
        layout.describe(interp.kb()),
    );
}

/// THE TICKET'S ACCEPTANCE: a host that hand-builds a short dictionary is refused AT
/// CONSTRUCTION, and the refusal names the spec, the provider and both halves.
///
/// BACKED OUT (drop the `refuse_arity` call from `alloc_dictionary`): this row fails —
/// the short dictionary is built and handed back, which is the pre-WI-867 behaviour
/// under a new name.
#[test]
fn wi867_a_short_dictionary_is_refused_at_construction() {
    let mut interp = crate::common::interp_for(SRC);
    let ord = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Ord")
        .unwrap();
    let int64 = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Int64")
        .unwrap();

    let err = match interp.alloc_dictionary(ord, int64, []) {
        Err(e) => format!("{e}"),
        Ok(_) => panic!("a dictionary for `Ord` at `Int64` bundling nothing is short"),
    };
    // The ticket's words: the spec, the provider, and BOTH HALVES. The halves are the
    // part a bare "expected 1" cannot give — which half is short is the whole
    // difficulty `DictLayout` exists to resolve.
    for needle in [
        "anthill.prelude.Ord",
        "anthill.prelude.Int64",
        "bundling 0",
        "1 slot(s)",
        "for spec",
        "for provider",
    ] {
        assert!(
            err.contains(needle),
            "the refusal must name {needle:?}; got: {err}",
        );
    }
}

/// THE CONTROL, and it is what makes the row above a finding rather than a tautology:
/// the constructor accepts the RIGHT number, and the same short shape is still
/// buildable through `alloc_dictionary_unchecked` — so what changed is the
/// constructor a host is pointed at, not the value machinery underneath.
#[test]
fn wi867_the_right_shape_is_built_and_the_unchecked_one_still_is() {
    let mut interp = crate::common::interp_for(SRC);
    let ord = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Ord")
        .unwrap();
    let int64 = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Int64")
        .unwrap();

    let sub = interp
        .alloc_dictionary_unchecked(int64, [])
        .expect("the stdlib defines anthill.realization.runtime.Dictionary");
    let ok = interp
        .alloc_dictionary(ord, int64, [sub])
        .expect("one sub-slot is what the layout wants");
    assert_eq!(ok.arity(), 1, "and it carries the slot it was given");

    assert!(
        interp.alloc_dictionary_unchecked(int64, []).is_some(),
        "the unchecked constructor still builds any shape — it is the VALUE carrier, \
         and the fixtures that drive projection and reflection need it",
    );
}

/// THE BOUNDARY GUARD IS STILL THERE, and this says so rather than assuming it: the
/// constructor is a second line, not a replacement. A dictionary that did not come
/// from `alloc_dictionary` — because a host used the unchecked constructor, or built
/// the value some other way — is still refused at the entry.
///
/// Both refusals are now phrased by ONE owner (`DictLayout::refuse_arity`), so a host
/// cannot be told two different stories about one wrong shape. What differs is the
/// attribution: this one names `call_with_requirements` and the entry op, the
/// construction one names nothing but the pair, because at construction there is no
/// call to blame yet — which is the point of moving it earlier.
#[test]
fn wi867_the_entry_boundary_still_refuses_a_short_dictionary() {
    let mut interp = crate::common::interp_for(SRC);
    let int64 = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Int64")
        .unwrap();
    let short = interp
        .alloc_dictionary_unchecked(int64, [])
        .expect("the value carrier builds any shape");

    let err = match interp.call_with_requirements(
        "wi867.host.Entry.main",
        &[Value::Int(3)],
        smallvec::SmallVec::from_iter([short]),
    ) {
        Err(e) => format!("{e}"),
        Ok(v) => panic!("a short dictionary must not reach the body; got {v:?}"),
    };
    assert!(
        err.contains("call_with_requirements") && err.contains("anthill.prelude.Ord"),
        "the boundary refusal names the entry and the slot's spec; got: {err}",
    );
}

/// …AND A LAYOUT-VALID CHANNEL STILL RUNS. Without this row the two refusals above
/// would be satisfied by a constructor that refuses everything.
#[test]
fn wi867_a_layout_valid_channel_runs() {
    let mut interp = crate::common::interp_for(SRC);
    let ord = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Ord")
        .unwrap();
    let int64 = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Int64")
        .unwrap();
    let sub = interp.alloc_dictionary_unchecked(int64, []).unwrap();
    let dict = interp
        .alloc_dictionary(ord, int64, [sub])
        .expect("layout-valid");

    match interp.call_with_requirements(
        "wi867.host.Entry.main",
        &[Value::Int(3)],
        smallvec::SmallVec::from_iter([dict]),
    ) {
        Ok(Value::Int(n)) => assert_eq!(n, 3, "`main` returns its argument"),
        other => panic!("a layout-valid channel must run the entry; got {other:?}"),
    }
}
