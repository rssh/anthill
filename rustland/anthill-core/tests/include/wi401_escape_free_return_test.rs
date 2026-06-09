//! WI-401: reject the ABSTRACTING (sealing) return so the base model is escape-free
//! (docs/design/path-dependent-types.md §5). A return must be INTERFACE-EXPRESSIBLE —
//! concrete, rooted at the operation's own inputs (a param's type / its type-params), or
//! (the deferred WI-402 admit-form) made manifest by an `ensures`. The one thing that
//! escapes is a concrete carrier UPCAST to the bare abstract spec it provides
//! (`seal(s: SubscriberStore) -> DataProvider = s`): the `K = String` is erased, so the
//! resulting `DataProvider.K` roots at nothing in scope — the ML avoidance problem. This
//! removes the only hidden-local-type introducer (sealing), so every rigid path roots at
//! an in-scope param / global.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

const PRELUDE: &str = r#"
  import anthill.prelude.String
  sort DataProvider
    sort K = ?
  end
  sort SubscriberStore
    provides DataProvider[K = String]
    entity subscriberStore
  end
"#;

/// THE escape: a concrete carrier returned as the BARE abstract spec it provides. The body
/// (`s : SubscriberStore`) conforms to `DataProvider` only by the provider upcast, which
/// erases `K = String` — so `DataProvider.K` would escape. WI-401 rejects it.
#[test]
fn abstracting_return_is_rejected() {
    let seal = format!(
        "namespace test.wi401.seal\n{PRELUDE}\n  operation seal(s: SubscriberStore) -> DataProvider = s\nend\n"
    );
    let errs = load_errors(&[&seal]);
    assert!(
        errs.iter().any(|e| e.contains("abstracting return") || e.contains("escape")),
        "seal(s: SubscriberStore) -> DataProvider = s upcasts a concrete carrier to a bare \
         spec — must be rejected as an abstracting return; got: {errs:?}",
    );
}

/// SAME base sort introduces no NEW abstraction: `p` is already an abstract `DataProvider`,
/// and returning it as `DataProvider` roots the abstractness at the input `p` (interface,
/// not hidden-local). Allowed.
#[test]
fn same_sort_abstract_return_is_allowed() {
    let ok = format!(
        "namespace test.wi401.passthrough\n{PRELUDE}\n  operation relay(p: DataProvider) -> DataProvider = p\nend\n"
    );
    assert!(
        load_errors(&[&ok]).is_empty(),
        "relay(p: DataProvider) -> DataProvider = p is input-rooted (no new abstraction); \
         must be allowed; got: {:?}",
        load_errors(&[&ok]),
    );
}

/// A CONCRETE return (returning the carrier as itself) is interface-expressible — no
/// abstract member to escape. Allowed (the provider upcast is not taken).
#[test]
fn concrete_return_is_allowed() {
    let ok = format!(
        "namespace test.wi401.concrete\n{PRELUDE}\n  operation keep(s: SubscriberStore) -> SubscriberStore = s\nend\n"
    );
    assert!(
        load_errors(&[&ok]).is_empty(),
        "keep(s: SubscriberStore) -> SubscriberStore = s is concrete; must be allowed; got: {:?}",
        load_errors(&[&ok]),
    );
}

/// A type-parameter return is rooted at the operation's own type-param (an input) — the
/// caller instantiates it. Allowed.
#[test]
fn type_param_return_is_allowed() {
    let ok = r#"
namespace test.wi401.tparam
  operation id[T](x: T) -> T = x
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "id[T](x: T) -> T = x is rooted at the op's type-param; must be allowed; got: {:?}",
        load_errors(&[ok]),
    );
}

/// A MANIFEST spec return that binds every member roots them at the op's inputs (here the
/// element type-param `Elem`), so nothing abstract escapes: `List provides Stream[T, {}]`,
/// and `toStream(l: List[Elem]) -> Stream[T = Elem, E = {}] = l` carries both members.
/// Allowed (the bare-spec escape check must not fire on a manifest return).
#[test]
fn manifest_spec_return_is_allowed() {
    let ok = r#"
namespace test.wi401.manifest
  import anthill.prelude.{List, Stream}
  operation toStream[Elem](l: List[T = Elem]) -> Stream[T = Elem, E = {}] = l
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "a manifest Stream[T = Elem, E = {{}}] return binds every member (input-rooted) and \
         must be allowed; got: {:?}",
        load_errors(&[ok]),
    );
}
