//! WI-201: bare spec-sort member sugar — `Spec.Member` in an operation signature
//! type position (e.g. `s: WorkItemStore.State`).
//!
//! Desugars CARRIER-DIRECT (design path-dependent-types.md §5.4, user-confirmed
//! 2026-06-16): a bare `Spec.Member`, where `Member` is a declared type-param of the
//! spec sort `Spec` and no carrier is in scope, lowers to a fresh op type-param `?P`
//! whose synthesized `requires Spec[Member = ?P]` constrains it — the type at that
//! position IS `?P` (NOT a `?P.Member` projection). Reading A, not the ticket's
//! original "rides RigidTypeProjection" prose: the WorkItemStore.State driving case
//! projects the spec's SOLE param/carrier, so a `?P.State` projection could never
//! infer `?P` from an argument (non-injective). `?P` typechecks identically to the
//! explicit `[P](…) requires Spec[Member = P]` form and infers at concrete calls.
//!
//! Disambiguation:
//!   - INSIDE an impl that binds the carrier (`fact WorkItemStore[State = WIS]`),
//!     `WorkItemStore.State` NARROWS to the bound carrier (WIS) — order-independent of
//!     the fact-vs-op source order.
//!   - a member the spec does NOT declare (`Spec.Nope`) stays LOUD.
//!   - the sugar fires ONLY in operation signatures; a bare-spec member in a
//!     sort/entity field stays the loud `RigidTypeProjection` conflation error.

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

/// The shared WorkItemStore-shaped spec + carrier: `Store` has a SOLE type-param
/// `State` (its carrier — the slot a `fact`/`provides` binds); `WIS` is the concrete
/// state shape an impl carries. (`peek` gives the spec a member op so it is a real
/// interface.)
const STORE: &str = r#"
  sort Store
    sort State = ?
    operation peek(s: State) -> Bool
  end
  enum WIS
    entity wis(n: Int64)
  end
"#;

fn with_store(ns: &str, rest: &str) -> String {
    format!(
        "namespace test.wi201.{ns}\n  import anthill.prelude.{{Int64, Bool}}\n{STORE}\n{rest}\nend\n"
    )
}

/// CORE: a bare `Store.State` param desugars to a fresh `?P` + synthesized requires,
/// loads clean, and a CONCRETE call infers `?P` from the argument's type — exactly
/// like the explicit `[P](s: P) requires Store[State = P]` form.
#[test]
fn bare_spec_member_param_infers_at_concrete_call() {
    let sugar = with_store(
        "infer",
        "  operation useSugar(s: Store.State) -> Int64\n  \
         operation callIt(x: WIS) -> Int64 = useSugar(x)\n",
    );
    let explicit = with_store(
        "infer_explicit",
        "  operation useExplicit[P](s: P) -> Int64 requires Store[State = P]\n  \
         operation callIt(x: WIS) -> Int64 = useExplicit(x)\n",
    );
    assert!(
        load_errors(&[&sugar]).is_empty(),
        "bare Store.State param + concrete call should load clean",
    );
    assert!(
        load_errors(&[&explicit]).is_empty(),
        "the explicit desugaring this lowers to should also load clean",
    );
}

/// DEDUP: two refs to the SAME `Store.State` in one signature (param + return) share
/// one `?P`, so an identity body `= s` conforms to the declared return.
#[test]
fn two_refs_in_one_signature_share_one_carrier() {
    let src = with_store(
        "share",
        "  operation idState(s: Store.State) -> Store.State = s\n",
    );
    assert!(
        load_errors(&[&src]).is_empty(),
        "param `Store.State` and return `Store.State` are the same `?P` ⟹ `= s` conforms",
    );
}

/// DISTINCT operations get DISTINCT carriers: each op gets its own fresh accumulator,
/// so two independent sugar operations load clean side by side (the sharing is scoped
/// to one signature, never a single global var).
#[test]
fn distinct_operations_get_distinct_carriers() {
    let src = with_store(
        "distinct",
        "  operation first(s: Store.State) -> Int64\n  \
         operation second(s: Store.State) -> Int64\n",
    );
    assert!(
        load_errors(&[&src]).is_empty(),
        "two operations each minting their own `?P` should load clean",
    );
}

/// NARROWING: inside an impl that binds `Store[State = WIS]`, `Store.State` denotes the
/// bound carrier WIS — so a body returning `s` conforms to `-> WIS`.
#[test]
fn carrier_in_scope_narrows_to_bound_type() {
    let src = with_store(
        "narrow",
        "  sort FileStore\n    fact Store[State = WIS]\n    \
         operation idWis(s: Store.State) -> WIS = s\n  end\n",
    );
    assert!(
        load_errors(&[&src]).is_empty(),
        "inside the binding impl, Store.State ≡ WIS ⟹ `s` conforms to `-> WIS`",
    );
}

/// The narrowing is REAL (WIS, not a generic existential): a body returning the
/// narrowed `s` under a declared `-> Int64` is rejected with the CONCRETE WIS type.
#[test]
fn carrier_in_scope_narrowing_is_real() {
    let src = with_store(
        "narrow_real",
        "  sort FileStore\n    fact Store[State = WIS]\n    \
         operation badRet(s: Store.State) -> Int64 = s\n  end\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("Int64") && e.contains("WIS")),
        "narrowed Store.State is WIS, rejected against -> Int64 with the concrete type; got: {errs:?}",
    );
}

/// The narrowing is ORDER-INDEPENDENT: the using operation may appear BEFORE the
/// binding `fact` in source (the bindings are pre-scanned from the parse items).
#[test]
fn carrier_in_scope_narrowing_is_order_independent() {
    let src = with_store(
        "narrow_order",
        "  sort FileStore\n    \
         operation idWis(s: Store.State) -> WIS = s\n    \
         fact Store[State = WIS]\n  end\n",
    );
    assert!(
        load_errors(&[&src]).is_empty(),
        "op declared before the binding fact still narrows (pre-scan is order-independent)",
    );
}

/// A POSITIONAL binding (`fact Store[WIS]`) narrows too — mapped to the spec's first
/// declared parameter, identical to `fact Store[State = WIS]`.
#[test]
fn carrier_in_scope_narrowing_positional_binding() {
    let src = with_store(
        "narrow_pos",
        "  sort FileStore\n    fact Store[WIS]\n    \
         operation idWis(s: Store.State) -> WIS = s\n  end\n",
    );
    assert!(
        load_errors(&[&src]).is_empty(),
        "positional `fact Store[WIS]` narrows Store.State to WIS",
    );
}

/// OUTSIDE a binding impl the sugar stays a GENERIC existential — a body returning it
/// under `-> WIS` is rejected (`?State`, not WIS). Guards that narrowing is scoped to
/// the binding sort, not applied globally.
#[test]
fn no_carrier_in_scope_stays_generic() {
    let src = with_store(
        "generic",
        "  operation gen(s: Store.State) -> WIS = s\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("WIS") && (e.contains("State") || e.contains("?"))),
        "no binding in scope ⟹ Store.State is a generic existential, not WIS; got: {errs:?}",
    );
}

/// LOUD: a member the spec does NOT declare (`Store.Nope`) never silently synthesizes
/// a carrier — it stays the loud no-member error.
#[test]
fn undeclared_member_is_loud() {
    let src = with_store(
        "undeclared",
        "  operation bad(s: Store.Nope) -> Int64\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("Nope")),
        "Store.Nope: no such member ⟹ loud, never a silent carrier; got: {errs:?}",
    );
}

/// SPEC-ONLY: a parameterized DATA sort (one with constructors — `Option`, `List`, a
/// user enum) is NOT a spec, so `DataSort.T` in an op signature stays the loud
/// conflation error, never a silent existential. (`T` is a data type-param, not an
/// associated spec member.)
#[test]
fn data_sort_member_is_not_sugar() {
    let src = format!(
        "namespace test.wi201.datasort\n  import anthill.prelude.Int64\n\
         \x20 enum Box\n    sort T = ?\n    entity box(v: T)\n  end\n\
         \x20 operation weird(x: Box.T) -> Int64\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("conflate distinct carriers")),
        "Box has constructors ⟹ Box.T is not the spec sugar, stays loud; got: {errs:?}",
    );
}

/// A fact binding the spec member to a NON-concrete carrier (a logic var) does not
/// narrow — it falls back to the fresh `?P` existential rather than leaking an
/// uninferable var into the signature (so a body under `-> WIS` is rejected as the
/// generic `?State`, not the var).
#[test]
fn non_concrete_binding_falls_back_to_existential() {
    let src = with_store(
        "nonconcrete",
        "  sort FileStore\n    fact Store[State = ?x]\n    \
         operation idWis(s: Store.State) -> WIS = s\n  end\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("WIS") && !e.contains("?x")),
        "a var-valued binding falls back to the generic existential, never narrows to ?x; got: {errs:?}",
    );
}

/// CONFLICTING carrier facts for one `(spec, member)` do not silently last-win: the
/// ambiguous binding is dropped, so the sugar mints a fresh existential (the body
/// under `-> WIS` is rejected as the generic `?State`, not one of the two carriers).
#[test]
fn conflicting_carrier_bindings_do_not_narrow() {
    let src = with_store(
        "conflict",
        "  enum WIS2\n    entity wis2(n: Int64)\n  end\n  \
         sort FileStore\n    fact Store[State = WIS]\n    fact Store[State = WIS2]\n    \
         operation idWis(s: Store.State) -> WIS = s\n  end\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("WIS") && e.contains("State")),
        "two conflicting carrier facts ⟹ no narrowing, a generic existential; got: {errs:?}",
    );
}

/// SCOPED to operation signatures: a bare-spec member in a sort/entity FIELD type
/// (not an op signature) keeps the loud `RigidTypeProjection` conflation error — the
/// sugar accumulator is armed only while loading an operation signature.
#[test]
fn bare_spec_member_in_entity_field_stays_loud() {
    let src = with_store(
        "field",
        "  sort Holder\n    entity holder(s: Store.State)\n  end\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("conflate distinct carriers")),
        "Store.State in an entity field is not an op signature ⟹ stays loud; got: {errs:?}",
    );
}
