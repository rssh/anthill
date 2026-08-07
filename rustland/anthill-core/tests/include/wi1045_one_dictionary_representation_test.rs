//! WI-1045 — the eval-side `RequirementArena` is retired: a dictionary has ONE
//! representation, and the crossing converts nothing.
//!
//! Design: `docs/design/requirement-channel.md` §9.
//!
//! Before this there were TWO. σ carried `Dictionary(sub₀ … subₙ₋₁, impl: S)` — an
//! ordinary structured value (WI-1040) — while eval carried a `RequirementHandle`,
//! a refcounted slot whose identity was `(arena, raw)`, and
//! `eval_requirement_chain_node` converted term → handle at the SLD→eval edge. Two
//! identities for one thing is a hazard the channel doc had to WARN about: two
//! scratch interpreters are two arenas, so one dictionary got two `raw()`s and
//! every comparison had to be routed through the WI-1019 view or it silently
//! answered wrong. This deletes the hazard rather than documenting it, and deletes
//! the boundary at which the two forms could disagree.
//!
//! ## What this file DRIVES
//!
//! Each test builds a dictionary on a side and asserts a VALUE — never that
//! something loaded. The two sides are:
//!
//!  * **σ** — `?d = require[Desc[T]]` in a rule clause, resolved by the SLD
//!    builtin (`read_dictionary_into` → `fetch_dictionary`);
//!  * **eval** — an operation frame's `requirements` channel, entered through
//!    `Interpreter::call_with_requirements` and read by the body's
//!    `var_ref(__req_*)`.
//!
//! ## The refcount tests are DELETED, not ported
//!
//! `requirement_arena.rs` held eight unit tests about allocation, cascade drop,
//! slot sharing, free-list reuse and `(arena, raw)` identity. They went with the
//! file. Porting them would have been the way this retirement half-lands: a suite
//! that keeps testing the retired store reads as coverage while measuring
//! something that no longer exists. Two of their CLAIMS survive here, restated
//! against the value:
//!
//!  * "a projected sub-requirement is the child" → [`a_conditional_provisions_sub_dictionary_projects_by_index_on_both_sides`];
//!  * "two arenas' slot 0 are not one dictionary" →
//!    `wi1019_native_carrier_view_test::two_dictionaries_over_different_impls_are_not_equal`,
//!    which also pins the converse the arena could not express — one dictionary
//!    built on two sides IS one value.
//!
//! The arena live-count halves of `wi223_apply_within_test` and
//! `wi223_requirement_value_forms_test` were dropped for the same reason, each
//! with a note at its site.
//!
//! ## CONTROLS — what fails when the change is backed out
//!
//! | test | backed out ⇒ |
//! |---|---|
//! | `a_sigma_dictionary_dispatches_an_operation_frame` | does not COMPILE (the frame took a `RequirementHandle`), and semantically: the σ value had to be converted, so the answer came from whatever the conversion produced |
//! | `the_value_the_resolver_bound_is_the_value_the_frame_reads` | FAILS — the frame delivered `Value::Requirement(handle)`, a different carrier that compared equal only THROUGH the view, never as the same value |
//! | `a_conditional_provisions_sub_dictionary_projects_by_index_on_both_sides` | the σ half passes either way (WI-1040 shipped it); the EVAL half is what moved |
//! | `the_marker_is_refused_at_every_dispatch_read` | passes either way BY DESIGN — WI-857's refusal is what must SURVIVE the carrier change, so it is a regression guard, not a new claim |
//! | `the_ir_construction_node_and_the_value_share_one_constructor` | FAILS — the node was `Expr.construct_requirement(impl_functor =, requirements = <list>)`: a different functor, different key names, and a cons spine where the value has positional children |

use anthill_core::eval::value::Dictionary;
use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::term_view::{views_structurally_equal, TermView, ViewHead};

/// A spec `Desc` — itself `requires Base[T]`, so its dictionary carries a NESTED
/// sub-dictionary (WI-857: the spec's own chain is the dictionary's prefix) — and
/// two carriers supplying it, `Leaf` → `7` and `Other` → `9`. `Driver` is the
/// `requires`-carrying sort whose body dispatches the spec op through its frame
/// slot, which is the eval side of the crossing.
///
/// `describe` is BODY-LESS on purpose. That is what makes a body call to it defer
/// to the frame's dictionary (`DeferToRequirement`) instead of folding a default
/// or resolving from the receiver VALUE — MEASURED: with a defaulted `describe`,
/// `Driver.run` answered `7` under BOTH dictionaries, because the argument decided
/// and the frame slot was never read.
///
/// Two distinguishable carrier answers is the other half: `7` and `9` are supplied
/// by different sorts, so "dispatched through THIS dictionary" is measured rather
/// than assumed.
const SRC: &str = r#"
namespace test.wi1045
  import anthill.prelude.Int64

  sort Base
    sort T = ?
    operation base(x: T) -> Int64
  end

  sort Desc
    sort T = ?
    requires Base[T]
    -- BODY-LESS, so a body call to it defers to the caller's frame slot
    -- (`DeferToRequirement`) — the eval side of the crossing.
    operation describe(x: T) -> Int64
    -- Defaulted, and here only to be the rule clause's WITNESS: it grounds
    -- `require[Desc[T]]` without being the op whose dispatch is under test.
    operation tag(x: T) -> Int64 = 0
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Base[T = Leaf]
    provides Desc[T = Leaf]
    operation base(x: Leaf) -> Int64 = 3
    operation describe(x: Leaf) -> Int64 = 7
    operation mk() -> Leaf = leaf()
  end

  sort Other
    import anthill.prelude.Int64
    entity other
    provides Base[T = Other]
    provides Desc[T = Other]
    operation base(x: Other) -> Int64 = 4
    operation describe(x: Other) -> Int64 = 9
    operation mk() -> Other = other()
  end

  sort Driver
    sort T = ?
    requires Desc[T]
    operation run(x: T) -> Int64 = Desc.describe(x)
  end

  rule leafDict(?d) :- ?d = require[Desc[T]], Desc.tag(leaf(), ?i)
  rule otherDict(?d) :- ?d = require[Desc[T]], Desc.tag(other(), ?i)
end
"#;

/// The single dictionary `{ns}.{rule}(?d)` binds, as the σ side built it.
///
/// Panics on anything but one definite answer — "the query returned nothing" must
/// never read as a pass, and a second answer would mean the rule is not the
/// single-provider case this file is about.
fn sigma_dictionary(rule: &str) -> (Interpreter, Value) {
    let mut kb = crate::common::load_kb_with(SRC);
    let sols = crate::common::query_unary(&mut kb, &format!("test.wi1045.{rule}"));
    let value = match sols.as_slice() {
        [(v, true)] => v.clone(),
        other => panic!("`{rule}(?d)` must bind exactly one definite dictionary, got {other:?}"),
    };
    // A FRESH interpreter needs its builtins bound — `register_standard_builtins`
    // is per-interpreter, not per-KB (WI-968).
    let mut interp = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    (interp, value)
}

/// A carrier value, built by RUNNING its constructor op rather than assembled by
/// hand — so the value that reaches `Driver.run` is the one the language makes.
fn carrier(interp: &mut Interpreter, sort: &str) -> Value {
    interp
        .call(&format!("test.wi1045.{sort}.mk"), &[])
        .unwrap_or_else(|e| panic!("{sort}.mk() must run, got {e:?}"))
}

/// The dictionary a `Value` IS — the ONE boundary check in the crate. Before
/// WI-1045 this crossing did not exist as a check: it was a CONVERSION
/// (`eval_requirement_chain_node`) that minted an arena handle with a fresh
/// identity.
fn as_dictionary(interp: &Interpreter, v: &Value) -> Dictionary {
    Dictionary::from_value(interp.kb(), v)
        .unwrap_or_else(|| panic!("expected a dictionary value, got {v:?}"))
}

// ── (a) + (b): σ builds it, an operation frame reads it ─────────────────────

/// ACCEPTANCE (a) + (b) — a dictionary the SLD fetch built is installed into an
/// operation call's frame with NO conversion step, and the body's dispatch reads
/// it: `Driver.run` answers the CARRIER's `7`, not the spec default's `1`.
///
/// The `Other` arm is what makes that non-vacuous: the SAME op with the SAME
/// argument answers `9` when the dictionary names the other carrier, so the answer
/// is decided by the dictionary and by nothing else. (`run`'s argument is a `Leaf`
/// in both arms deliberately — if dispatch were reading the VALUE rather than the
/// frame slot, both arms would answer `7`.)
#[test]
fn a_sigma_dictionary_dispatches_an_operation_frame() {
    let run = |rule: &str| -> i64 {
        let (mut interp, v) = sigma_dictionary(rule);
        let dict = as_dictionary(&interp, &v);
        let leaf = carrier(&mut interp, "Leaf");
        let got = interp.call_with_requirements(
            "test.wi1045.Driver.run",
            &[leaf],
            smallvec::smallvec![dict],
        );
        match got {
            Ok(Value::Int(n)) => n,
            other => panic!("Driver.run under the {rule} dictionary must answer an Int, got {other:?}"),
        }
    };

    assert_eq!(
        run("leafDict"), 7,
        "the frame must dispatch through the dictionary σ bound — `7` is `Leaf`'s \
         own `describe`, and `1` would be the spec default (no dictionary read)",
    );
    assert_eq!(
        run("otherDict"), 9,
        "and the dictionary DECIDES: the same op on the same argument answers \
         `Other`'s `9` when the frame carries `Other`'s dictionary",
    );
}

/// ACCEPTANCE (a) — the crossing converts NOTHING: the value an operation body
/// reads out of `frame.requirements` is the very value σ bound.
///
/// Asserted two ways because they fail differently. `views_structurally_equal` is
/// the weaker claim and is the one that held BEFORE this change (through the
/// WI-1019 view, which is exactly what the channel doc had to warn was the only
/// safe comparison). `Dictionary::from_value(..) == ..` is the new one: both sides
/// are the same type, so they compare directly, with no view to route through and
/// no arena half to drop.
#[test]
fn the_value_the_resolver_bound_is_the_value_the_frame_reads() {
    let (mut interp, bound) = sigma_dictionary("leafDict");
    let dict = as_dictionary(&interp, &bound);

    // Seed a frame with the σ dictionary and run a body that reads it back by
    // name — the `var_ref(__req_*)` read, which is where a body meets its
    // requirement channel.
    let var_ref_sym = interp.kb().try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("reflect.Expr.var_ref is in the stdlib");
    let req_name = interp.kb_mut().intern("__req_probe");
    let name_field = interp.kb_mut().intern("name");
    let name_ref = interp.kb_mut().alloc(anthill_core::kb::term::Term::Ref(req_name));
    let expr = interp.kb_mut().alloc(anthill_core::kb::term::Term::Fn {
        functor: var_ref_sym,
        pos_args: smallvec::SmallVec::new(),
        named_args: smallvec::SmallVec::from_slice(&[(name_field, name_ref)]),
    });

    let read_back = interp
        .run_with_requirements(expr, smallvec::smallvec![(req_name, dict.clone())])
        .expect("a body reading its requirement param must reduce");

    assert!(
        views_structurally_equal(interp.kb(), &bound, &read_back),
        "the frame read must present the same shape σ bound — got {read_back:?}",
    );
    assert_eq!(
        as_dictionary(&interp, &read_back), dict,
        "and it must BE the same dictionary: one type, compared directly. Before \
         WI-1045 the frame held an arena handle, so this comparison could not even \
         be spelled — only the view above could",
    );

    // NON-VACUITY: the read reports WHAT WAS SEEDED, not a constant. Seeding the
    // other carrier's dictionary through the same body must deliver that one.
    let (_, other_bound) = sigma_dictionary("otherDict");
    let other = as_dictionary(&interp, &other_bound);
    assert_ne!(other, dict, "the two rules must bind different dictionaries");
    let read_other = interp
        .run_with_requirements(expr, smallvec::smallvec![(req_name, other.clone())])
        .expect("the same body under the other dictionary must reduce");
    assert_eq!(
        as_dictionary(&interp, &read_other), other,
        "the frame read follows what was seeded — without this, both assertions \
         above would hold for a body that ignored its channel and answered a \
         constant",
    );
}

// ── (c) nested sub-dictionaries ─────────────────────────────────────────────

/// ACCEPTANCE (c) — a spec whose own `requires` chain is non-empty produces a
/// dictionary with a nested sub-dictionary, and slot `k` reads the same on both
/// sides: through [`Dictionary::sub`] (what the eval's `requirement_at_sort` and
/// `expand_dispatching_dict` call) and through the reflect `Dictionary.sub`
/// builtin (what anthill code calls).
///
/// `Desc requires Base[T]` (WI-857's layout: the SPEC's own chain is the
/// dictionary's prefix), so `Desc[Leaf]` bundles `Base[Leaf]` at slot 0.
///
/// The EVAL half — a body reaching a sub-slot's op transitively, which is a
/// `requirement_at_sort` projection at run time — is driven by
/// `wi857_dictionary_layout_test::a_requires_eq_holder_reaches_partialeq_transitively`
/// and is not duplicated; what is new here is that the σ-BUILT dictionary projects
/// identically through BOTH readers, which is what "one representation" claims.
#[test]
fn a_conditional_provisions_sub_dictionary_projects_by_index_on_both_sides() {
    let (mut interp, bound) = sigma_dictionary("leafDict");
    let dict = as_dictionary(&interp, &bound);

    assert_eq!(
        dict.arity(), 1,
        "WI-857: a `Desc` dictionary carries the SPEC's own chain as its prefix, and \
         `Desc requires Base[T]` — so it bundles exactly one sub-dictionary",
    );
    let sub = dict.sub(0).expect("slot 0");

    // The reflect face, over the SAME value — the read anthill code makes.
    let via_builtin = interp
        .call("anthill.realization.runtime.Dictionary.sub", &[bound.clone(), Value::Int(0)])
        .expect("Dictionary.sub must project slot 0");
    assert_eq!(
        as_dictionary(&interp, &via_builtin), sub,
        "slot 0 read through the reflect face and through the internal projection \
         must be ONE value — there is no second representation for them to differ in",
    );

    // …and it is a real sub-dictionary, not an empty one that would compare equal
    // to anything: `PartialEq[Int64]` is supplied by `Int64` itself.
    let impl_qn = interp.kb().qualified_name_of(sub.impl_sort()).to_string();
    assert_eq!(
        impl_qn, "test.wi1045.Leaf",
        "the bundled `Base[Leaf]` names the carrier that supplies it",
    );
}

// ── (d) the marker survives the carrier change ──────────────────────────────

/// ACCEPTANCE (d) — WI-857's `NoProvider` marker is still refused at every
/// dispatch read.
///
/// A marker dictionary pins no provider, so dispatching through it would silently
/// fall through to the spec's own default — taking the host answer where a
/// provider's was wanted. Both reflect dispatch faces must refuse it, and the
/// in-body projection refusal is
/// `wi857_dictionary_layout_test::reading_an_unprovided_spec_half_slot_is_loud`.
///
/// PASSES EITHER WAY BY DESIGN: this is a regression guard on WI-857, not a new
/// claim. The carrier under it changed; the refusal must not have.
#[test]
fn the_marker_is_refused_at_every_dispatch_read() {
    let mut interp = crate::common::interp_for(SRC);
    let marker_sym = interp.kb_mut().intern("anthill.reflect.NoProvider");
    let marker = crate::common::dict(&interp, marker_sym, []).into_value();
    let eq_op = interp.kb().try_resolve_symbol("anthill.prelude.PartialEq.eq")
        .expect("PartialEq.eq is in the stdlib");

    let err = interp
        .call(
            "anthill.realization.runtime.Dictionary.resolveOp",
            &[marker.clone(), Value::SymbolRef(eq_op)],
        )
        .expect_err("resolveOp MINTS A CALLABLE, so a marker must not resolve one");
    assert!(
        format!("{err}").contains("no provider"),
        "and the refusal must name the marker, got {err}",
    );

    let err = interp
        .call("anthill.realization.runtime.Dictionary.ops", &[marker])
        .expect_err("the BULK face must refuse the marker up front, not answer `nil`");
    assert!(
        format!("{err}").contains("no provider"),
        "…with the same reason — an empty list would be the quieter wrong answer, \
         got {err}",
    );
}

// ── one spelling ────────────────────────────────────────────────────────────

/// The IR CONSTRUCTION node and the VALUE it evaluates to are ONE constructor:
/// same functor, same key set (positional sub-dictionaries, one named `impl`).
///
/// The node was `anthill.reflect.Expr.construct_requirement(impl_functor = …,
/// requirements = <cons list>)` — a different functor, different key names, and a
/// LIST where the value has positional children. Channel doc §9 made collapsing
/// them a condition of this ticket rather than a branch of one.
///
/// Asserted by comparing the HEADS of all THREE carriers one dictionary rides —
/// the `TermId` the typer emits, the `NodeOccurrence` the materializer builds from
/// it, and the `Value` it evaluates to. That is the strongest form available: if
/// the functor or either arity differed on any of them, they would key differently
/// in the discrim tree and fingerprint differently.
///
/// The OCCURRENCE arm is the one WI-1045's review added. It headed `Opaque` while
/// the other two agreed, which is a third head for the thing "one representation"
/// says has one — and unlike `Expr::ApplyWithin` (whose faithful twin is the
/// WRAPPED reflect shape, so a transparent head would be a WI-425/WI-815
/// cross-carrier miss), this node's twin IS what its head says.
#[test]
fn the_ir_construction_node_and_the_value_share_one_constructor() {
    let mut interp = crate::common::interp_for(SRC);
    let leaf = interp.kb().try_resolve_symbol("test.wi1045.Leaf")
        .expect("Leaf is declared above");
    let inner = crate::common::dict_term(interp.kb_mut(), leaf, &[]);
    let node = crate::common::dict_term(interp.kb_mut(), leaf, &[inner]);

    let value = interp
        .run_with_requirements(node, smallvec::SmallVec::new())
        .expect("the Dictionary IR node must reduce");

    let occ = anthill_core::kb::node_occurrence::materialize_from_handle(interp.kb(), node);
    let term_head = anthill_core::kb::term_view::TermIdView(node).head(interp.kb());
    let occ_head = Value::Node(occ).head(interp.kb());
    let value_head = value.head(interp.kb());
    assert_eq!(
        format!("{term_head:?}"), format!("{value_head:?}"),
        "the construction node and the value it evaluates to must present the SAME \
         head — one functor, one key set (requirement-channel.md §9)",
    );
    assert_eq!(
        format!("{occ_head:?}"), format!("{value_head:?}"),
        "and so must the OCCURRENCE carrier — three carriers of one dictionary, \
         one head",
    );
    match value_head {
        ViewHead::Functor { functor: Some(f), pos_arity, named_arity } => {
            assert_eq!(
                interp.kb().qualified_name_of(f), "anthill.realization.runtime.Dictionary",
                "and that functor is the DICTIONARY's, not a second constructor's",
            );
            assert_eq!(pos_arity, 1, "one positional sub-dictionary");
            assert_eq!(named_arity, 1, "and `impl`");
        }
        other => panic!("a dictionary presents a constructor head, got {other:?}"),
    }
}
