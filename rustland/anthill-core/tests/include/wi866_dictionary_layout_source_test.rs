//! WI-866 — the dictionary layout's NUMBER has the same one source its ORDER does,
//! and the dictionary's SPEC is decided rather than defaulted.
//!
//! WI-857 established the layout (spec half ++ provider half) and gave it one owner,
//! [`anthill_core::kb::typing::DictLayout`]. Two gaps in that invariant survived.
//! This file pins the SECOND; the first is synthetic and is pinned where it is
//! decided, in `kb::typing`'s `wi866_dict_layout_agreement_tests` — no program can
//! part a produced layout from the predicted one, since both walk the same chains, so
//! the divergence is built by hand against `divergence_from`, and
//! `check_against_prediction` is what would catch a real one at either producer.
//!
//! THE GAP HERE: both readers of "which spec is this dictionary laid out against"
//! wrote it as `impl_parent_of_op(op).unwrap_or(provider)`, an `unwrap_or` that folded
//! three unrelated answers into one and whose comment named the shape it never
//! reached. The rows below MEASURE the shapes an operation's canonical name can take.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::typing::{dict_layout, dispatch_spec_of_op, DispatchSpec};
use anthill_core::kb::KnowledgeBase;

/// Three operation shapes in one load, so the rows share every other variable:
/// a SORT MEMBER (`Holder.cmp`), a NAMESPACE-LEVEL operation (`nsLevel`), and a
/// TOP-LEVEL one (`topLevel`, outside every `namespace`).
///
/// `Holder` carries a two-entry `requires` chain over a spec whose own chain is
/// non-empty, which is WI-857's reproducer shape: it makes `Driver.main` an actual
/// two-half-dictionary dispatch rather than a witness-provider one.
const SRC: &str = r#"
operation topLevel(x: Int64) -> Int64
  = x

namespace wi866.shapes
  import anthill.prelude.{Int64, Bool, Eq, Ord, WeakOrd}

  operation nsLevel(x: Int64) -> Int64
    = x

  sort Holder
    sort T = ?
    requires Eq[T]
    requires Ord[T]
    operation cmp(a: T, b: T) -> Int64 = WeakOrd.compare(a, b)
  end

  sort Driver
    operation main(n: Int64) -> Int64 = Holder.cmp(nsLevel(7), topLevel(3))
  end
end
"#;

fn spec_name(kb: &KnowledgeBase, qn: &str) -> String {
    let op = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("{qn} must resolve — the fixture declares it"));
    match dispatch_spec_of_op(kb, op) {
        DispatchSpec::Spec(s) => kb.qualified_name_of(s).to_string(),
        DispatchSpec::NoSpec => "<no spec>".to_string(),
        DispatchSpec::UnresolvableParent => "<unresolvable parent>".to_string(),
    }
}

/// THE MEASUREMENT. Each row is one shape of canonical name, and the answers differ:
///
/// ```text
///   Holder.cmp              dotted, parent is a Sort       -> the sort
///   wi866.shapes.nsLevel    dotted, parent is a namespace  -> <no spec>
///   topLevel                DOT-LESS                       -> <no spec>
/// ```
///
/// BACK-OUT, and it is one row: point `dispatch_spec_of_op` at the pre-WI-866
/// derivation (`impl_parent_of_op(op).map_or(NoSpec, Spec)`) and the `nsLevel` row
/// answers `wi866.shapes` — a NAMESPACE named as a dictionary's spec. `Holder.cmp`
/// and `topLevel` pass either way BY DESIGN: the first is what the split already got
/// right, and the second is the only shape the `unwrap_or` ever actually served,
/// contrary to the comment that stood over it.
///
/// The fourth shape is `UnresolvableParent` — the one the ticket got wrong; see
/// `wi866_an_unresolvable_parent_is_the_wi234_form`.
#[test]
fn wi866_dispatch_spec_of_op_answers_by_shape() {
    let kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        spec_name(&kb, "wi866.shapes.Holder.cmp"),
        "wi866.shapes.Holder",
        "a SORT MEMBER's parent sort IS the dictionary's spec-half owner",
    );
    assert_eq!(
        spec_name(&kb, "wi866.shapes.nsLevel"),
        "<no spec>",
        "a NAMESPACE-level operation names no spec — a namespace declares no type \
         params and owns no requirement slots. This is the shape the `unwrap_or` \
         never reached and the shape its comment claimed",
    );
    assert_eq!(
        spec_name(&kb, "topLevel"),
        "<no spec>",
        "a TOP-LEVEL operation's canonical name is DOT-LESS, which is the shape the \
         `unwrap_or` actually served",
    );
}

/// WHAT THE NAMESPACE ROW BUYS, since it buys nothing arithmetically: every
/// `DictLayout::arity` and every `slots_for` answer is identical under both readings
/// (a namespace declares no `requires`, so its half counts 0 and the one-list reading
/// puts every slice in the same place). What differs is the only text a reader gets
/// when `expand_dispatching_dict`'s arity guard fires.
///
/// BACK-OUT: with the pre-WI-866 derivation the layout for a namespace-level
/// `dispatched_from` is `dict_layout(<the namespace>, provider)`, and its `describe`
/// names `wi866.shapes` as a SPEC — a sort-shaped claim about a namespace, in the
/// sentence that is supposed to explain which half of the dictionary is short.
#[test]
fn wi866_a_namespace_is_no_longer_described_as_a_spec() {
    let mut kb = crate::common::load_kb_with(SRC);
    let ns = kb.try_resolve_symbol("wi866.shapes").expect(
        "the namespace is a registered symbol — that is why it reached the \
                 `unwrap_or` as a `Some`",
    );
    let provider = kb
        .try_resolve_symbol("anthill.prelude.Int64")
        .expect("Int64 is a carrier-keyed provider");

    let old_reading = dict_layout(&mut kb, ns, provider).describe(&kb);
    assert!(
        old_reading.contains("spec `wi866.shapes`"),
        "the pre-WI-866 reading renders the namespace as the dictionary's spec; got: \
         {old_reading}",
    );

    let new_reading = dict_layout(&mut kb, provider, provider).describe(&kb);
    assert!(
        !new_reading.contains("wi866.shapes"),
        "the spec-less reading names only the provider, which is the whole of what \
         such a dictionary is; got: {new_reading}",
    );
    assert_eq!(
        dict_layout(&mut kb, ns, provider).arity(),
        dict_layout(&mut kb, provider, provider).arity(),
        "and the two readings still COUNT the same, which is why nothing failed \
         before — the defect was never arithmetic",
    );
}

/// THE ARM THE TICKET EXPECTED TO BE A RAISE, and is not.
///
/// WI-866 reads `UnresolvableParent` — a dotted canonical name whose parent segment is
/// not a registered symbol — as an inconsistent KB, and asked for both readers to
/// complain rather than "silently degrade to the one-list reading". MEASURED against
/// the suite, that is a live and DELIBERATE shape: the WI-234 Model 1 dispatch form
/// mints a synthetic spec-op-like symbol whose parent is never registered, and lets
/// the dispatching dict's own functor select the impl. Raising took
/// `wi223 apply_within_with_requirement_dispatch_resolves_via_handle_functor` from
/// green to `Internal("… parent segment resolves to nothing …")`.
///
/// So the arm exists to NAME the case, not to refuse it. What refuses a genuinely
/// wrong one-list reading is downstream and was already loud before this ticket: a
/// spec that really did contribute a half makes the dictionary longer than the
/// one-list layout counts, which is `expand_dispatching_dict`'s arity raise. This row
/// drives the classification directly, since no source syntax can write the name.
///
/// BACK-OUT: with the pre-WI-866 derivation this symbol answers `NoSpec` — the same
/// reading, for no stated reason, which is what let the ticket mistake it for a
/// defect.
#[test]
fn wi866_an_unresolvable_parent_is_the_wi234_form() {
    let mut kb = crate::common::load_kb_with(SRC);
    // Exactly what WI-234 Model 1 mints: a dotted name under a `Spec` that is not,
    // and never becomes, a registered symbol.
    let synthetic = kb.intern("wi866.shapes.NotASort.foo");
    assert!(
        kb.try_resolve_symbol("wi866.shapes.NotASort").is_none(),
        "the fixture must leave the parent segment unregistered, or this row is \
         measuring the sort-member case",
    );
    assert!(
        matches!(
            dispatch_spec_of_op(&kb, synthetic),
            DispatchSpec::UnresolvableParent
        ),
        "a dotted name whose parent resolves to nothing is its own answer, told apart \
         from `NoSpec` even though both take the one-list reading",
    );
}

/// The live path: `Driver.main` dispatches `WeakOrd.compare` through a `Holder`
/// dictionary with BOTH halves non-empty — WI-857's reproducer shape — with the
/// namespace-level and top-level operations supplying its arguments.
///
/// PASSES EITHER WAY BY DESIGN. It is the control for the refactor, not evidence for
/// the finding, and it is deliberately not claimed to exercise all three arms:
/// MEASURED with a probe on `expand_dispatching_dict`, this program reaches the
/// changed derivation exactly TWICE, both `Spec(..)` (`Holder.cmp` and
/// `WeakOrd.compare`). `nsLevel` and `topLevel` are requires-free calls that carry no
/// dispatching dictionary at all, so they never reach that site — a spec-less
/// operation reaching it needs a dict from somewhere else, which is what
/// `test.wi223.apply_within.produce` and `test.wi223.thread_through.read_my_req` do
/// (the `NoSpec` arm, 2 reaches across `wi_tests`) and `test.wi223.dispatch_form.Spec
/// .foo` does (the `UnresolvableParent` arm, 1 reach). Nothing in a WI-866 fixture
/// covers those two arms end to end; the wi223 file is what does.
#[test]
fn wi866_the_two_half_dispatch_still_runs() {
    let mut interp = crate::common::interp_for(SRC);
    match interp.call("wi866.shapes.Driver.main", &[Value::Int(0)]) {
        Ok(Value::Int(n)) => assert_eq!(
            n, 1,
            "compare(7, 3) is 1 for the prelude's ascending Int64 order",
        ),
        other => panic!("the two-half dispatch must run; got {other:?}"),
    }
}

// ── the SECOND producer: no dictionary is emitted short of its layout ──────

/// EVERY DICTIONARY THE LOADER EMITS, CENSUSED — not a fixture's.
///
/// WI-857's invariant is that a dictionary bundles exactly
/// `dict_layout(spec, provider).arity()` slots. `dict_sub_goals` now says so at its
/// own producer (`check_against_prediction`), but the WI-415 parent-bundle producer
/// (`build_dispatching_dict_from_chain`) had no such check and, on the
/// `require_complete = false` route, silently DROPPED a dep that failed to project —
/// leaving a dictionary with fewer slots than its own layout counts.
///
/// MEASURED before the fix, over the `anthill-core` suite: 2434 of 100641 emitted
/// dictionaries were short. 2401 were EMPTY where one slot was wanted, 25 empty where
/// two were, and one was PARTIAL (1 of 2) — the shape that mis-slots if anything
/// indexes it. They never reached a frame, because that route's term is
/// diagnostic-only (`req_insertion.rs`), which is exactly why a green suite could
/// carry them: an empty bundle is indistinguishable from a legitimately chain-free
/// one, so each of those entries told a reflection consumer "this call needs no
/// requirements" where in fact none could be built.
///
/// THIS ROW WALKS THE POPULATION rather than a fixture, because the fixture is not
/// where the defect lived — `anthill.prelude.PartialOrd` alone accounted for 2101 of
/// the 2434, and no WI-866 fixture would have produced one. Every rewritten
/// `apply_within` the load recorded is opened, its dispatching dictionary read, and
/// its slot count compared with the layout its own `impl` names.
///
/// BACKED OUT (restore `None => {}` in `build_dispatching_dict_from_chain`, and drop
/// the producer-side check so the emitted shape is what is measured): this row fails
/// with `` `wi866.shapes.Holder`: 0 slot(s) emitted, layout wants 2 `` — this
/// fixture's own two-entry chain, dropped whole. ONE violation here, where the
/// suite-wide probe counted 2434: the census sees only the rewrites recorded in THIS
/// KB, so it is a witness for the class, not a recount of it.
#[test]
fn wi866_no_emitted_dictionary_is_short_of_its_layout() {
    use anthill_core::kb::term::Term;

    let mut kb = crate::common::load_kb_with(SRC);
    let dict_ctor = kb
        .try_resolve_symbol("anthill.realization.runtime.Dictionary")
        .expect("the runtime Dictionary constructor is a stdlib name");
    let dict_impl = kb
        .try_resolve_symbol("anthill.realization.runtime.Dictionary.impl")
        .expect("…and so is its `impl` key");

    // Collect first: reading a layout needs `&mut kb`, and the walk borrows it.
    let mut dicts: Vec<(usize, Symbol)> = Vec::new();
    let mut stack: Vec<anthill_core::kb::term::TermId> =
        kb.dispatch_origin_iter().map(|(t, _)| t).collect();
    let recorded = stack.len();
    let mut seen = std::collections::HashSet::new();
    while let Some(tid) = stack.pop() {
        if !seen.insert(tid) {
            continue;
        }
        let Term::Fn {
            functor,
            pos_args,
            named_args,
        } = kb.get_term(tid)
        else {
            continue;
        };
        if *functor == dict_ctor {
            if let Some((_, impl_ref)) = named_args.iter().find(|(k, _)| *k == dict_impl) {
                if let Term::Ref(provider) = kb.get_term(*impl_ref) {
                    dicts.push((pos_args.len(), *provider));
                }
            }
        }
        stack.extend(pos_args.iter().copied());
        stack.extend(named_args.iter().map(|(_, v)| *v));
    }

    assert!(
        recorded > 0 && !dicts.is_empty(),
        "the walk must find dictionaries to judge, or it is measuring nothing: \
         {recorded} recorded rewrite(s), {} dictionar(ies)",
        dicts.len(),
    );

    let mut short: Vec<String> = Vec::new();
    for (slots, provider) in dicts {
        // A dictionary's own `impl` names its provider, and the parent-bundle shape
        // this producer builds has spec == provider (the layout's one-list rule).
        // A marker functor (`anthill.reflect.NoProvider…`, WI-865) is an ABSENCE, not
        // a provider, and bundles nothing by design.
        if kb
            .qualified_name_of(provider)
            .starts_with("anthill.reflect.NoProvider")
        {
            continue;
        }
        let want = dict_layout(&mut kb, provider, provider).arity();
        if slots != want {
            short.push(format!(
                "`{}`: {slots} slot(s) emitted, layout wants {want}",
                kb.qualified_name_of(provider),
            ));
        }
    }
    assert!(
        short.is_empty(),
        "no emitted dictionary may be short of the layout it is indexed by; {} \
         violation(s):\n  {}",
        short.len(),
        short.join("\n  "),
    );
}
