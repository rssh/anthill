//! WI-20260919-HXGXF (proposal 065 §2) — derive `anthill.reflect.TypeValue` for every
//! sort, CONDITIONAL for a parametric one.
//!
//! `TypeValue[T]` is evidence that the rigid `T` may be read as a value, and
//! `type_value()` answers the `Type` it names. The instance is what carries that
//! evidence to run time, and it is DERIVED for every sort — never written (065 §2: a
//! forgeable instance turns every type read into a claim instead of a fact).
//!
//! **THE SAME SHAPE `eq_derive` RUNS, WITH ONE DIFFERENCE THAT MATTERS.** A concrete sort
//! gets an unconditional row; a parametric one gets a row conditioned on its parameters —
//! `Box provides TypeValue[T = Box] :- TypeValue[T = V]`, which is
//! `Typeable a => Typeable (Box a)`. Where the `NonEq` mirror (WI-20260919-9KYPA) spells
//! a DISJUNCTION as one clause per parameter, this is a CONJUNCTION in ONE clause: a type
//! is nameable iff EVERY argument is, exactly as a composite is lawfully `Eq` iff every
//! field is.
//!
//! **THE CONDITION ORDER IS LOAD-BEARING.** The conditions are emitted in the carrier's
//! DECLARATION order, and `eval::builtins::type_value_of_self` reads the dispatching
//! dictionary positionally — sub `i` after the carrier's own `requires` is the evidence
//! for parameter `i`. Reordering them here silently answers `Duo[L = Bang, R = Boom]` for
//! `Duo[L = Boom, R = Bang]`. The builtin re-derives the same offset and checks the count,
//! so a disagreement is loud rather than a wrong type — but it is a disagreement this
//! module is the one to avoid.
//!
//! **WHY THE ROWS CARRY NO OPERATION.** `TypeValue.type_value` is body-less and backed by
//! a BUILTIN on the spec op (`BuiltinTag::TypeValueOf`, registered in `load`), so one
//! backing serves every carrier and no derived row needs a member. That is forced, not
//! chosen: `type_value()` is nullary, so nothing but the dictionary names the type, so the
//! call must reach the requirement slot — and a spec op with a DEFAULT BODY is dispatched
//! statically and never does (measured: the body ran with an empty requirements frame).
//! See the spec's own comment in `stdlib/anthill/reflect/reflect.anthill`.
//!
//! SCOPE: sorts. Structural FORMERS (named tuples, arrows) have no sort to carry a
//! provision and are deliberately out — they need a structural reading, the same open
//! shape as the named-tuple key in `docs/kernel-language.md` §8.3.

use std::collections::HashSet;

use crate::intern::Symbol;
use crate::kb::term::Term;
use crate::kb::KnowledgeBase;

/// Every sort that should carry a `TypeValue` row, in `SortInfo` fact order so the clause
/// indices a program gets do not depend on a hash iteration order.
///
/// `SortInfo` is the canonical record of a DECLARED sort — the same list
/// `build_sort_info_index` buckets — so this reaches an abstract carrier (`Map`, `Set`)
/// as well as a concrete one. That is deliberate: `Map[K = Int64, V = Int64]` is a type an
/// author writes, so it needs to be nameable, and `check_provider_operations` skips a
/// value-less carrier anyway.
fn declared_sorts(kb: &KnowledgeBase) -> Vec<Symbol> {
    let Some(sort_info_sym) = kb.try_resolve_symbol("anthill.reflect.SortInfo") else {
        return Vec::new();
    };
    let mut out: Vec<Symbol> = Vec::new();
    let mut seen: HashSet<Symbol> = HashSet::new();
    for rid in kb.rules_by_functor(sort_info_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else {
            continue;
        };
        let Some(name_tid) = super::typing::get_named_arg(kb, &named, "name") else {
            continue;
        };
        // The same two shapes `build_sort_info_index` accepts, read the same way, so the
        // domain here and the index there cannot drift.
        let name_sym = match kb.get_term(name_tid) {
            Term::Ref(s) => *s,
            Term::Fn { functor, .. } => *functor,
            _ => continue,
        };
        if seen.insert(kb.canonical_sort_sym(name_sym)) {
            out.push(name_sym);
        }
    }
    out
}

/// WI-20260919-HXGXF — assert the derived rows. A post-load pass; see the module header.
///
/// Placement mirrors `eq_derive::run`'s reason and not its hazard: these rows ARE backed
/// (the spec-op builtin), so they are held to `check_provider_operations` like any written
/// provision and need no unbacked mark. What they must be after is the `SortInfo` walk
/// that `declared_sorts` reads.
///
/// IDEMPOTENT ACROSS LOAD PHASES, by the same guard `eq_derive` uses: a later phase
/// re-runs this with phase 1's rows already in the relation, and a second
/// `record_derived_conditions` would file a duplicate clause that `provision_conditions`
/// would then read as a real alternative — which `provision_layout_key` turns into "no
/// slots at all", so the dictionary would arrive empty and every type read would fail.
pub(crate) fn run(kb: &mut KnowledgeBase) -> Vec<super::load::LoadError> {
    let Some(spec) = kb.try_resolve_symbol("anthill.reflect.TypeValue") else {
        return Vec::new();
    };
    // DERIVED-ONLY (065 §2), checked HERE and not in a pass of its own, because here is
    // the one moment the two populations are distinguishable: this runs before a single
    // row is derived, so every `TypeValue` provision standing in the relation now is one
    // an author wrote. A later check would have to tell its own output from theirs.
    //
    // Reads the provision relation rather than the three SYNTAXES that fill it (a
    // carrier's body, a `namespace <Carrier>` block, a witness sort), so a spelling
    // cannot escape by being added elsewhere — the WI-835 lesson about enumerating
    // positions instead of reading the producer.
    let mut errors: Vec<super::load::LoadError> = super::typing::provision_carriers_of_spec(kb, spec)
        .into_iter()
        .filter(|c| {
            // Not one of OURS from an earlier phase. See
            // [`KnowledgeBase::derived_type_value_carriers`] for why provenance has to be
            // recorded rather than read off the relation.
            !kb.derived_type_value_carriers
                .contains(&kb.canonical_sort_sym(*c))
        })
        .map(|c| super::load::LoadError::HandWrittenTypeValue {
            carrier: kb.qualified_name_of(c).to_string(),
        })
        .collect();
    // Deterministic order by the one field the variant carries, so a multi-carrier
    // refusal reads the same on every run. Keyed on `carrier` directly rather than on a
    // `{:?}` rendering, which allocated two Strings per COMPARISON.
    errors.sort_by(|a, b| match (a, b) {
        (
            super::load::LoadError::HandWrittenTypeValue { carrier: x },
            super::load::LoadError::HandWrittenTypeValue { carrier: y },
        ) => x.cmp(y),
        _ => std::cmp::Ordering::Equal,
    });
    errors.dedup_by(|a, b| match (a, b) {
        (
            super::load::LoadError::HandWrittenTypeValue { carrier: x },
            super::load::LoadError::HandWrittenTypeValue { carrier: y },
        ) => x == y,
        _ => false,
    });
    // THE DEMAND GATE. Deriving a row for every sort grows the provider relation by 77%
    // (219 → 387 provisions) and costs ~113ms per load — of which only ~5ms is this pass;
    // the rest is `type_check_sorts`, `check_provider_requires` and
    // `derive_forwarded_provisions` walking a bigger relation. Measured with
    // `ANTHILL_LOAD_TIMING=1` over 3-run averages (a single run carries ~35ms of noise,
    // a third of the effect).
    //
    // So derive NOTHING until something asks. Today nothing does — zero `requires
    // TypeValue` in stdlib, anthill-stl or examples — so the cost is zero, while this
    // feature's own tests write the clause and get the full derivation. Step 3
    // (WI-20260919-N31XX) is what makes the clause appear at every rigid value read, and
    // at that point the gate opens by itself: it keys on the REQUIREMENT existing, so
    // step 3 removes nothing and there is no flag left behind.
    //
    // COARSE ON PURPOSE — "does anyone ask?", not "which carriers do they ask about". The
    // precise question needs the concrete bindings at call sites, which exist only after
    // the typer, and this pass must run BEFORE it (the typer resolves a call's `requires`
    // against the provider relation). Narrowing it further is the scaling work's job, not
    // a gate's.
    if !super::typing::any_requirement_names_spec(kb, spec) {
        return errors;
    }
    let spec_canon = kb.canonical_sort_sym(spec);
    // The carriers that ALREADY provide `TypeValue` — an author's (refused above) or this
    // pass's own from an earlier load phase. Read once; see the loop for why.
    let already: HashSet<Symbol> = super::typing::provision_carriers_of_spec(kb, spec)
        .into_iter()
        .map(|c| kb.canonical_sort_sym(c))
        .collect();
    // Every sort that some provision names as a SPEC — `Iterable`, `PartialEq`,
    // `IndexedSeq`, … A spec is a BOUND, not a carrier, and deriving a row for one is not
    // a harmless extra: `List provides Iterable`, so a goal `TypeValue[T = List[T =
    // Int64]]` reaches `Iterable`'s row by subsumption and stands beside `List`'s own.
    // MEASURED before this filter: `List[T = Int64]` was refused "ambiguous among
    // providers: anthill.prelude.PersistentCollection, anthill.prelude.PartialEq,
    // anthill.prelude.FiniteCollection, anthill.prelude.IndexedSeq,
    // anthill.prelude.Iterable, anthill.prelude.Iteration" — six of `List`'s own bounds
    // competing with it to say what `List[T = Int64]` is.
    let specs: HashSet<Symbol> = super::typing::all_provisions(kb)
        .iter()
        .map(|p| kb.canonical_sort_sym(p.spec))
        .collect();
    for s in declared_sorts(kb) {
        // Never derive FOR the spec itself: `TypeValue provides TypeValue` is a
        // self-provision the coherence walk would have to arbitrate, and it names nothing
        // an author writes.
        let cs = kb.canonical_sort_sym(s);
        if cs == spec_canon {
            continue;
        }
        // A TYPE PARAMETER IS NOT A CARRIER, and admitting one is not a harmless extra
        // row: `SortInfo` records `sort M = ?` inside `sort Monad` the same as any sort,
        // but its name term is a VARIABLE, so `TypeValue[T = M]` unifies with every goal
        // and becomes a universal provider. MEASURED before this filter: every
        // `tv[B = Boom]()` was refused "ambiguous among providers:
        // anthill.prelude.DelayMonad.M, anthill.prelude.PartialEq, anthill.prelude.Monad.M"
        // — three parameters standing in for the 200-odd real carriers.
        if super::typing::is_sort_param_symbol(kb, s) {
            continue;
        }
        if specs.contains(&cs) {
            continue;
        }
        // ALREADY-PROVIDING carriers come from the set read ONCE above, not from a
        // `sort_provides` call per sort. That predicate is a TRANSITIVE walk over the
        // provider relation, and `kb.provides_index` is not built this early in the
        // pipeline, so each call is a live relation scan — ~200 of them over a relation
        // this pass is itself growing, which is quadratic in the sort count.
        //
        // The DIRECT reading is also the right question: what matters is whether this
        // carrier already has its OWN row, not whether it reaches one through a spec it
        // provides. A transitive hit would skip a carrier that needs a row of its own.
        if already.contains(&cs) {
            continue;
        }
        let params: Vec<Symbol> = kb.type_param_syms_of(s).to_vec();
        let conds: Vec<(Symbol, Symbol)> = params.into_iter().map(|p| (spec, p)).collect();
        super::eq_derive::assert_derived_provision(kb, s, spec, &conds);
        kb.derived_type_value_carriers.insert(cs);
    }
    errors
}
