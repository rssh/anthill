//! WI-954 — A TYPE PARAMETER'S CANONICAL VARIABLE IS PUBLISHED BY THE LOADER,
//! AND THERE IS NOWHERE ELSE TO GET IT.
//!
//! The loader mints exactly one logical variable per declared type parameter and used
//! to drop the mapping. Readers rebuilt it, each by its own route — `SortAlias` for an
//! `alias`-form declaration, `OperationInfo.type_params` for a bracket parameter — and
//! `typing::type_param_global_var` was the two-rung ladder that picked between them.
//! WI-954 publishes the mapping (`KnowledgeBase::type_param_canonical_var`), and that
//! function is now one read of it.
//!
//! ONE READER KEPT ITS OLD CHANNEL, on review: `ground_rigid_projection_if_concrete`
//! asks whether an operation's BRACKET declared a name (the WI-383 split), which is not
//! the question this map answers. A symbol registered as both `Sort` and `Operation`
//! owns ONE scope, so no scope-keyed read can separate a sort body's `sort T = ?` from
//! an operation's `[T]`, and WI-402's carrier is op-scoped without being a bracket
//! parameter. `op_info::declared_type_param_var` stays for that one caller.
//!
//! THE RUNG ORDER THE TICKET NAMED WAS NOT A LIVE HAZARD, and saying so is part of
//! what these tests are for. WI-402's existential carrier (`-> C ensures Spec[C, …]`)
//! IS an op-scoped parameter that publishes as an ALIAS, so "declared by an operation"
//! did not imply "found by the operation rung" — but the two rungs are DISJOINT on it:
//! `detect_existential_carrier` refuses the rewrite when the bracket already declares
//! the return name, so `OperationInfo.type_params` never holds the carrier's name and
//! the operation rung answers `None` for it whichever way round they run. What the
//! ladder really got wrong is measured below. Either way there is no order left, and
//! the three shapes here — sort parameter, op BRACKET parameter, op-scoped existential
//! CARRIER — are each answered by their own declaration.
//!
//! WHAT FAILS WITH THE CHANGE BACKED OUT. The back-out actually run is
//! `type_param_global_var` forced to `resolve_sort_alias` alone (the second rung's
//! `op_info` reader is deleted, so the full ladder cannot be restored without
//! rebuilding it); two of the six fail under it, and which two is the point:
//!
//!  * `a_declaration_that_is_not_a_type_parameter_denotes_no_parameter_variable` —
//!    THE ONE THAT MEASURES THIS TICKET. The ladder's FIRST rung was
//!    `resolve_sort_alias`, ungated, and a top-level opaque `sort Term = ?` has a
//!    `SortAlias` with a `Var` target while registering no type parameter anywhere.
//!    MEASURED over three corpus tiers: 8 symbols answered `Some(var)` from the ladder
//!    and `None` from the declaration, all 8 of them namespace-level abstract sorts,
//!    and ZERO declared type parameters disagreed. This is the only test here that the
//!    FULL two-rung ladder would also fail — the second rung answers for bracket
//!    parameters, not for these.
//!  * `three_declarations_three_variables` — fails under the alias rung alone, because
//!    `pick[E]` resolves through no alias, and PASSES under the full two-rung ladder by
//!    design. It is WI-943's property extended to the third shape; its value here is
//!    that it covers the bracket channel, so a map that published only the alias-form
//!    parameters could not pass.
//!  * `an_existential_carrier_resolves_to_the_variable_its_own_declaration_published`
//!    — PASSES EITHER WAY BY DESIGN. The carrier's variable IS its `SortAlias` target,
//!    so the alias rung and the map agree by construction. It is here because a map can
//!    publish the WRONG variable, which a rung reading the alias directly cannot.
//!  * `the_carrier_is_not_a_parameter_of_its_enclosing_sort` — fails against a
//!    name-derived reconstruction (`<Sort>.<op>.C` read as a parameter named `op.C` of
//!    `<Sort>`), which is WI-955's measured defect. It passes today through a different
//!    route than it did then, so it is re-pinned here rather than assumed.
//!  * `every_declared_parameter_in_the_stdlib_publishes_its_own_variable` — the
//!    COMPLETENESS half over a real population (96 declared parameters). It passes
//!    under the alias rung too — every stdlib SORT parameter has an alias — and it is
//!    here for the failure mode only a store has: a producer that stops publishing.
//!  * `the_fixture_dispatches` — passes either way; it is here so the fixture is known
//!    to be a program that runs, not four assertions about a map and nothing driven.

use anthill_core::intern::Symbol;
use anthill_core::kb::typing::type_param_global_var;
use anthill_core::kb::KnowledgeBase;

/// One sort with a parameter, one operation with a BRACKET parameter, and one with an
/// op-scoped existential CARRIER — the three shapes that used to publish through two
/// different channels. `MemStore` is the concrete witness `mk` returns.
const SRC: &str = r#"
namespace test.wi954
  import anthill.prelude.{String, Int64}

  sort KVStore
    sort K = ?
    sort V = ?
    operation describe(s: KVStore) -> String
  end

  sort MemStore
    provides KVStore[K = String, V = String]
    entity memStore
    operation describe(s: MemStore) -> String = "mem"
  end

  sort Holder
    sort T = ?
    entity holder(item: T)
    operation pick[E](a: E, b: E) -> E = a
    operation mk() -> C ensures KVStore[C, K = String, V = String] = memStore
  end

  sort Driver
    operation run(n: Int64) -> Int64 = Holder.pick(n, 7)
  end
end
"#;

fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
    kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("`{qn}` must be a defined symbol"))
}

fn var_of(kb: &KnowledgeBase, qn: &str) -> u32 {
    type_param_global_var(kb, sym(kb, qn))
        .unwrap_or_else(|| panic!("`{qn}` must resolve to a canonical parameter variable"))
        .raw()
}

/// The carrier's variable is the one ITS OWN declaration published — read back off the
/// `SortAlias` fact `build_existential_return` asserts, which is the declaration side.
#[test]
fn an_existential_carrier_resolves_to_the_variable_its_own_declaration_published() {
    let kb = crate::common::load_kb_with(SRC);
    let c = sym(&kb, "test.wi954.Holder.mk.C");
    let declared = crate::common::sort_alias_backing_var(&kb, c)
        .expect("an existential carrier is registered like `sort C = ?` — a SortAlias to a Var")
        .raw();
    assert_eq!(
        var_of(&kb, "test.wi954.Holder.mk.C"),
        declared,
        "the carrier's written occurrences must denote the variable its declaration minted",
    );
}

/// Three declarations, three variables — and none of them each other's. The
/// discriminating half: agreement alone would be satisfied by a reader that answered
/// one variable for everything.
#[test]
fn three_declarations_three_variables() {
    let kb = crate::common::load_kb_with(SRC);
    let sort_param = var_of(&kb, "test.wi954.Holder.T");
    let bracket = var_of(&kb, "test.wi954.Holder.pick.E");
    let carrier = var_of(&kb, "test.wi954.Holder.mk.C");
    assert_ne!(sort_param, bracket, "`Holder.T` and `pick[E]` are two parameters");
    assert_ne!(sort_param, carrier, "`Holder.T` and `mk`'s carrier are two parameters");
    assert_ne!(bracket, carrier, "`pick[E]` and `mk`'s carrier are two parameters");
}

/// The carrier is declared in the OPERATION's scope, two segments below the sort. A
/// reconstruction that recovered a parameter's owner by slicing its qualified name read
/// `mk.C` as a parameter OF `Holder` and injected a spurious binding into every type
/// built for it (WI-955). The owner is the scope link now, on both sides of the map.
#[test]
fn the_carrier_is_not_a_parameter_of_its_enclosing_sort() {
    let kb = crate::common::load_kb_with(SRC);
    let holder = sym(&kb, "test.wi954.Holder");
    assert_eq!(
        kb.type_params_of_sort(holder),
        vec!["T".to_string()],
        "`Holder` declares exactly one type parameter",
    );
    assert!(
        kb.type_param_sym_of(holder, "C").is_none(),
        "`Holder` does not declare `C` — its operation does",
    );
    assert_eq!(
        kb.type_param_sym_of(sym(&kb, "test.wi954.Holder.mk"), "C"),
        Some(sym(&kb, "test.wi954.Holder.mk.C")),
        "`mk` declares `C`, and it is the symbol the carrier is defined under",
    );
}

/// CONTROL, and the one that measures the change. `anthill.reflect.Term` is a
/// namespace-level `sort Term = ?`: it HAS a `SortAlias` whose target is a `Var`, and it
/// is not a type parameter of anything (`add_type_param` is gated on the enclosing scope
/// being a SORT). Both halves are asserted, so the test cannot pass by the alias having
/// gone away.
#[test]
fn a_declaration_that_is_not_a_type_parameter_denotes_no_parameter_variable() {
    let kb = crate::common::load_kb_with(SRC);
    for qn in ["anthill.reflect.Term", "anthill.prelude.Unit"] {
        let s = sym(&kb, qn);
        assert!(
            crate::common::sort_alias_backing_var(&kb, s).is_some(),
            "`{qn}` must still be backed by a `SortAlias` to a Var — otherwise this \
             control measures nothing",
        );
        assert_eq!(
            type_param_global_var(&kb, s),
            None,
            "`{qn}` declares no type parameter, so it denotes no parameter variable \
             (the pre-WI-954 ladder answered with its alias var)",
        );
    }
}

/// COMPLETENESS over the real corpus: every parameter a stdlib sort declares has a
/// published variable, and no two parameters share one. The map is a store, so it can
/// be INCOMPLETE in a way a ladder cannot; this is what would catch a producer that
/// stopped publishing.
#[test]
fn every_declared_parameter_in_the_stdlib_publishes_its_own_variable() {
    let kb = crate::common::load_kb_with(SRC);
    let sorts: Vec<Symbol> = kb.sort_info_iter().map(|(s, _)| *s).collect();
    let mut seen: std::collections::HashMap<u32, Symbol> = std::collections::HashMap::new();
    let mut params = 0usize;
    for s in sorts {
        for &p in kb.type_param_syms_of(s) {
            params += 1;
            let v = type_param_global_var(&kb, p).unwrap_or_else(|| {
                panic!("`{}` is declared by `{}` but publishes no variable",
                       kb.qualified_name_of(p), kb.qualified_name_of(s))
            });
            if let Some(prev) = seen.insert(v.raw(), p) {
                assert_eq!(
                    prev,
                    p,
                    "`{}` and `{}` are two declarations sharing one variable",
                    kb.qualified_name_of(prev),
                    kb.qualified_name_of(p),
                );
            }
        }
    }
    assert!(params >= 90, "the stdlib supplies 96 declared parameters; got {params}");
}

/// DRIVEN: the bracket parameter's identity decides a real dispatch. Kept small — the
/// heavier drives of the same identity are `wi943_type_param_identity_test`'s — but
/// present, so this suite is not four assertions about a map plus nothing running.
#[test]
fn the_fixture_dispatches() {
    let mut interp = crate::common::interp_for(SRC);
    match interp.call("test.wi954.Driver.run", &[anthill_core::eval::Value::Int(3)]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(n, 3, "`pick` returns its first argument"),
        other => panic!("`Driver.run` must dispatch through `pick[E]`; got {other:?}"),
    }
}
