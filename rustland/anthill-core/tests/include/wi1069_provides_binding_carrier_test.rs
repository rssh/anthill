//! WI-1069 — WHAT A `provides` CLAUSE'S BINDINGS MEAN. The ticket asked whether
//! `provides Spec[T = Other]` should be refused, on the reading that it "files
//! SILENTLY under the sort it is written in" and so puts the wrong carrier on record.
//!
//! IT IS NOT REFUSED, AND THE READING IS WRONG. `SortProvidesInfo` carries TWO
//! questions in two fields, and both are answered correctly:
//!
//! | field | question | comes from |
//! |---|---|---|
//! | `sort_ref` | who PROVIDES — whose member set is the dictionary | the enclosing scope |
//! | the spec view's carrier binding | provides it FOR WHAT | the clause's bindings |
//!
//! A clause whose carrier binding names something other than its provider is a
//! WITNESS — the first-class shape 058 §3.6 is built on. `provision_carrier_binding`
//! (`kb/typing.rs`) reads the carrier off the spec's FIRST declared type parameter,
//! and `witness_dispatch_carrier_value` classifies provider ≠ carrier as the witness
//! kind. stdlib's own `reflect/typing.anthill` documents the shape by example:
//! `sort ListOrd provides Ord[T = List[T = E]]  ->  List[T = E]`.
//!
//! THE POPULATION A REFUSAL WOULD HAVE BROKEN — MEASURED BY IMPLEMENTING THE REFUSAL,
//! not by grepping, and that distinction is the whole result. The ticket scoped its
//! count to stdlib / anthill-stl / anthill-cpp-gen / examples / anthill-todo and a
//! textual scan of those answers ZERO — but a text scan cannot tell a carrier binding
//! from a type-parameter binding, which is the only question that matters here. The
//! refusal was therefore written into `load_provides_clause`, keyed on the codebase's
//! own carrier reader (`witness_dispatch_carrier_value`), and the workspace run:
//!
//! * In its plain form — "the spec's carrier parameter must name the enclosing sort" —
//!   it refuses THE SHIPPED STANDARD LIBRARY at five sites: `List`, `Relation`,
//!   `FiniteStream`, `MappedStream`, `FilteredStream`. Each writes `provides Spec[T]`
//!   binding the carrier param to one of its OWN type parameters, which the classifier
//!   reports as a witness for that type VARIABLE (measured: `provision_carrier` answers
//!   `List | Stream | T`). So the naive rule is dead on arrival, exactly as the ticket
//!   suspected but for a reason its corpus count could not have surfaced.
//! * With THAT SHAPE EXEMPTED — the guard extended to pass a carrier naming one of the
//!   provider's own declared type parameters, which is the most careful form the ticket
//!   describes — the stdlib loads clean and **90 tests across 25 modules fail**,
//!   concentrated in the witness core: `wi837_witness_eq_dispatch_test` (8),
//!   `wi450_witness_dispatch_test` (5), `wi860_default_provider_relations_test` (5),
//!   `wi391_binding_extractability_test` (3), `wi463_unqualified_witness_dispatch_test`
//!   (2), `wi1010`/`wi1012`/`wi1035` (2 each), and the escape-gate and
//!   existential-return suites that lean on witness provisions. (That exemption was
//!   written FOR the experiment. No such fold exists in the shipped classifier —
//!   `provision_carrier_binding` filters the carrier base on `SymbolKind::Sort` alone —
//!   which is the whole of WI-1076 below.)
//!
//! So the answer is (b): the shape is legal, it is THE witness spelling, and what
//! needed fixing was the prose that said otherwise.
//!
//! ONE RESIDUE, SPUN OUT AS **WI-1076** and since DELIVERED. The ticket said
//! identifying the carrier parameter "is itself unsettled", and it was right:
//! `provision_carrier_binding` picked it POSITIONALLY, which is correct for a spec that
//! HAS a carrier parameter and wrong for a SELF-REPRESENTING one, whose operations
//! receive on the spec sort itself and which declares none. Seven stdlib provisions
//! were filed at a type VARIABLE and contributed no inferred default row.
//! `spec_carrier_param` now decides it by asking which parameter the operations take —
//! NOT `spec_is_self_representing`, which was measured to refuse a program that loads
//! and was rejected. Six of the seven are closed; see
//! `wi1076_self_representing_spec_carrier_test` for the residue and both controls.
//!
//! It never touched this file's rows: the fixtures below use `Desc`, a
//! carrier-parameterized spec (`describe(x: T)` receives on the parameter), so every
//! assertion here reads the same before and after WI-1076.
//!
//! WHAT THIS FILE PINS, and none of it was under test before: the relation answers
//! the FOREIGN carrier (nothing else asserts where the carrier comes from), and the
//! `provides` and `fact` spellings of one witness IN ONE SORT BODY record THE SAME
//! PROVISION. That second row is what refutes the ticket's measurement, which compared
//! a `provides` clause in a namespace body against a `fact` one level OUT — two
//! different scopes, so of course two different answers.
//!
//! "THE SAME PROVISION" IS THE EXACT CLAIM, and an earlier draft of this file
//! overstated it as "the same statement". They are not: a `fact` ALSO asserts its head
//! into the rule/fact index, so a goal `Desc(T: ?q)` answers once under the `fact`
//! spelling and NOT AT ALL under `provides` — measured, and pinned below by
//! `the_two_spellings_diverge_outside_the_provision`, which is the row that keeps this
//! file's conclusion no wider than its instrument. Two further divergences are known
//! and not pinned here because they belong to their own tickets: a non-parametric spec
//! WITH CONSTRUCTORS emits no provision from a `fact` at all (`maybe_emit_fact_provides_
//! info`'s early return, pinned by `wi210_dispatch_test::fact_for_non_spec_sort_does_
//! not_emit_provides_info`), and `provides … :- conditions` has no `fact` spelling.
//!
//! WHAT FAILS UNDER THAT REFUSAL, in this file: the three cases marked WITNESS. The
//! two marked CONTROL pass either way BY DESIGN and are why the other three mean
//! something — the self-provision (a reader that called every binding foreign would
//! satisfy the witness rows too) and the address-with-no-type refusal (which keeps the
//! recorded decision from reading as "the bindings always win"). Their purity is
//! load-bearing and was itself measured: an earlier draft put a witness program inside
//! the self-provision test, and it failed under the guard — a control that moves with
//! the treatment is not a control.
//!
//! REFERENCE: WI-1000 (`ProvidesClauseNeedsSort`, and the production in a namespace
//! body), WI-860 (`provision_carrier_binding`, the one owner of "which parameter is
//! the carrier"), WI-859 (a binding naming the provider's OWN type param folds back
//! to self), proposal 058 §3.6 / §4, kernel-language §5.1, §8.7.

use crate::wi860_default_provider_relations_test::relation_rows;
use anthill_core::eval::Value;

/// A spec, an inert carrier, and a SEPARATE sort making the claim — so provider and
/// carrier are distinct by construction and `claim` is the only thing that varies.
///
/// `Desc.describe` is deliberately BODY-LESS: with no default to fall back on, a
/// `probe()` that answers at all is proof the claim was read, where a defaulted spec
/// op would answer whether or not the witness was found (WI-1010's lesson).
fn witness_program(ns: &str, claim: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
  end

  sort LeafDesc
    import anthill.prelude.Int64
    {claim}
    operation describe(x: Leaf) -> Int64 = 7
  end

  operation probe() -> Int64 = Desc.describe(leaf())
end
"#
    )
}

/// The SELF-provision twin of [`witness_program`]: one sort, claiming for itself. The
/// control neighbour — an assertion that a foreign binding is read as foreign means
/// nothing unless a self binding is still read as self.
fn self_program(ns: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  operation probe() -> Int64 = Desc.describe(leaf())
end
"#
    )
}

/// `provision_carrier(?P, ?S, ?C)` rows mentioning the local spec — the stdlib
/// contributes many rows and only this program's are the subject.
fn desc_rows(kb: &mut anthill_core::kb::KnowledgeBase) -> Vec<String> {
    relation_rows(kb, "provision_carrier", 3)
        .into_iter()
        .filter(|r| r.contains("| Desc |"))
        .collect()
}

/// `{ns}.probe` as an Int — the dispatch half, which no reading of the fact layer can
/// stand in for.
fn probe(ns: &str, src: &str) -> i64 {
    let op = format!("{ns}.probe");
    match crate::common::interp_for(src)
        .call(&op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
    {
        Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// WITNESS — THE ACCEPTANCE. The clause's binding names `Leaf`, the clause is written
/// in `LeafDesc`, and the relation answers BOTH: provider `LeafDesc`, carrier `Leaf`.
///
/// This is the assertion the ticket says is impossible ("the clause's bindings are the
/// SPEC's arguments" and therefore inert as a carrier selector). The carrier is read
/// from the binding and from nowhere else — there is no other text in the program
/// naming `Leaf` as this provision's carrier.
#[test]
fn a_provides_clause_binding_a_foreign_carrier_records_a_witness() {
    let ns = "test.wi1069.witness";
    let mut kb = crate::common::load_kb_with(&witness_program(ns, "provides Desc[T = Leaf]"));
    assert_eq!(
        desc_rows(&mut kb),
        vec!["LeafDesc | Desc | Leaf".to_string()],
        "the provider comes from the enclosing scope and the CARRIER from the \
         clause's binding — a `provides` clause naming another carrier is a witness, \
         not a provision mis-filed under its writer"
    );
    // The negative half, and it lives HERE rather than beside the self-provision so
    // that the control stays pure: `Leaf` writes no provision in this program, so a
    // reader that folded the foreign binding back into a self-provision would show up
    // as `self_provides` holding for it.
    assert!(
        !relation_rows(&mut kb, "self_provides", 2).contains(&"Leaf | Desc".to_string()),
        "the witness program's `Leaf` provides nothing itself — the binding names its \
         carrier, it does not make the carrier its own provider"
    );
}

/// CONTROL — the neighbour that makes the row above mean something. The same spec,
/// claimed by the carrier itself: the binding names `Leaf` and so does the scope, and
/// the reader must answer `Leaf` for BOTH, not treat every binding as foreign.
///
/// `self_provides` is asserted beside it because that is the relation 058 §3.6's
/// defaults are inferred from, and it is what must NOT hold for the witness program.
#[test]
fn a_self_provision_is_still_read_as_self() {
    let ns = "test.wi1069.self";
    let mut kb = crate::common::load_kb_with(&self_program(ns));
    assert_eq!(
        desc_rows(&mut kb),
        vec!["Leaf | Desc | Leaf".to_string()],
        "a binding naming the enclosing sort is the SELF provision — the reader must \
         distinguish the two, not report every binding as a foreign carrier"
    );
    assert!(
        relation_rows(&mut kb, "self_provides", 2).contains(&"Leaf | Desc".to_string()),
        "the carrier's own provision must still be its own"
    );
}

/// WITNESS — THE ROW THAT REFUTES THE TICKET. `provides Spec[T = Other]` and
/// `fact Spec[T = Other]` written in ONE sort body record THE SAME PROVISION.
///
/// `load_fact` takes `sort_ref` from the enclosing scope whenever that scope names a
/// type (`kb/load.rs`, `has_kind(domain, SymbolKind::Sort)`), which is exactly what
/// `load_provides_clause` does unconditionally — so inside a sort the two spellings
/// cannot disagree ABOUT THE PROVISION. The ticket's measured pair differed because it
/// compared a clause in a NAMESPACE body against a `fact` one level OUT; the scope was
/// the variable, not the spelling.
///
/// Asserted as row EQUALITY rather than two separate expectations: the claim is that
/// they agree, and two hand-written expectations would keep passing if both drifted.
///
/// SCOPED TO THE PROVISION, and the sibling below is why that scoping is written down
/// rather than assumed — the two spellings do NOT agree about everything.
#[test]
fn the_provides_and_fact_spellings_of_one_witness_agree() {
    let mut via_provides =
        crate::common::load_kb_with(&witness_program("test.wi1069.sp", "provides Desc[T = Leaf]"));
    let mut via_fact =
        crate::common::load_kb_with(&witness_program("test.wi1069.sf", "fact Desc[T = Leaf]"));
    let (p, f) = (desc_rows(&mut via_provides), desc_rows(&mut via_fact));
    assert_eq!(
        p,
        vec!["LeafDesc | Desc | Leaf".to_string()],
        "the `provides` spelling must record the witness"
    );
    assert_eq!(
        p, f,
        "inside a sort body the two spellings record ONE PROVISION — both take the \
         provider from the scope and the carrier from the bindings"
    );
}

/// THE DIVERGENCE ROW — where the two spellings are NOT interchangeable, and the
/// reason the test above is scoped to the provision rather than to the statement.
///
/// A `fact` is a rule with an empty body, so `load_fact` also asserts its head into the
/// rule/fact index; `load_provides_clause` asserts `SortProvidesInfo` and nothing else.
/// The provision is therefore identical and the QUERYABLE SURFACE is not: a goal naming
/// the spec directly answers under `fact` and not under `provides`.
///
/// This row exists because the conclusion without it was measurably too wide — the file
/// claimed "the same statement" on the strength of an instrument that only ever read
/// `provision_carrier`. Driving the place two spellings SHOULD differ is what separates
/// "they agree" from "my instrument cannot tell them apart".
///
/// It is also the standing reason 059's fact ban costs something real rather than
/// nothing: what an entry loses with the `fact` spelling is this surface, not the claim.
#[test]
fn the_two_spellings_diverge_outside_the_provision() {
    use anthill_core::kb::resolve::ResolveConfig;
    use anthill_core::kb::term::{Term, Var};
    use smallvec::SmallVec;

    /// Solutions of `{ns}.Desc(T: ?q)` — the spec named as a goal in its own right.
    fn spec_goal_solutions(ns: &str, claim: &str) -> usize {
        let mut kb = crate::common::load_kb_with(&witness_program(ns, claim));
        let functor = kb
            .try_resolve_symbol(&format!("{ns}.Desc"))
            .expect("the spec sort must resolve");
        let q = kb.intern("q");
        let vid = kb.fresh_var(q);
        let var = kb.alloc(Term::Var(Var::Global(vid)));
        let t_arg = kb.intern("T");
        let goal = kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(t_arg, var)]),
        });
        kb.resolve(&[goal], &ResolveConfig::default()).len()
    }

    assert_eq!(
        spec_goal_solutions("test.wi1069.fdiv", "fact Desc[T = Leaf]"),
        1,
        "a `fact` is a rule with an empty body, so its head is also an answerable goal"
    );
    assert_eq!(
        spec_goal_solutions("test.wi1069.pdiv", "provides Desc[T = Leaf]"),
        0,
        "a `provides` clause asserts the provision and NOTHING ELSE — so the two \
         spellings agree about the provision and differ about the fact index, and \
         'the same provision' is the exact claim this file is entitled to make"
    );
}

/// WITNESS — the dispatch half. A green load and an answered relation are both
/// readings of the fact layer; this is the one assertion that the dictionary actually
/// reaches the witness's member.
///
/// Both spellings are driven, which is what makes it a twin rather than a second copy
/// of `wi1010`'s witness row: that one drives the `provides` route against a DEFAULTED
/// spec op, and the in-sort-body `fact` route is driven nowhere else.
#[test]
fn a_witness_written_either_way_dispatches() {
    for (ns, claim) in [
        ("test.wi1069.dp", "provides Desc[T = Leaf]"),
        ("test.wi1069.df", "fact Desc[T = Leaf]"),
    ] {
        assert_eq!(
            probe(ns, &witness_program(ns, claim)),
            7,
            "`{claim}` must supply `Desc.describe` for `Leaf` — the spec op is \
             body-less, so an answer at all is the witness dispatching"
        );
    }
}

/// CONTROL — the ONE case where the scope really does decide, kept beside the rows
/// above so the recorded decision does not read as "the bindings always win".
///
/// At an address no type occupies there is no provider for the bindings to be about,
/// and WI-1000 refuses the clause rather than deriving a carrier from them. Passes
/// either way by design: the ticket's proposed guard is about a clause that HAS a
/// sort at its address.
#[test]
fn a_provides_clause_at_an_address_no_type_occupies_is_still_refused() {
    let src = r#"namespace test.wi1069.orphan
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
  end

  namespace NotASort
    provides Desc[T = Leaf]
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.iter()
            .any(|e| e.contains("a `provides` clause needs a type at its address")
                && e.contains("test.wi1069.orphan.NotASort")),
        "a `provides` clause in a namespace naming no type is refused, bindings or \
         no bindings: {errs:?}"
    );
}
