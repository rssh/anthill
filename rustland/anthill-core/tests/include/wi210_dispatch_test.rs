//! WI-210 — spec/impl call-site dispatch via fact.
//!
//! Phase 1: the loader auto-emits `SortProvidesInfo` for
//! `fact Spec[bindings]` clauses appearing inside a sort body, when
//! the named functor is itself a parameterized sort. This brings
//! `fact` in line with the existing `provides` clause path so the
//! existing proposal-030 / WI-119 specialization-witness machinery
//! (and WI-210's upcoming dispatch query) can find the impl.


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadResult};
use anthill_core::kb::typing::{
    lookup_spec_op_dispatch,
    find_unique_impl_op,
    DispatchOutcome,
    type_check_expr,
    TypingEnv,
};
use anthill_core::kb::subst::Substitution;
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

/// Phase 1/2 helper: discards errors. Used by tests that only inspect
/// post-load KB state (e.g. SortProvidesInfo emission) and don't
/// require the load to be error-free.
fn load_with(extra: &str) -> KnowledgeBase {
    load_capturing_errors(extra).0
}

/// Phase 3 helper: returns errors so dispatch-failure diagnostics
/// can be asserted directly. The WI-210 dispatch-failure marker
/// surfaces as a LoadError via load_phase_inner's all_errors.
fn load_capturing_errors(
    extra: &str,
) -> (KnowledgeBase, LoadResult, Vec<load::LoadError>) {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(r) => (kb, r, vec![]),
        Err(errs) => (kb, LoadResult::default(), errs),
    }
}

/// Render every `SortProvidesInfo` head the KB knows about, sorted.
fn provides_info_heads(kb: &mut KnowledgeBase) -> Vec<String> {
    let sym = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo")
        .expect("SortProvidesInfo registered");
    let rids: Vec<_> = kb.by_functor(sym).into_iter().collect();
    let heads: Vec<_> = rids.iter().map(|&r| kb.rule_head(r)).collect();
    let printer = TermPrinter::new(kb);
    let mut out: Vec<String> = heads.into_iter()
        .map(|h| printer.print_term(h))
        .collect();
    out.sort();
    out
}

#[test]
fn fact_clause_inside_sort_body_emits_provides_info() {
    // Mirror of the `provides_clause_emits_specialization_proof_record`
    // test in specialization_witness_test.rs, but using the `fact`
    // sugar form. The kernel-language spec §1418 says `fact S[T]`
    // inside a sort body means spec satisfaction; this test pins
    // that the loader actually emits the SortProvidesInfo so
    // downstream consumers find it.
    let src = r#"
        namespace wi210.fact_emits
          export Wi210SpecA, Wi210ImplB
          sort Wi210SpecA
            sort State = ?
          end
          sort Wi210ImplB
            fact Wi210SpecA[State = Wi210ImplB]
          end
        end
    "#;
    let mut kb = load_with(src);
    let heads = provides_info_heads(&mut kb);
    let found = heads.iter().any(|h|
        h.contains("Wi210ImplB") && h.contains("Wi210SpecA")
    );
    assert!(found,
        "expected SortProvidesInfo for Wi210ImplB/Wi210SpecA; saw:\n{heads:#?}");
}

#[test]
fn fact_clause_at_namespace_emits_with_carrier_as_sort_ref() {
    // Namespace-level `fact Spec[bindings]` (the stdlib convention
    // for primitive carriers like Int satisfying Numeric) emits a
    // SortProvidesInfo with sort_ref = the carrier (first binding
    // value), not the namespace itself. Mirrors the proposal-036
    // pattern semantically: "X satisfies Spec at these bindings,"
    // where X is the carrier. Pending WI-213 (builtin sort concept)
    // which will let stdlib put these facts inside a real sort body.
    let src = r#"
        namespace wi210.ns_emits
          export Wi210NsSpec, Wi210NsCarrier
          sort Wi210NsSpec
            sort State = ?
          end
          sort Wi210NsCarrier
            entity wi210_nc
          end
          fact Wi210NsSpec[State = Wi210NsCarrier]
        end
    "#;
    let mut kb = load_with(src);
    let heads = provides_info_heads(&mut kb);
    let found = heads.iter().any(|h|
        h.contains("Wi210NsCarrier") && h.contains("Wi210NsSpec")
    );
    assert!(found,
        "namespace-level fact must emit SortProvidesInfo with the \
         carrier as sort_ref; saw:\n{heads:#?}");
}

#[test]
fn fact_for_non_spec_sort_does_not_emit_provides_info() {
    // `fact RegularSort(...)` where RegularSort has no type params
    // is asserting an instance of a constructor-shaped sort, not
    // claiming spec satisfaction. Must NOT emit SortProvidesInfo.
    let src = r#"
        namespace wi210.non_spec
          export Wi210Color, Wi210Holder
          sort Wi210Color
            entity wi210_red
            entity wi210_green
          end
          sort Wi210Holder
            fact Wi210Color[count = 0]
          end
        end
    "#;
    // Wi210Color has no `sort X = ?` decl, so the gate must skip
    // SortProvidesInfo emission regardless of whether the binding
    // shape is parametric-looking. Using a literal (`0`) for the
    // value keeps the fixture independent of cross-sort name
    // resolution.
    // Wi210Color has no `sort X = ?` decl, so even with bracket
    // notation this should not be treated as spec satisfaction.
    let mut kb = load_with(src);
    let heads = provides_info_heads(&mut kb);
    let found = heads.iter().any(|h|
        h.contains("Wi210Holder") && h.contains("Wi210Color")
    );
    assert!(!found,
        "fact for non-parametric sort must not emit SortProvidesInfo; saw:\n{heads:#?}");
}

// ─── Phase 2: spec-op detection helper ──────────────────────────

#[test]
fn lookup_spec_op_dispatch_recognizes_body_less_op_on_parametric_sort() {
    // WorkItemStore declares `commit` without a body; State is `?`;
    // this op is dispatch-eligible.
    let src = r#"
        namespace wi210p2.spec
          export Wi210Spec
          sort Wi210Spec
            sort State = ?
            operation wi210_op(s: State) -> State
          end
        end
    "#;
    let kb = load_with(src);
    let op_sym = kb.try_resolve_symbol("wi210p2.spec.Wi210Spec.wi210_op")
        .expect("op symbol registered");
    let parent = lookup_spec_op_dispatch(&kb, op_sym)
        .expect("body-less op on parametric sort should be a spec op");
    let parent_qn = kb.qualified_name_of(parent);
    assert_eq!(parent_qn, "wi210p2.spec.Wi210Spec",
        "spec-op's parent sort should be Wi210Spec; got {parent_qn}");
}

#[test]
fn lookup_spec_op_dispatch_rejects_op_with_body() {
    // Op has a body — even though the parent has type params, this
    // op is the impl, not the spec.
    let src = r#"
        namespace wi210p2.with_body
          export Wi210Impl
          sort Wi210Impl
            sort State = ?
            operation wi210_op(s: State) -> State = s
          end
        end
    "#;
    let kb = load_with(src);
    let op_sym = kb.try_resolve_symbol("wi210p2.with_body.Wi210Impl.wi210_op")
        .expect("op symbol registered");
    assert!(lookup_spec_op_dispatch(&kb, op_sym).is_none(),
        "op with body must not be a spec op (would dispatch to itself)");
}

#[test]
fn lookup_spec_op_dispatch_rejects_op_on_non_parametric_sort() {
    // Sort has no `sort X = ?` declaration; this op is just a
    // free-standing operation, not a spec op.
    let src = r#"
        namespace wi210p2.no_params
          export Wi210Plain
          sort Wi210Plain
            entity wi210_e
            operation wi210_op(x: Wi210Plain) -> Wi210Plain
          end
        end
    "#;
    let kb = load_with(src);
    let op_sym = kb.try_resolve_symbol("wi210p2.no_params.Wi210Plain.wi210_op")
        .expect("op symbol registered");
    assert!(lookup_spec_op_dispatch(&kb, op_sym).is_none(),
        "op on non-parametric sort must not be a spec op");
}

// ─── Phase 3 dispatch tests (proposal 038) ───────────────────────
//
// Builtin-sort unification (proposal 038) makes candidate binding
// values resolve to the same Symbol whether referenced bare (`Int`)
// or via the `anthill.prelude.Int` qualified path. find_unique_impl_op
// can therefore deterministically match per-call substitutions
// against SortProvidesInfo records emitted from per-language binding
// blocks (e.g. `provides Int language rust { fact Numeric[T = Int] }`).

#[test]
fn stdlib_namespace_facts_emit_provides_info_for_numeric() {
    // Stdlib's `fact Numeric[Int]` at namespace anthill.prelude.Int
    // (after Phase 1's namespace-level handling) should emit a
    // SortProvidesInfo recording Int as a Numeric impl. Pending
    // WI-213 (builtin sort concept) which lets stdlib put these
    // facts inside `builtin sort Int { ... }` bodies — but the
    // semantics are equivalent: Int satisfies Numeric.
    let mut kb = load_with("");
    let heads = provides_info_heads(&mut kb);
    let dump: Vec<&String> = heads.iter()
        .filter(|h| h.contains("Numeric"))
        .collect();
    eprintln!("WI210-DBG Numeric SortProvidesInfo heads: {dump:#?}");
    let int_numeric = heads.iter().any(|h|
        h.contains("Numeric") && h.contains("Int")
    );
    assert!(int_numeric,
        "expected Int to be recorded as a Numeric impl; saw heads with Numeric:\n{dump:#?}");
}

#[test]
fn store_anthill_emits_provides_info_for_workitemstore() {
    // End-to-end: anthill-todo's actual store.anthill writes
    // `fact WorkItemStore[State = WIS]` inside `sort
    // FileBasedWorkitemStore`. After WI-210 phase 1, this should
    // produce a SortProvidesInfo record.
    let mut kb = load_with_store();
    let heads = provides_info_heads(&mut kb);
    let found = heads.iter().any(|h|
        h.contains("FileBasedWorkitemStore") && h.contains("WorkItemStore")
    );
    assert!(found,
        "expected SortProvidesInfo recording FileBasedWorkitemStore as \
         WorkItemStore impl; saw:\n{heads:#?}");
}

// ─── Phase 3 dispatch outcome tests (proposal 038) ────────────────

/// Build a per-call substitution that binds the named type-param of
/// `spec_qn` (e.g. "T", "State") to the named carrier sort. Mirrors
/// what the typer's `check_apply` constructs when unifying the call
/// args against the op's params.
fn subst_with_param(
    kb: &mut KnowledgeBase,
    spec_qn: &str,
    param_short: &str,
    carrier_qn: &str,
) -> Substitution {
    use anthill_core::kb::term::{Term, Var};
    let param_qn = format!("{spec_qn}.{param_short}");
    let param_sym = kb.try_resolve_symbol(&param_qn)
        .unwrap_or_else(|| panic!("{} not registered", param_qn));
    let alias_sym = kb.try_resolve_symbol("SortAlias").expect("SortAlias");
    let mut param_var = None;
    for rid in kb.by_functor(alias_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
        let head = kb.rule_head(rid);
        if let Term::Fn { pos_args, .. } = kb.get_term(head).clone() {
            if pos_args.len() < 2 { continue; }
            if let Term::Fn { functor, .. } = kb.get_term(pos_args[0]) {
                if *functor == param_sym {
                    if let Term::Var(Var::Global(v)) = kb.get_term(pos_args[1]) {
                        param_var = Some(*v);
                    }
                }
            }
        }
    }
    let param_var = param_var.unwrap_or_else(||
        panic!("{}'s SortAlias not found for {spec_qn}", param_short));

    let carrier_sym = kb.try_resolve_symbol(carrier_qn)
        .unwrap_or_else(|| panic!("{} not registered", carrier_qn));
    let carrier_term = kb.make_sort_ref(carrier_sym);

    let mut subst = Substitution::new();
    subst.bind_term(param_var, carrier_term);
    subst
}

fn subst_with_t(kb: &mut KnowledgeBase, spec_qn: &str, carrier_qn: &str) -> Substitution {
    subst_with_param(kb, spec_qn, "T", carrier_qn)
}

/// Read `anthill-todo/store.anthill` and load it on top of stdlib + rustland
/// bindings. Used by the WorkItemStore dispatch tests below.
fn load_with_store() -> KnowledgeBase {
    let path = crate::common::workspace_root().join("anthill-todo/store.anthill");
    let src = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    load_with(&src)
}

/// Run dispatch for `WorkItemStore.<op_short>` at the State=WIS binding;
/// panic with diagnostics if the outcome isn't `Unique`. Returns the loaded
/// KB plus the resolved impl op symbol.
fn dispatch_workitemstore_op(op_short: &str) -> (KnowledgeBase, anthill_core::intern::Symbol) {
    let mut kb = load_with_store();
    let op_qn = format!("anthill.todo.store.WorkItemStore.{op_short}");
    let op_sym = kb.try_resolve_symbol(&op_qn)
        .unwrap_or_else(|| panic!("{op_qn} not registered"));
    let spec_sort = lookup_spec_op_dispatch(&kb, op_sym)
        .unwrap_or_else(|| panic!("{op_qn} is not a spec op"));
    let subst = subst_with_param(
        &mut kb,
        "anthill.todo.store.WorkItemStore",
        "State",
        "anthill.todo.store.FileBasedWorkitemStore.WIS",
    );
    let op_short_sym = kb.intern(op_short);
    match find_unique_impl_op(&mut kb, &subst, spec_sort, op_short_sym, &[]) {
        DispatchOutcome::Unique(s) => (kb, s),
        other => panic!("expected Unique dispatch for {op_qn} at State=WIS; got {other:?}"),
    }
}

#[test]
fn dispatch_unique_finds_int_impl_for_numeric_add() {
    // `add` on Numeric is dispatch-eligible; with the rustland binding
    // emitting `fact Numeric[T = Int]`, find_unique_impl_op should
    // resolve a Unique outcome whose impl sort is Int.
    let mut kb = load_with("");
    let add_sym = kb.try_resolve_symbol("anthill.prelude.Numeric.add")
        .expect("Numeric.add registered");
    let spec_sort = lookup_spec_op_dispatch(&kb, add_sym)
        .expect("Numeric.add is a spec op");
    let subst = subst_with_t(&mut kb, "anthill.prelude.Numeric", "anthill.prelude.Int");
    let op_short = kb.intern("add");
    let outcome = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &[]);
    assert!(matches!(outcome, DispatchOutcome::Unique(_)),
        "expected Unique impl for Numeric add at T=Int; got {outcome:?}");
}

#[test]
fn dispatch_no_match_when_carrier_lacks_impl() {
    // Numeric has impls for Int / Float / BigInt but not Bool. A
    // per-call subst at T=Bool must yield NoMatch (impls exist but
    // none cover Bool).
    let mut kb = load_with("");
    let add_sym = kb.try_resolve_symbol("anthill.prelude.Numeric.add")
        .expect("Numeric.add registered");
    let spec_sort = lookup_spec_op_dispatch(&kb, add_sym)
        .expect("Numeric.add is a spec op");
    let subst = subst_with_t(&mut kb, "anthill.prelude.Numeric", "anthill.prelude.Bool");
    let op_short = kb.intern("add");
    let outcome = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &[]);
    assert_eq!(outcome, DispatchOutcome::NoMatch,
        "expected NoMatch for Numeric.add at T=Bool (no Bool/Numeric binding); got {outcome:?}");
}

#[test]
fn dispatch_ambiguous_when_two_impls_match_same_binding() {
    // Two parallel `provides Foo language X` blocks claim the same
    // binding for the same spec — find_unique_impl_op must reject as
    // Ambiguous (coherence rule (C)). We construct two independent
    // impl sorts that each provide AmbSpec at T=AmbCarrier.
    let mut kb = load_with(r#"
        namespace wi210p3.amb
          export AmbSpec, AmbCarrier, AmbA, AmbB
          sort AmbSpec
            sort T = ?
            operation amb_op(x: T) -> T
          end
          sort AmbCarrier
            entity amb_e
          end
          sort AmbA
            fact AmbSpec[T = AmbCarrier]
            operation amb_op(x: AmbCarrier) -> AmbCarrier = x
          end
          sort AmbB
            fact AmbSpec[T = AmbCarrier]
            operation amb_op(x: AmbCarrier) -> AmbCarrier = x
          end
        end
    "#);
    let amb_op_sym = kb.try_resolve_symbol("wi210p3.amb.AmbSpec.amb_op")
        .expect("AmbSpec.amb_op registered");
    let spec_sort = lookup_spec_op_dispatch(&kb, amb_op_sym)
        .expect("AmbSpec.amb_op is a spec op");
    let subst = subst_with_t(&mut kb, "wi210p3.amb.AmbSpec", "wi210p3.amb.AmbCarrier");
    let op_short = kb.intern("amb_op");
    let outcome = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &[]);
    assert_eq!(outcome, DispatchOutcome::Ambiguous,
        "expected Ambiguous when two impls provide the same binding; got {outcome:?}");
}

#[test]
fn dispatch_polymorphic_candidate_matches_any_per_call_value() {
    // LogicalStream's `fact Stream[T]` (T = LogicalStream's own type-param)
    // records a universally-quantified impl. The matcher must treat such
    // a candidate's binding value as a wildcard against the per-call concrete.
    let mut kb = load_with("");
    let head_sym = kb.try_resolve_symbol("anthill.prelude.Stream.head")
        .expect("Stream.head registered");
    let spec_sort = lookup_spec_op_dispatch(&kb, head_sym)
        .expect("Stream.head is a spec op");
    let subst = subst_with_param(
        &mut kb,
        "anthill.prelude.Stream",
        "T",
        "anthill.prelude.Int",
    );
    let op_short = kb.intern("head");
    let outcome = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &[]);
    assert!(matches!(outcome, DispatchOutcome::Unique(_)),
        "expected Unique dispatch for Stream.head with polymorphic LogicalStream \
         impl candidate at T=Int; got {outcome:?}");
}

#[test]
fn dispatch_unique_finds_filebased_impl_for_workitemstore_commit() {
    // WI-210 acceptance smoke test: commit(s, w) for s: Cell[V = WIS] must
    // dispatch to FileBasedWorkitemStore.commit. Multi-arg State-binding
    // case, against anthill-todo's actual store.anthill.
    let (kb, impl_sym) = dispatch_workitemstore_op("commit");
    let impl_qn = kb.qualified_name_of(impl_sym).to_string();
    assert!(
        impl_qn.contains("FileBasedWorkitemStore") && impl_qn.ends_with(".commit"),
        "expected impl to be FileBasedWorkitemStore.commit; got {impl_qn}"
    );
}

#[test]
fn dispatch_unique_finds_filebased_impl_for_workitemstore_lookup() {
    // Different return type from commit (Option[Term] vs Unit) — pins that
    // dispatch isn't accidentally keyed on signature shape.
    let _ = dispatch_workitemstore_op("lookup");
}

#[test]
fn dispatch_commit_s_w_type_checks_via_workitemstore_satisfaction() {
    use anthill_core::kb::term::Term;
    use smallvec::SmallVec;
    // Exercises the typer's check_apply path end-to-end (parse → unify →
    // dispatch), not just the manual-subst entry point above.
    let domain_src = std::fs::read_to_string(
        crate::common::workspace_root().join("anthill-todo/domain.anthill")
    ).expect("read domain.anthill");
    let store_src = std::fs::read_to_string(
        crate::common::workspace_root().join("anthill-todo/store.anthill")
    ).expect("read store.anthill");
    let combined = format!("{domain_src}\n{store_src}");

    let mut kb = load_with(&combined);
    let commit_sym = kb.try_resolve_symbol("anthill.todo.store.WorkItemStore.commit")
        .expect("WorkItemStore.commit registered");
    let cell_sym = kb.try_resolve_symbol("anthill.prelude.Cell")
        .expect("Cell registered");
    let wis_sym = kb.try_resolve_symbol("anthill.todo.store.FileBasedWorkitemStore.WIS")
        .expect("FileBasedWorkitemStore.WIS registered");
    let workitem_sym = kb.try_resolve_symbol("anthill.stage0.WorkItem")
        .expect("anthill.stage0.WorkItem registered");

    // Cell[V = WIS] must use the canonical `parameterized(...)` form —
    // a bare `Term::Fn(Cell, [V=WIS])` doesn't match the spec param's
    // stored type and unify_types falls through to types_compatible.
    let v_field = kb.intern("V");
    let wis_ty = kb.make_sort_ref(wis_sym);
    let cell_base = kb.make_sort_ref(cell_sym);
    let cell_wis = kb.make_parameterized_type(cell_base, &[(v_field, wis_ty)]);
    let workitem_ty = kb.make_sort_ref(workitem_sym);

    let apply_arg_sym = kb.try_resolve_symbol("anthill.reflect.ApplyArg")
        .expect("ApplyArg registered");
    let var_ref_sym = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref registered");
    let name_arg = kb.intern("name");
    let value_arg = kb.intern("value");
    let s_sym = kb.intern("s");
    let w_sym = kb.intern("w");
    let apply_sym = kb.intern("apply");
    let fn_arg = kb.intern("fn");
    let args_arg = kb.intern("args");

    let s_ref = kb.alloc(Term::Ref(s_sym));
    let w_ref = kb.alloc(Term::Ref(w_sym));
    let commit_ref = kb.alloc(Term::Ref(commit_sym));

    let var_s = kb.alloc(Term::Fn {
        functor: var_ref_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_arg, s_ref)]),
    });
    let var_w = kb.alloc(Term::Fn {
        functor: var_ref_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_arg, w_ref)]),
    });
    let arg_s = kb.alloc(Term::Fn {
        functor: apply_arg_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_arg, s_ref), (value_arg, var_s)]),
    });
    let arg_w = kb.alloc(Term::Fn {
        functor: apply_arg_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_arg, w_ref), (value_arg, var_w)]),
    });
    let args_list = kb.build_list(&[arg_s, arg_w]);

    let apply_term = kb.alloc(Term::Fn {
        functor: apply_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(fn_arg, commit_ref), (args_arg, args_list)]),
    });

    let mut env = TypingEnv::empty();
    env.bind_var("s".to_string(), cell_wis);
    env.bind_var("w".to_string(), workitem_ty);

    let result = type_check_expr(&mut kb, &env, apply_term);
    assert!(result.is_some(),
        "expected commit(s, w) for s:Cell[V=WIS] / w:WorkItem to type-check \
         (dispatch should resolve to FileBasedWorkitemStore.commit)");
}

#[test]
fn dispatch_int_add_x_x_type_checks_via_spec_satisfaction() {
    use anthill_core::kb::term::Term;
    use smallvec::SmallVec;
    // Acceptance criterion #3 (proposal 038): `add(x, x)` for x:Int
    // type-checks via Int's spec satisfaction — i.e. the dispatch hook
    // resolves to Unique without bailing the typer.
    let mut kb = load_with("");
    let add_sym = kb.try_resolve_symbol("anthill.prelude.Numeric.add")
        .expect("Numeric.add registered");
    let int_sym = kb.try_resolve_symbol("anthill.prelude.Int")
        .expect("Int registered");
    let int_type = kb.make_sort_ref(int_sym);

    let apply_arg_sym = kb.try_resolve_symbol("anthill.reflect.ApplyArg")
        .expect("ApplyArg registered");
    let var_ref_sym = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref registered");
    let name_arg = kb.intern("name");
    let value_arg = kb.intern("value");
    let x_sym = kb.intern("x");
    let a_sym = kb.intern("a");
    let b_sym = kb.intern("b");
    let apply_sym = kb.intern("apply");
    let fn_arg = kb.intern("fn");
    let args_arg = kb.intern("args");

    // Allocate sub-terms first so we can compose them without overlapping borrows.
    let x_ref = kb.alloc(Term::Ref(x_sym));
    let a_ref = kb.alloc(Term::Ref(a_sym));
    let b_ref = kb.alloc(Term::Ref(b_sym));
    let add_ref = kb.alloc(Term::Ref(add_sym));

    let var_x = kb.alloc(Term::Fn {
        functor: var_ref_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_arg, x_ref)]),
    });
    let arg_a = kb.alloc(Term::Fn {
        functor: apply_arg_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_arg, a_ref), (value_arg, var_x)]),
    });
    let arg_b = kb.alloc(Term::Fn {
        functor: apply_arg_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_arg, b_ref), (value_arg, var_x)]),
    });
    let args_list = kb.build_list(&[arg_a, arg_b]);

    let apply_term = kb.alloc(Term::Fn {
        functor: apply_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(fn_arg, add_ref), (args_arg, args_list)]),
    });

    let mut env = TypingEnv::empty();
    env.bind_var("x".to_string(), int_type);

    let result = type_check_expr(&mut kb, &env, apply_term);
    assert!(result.is_some(),
        "expected add(x, x) for x:Int to type-check; got None (dispatch likely failed)");
}
