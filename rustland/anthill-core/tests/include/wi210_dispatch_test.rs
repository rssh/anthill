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
    let rids: Vec<_> = kb.rules_by_functor(sym).into_iter().collect();
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
    // for primitive carriers like Int64 satisfying Numeric) emits a
    // SortProvidesInfo with sort_ref = the carrier (first binding
    // value), not the namespace itself. Mirrors the proposal-036
    // pattern semantically: "X satisfies Spec at these bindings,"
    // where X is the carrier. Pending WI-213 (builtin sort concept)
    // which will let stdlib put these facts inside a real sort body.
    let src = r#"
        namespace wi210.ns_emits
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
          sort Wi210Color
            entity wi210_red
            entity wi210_green
          end
          sort Wi210Holder
            fact Wi210Color[count = ?]
          end
        end
    "#;
    // Wi210Color has no `sort X = ?` decl, so the gate must skip
    // SortProvidesInfo emission regardless of whether the binding
    // shape is parametric-looking. Using an anonymous type variable
    // (`?`) for the value keeps the fixture independent of cross-sort
    // name resolution.
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
// values resolve to the same Symbol whether referenced bare (`Int64`)
// or via the `anthill.prelude.Int64` qualified path. find_unique_impl_op
// can therefore deterministically match per-call substitutions
// against SortProvidesInfo records emitted from per-language binding
// blocks (e.g. `provides Int64 language rust { fact Numeric[T = Int64] }`).

#[test]
fn stdlib_namespace_facts_emit_provides_info_for_numeric() {
    // Stdlib's `fact Numeric[Int64]` at namespace anthill.prelude.Int64
    // (after Phase 1's namespace-level handling) should emit a
    // SortProvidesInfo recording Int64 as a Numeric impl. Pending
    // WI-213 (builtin sort concept) which lets stdlib put these
    // facts inside `builtin sort Int64 { ... }` bodies — but the
    // semantics are equivalent: Int64 satisfies Numeric.
    let mut kb = load_with("");
    let heads = provides_info_heads(&mut kb);
    let dump: Vec<&String> = heads.iter()
        .filter(|h| h.contains("Numeric"))
        .collect();
    eprintln!("WI210-DBG Numeric SortProvidesInfo heads: {dump:#?}");
    let int_numeric = heads.iter().any(|h|
        h.contains("Numeric") && h.contains("Int64")
    );
    assert!(int_numeric,
        "expected Int64 to be recorded as a Numeric impl; saw heads with Numeric:\n{dump:#?}");
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
    for rid in kb.rules_by_functor(alias_sym) {
        if !kb.is_fact(rid) { continue; }
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
    subst.bind_term(kb, param_var, carrier_term);
    subst
}

fn subst_with_t(kb: &mut KnowledgeBase, spec_qn: &str, carrier_qn: &str) -> Substitution {
    subst_with_param(kb, spec_qn, "T", carrier_qn)
}

/// Read `rustland/anthill-todo/anthill/store.anthill` and load it on top of stdlib + rustland
/// bindings. Used by the WorkItemStore dispatch tests below.
fn load_with_store() -> KnowledgeBase {
    let path = crate::common::workspace_root().join("rustland/anthill-todo/anthill/store.anthill");
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
    // emitting `fact Numeric[T = Int64]`, find_unique_impl_op should
    // resolve a Unique outcome whose impl sort is Int64.
    let mut kb = load_with("");
    let add_sym = kb.try_resolve_symbol("anthill.prelude.Numeric.add")
        .expect("Numeric.add registered");
    let spec_sort = lookup_spec_op_dispatch(&kb, add_sym)
        .expect("Numeric.add is a spec op");
    let subst = subst_with_t(&mut kb, "anthill.prelude.Numeric", "anthill.prelude.Int64");
    let op_short = kb.intern("add");
    let outcome = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &[]);
    assert!(matches!(outcome, DispatchOutcome::Unique(_)),
        "expected Unique impl for Numeric add at T=Int64; got {outcome:?}");
}

#[test]
fn dispatch_no_candidates_when_carrier_lacks_impl() {
    // Numeric has impls for Int64 / Float / BigInt but not Bool. A
    // per-call subst at T=Bool must yield NoCandidates: the existing
    // Numeric[Int64]/Float/BigInt impls are independent specifications
    // about different sorts and must not gate Bool dispatch (same
    // rationale as `Eq[T=Type]` not gating `Eq[T=Int64]`).
    let mut kb = load_with("");
    let add_sym = kb.try_resolve_symbol("anthill.prelude.Numeric.add")
        .expect("Numeric.add registered");
    let spec_sort = lookup_spec_op_dispatch(&kb, add_sym)
        .expect("Numeric.add is a spec op");
    let subst = subst_with_t(&mut kb, "anthill.prelude.Numeric", "anthill.prelude.Bool");
    let op_short = kb.intern("add");
    let outcome = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &[]);
    assert_eq!(outcome, DispatchOutcome::NoCandidates,
        "expected NoCandidates for Numeric.add at T=Bool (no Bool/Numeric binding); got {outcome:?}");
}

#[test]
fn dispatch_ambiguous_when_two_impls_match_same_binding() {
    // Two parallel `provides Foo language X` blocks claim the same
    // binding for the same spec — find_unique_impl_op must reject as
    // Ambiguous (coherence rule (C)). We construct two independent
    // impl sorts that each provide AmbSpec at T=AmbCarrier.
    let mut kb = load_with(r#"
        namespace wi210p3.amb
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

/// WI-350 — load a synthetic *self-receiver* spec `Box` (`peek(b: Box)` —
/// `b` typed with the spec sort itself, not its type-parameter) with two
/// carrier impls (`ListBox`, `StreamBox`). Box's only parameter `T` is the
/// *element*, so the carrier is not a binding: every impl's universally-
/// quantified `fact Box[T]` matches a per-call `Box[T = Int64]` goal.
fn load_box_two_carriers() -> KnowledgeBase {
    load_with(r#"
        namespace wi350.box
          sort Box
            sort T = ?
            operation peek(b: Box) -> T
          end
          sort ListBox
            sort T = ?
            entity lbox(item: T)
            fact Box[T]
            operation peek(b: ListBox) -> T = match b case lbox(x) -> x
          end
          sort StreamBox
            sort T = ?
            entity sbox(item: T)
            fact Box[T]
            operation peek(b: StreamBox) -> T = match b case sbox(x) -> x
          end
        end
    "#)
}

#[test]
fn wi350_self_receiver_spec_is_ambiguous_without_carrier() {
    // Baseline: with no receiver carrier, the per-call binding `Box[T = Int64]`
    // matches BOTH carriers' `fact Box[T]` — exactly the pathology WI-350
    // describes ("EVERY Stream-op call is DispatchAmbiguous"). This is the
    // `dispatch_spec_op_cached(.., carrier = None)` path.
    let mut kb = load_box_two_carriers();
    let peek_sym = kb.try_resolve_symbol("wi350.box.Box.peek")
        .expect("Box.peek registered");
    let spec_sort = lookup_spec_op_dispatch(&kb, peek_sym)
        .expect("Box.peek is a spec op");
    let subst = subst_with_t(&mut kb, "wi350.box.Box", "anthill.prelude.Int64");
    let op_short = kb.intern("peek");
    let outcome = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &[]);
    assert_eq!(outcome, DispatchOutcome::Ambiguous,
        "two carrier impls + no carrier discriminator must be Ambiguous; got {outcome:?}");
}

#[test]
fn wi350_concrete_carrier_disambiguates_self_receiver_spec() {
    use anthill_core::kb::typing::dispatch_spec_op_cached;
    // The fix: threading the receiver's concrete carrier (`ListBox`) keeps
    // only that carrier's impl, so the same goal resolves Unique.
    let mut kb = load_box_two_carriers();
    let peek_sym = kb.try_resolve_symbol("wi350.box.Box.peek")
        .expect("Box.peek registered");
    let spec_sort = lookup_spec_op_dispatch(&kb, peek_sym)
        .expect("Box.peek is a spec op");
    let listbox_sym = kb.try_resolve_symbol("wi350.box.ListBox")
        .expect("ListBox registered");
    let listbox_peek = kb.try_resolve_symbol("wi350.box.ListBox.peek")
        .expect("ListBox.peek registered");
    let subst = subst_with_t(&mut kb, "wi350.box.Box", "anthill.prelude.Int64");
    let op_short = kb.intern("peek");

    let (outcome, _tree) = dispatch_spec_op_cached(
        &mut kb, &subst, spec_sort, op_short, &[], Some(listbox_sym),
    );
    assert_eq!(outcome, DispatchOutcome::Unique(listbox_peek),
        "carrier = ListBox must resolve uniquely to ListBox.peek; got {outcome:?}");
}

#[test]
fn wi350_abstract_stream_receiver_types_via_interface_with_two_impls() {
    use anthill_core::kb::term::Term;
    use anthill_core::kb::typing::{extract_sort_ref_sym, get_named_arg};
    use smallvec::SmallVec;
    // Add a SECOND Stream impl alongside LogicalStream, so a per-call
    // `Stream[T = …]` goal is genuinely ambiguous by binding (both impls'
    // `fact Stream[T]` match). An abstract receiver `s : Stream[T = Term]`
    // — base sort IS the spec — must still type through `Stream.head`'s
    // interface to `Option[T = Term]`, NOT resolve `Ambiguous`: the
    // concrete impl is the runtime value's own concern (WI-350 case b).
    // Pre-WI-350 this raised `DispatchAmbiguous`.
    let mut kb = load_with(r#"
        namespace wi350.stream2
          import anthill.prelude.{Stream, Option, Pair}
          sort MyStream2
            sort T = ?
            fact Stream[T]
            operation splitFirst(s: MyStream2[?A])
              -> Option[Pair[?A, MyStream2[?A]]]
          end
        end
    "#);

    let head_sym = kb.try_resolve_symbol("anthill.prelude.Stream.head")
        .expect("Stream.head registered");
    let stream_sym = kb.try_resolve_symbol("anthill.prelude.Stream")
        .expect("Stream registered");
    let term_sym = kb.try_resolve_symbol("anthill.reflect.Term")
        .expect("Term registered");
    let error_sym = kb.try_resolve_symbol("anthill.prelude.Error")
        .expect("Error registered");

    // Sanity: there really are ≥2 Stream providers now.
    let providers: Vec<String> = provides_info_heads(&mut kb)
        .into_iter().filter(|h| h.contains("Stream")).collect();
    assert!(providers.len() >= 2,
        "expected ≥2 Stream impls (LogicalStream + MyStream2); saw:\n{providers:#?}");

    let t_field = kb.intern("T");
    let e_field = kb.intern("E");
    let term_ty = kb.make_sort_ref(term_sym);
    let error_ty = kb.make_sort_ref(error_sym);
    let stream_base = kb.make_sort_ref(stream_sym);
    let stream_concrete = kb.make_parameterized_type(
        stream_base, &[(t_field, term_ty), (e_field, error_ty)],
    );

    let apply_arg_sym = kb.try_resolve_symbol("anthill.reflect.ApplyArg")
        .expect("ApplyArg registered");
    let var_ref_sym = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref registered");
    let name_arg = kb.intern("name");
    let value_arg = kb.intern("value");
    let s_sym = kb.intern("s");
    let apply_sym = kb.intern("apply");
    let fn_arg = kb.intern("fn");
    let args_arg = kb.intern("args");

    let s_ref = kb.alloc(Term::Ref(s_sym));
    let head_ref = kb.alloc(Term::Ref(head_sym));
    let var_s = kb.alloc(Term::Fn {
        functor: var_ref_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_arg, s_ref)]),
    });
    let arg_s = kb.alloc(Term::Fn {
        functor: apply_arg_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_arg, s_ref), (value_arg, var_s)]),
    });
    let args_list = kb.build_list(&[arg_s]);
    let apply_term = kb.alloc(Term::Fn {
        functor: apply_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(fn_arg, head_ref), (args_arg, args_list)]),
    });

    let mut env = TypingEnv::empty();
    env.bind_var(s_sym, anthill_core::eval::Value::Term(stream_concrete));

    let result = type_check_expr(&mut kb, &env, apply_term)
        .expect("head(s) on abstract Stream[T] must type-check (not Ambiguous) with ≥2 impls");
    let ty = result.ty.expect_term();
    let ty_str = TermPrinter::new(&kb).print_term(ty);
    // WI-361: term-backed `Option[T = …]` = `Fn{Option, named}` — the base sort
    // IS the functor (no deep `parameterized(base: sort_ref(…))` wrapper).
    let base = match kb.get_term(ty) {
        Term::Fn { functor, .. } => *functor,
        _ => panic!("expected parameterized Option return; got {ty_str}"),
    };
    assert_eq!(kb.qualified_name_of(base), "anthill.prelude.Option",
        "abstract-receiver head must type via interface to Option; got {ty_str}");
}

#[test]
fn dispatch_polymorphic_candidate_matches_any_per_call_value() {
    use anthill_core::kb::typing::dispatch_spec_op_cached;
    // A `fact Stream[T]` (T = the impl's own type-param) records a
    // universally-quantified impl; the matcher must treat such a candidate's
    // binding value as a wildcard against the per-call concrete T. With
    // proposal-002 List now also a Stream impl, `Stream` is a self-receiver
    // spec with ≥2 carriers, so the carrier discriminates (WI-350): supplying
    // the receiver's carrier (`LogicalStream`) picks that impl uniquely at
    // T = Int64, while the carrier-less compat path is genuinely Ambiguous.
    let mut kb = load_with("");
    let head_sym = kb.try_resolve_symbol("anthill.prelude.Stream.head")
        .expect("Stream.head registered");
    let spec_sort = lookup_spec_op_dispatch(&kb, head_sym)
        .expect("Stream.head is a spec op");
    let logical_stream = kb.try_resolve_symbol("anthill.prelude.LogicalStream")
        .expect("LogicalStream registered");
    let subst = subst_with_param(
        &mut kb,
        "anthill.prelude.Stream",
        "T",
        "anthill.prelude.Int64",
    );
    let op_short = kb.intern("head");

    // Carrier = LogicalStream: the universal `fact Stream[T]` candidate
    // matches the per-call T = Int64 and the carrier filter keeps only it.
    let (with_carrier, _) = dispatch_spec_op_cached(
        &mut kb, &subst, spec_sort, op_short, &[], Some(logical_stream),
    );
    assert!(matches!(with_carrier, DispatchOutcome::Unique(_)),
        "expected Unique dispatch for Stream.head at carrier=LogicalStream, T=Int64; \
         got {with_carrier:?}");

    // Carrier-less compat path: ≥2 Stream impls both match the universal
    // binding, so dispatch is Ambiguous without a carrier to discriminate.
    let no_carrier = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &[]);
    assert_eq!(no_carrier, DispatchOutcome::Ambiguous,
        "expected Ambiguous for carrier-less Stream.head with ≥2 impls; got {no_carrier:?}");
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
        crate::common::workspace_root().join("rustland/anthill-todo/anthill/store.anthill")
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
    let s_sym = kb.intern("s");
    let w_sym = kb.intern("w");
    env.bind_var(s_sym, anthill_core::eval::Value::Term(cell_wis));
    env.bind_var(w_sym, anthill_core::eval::Value::Term(workitem_ty));

    let result = type_check_expr(&mut kb, &env, apply_term);
    assert!(result.is_ok(),
        "expected commit(s, w) for s:Cell[V=WIS] / w:WorkItem to type-check \
         (dispatch should resolve to FileBasedWorkitemStore.commit); got {:?}",
         result.as_ref().err());
}

#[test]
fn dispatch_int_add_x_x_type_checks_via_spec_satisfaction() {
    use anthill_core::kb::term::Term;
    use smallvec::SmallVec;
    // Acceptance criterion #3 (proposal 038): `add(x, x)` for x:Int
    // type-checks via Int64's spec satisfaction — i.e. the dispatch hook
    // resolves to Unique without bailing the typer.
    let mut kb = load_with("");
    let add_sym = kb.try_resolve_symbol("anthill.prelude.Numeric.add")
        .expect("Numeric.add registered");
    let int_sym = kb.try_resolve_symbol("anthill.prelude.Int64")
        .expect("Int64 registered");
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
    let x_sym = kb.intern("x");
    env.bind_var(x_sym, anthill_core::eval::Value::Term(int_type));

    let result = type_check_expr(&mut kb, &env, apply_term);
    assert!(result.is_ok(),
        "expected add(x, x) for x:Int to type-check; got {:?} (dispatch likely failed)",
        result.as_ref().err());
}

// ─── Override is a `provides` concept, not a `requires` one ───────
//
// Design note (operation override, kernel-language.md §8.7): a sort
// that *provides* a spec (`fact Spec[...]`) and supplies its own
// operation overrides the spec's, and participates in dispatch. A
// sort that merely *requires* the spec and happens to declare a
// same-named operation is NOT overriding — that op is unrelated and
// must not enter the spec's dispatch candidate set.

#[test]
fn requires_user_with_same_named_op_does_not_provide_or_override() {
    let (mut kb, load_result, _errs) = load_capturing_errors(r#"
        namespace ovr.req_vs_prov
          sort OvrSpec
            sort T = ?
            operation ovr_op(x: T) -> T
          end
          sort OvrCarrier
            entity ovr_e
          end
          sort OvrProv
            fact OvrSpec[T = OvrCarrier]
            operation ovr_op(x: OvrCarrier) -> OvrCarrier = x
          end
          sort OvrReq
            requires OvrSpec[T = OvrCarrier]
            operation ovr_op(x: OvrCarrier) -> OvrCarrier = x
          end
        end
    "#);

    // 1. The provider emits SortProvidesInfo; the requires-user does NOT.
    let heads = provides_info_heads(&mut kb);
    assert!(heads.iter().any(|h| h.contains("OvrProv") && h.contains("OvrSpec")),
        "OvrProv (fact OvrSpec) must emit SortProvidesInfo; saw:\n{heads:#?}");
    assert!(!heads.iter().any(|h| h.contains("OvrReq") && h.contains("OvrSpec")),
        "OvrReq (requires OvrSpec) must NOT emit SortProvidesInfo — \
         requires is not provides; saw:\n{heads:#?}");

    // 2. The requires-user's op is a distinct symbol from the spec op
    //    (it shadows the inherited name; it is not the spec op itself).
    let spec_op = kb.try_resolve_symbol("ovr.req_vs_prov.OvrSpec.ovr_op")
        .expect("OvrSpec.ovr_op registered");
    let req_op = kb.try_resolve_symbol("ovr.req_vs_prov.OvrReq.ovr_op")
        .expect("OvrReq.ovr_op registered");
    assert_ne!(spec_op, req_op,
        "the requires-user's same-named op must be a distinct symbol, not the spec op");

    // 3. Dispatch for OvrSpec at T=OvrCarrier resolves uniquely to the
    //    provider — the requires-user is not in the candidate set.
    let spec_sort = lookup_spec_op_dispatch(&kb, spec_op)
        .expect("OvrSpec.ovr_op is a spec op");
    let subst = subst_with_t(&mut kb, "ovr.req_vs_prov.OvrSpec", "ovr.req_vs_prov.OvrCarrier");
    let op_short = kb.intern("ovr_op");
    match find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &[]) {
        DispatchOutcome::Unique(s) => {
            let qn = kb.qualified_name_of(s).to_string();
            assert!(qn.contains("OvrProv"),
                "dispatch must resolve to the provider OvrProv.ovr_op; got {qn}");
        }
        other => panic!(
            "expected Unique dispatch to the provider (requires-user must not \
             contribute a candidate); got {other:?}"),
    }

    // 4. WI-346: the same-named op on the requires-user is now flagged as an
    //    advisory shadow (the WI-345 channel's first consumer). It does not
    //    override, so the author is warned they likely meant `provides`.
    assert!(
        load_result.warnings.iter().any(|w| {
            let s = w.to_string();
            s.contains("OvrReq") && s.contains("ovr_op") && s.contains("OvrSpec")
        }),
        "expected a RequiresShadow warning for OvrReq.ovr_op shadowing OvrSpec.ovr_op; \
         got: {:?}",
        load_result.warnings.iter().map(|w| w.to_string()).collect::<Vec<_>>());
}
