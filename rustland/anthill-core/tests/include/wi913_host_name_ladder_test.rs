//! WI-913 — the HOST-SUPPLIED-NAME positions that resolved absolute-only.
//!
//! WI-908 made `KnowledgeBase::resolve_name_in_global` THE ladder for a name that
//! arrives from outside the KB's source text (an extent owner's functor, a
//! `FactRef`'s owner). These positions ask the same question of a name that arrives
//! as a runtime `String` — from an anthill program, not from a source occurrence —
//! and each answered it with `try_resolve_symbol`, i.e. `by_qualified_name` and
//! nothing else:
//!
//!   * `anthill.reflect.lookup_symbol` — BOTH of its backings: the eval-side host fn
//!     (`anthill-stl/src/reflect/builtins.rs::lookup_symbol_op`, driven by that
//!     crate's own `lookup_symbol_reads_the_implicit_tier`) and the SLD-side
//!     `KnowledgeBase::builtin_lookup_symbol`. One operation, two backings — the
//!     WI-984 shape, and the reason the ticket's four positions are five.
//!   * `anthill.reflect.make_fn` / `make_apply` — a functor named by a `Value::Str`
//!     inside a program.
//!   * `anthill.persistence.Store.monotonicity` — its `Value::Str` functor arm.
//!
//! WHAT THE SWITCH ACTUALLY TRADES, measured rather than assumed: the ladder is
//! NOT a widening of the absolute lookup. It ADDS the implicit tier (`cons`, `nil`,
//! `some`, `none`, `and`, `not`, `SortInfo`, `SortView`, `OperationInfo` — bare
//! names that resolved to NOTHING before), and it RE-SPELLS the two classes whose
//! only reading was the absolute one: the qualified-only kernel registrations
//! (`Sort`, `Fact`, `Member`, `meta`, …) and any name meant at the root regardless
//! of scope now take the `..a.b.c` form (WI-1075), because since that ticket an
//! UNMARKED dotted path is the RELATIVE reading and the absolute one has its own
//! spelling. Both directions are driven below —
//! `a_qualified_only_kernel_name_is_reachable_only_by_the_root_spelling` and
//! `the_absolute_spelling_names_the_root_from_a_host_string`.
//!
//! ONE thing genuinely stops resolving: a FIELD named by path, which
//! `resolve_dotted_in_kb` refuses in every reading as a category error (a field is
//! reached by dot dispatch on a value). Censused, not assumed — see
//! `a_field_is_not_nameable_by_path_from_a_host_string`.
//!
//! A short USER name is unaffected in either direction — `<global>` has no imports
//! from a source file, so `Color` denotes nothing here before or after. Only a
//! top-level `-i` import (WI-853) puts one in reach. That is the CONTROL row:
//! `a_short_user_name_denotes_nothing_either_way` passes on both sides by design.

use anthill_core::eval::{EvalError, Interpreter, Value};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

use crate::common::{interp_for, load_kb_with};

const FIXTURE: &str = r#"
namespace test.wi913
  sort Color
    entity red
    entity green
  end
end
"#;

/// Run the SLD goal `lookup_symbol(<name>, ?r)` and report the symbol it bound,
/// by qualified name — `None` when the builtin failed (its only "no" shape).
fn sld_lookup_symbol(kb: &mut KnowledgeBase, name: &str) -> Option<String> {
    let name_str = kb.alloc(Term::Const(Literal::String(name.into())));
    let result_sym = kb.intern("?result");
    let result_vid = kb.fresh_var(result_sym);
    let result_var = kb.alloc(Term::Var(Var::Global(result_vid)));
    let ls_sym = kb.resolve_symbol("anthill.reflect.lookup_symbol");
    let goal = kb.alloc(Term::Fn {
        functor: ls_sym,
        pos_args: SmallVec::from_slice(&[name_str, result_var]),
        named_args: SmallVec::new(),
    });

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    let sol = solutions.first()?;
    let bound = sol
        .subst
        .resolve_as_value(result_vid)
        .cloned()
        .expect("lookup_symbol binds its result on success");
    let sym = kb
        .value_symbol(&bound)
        .expect("lookup_symbol binds a symbol reference");
    Some(kb.qualified_name_of(sym).to_string())
}

/// The functor symbol of a `Value::Term` holding a `Term::Fn`, by qualified name.
fn term_fn_functor_name(interp: &Interpreter, v: &Value) -> String {
    let Value::Term { id, .. } = v else {
        panic!("expected a Value::Term, got {v:?}");
    };
    match interp.kb().get_term(*id) {
        Term::Fn { functor, .. } => interp.kb().qualified_name_of(*functor).to_string(),
        other => panic!("expected a Term::Fn, got {other:?}"),
    }
}

/// A one-element reflect argument list, `cons(elem, nil())` — the positional
/// cons shape `reflect_cons_to_vec` reads from anthill-source lists.
fn one_arg_list(interp: &mut Interpreter, elem: Value) -> Value {
    let entity = |interp: &mut Interpreter, qname: &str, pos: Vec<Value>| {
        let functor = interp
            .kb_mut()
            .try_resolve_symbol(qname)
            .unwrap_or_else(|| panic!("resolve `{qname}`"));
        Value::Entity {
            functor,
            pos: pos.into(),
            named: vec![].into(),
        }
    };
    let nil = entity(interp, "anthill.prelude.List.nil", vec![]);
    entity(interp, "anthill.prelude.List.cons", vec![elem, nil])
}

/// `cons(?x, nil())` — one `Term`-carried logic-variable hole, the shape a
/// `make_fn` caller builds a goal pattern from.
fn one_term_arg(interp: &mut Interpreter) -> Value {
    let hole = {
        let kb = interp.kb_mut();
        let name = kb.intern("?x");
        let vid = kb.fresh_var(name);
        Value::term(kb.alloc(Term::Var(Var::Global(vid))))
    };
    one_arg_list(interp, hole)
}

// ── The ticket's FIRST STEP: one operation, two backings ─────────

/// INVERTED IN WI-909's THIRD PASS, which removed the last four rows (the constructors)
/// and left `load::PRELUDE_QUALIFIED` EMPTY. There is no implicit tier: at `<global>` a
/// bare name resolves only if something is in scope there, and nothing is.
///
/// The row is kept and inverted rather than deleted because WI-913's finding lives in
/// it — `builtin_lookup_symbol` used to read `by_qualified_name`, which consults no
/// scope, and the fix was to give it the ladder. That fix STANDS; what changed is that
/// the ladder's lowest rung is gone, so the ladder's answer for a bare short name is
/// now "nothing". A future reader asking "did WI-913 regress?" needs to see that
/// distinction here rather than infer it from an absence.
///
/// THE QUALIFIED NAME IS THE MIGRATION, and asserting it is what keeps this row from
/// passing merely because the whole operation broke.
#[test]
fn sld_lookup_symbol_no_longer_reads_a_bare_prelude_name() {
    let mut kb = load_kb_with(FIXTURE);
    assert_eq!(
        sld_lookup_symbol(&mut kb, "cons").as_deref(),
        None,
        "the implicit tier is empty since WI-909, so a bare `cons` denotes nothing at \
         `<global>` -- it is neither in scope there nor on any rung below",
    );
    assert_eq!(
        sld_lookup_symbol(&mut kb, "anthill.prelude.List.cons").as_deref(),
        Some("anthill.prelude.List.cons"),
        "control: the ladder itself still works -- the QUALIFIED name resolves, which is \
         what says the row above measures the missing rung and not a broken operation",
    );
}

/// …AND THE REFLECT RESULT SORTS DO **NOT** ANSWER BARE — inverted in WI-909, which took
/// the eight of them off `load::PRELUDE_QUALIFIED` along with `push_choice` and the
/// `BigInt` conversions. This row used to assert the opposite; it is kept, inverted,
/// rather than deleted, because "a bare `SortInfo` denotes its target here" is exactly
/// the belief a reader of the surrounding code would carry in.
///
/// THE CONTROL IS `MemberInfo`, and it is what makes this a CONSISTENCY claim rather
/// than a regression: `MemberInfo` and `DescriptionInfo` are the same reflect result-sort
/// population — same `register_stdlib_scopes` block, same loader emission — and were
/// never on the tier, so they have ALWAYS answered `None` here. The rung covered eight of
/// ten members of one vocabulary. Asserting the two side by side is the whole argument
/// for the removal, in the currency this file reads.
///
/// The QUALIFIED name still answers, which is the migration: a host that means the
/// reflect sort says so, exactly as it always had to for `MemberInfo`.
#[test]
fn sld_lookup_symbol_does_not_read_the_reflect_sorts() {
    let mut kb = load_kb_with(FIXTURE);
    assert_eq!(
        sld_lookup_symbol(&mut kb, "SortInfo").as_deref(),
        None,
        "`SortInfo` left the implicit tier in WI-909; a bare short name resolves only \
         when it is in scope at `<global>` or on the tier, and it is neither",
    );
    assert_eq!(
        sld_lookup_symbol(&mut kb, "MemberInfo").as_deref(),
        sld_lookup_symbol(&mut kb, "SortInfo").as_deref(),
        "control: the two are one vocabulary and must answer alike. `MemberInfo` was \
         never on the tier, so this equality is what says WI-909 removed an \
         inconsistency rather than a capability",
    );
    assert_eq!(
        sld_lookup_symbol(&mut kb, "anthill.reflect.SortInfo").as_deref(),
        Some("anthill.reflect.SortInfo"),
        "…and the qualified name is the migration, as it always was for `MemberInfo`",
    );
}

// ── make_fn / make_apply ─────────────────────────────────────────

/// INVERTED WITH ITS SIBLING ABOVE (WI-909's third pass). `make_fn` still resolves
/// "by qualified-or-short name" exactly as `reflect.anthill` declares -- but a SHORT
/// name now has nowhere to resolve, so the bare spelling is refused and the qualified
/// one answers. The refusal is LOUD (`EvalError::Internal`), which is the whole reason
/// this position needs no migration guard: a program handing `make_fn` a bare `cons`
/// finds out.
#[test]
fn make_fn_refuses_a_bare_prelude_name_and_takes_the_qualified_one() {
    let mut interp = interp_for(FIXTURE);
    let args = one_term_arg(&mut interp);
    let err = interp
        .call("anthill.reflect.make_fn", &[Value::Str("cons".into()), args])
        .expect_err("a bare `cons` denotes nothing since the tier was emptied");
    assert!(
        format!("{err:?}").contains("cons"),
        "the refusal must name the symbol it could not resolve: {err:?}"
    );
    let args = one_term_arg(&mut interp);
    let built = interp
        .call(
            "anthill.reflect.make_fn",
            &[Value::Str("anthill.prelude.List.cons".into()), args],
        )
        .expect("control: the qualified name is the migration and still resolves");
    assert_eq!(
        term_fn_functor_name(&interp, &built),
        "anthill.prelude.List.cons",
    );
}

/// CONTROL — passes on BOTH sides, by design: a fully-qualified name is the one
/// spelling on which the absolute rung and the ladder always coincide, so this row
/// measures that routing costs the qualified case nothing.
#[test]
fn make_fn_still_resolves_a_qualified_functor() {
    let mut interp = interp_for(FIXTURE);
    let args = one_term_arg(&mut interp);
    let built = interp
        .call(
            "anthill.reflect.make_fn",
            &[Value::Str("test.wi913.Color.red".into()), args],
        )
        .expect("make_fn accepts a qualified name");
    assert_eq!(
        term_fn_functor_name(&interp, &built),
        "test.wi913.Color.red",
    );
}

/// FAILS PRE-FIX (`EvalError::Internal("make_apply: unknown symbol `cons`")`).
/// `make_apply` is `make_fn`'s occurrence-building twin (WI-722); it took the same
/// absolute-only reading of the same kind of name.
///
/// THE NAME MOVED TWICE AND THEN THE SUBJECT DID. It was `not` until WI-20260826-XED22,
/// then `cons`; both moves kept the row's subject — a HOST passing a bare string that the
/// tier answers. WI-909's third pass emptied the tier, so there is no bare string left
/// for it to answer and the subject is now the QUALIFIED spelling: `make_apply` must
/// still resolve a host-supplied name through the ladder (WI-722's finding), and the
/// ladder's answer for a short one is nothing. Its `make_fn` twin above carries the
/// refusal half; this row carries the positive half, so the pair still reads together.
#[test]
fn make_apply_resolves_a_qualified_functor() {
    use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
    use anthill_core::span::{SourceId, SourceSpan};

    let mut interp = interp_for(FIXTURE);
    let span = SourceSpan::new(SourceId::from_raw(0), 0, 3);
    let arg = Value::Node(NodeOccurrence::new_expr(
        Expr::Const(Literal::Bool(true)),
        span,
        None,
    ));
    let from = Value::Node(NodeOccurrence::new_expr(
        Expr::Const(Literal::Bool(true)),
        span,
        None,
    ));
    let args = one_arg_list(&mut interp, arg);

    let built = interp
        .call(
            "anthill.reflect.make_apply",
            &[
                Value::Str("anthill.prelude.List.cons".into()),
                args,
                from,
            ],
        )
        .expect("WI-909: the tier is empty, so the QUALIFIED name is the one that resolves");
    let Value::Node(occ) = &built else {
        panic!("make_apply returns a NodeOccurrence, got {built:?}");
    };
    match occ.as_expr().expect("make_apply returns an expression node") {
        Expr::Apply { functor, .. } => {
            assert_eq!(
                interp.kb().qualified_name_of(*functor),
                "anthill.prelude.List.cons"
            )
        }
        other => panic!("expected Expr::Apply, got {other:?}"),
    }
}

// ── Store.monotonicity's `Value::Str` functor arm ────────────────

/// FAILS PRE-FIX (`EvalError::TypeMismatch { expected: "Symbol (functor)" }` — the
/// string named nothing, so the `or_else` arm answered `None` and the whole read
/// fell to the type error). The policy answer itself is the `monotone` default;
/// what this drives is that the NAME is understood at all.
///
/// The store argument is a `FileStore`-shaped value only because `monotonicity`
/// validates its shape; it selects nothing (1-to-1 routing binds the functor).
#[test]
fn monotonicity_resolves_a_qualified_functor_name() {
    use anthill_core::persistence::file_store::{FileConvention, FileStore};

    let dir = tempfile::tempdir().expect("tempdir");
    let mut interp = interp_for(FIXTURE);
    let store_val = {
        let fs = interp.kb_mut().intern("FileStore");
        let flat = interp.kb_mut().intern("Flat");
        let root_sym = interp.kb_mut().intern("root");
        let convention_sym = interp.kb_mut().intern("convention");
        Value::Entity {
            functor: fs,
            pos: vec![].into(),
            named: vec![
                (
                    root_sym,
                    Value::Str(dir.path().to_str().unwrap().to_string()),
                ),
                (
                    convention_sym,
                    Value::Entity {
                        functor: flat,
                        pos: vec![].into(),
                        named: vec![].into(),
                    },
                ),
            ]
            .into(),
        }
    };
    let key = interp
        .store_canonical_key(&store_val)
        .expect("canonical key");
    interp
        .register_mirror(
            key,
            Box::new(FileStore::new(dir.path().to_path_buf(), FileConvention::Flat)),
            &[],
        )
        .expect("a file store declares no intrinsic policy");

    let answer = interp
        .call(
            "anthill.persistence.Store.monotonicity",
            &[store_val, Value::Str("anthill.prelude.List.cons".into())],
        )
        .expect("WI-909: the tier is empty, so `monotonicity` takes the QUALIFIED name");
    let expected = interp
        .kb_mut()
        .try_resolve_symbol("anthill.reflect.Monotonicity.monotone")
        .expect("reflect substrate loaded");
    match &answer {
        Value::Entity { functor, .. } => assert_eq!(*functor, expected),
        other => panic!("expected a Monotonicity entity, got {other:?}"),
    }
}

// ── The rows that pin what the switch RE-SPELLS, and what it costs ──

/// A SPELLING MOVES; NOTHING BECOMES UNREACHABLE. `Member` is one of the loader's
/// `KERNEL_META_SORTS`, registered with `define_qualified_only` precisely so that
/// user name resolution can never surface it (WI-422 / WI-423 — a `requires`-induced
/// scope link used to resurface it as a phantom rival to a user's own `sort Member`).
/// The absolute `try_resolve_symbol("Member")` these positions used DID reach it; the
/// ladder's unmarked readings do not, because they are name resolution and it is
/// excluded from name resolution by construction.
///
/// It is still nameable, by the spelling that says so: `..Member` — the root reading
/// (WI-1075), which a host means when it means the root regardless of scope. So this
/// is not WI-908's "one capability dropped" repeated; it is that capability re-spelled.
/// Both halves are asserted here, and the second is the half that would have made the
/// first a real loss if it failed.
///
/// FAILS PRE-FIX at BOTH flipping assertions: the unmarked spelling still resolved
/// (`Some("Member")`), and the marked one did not (`by_qualified_name` holds no key
/// `..Member`). Not a control — both sides move.
#[test]
fn a_qualified_only_kernel_name_is_reachable_only_by_the_root_spelling() {
    let mut kb = load_kb_with(FIXTURE);
    assert!(
        kb.try_resolve_symbol("Member").is_some(),
        "premise: `Member` IS registered, qualified-only — the row is about \
         which SPELLING reaches it, not about existence",
    );
    assert_eq!(
        sld_lookup_symbol(&mut kb, "Member"),
        None,
        "a delocalized kernel meta-sort is not a name ordinary resolution can denote",
    );
    assert_eq!(
        sld_lookup_symbol(&mut kb, "..Member").as_deref(),
        Some("Member"),
        "…and the root spelling still names it, so the reading moved rather than \
         the name being lost",
    );
    assert_eq!(
        sld_lookup_symbol(&mut kb, "..meta").as_deref(),
        Some("meta"),
        "same for a KERNEL_FUNCTORS entry",
    );
}

/// CONTROL — passes on both sides by design, and says why the fix is narrower than
/// it looks: `<global>` has no imports from a source file, so a short USER name is
/// out of reach before and after. Only a top-level `-i` import (WI-853) changes it.
#[test]
fn a_short_user_name_denotes_nothing_either_way() {
    let mut kb = load_kb_with(FIXTURE);
    assert_eq!(sld_lookup_symbol(&mut kb, "Color"), None);
    assert_eq!(sld_lookup_symbol(&mut kb, "Color.red"), None);
    assert_eq!(
        sld_lookup_symbol(&mut kb, "test.wi913.Color.red").as_deref(),
        Some("test.wi913.Color.red"),
        "…while the qualified spelling of the same entity is reachable, so the \
         two rows above are about the SPELLING, not about the fixture loading",
    );
}

/// THE HOST'S WAY TO SAY "the root". Since WI-1075 an unmarked dotted path is the
/// RELATIVE reading — head segment resolved in scope, tail appended — so a host name
/// resolves through the namespace chain the loader declares, and a host that means
/// the root regardless of what is in scope there spells it `..a.b.c`, exactly as
/// source does (kernel-language.md §8.6). Nothing drove that spelling at these
/// positions before; it is the capability that replaces the absolute lookup, not a
/// consolation for it.
#[test]
fn the_absolute_spelling_names_the_root_from_a_host_string() {
    let mut kb = load_kb_with(FIXTURE);
    assert_eq!(
        sld_lookup_symbol(&mut kb, "..anthill.prelude.List.cons").as_deref(),
        Some("anthill.prelude.List.cons"),
    );
    assert_eq!(
        sld_lookup_symbol(&mut kb, "..test.wi913.Color.red").as_deref(),
        Some("test.wi913.Color.red"),
    );
}

/// A FIELD IS NOT NAMEABLE BY PATH, and this is the one row where the routing takes
/// something away from a name that a loaded KB really holds. `resolve_dotted_in_kb`
/// refuses a field hit in BOTH its readings (WI-751 / WI-1075: a field is reached by
/// dot dispatch on a value, never by a path, so the hit is a category error rather
/// than a competing reading) — where the absolute `by_qualified_name` lookup these
/// positions used had no such rule and answered with the field symbol.
///
/// Censused rather than assumed: over a stdlib + `anthill-stl` load, 436 of the 441
/// dotted names the ladder does not reach are fields and the other 5 are `internal`
/// — nothing else. `kb::tests::wi913_every_dotted_name_is_reachable_or_explained`
/// is that census, kept as a test.
#[test]
fn a_field_is_not_nameable_by_path_from_a_host_string() {
    let mut kb = load_kb_with(FIXTURE);
    assert!(
        kb.try_resolve_symbol("anthill.geometry.Vec3.x").is_some(),
        "premise: the field symbol EXISTS under that qualified name",
    );
    assert_eq!(sld_lookup_symbol(&mut kb, "anthill.geometry.Vec3.x"), None);
    assert_eq!(
        sld_lookup_symbol(&mut kb, "..anthill.geometry.Vec3.x"),
        None,
        "…and the absolute spelling does not buy a way around it — the refusal is on \
         the ladder, not on one of its readings",
    );
}

// ── make_sort_ref_by_name ────────────────────────────────────────

/// FAILS PRE-FIX (`Modify` interned as a bare global symbol distinct from
/// `anthill.prelude.Modify`, which is WI-894's collapse: two scopes' same-spelled
/// names land on one bare name). The `intern` fallback is kept — see the site — but
/// it now runs only after the ladder, so a name the KB CAN denote is never twinned.
#[test]
fn make_sort_ref_by_name_prefers_the_ladder_over_a_bare_intern() {
    let mut kb = load_kb_with(FIXTURE);
    let modify = kb.make_sort_ref_by_name("Modify");
    let expected = kb
        .try_resolve_symbol("anthill.prelude.Modify")
        .expect("prelude Modify");
    let sym = anthill_core::kb::typing::extract_sort_ref_sym(
        &kb,
        &anthill_core::kb::term_view::TermIdView(modify),
    )
    .expect("a sort reference");
    assert_eq!(
        sym, expected,
        "`Modify` denotes the prelude sort, not a fresh bare twin",
    );
}

/// THE FALLIBLE SIBLING, and the reason it exists. A caller that must not receive a
/// phantom sort used to write a `try_resolve_symbol` PRE-CHECK and then call the
/// infallible form — two lookups for one question, safe only while both spelled it
/// the same way. Routing the mint through the ladder made them differ (the ladder is
/// strictly narrower: a field, an `internal` name), so the guard could admit a name
/// the mint then interned. `try_make_sort_ref_by_name` hands the caller the
/// resolution's own verdict, which is what the WI-714 `LogicalQuery` site now reads.
///
/// The divergence itself is not drivable — it is unrepresentable once the guard IS
/// the mint, which is the point of the change rather than a gap in the test. What is
/// drivable, and is here, is the verdict the caller now depends on.
#[test]
fn try_make_sort_ref_by_name_reports_instead_of_minting_a_phantom() {
    let mut kb = load_kb_with(FIXTURE);
    assert!(
        kb.try_make_sort_ref_by_name("anthill.reflect.LogicalQuery")
            .is_some(),
        "the WI-714 lowering's subject resolves",
    );
    assert!(
        kb.try_make_sort_ref_by_name("NoSuchSortAnywhere").is_none(),
        "a name that denotes nothing is REPORTED, never minted",
    );
    assert!(
        kb.try_make_sort_ref_by_name("anthill.geometry.Vec3.x")
            .is_none(),
        "…and so is a FIELD path, the class the old `try_resolve_symbol` pre-check \
         would have admitted while the mint interned a phantom",
    );
}

/// The `intern` fallback still answers for a name the KB genuinely does not have —
/// the behaviour `make_sort_ref_by_name`'s signature (`-> TermId`, no failure
/// channel) commits to. Passes on both sides; it is the guard that the row above
/// narrowed the fallback rather than deleting it.
#[test]
fn make_sort_ref_by_name_still_interns_a_name_the_kb_does_not_have() {
    let mut kb = load_kb_with(FIXTURE);
    let unknown = kb.make_sort_ref_by_name("NoSuchSortAnywhere");
    let sym = anthill_core::kb::typing::extract_sort_ref_sym(
        &kb,
        &anthill_core::kb::term_view::TermIdView(unknown),
    )
    .expect("a sort reference");
    assert_eq!(kb.qualified_name_of(sym), "NoSuchSortAnywhere");
}

/// A `make_fn` failure names the operation and the name — an `EvalError`, never a
/// silently-dropped functor. Passes on both sides (the message text changed with
/// the ladder; that it IS an error is what this pins).
#[test]
fn make_fn_is_loud_about_a_name_that_denotes_nothing() {
    let mut interp = interp_for(FIXTURE);
    let args = one_term_arg(&mut interp);
    let err = interp
        .call(
            "anthill.reflect.make_fn",
            &[Value::Str("no.such.Functor".into()), args],
        )
        .expect_err("an unresolvable functor name is an error");
    match err {
        EvalError::Internal(msg) => assert!(
            msg.contains("make_fn") && msg.contains("no.such.Functor"),
            "the error must name the operation and the name, got: {msg}",
        ),
        other => panic!("expected EvalError::Internal, got {other:?}"),
    }
}
