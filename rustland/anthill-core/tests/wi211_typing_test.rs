//! WI-211 — polymorphic type-arg propagation in `unify_types`.
//!
//! When the typer sees `Stream.head(s)` with `s : Stream[T = Term, E = Error]`,
//! the spec param's type is `sort_ref(Stream)` (bare). `unify_types` must
//! propagate the per-call bindings (`T = Term`, `E = Error`) into the spec's
//! sort-level type-param Vars so that the return type `Option[T = T]` walks
//! down to `Option[T = Term]`.

mod common;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::Term;
use anthill_core::kb::typing::{
    extract_sort_ref_sym, get_named_arg, type_check_expr, TypingEnv,
};
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;
use smallvec::SmallVec;

fn load_stdlib_kb() -> KnowledgeBase {
    let files = common::collect_stdlib_and_rust_bindings();
    let parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

#[test]
fn stream_head_on_concrete_stream_yields_option_with_concrete_t() {
    let mut kb = load_stdlib_kb();

    let head_sym = kb.try_resolve_symbol("anthill.prelude.Stream.head")
        .expect("Stream.head registered");
    let stream_sym = kb.try_resolve_symbol("anthill.prelude.Stream")
        .expect("Stream registered");
    let term_sym = kb.try_resolve_symbol("anthill.reflect.Term")
        .expect("Term registered");
    let error_sym = kb.try_resolve_symbol("anthill.prelude.Error")
        .expect("anthill.prelude.Error registered");

    let t_field = kb.intern("T");
    let e_field = kb.intern("E");
    let term_ty = kb.make_sort_ref(term_sym);
    let error_ty = kb.make_sort_ref(error_sym);
    let stream_base = kb.make_sort_ref(stream_sym);
    let stream_concrete = kb.make_parameterized_type(
        stream_base,
        &[(t_field, term_ty), (e_field, error_ty)],
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
    env.bind_var("s".to_string(), stream_concrete);

    let result = type_check_expr(&mut kb, &env, apply_term)
        .expect("Stream.head(s) for s:Stream[T=Term,E=Error] should type-check");
    let ty = result.ty;
    let ty_str = TermPrinter::new(&kb).print_term(ty);

    // The return type must be parameterized(Option, [T = sort_ref(Term)]).
    // Pre-fix it would have been parameterized(Option, [T = Var(_)]) — i.e.
    // an unbound Var because unify_parameterized_with_sort_ref hadn't
    // propagated the per-call bindings.
    let named_args = match kb.get_term(ty) {
        Term::Fn { named_args, .. } => named_args.clone(),
        _ => panic!("expected parameterized return type; got {ty_str}"),
    };
    let base = get_named_arg(&kb, &named_args, "base")
        .unwrap_or_else(|| panic!("missing base field; got {ty_str}"));
    let base_sym = extract_sort_ref_sym(&kb, base)
        .unwrap_or_else(|| panic!("base not a sort_ref; got {ty_str}"));
    assert_eq!(
        kb.qualified_name_of(base_sym),
        "anthill.prelude.Option",
        "expected Option base; got {ty_str}",
    );

    let bindings = get_named_arg(&kb, &named_args, "bindings")
        .unwrap_or_else(|| panic!("missing bindings field; got {ty_str}"));
    let mut t_value_sym = None;
    let mut cur = bindings;
    loop {
        let (functor, na) = match kb.get_term(cur) {
            Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
            _ => break,
        };
        if kb.resolve_sym(functor) == "nil" { break; }
        let head_binding = match get_named_arg(&kb, &na, "head") {
            Some(t) => t,
            None => break,
        };
        if let Term::Fn { named_args: bna, .. } = kb.get_term(head_binding).clone() {
            let param = get_named_arg(&kb, &bna, "param");
            let value = get_named_arg(&kb, &bna, "value");
            if let (Some(p), Some(v)) = (param, value) {
                if let Term::Ref(p_sym) = kb.get_term(p) {
                    if kb.resolve_sym(*p_sym) == "T" {
                        t_value_sym = extract_sort_ref_sym(&kb, v);
                    }
                }
            }
        }
        cur = match get_named_arg(&kb, &na, "tail") {
            Some(t) => t,
            None => break,
        };
    }

    let t_sym = t_value_sym
        .unwrap_or_else(|| panic!("expected T = sort_ref(...) in Option binding; got {ty_str}"));
    assert_eq!(
        kb.qualified_name_of(t_sym),
        "anthill.reflect.Term",
        "expected T = anthill.reflect.Term; got T = {} (full ty: {ty_str})",
        kb.qualified_name_of(t_sym),
    );
}
