//! WI-708 — a BODY reference to an operation's type parameter, read as a VALUE,
//! resolves through the frame's type-argument channel (WI-272).
//!
//! `operation ty[T]() -> Type = Cell[V = T]` reads `T` inside the type application
//! `Cell[V = T]`. The argument is EVALUATED (WI-707's `SortTypeArgs` frame), so `T`
//! reaches `reduce_var`, which consults `Frame.type_args` via `find_type_arg`.
//!
//! Before this, the two keyings disagreed: the channel was keyed by the bare
//! `OperationInfo.type_params` symbol (`kb.intern("T")`), but a body reference to `T`
//! resolves through the op scope to the op-scoped `<ns>.<op>.T` symbol `scan_operation_params`
//! defines. `find_type_arg`'s identity match always missed, so `T` fell through to the
//! WI-206 bare-sort arm and delivered a dangling `Ref(T)` instead of the binding. This
//! pins that a body type-param read now carries its binding.

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;

use crate::common::interp_for;

/// The WI-708 reproducer: `ty[T = Int64]()` must evaluate to `Cell[V = Int64]`, not the
/// dangling `Cell[V = Ref(T)]`. The explicit `[T = Int64]` binding rides the WI-272
/// channel into the callee frame; the body's `Cell[V = T]` reads it back.
#[test]
fn a_body_type_param_read_carries_its_binding() {
    let src = r#"
namespace test.wi708
  import anthill.prelude.{Cell, Int64, Type}

  operation ty[T]() -> Type = Cell[V = T]
  operation ty_int() -> Type = ty[T = Int64]()
end
"#;
    let mut interp = interp_for(src);

    let v = interp
        .call("test.wi708.ty_int", &[])
        .unwrap_or_else(|e| panic!("ty_int: {e:?}"));
    let id = match v {
        Value::Term { id, .. } => id,
        other => panic!("expected a Term-carried type, got {other:?}"),
    };

    let (functor, named) = match interp.kb().get_term(id).clone() {
        Term::Fn { functor, named_args, .. } => (functor, named_args),
        other => panic!("expected a parameterized `Fn` type term (`Cell[V = …]`), got {other:?}"),
    };
    assert_eq!(interp.kb().resolve_sym(functor), "Cell", "the base sort is Cell");
    assert_eq!(named.len(), 1, "one type argument (V)");
    assert_eq!(interp.kb().resolve_sym(named[0].0), "V", "keyed by the declared param V");

    // The V binding must be `Int64` — the type argument `T` was bound to. Before the
    // fix it was the op-scoped `Ref(T)` (a dangling self-reference to the param name).
    match interp.kb().get_term(named[0].1).clone() {
        Term::Ref(s) | Term::Ident(s) => assert_eq!(
            interp.kb().resolve_sym(s),
            "Int64",
            "the type param `T` must read as its binding `Int64`, not a dangling `Ref(T)`"
        ),
        other => panic!(
            "V must bind the resolved `Int64`, not a dangling param reference; got {other:?}"
        ),
    }
}

/// The same read through a SECOND, differently-bound instantiation proves the channel is
/// per-call, not a stale first binding leaking through.
#[test]
fn distinct_instantiations_read_distinct_bindings() {
    let src = r#"
namespace test.wi708b
  import anthill.prelude.{Cell, Int64, String, Type}

  operation ty[T]() -> Type = Cell[V = T]
  operation ty_int() -> Type = ty[T = Int64]()
  operation ty_str() -> Type = ty[T = String]()
end
"#;
    let mut interp = interp_for(src);

    let arg_sort = |interp: &mut anthill_core::eval::Interpreter, op: &str| -> String {
        let v = interp.call(&format!("test.wi708b.{op}"), &[]).unwrap_or_else(|e| panic!("{op}: {e:?}"));
        let id = match v { Value::Term { id, .. } => id, other => panic!("{op}: got {other:?}") };
        let named = match interp.kb().get_term(id).clone() {
            Term::Fn { named_args, .. } => named_args,
            other => panic!("{op}: expected Fn, got {other:?}"),
        };
        match interp.kb().get_term(named[0].1).clone() {
            Term::Ref(s) | Term::Ident(s) => interp.kb().resolve_sym(s).to_string(),
            other => panic!("{op}: expected a sort ref binding, got {other:?}"),
        }
    };

    assert_eq!(arg_sort(&mut interp, "ty_int"), "Int64");
    assert_eq!(arg_sort(&mut interp, "ty_str"), "String");
}

/// The channel is re-keyed by resolving the param's short name in the op scope. That must
/// be confined to a GENUINE op-scope type param: `op.type_params` also carries synthesized
/// bare-spec carriers (`mint_bare_spec_carrier`, a `?P` named after a spec member, NOT a
/// scope local). Resolving a carrier's member name walks the op scope's ENCLOSING parents,
/// so a member name colliding with a visible top-level sort would key the channel onto that
/// body-readable sort and HIJACK a body read of it (the value returned would be the inferred
/// carrier, not the sort). `op_scoped_type_param_symbol` gates on `is_type_param`, so a
/// carrier keeps its inert key and a body read of the colliding sort is untouched.
#[test]
fn a_bare_spec_carrier_name_collision_does_not_hijack_a_body_read() {
    let src = r#"
namespace test.wi708coll
  import anthill.prelude.{Cell, Int64, Type}

  -- A top-level sort whose name collides with the spec member `Store.State` below.
  sort State
    entity mkState(n: Int64)
  end

  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end

  enum WIS
    entity wis(n: Int64)
  end

  -- `s: Store.State` mints a bare-spec carrier `?P` named `State` into probe's type_params;
  -- the body reads the top-level `sort State` as a value.
  operation probe(s: Store.State) -> Type = Cell[V = State]
  operation callProbe() -> Type = probe(wis(n: 0))
end
"#;
    let mut interp = interp_for(src);
    let v = interp
        .call("test.wi708coll.callProbe", &[])
        .unwrap_or_else(|e| panic!("callProbe: {e:?}"));
    let id = match v { Value::Term { id, .. } => id, other => panic!("got {other:?}") };
    let named = match interp.kb().get_term(id).clone() {
        Term::Fn { named_args, .. } => named_args,
        other => panic!("expected a `Cell[V = …]` Fn, got {other:?}"),
    };
    let arg = match interp.kb().get_term(named[0].1).clone() {
        Term::Ref(s) | Term::Ident(s) => interp.kb().resolve_sym(s).to_string(),
        other => panic!("expected a sort ref binding, got {other:?}"),
    };
    assert_eq!(
        arg, "State",
        "the body read of `State` must be the top-level sort — a bare-spec carrier of the \
         same member name must NOT hijack it to the inferred carrier `WIS`"
    );
}
