//! WI-SPGBP — the `kb` parameter of `anthill.reflect.KB` is REAL.
//!
//! Before this ticket every `kb`-taking builtin destructured its first argument as
//! `_kb_arg` and used the interpreter's own KB; `kb()` returned a zero-field entity, and
//! `kb_execute`'s own doc said so outright. These tests drive the form the ticket settled
//! on — `execute(loaded(sources), q)` — through the ordinary builtin path.

use anthill_core::eval::value::Value;
use anthill_core::kb::term::{Term, Var};

use crate::common;

/// The scoped source. One sort, one entity, one fact — enough to ask a real question of.
const CANDIDATE: &str = r#"
namespace spgbp.rt
  sort Widget
    entity gadget(id: Int64)
  end

  fact gadget(id: 7)
end
"#;

/// `KB.loaded([CANDIDATE])`, as an anthill call through the registered builtin.
fn call_loaded(interp: &mut anthill_core::eval::Interpreter, sources: &[&str]) -> Value {
    let elements: Vec<Value> = sources.iter().map(|s| Value::Str((*s).to_string())).collect();
    let list = interp
        .build_list_value(elements, &[])
        .expect("build List[String]");
    interp
        .call("anthill.reflect.KB.loaded", &[list])
        .expect("KB.loaded")
}

/// WI-SPGBP — `KB.loaded` mints a layer, and dropping the value discards it.
///
/// WHAT FAILS WHEN BACKED OUT: without `kb_loaded` the first line is `UnknownOperation`;
/// without the arena sweep the last assertion still finds `Widget` resolvable.
#[test]
fn spgbp_loaded_mints_a_layer_and_dropping_it_discards() {
    let mut interp = common::interp_for("");
    assert_eq!(interp.layer_depth(), 0, "no layers before the first `loaded`");

    let layer = call_loaded(&mut interp, &[CANDIDATE]);
    assert!(
        matches!(layer, Value::Kb(_)),
        "`loaded` must answer a first-class KB value, got {layer:?}"
    );
    assert_eq!(interp.layer_depth(), 1);
    assert!(
        interp.kb().try_resolve_symbol("spgbp.rt.Widget").is_some(),
        "the scoped load's sort resolves while the layer is held"
    );

    drop(layer);
    interp.sweep_layers();

    assert_eq!(interp.layer_depth(), 0, "dropping the value discards the layer");
    assert_eq!(
        interp.kb().try_resolve_symbol("spgbp.rt.Widget"),
        None,
        "a discarded layer leaves NO resolvable name behind"
    );
}

/// WI-SPGBP — THE HEADLINE. A lazy `Stream[Solution]` from `execute` holds the KB it was
/// made from, so the scope cannot close under a search that has not finished.
///
/// This is the bug the ticket says a BRACKET form would have had: `execute` returns a
/// `StreamSource::Resolver` pumped later by `splitFirst`, so a scope popped at the
/// bracket's exit would leave the stream resolving against a base that is gone. Here the
/// only remaining holder between `drop(layer)` and the first pull is the stream itself.
///
/// WHAT FAILS WHEN BACKED OUT: drop the `layer` field from `StreamSource::Resolver` (or
/// have `kb_execute` ignore its first argument again, as it did before this ticket) and
/// the assertions after `drop(layer)` fail — the layer is discarded and the pull answers
/// nothing.
#[test]
fn spgbp_a_lazy_stream_keeps_its_layer_alive() {
    let mut interp = common::interp_for("");
    let layer = call_loaded(&mut interp, &[CANDIDATE]);

    // `pattern_query(gadget(id: ?i))` — the goal is a term over the LAYER's functor,
    // written with the caller's own symbol table. That it can be written at all is what
    // "a layer, not a second KB" buys.
    let gadget = interp
        .kb()
        .try_resolve_symbol("spgbp.rt.Widget.gadget")
        .expect("the layer's constructor resolves");
    let pattern_query = interp
        .kb()
        .try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
        .expect("pattern_query");
    let id_field = interp.kb_mut().intern("id");
    let term_field = interp.kb_mut().intern("term");
    let i_sym = interp.kb_mut().intern("i");
    let vi = interp.kb_mut().fresh_var(i_sym);
    let var_i = interp.kb_mut().alloc(Term::Var(Var::Global(vi)));

    let goal = Value::Entity {
        functor: gadget,
        pos: Vec::new().into(),
        named: vec![(id_field, Value::term(var_i))].into(),
    };
    let query = Value::Entity {
        functor: pattern_query,
        pos: Vec::new().into(),
        named: vec![(term_field, goal)].into(),
    };

    let stream = interp
        .call("anthill.reflect.KB.execute", &[layer.clone(), query])
        .expect("KB.execute");
    let handle = match stream {
        Value::Stream(h) => h,
        other => panic!("execute must answer a Stream, got {other:?}"),
    };

    // Everything but the STREAM lets go of the layer, and the sweep runs.
    drop(layer);
    interp.sweep_layers();
    assert_eq!(
        interp.layer_depth(),
        1,
        "the stream is the layer's last holder — the scope must NOT have closed"
    );
    assert!(
        interp.kb().try_resolve_symbol("spgbp.rt.Widget").is_some(),
        "the layer's definitions are still reachable to the pending search"
    );

    let first = interp
        .stream_split_first(&handle)
        .expect("pull the stream")
        .map(|(sol, _rest)| sol);
    assert!(
        first.is_some(),
        "the search must answer off the layer's own fact — this is the pull that a \
         bracket form would have made against a base that was already gone"
    );

    drop(handle);
    interp.sweep_layers();
    assert_eq!(interp.layer_depth(), 0);
    assert_eq!(
        interp.kb().try_resolve_symbol("spgbp.rt.Widget"),
        None,
        "once the stream is gone too, the scope closes"
    );
}

/// WI-SPGBP — a candidate that does not load RAISES, and leaves the KB untouched.
///
/// The diagnostics are the answer a checker is asking for, so this is an `Error` payload
/// rather than an internal fault. The KB assertion is the one that matters: a partially
/// applied layer is the state the ticket calls worse than none.
///
/// WHAT FAILS WHEN BACKED OUT: remove the `restore_scoped` on the failure path and
/// `layer_depth` is still 0 (nothing was pushed) while `spgbp.broken` is left resolvable.
#[test]
fn spgbp_a_source_that_does_not_load_raises_and_unwinds() {
    let mut interp = common::interp_for("");
    let elements = vec![Value::Str(
        r#"
namespace spgbp.broken
  sort Thing
    entity thing(id: NoSuchSortAnywhere)
  end
end
"#
        .to_string(),
    )];
    let list = interp
        .build_list_value(elements, &[])
        .expect("build List[String]");

    let err = interp
        .call("anthill.reflect.KB.loaded", &[list])
        .expect_err("a source naming an undeclared sort must not load");
    assert!(
        matches!(err, anthill_core::eval::EvalError::Raised { .. }),
        "a load failure is an Error-effect payload, not an internal fault: {err:?}"
    );

    assert_eq!(interp.layer_depth(), 0, "a failed `loaded` pushes no layer");
    assert_eq!(
        interp.kb().try_resolve_symbol("spgbp.broken.Thing"),
        None,
        "a failed `loaded` leaves the KB exactly as it found it"
    );
}

/// WI-SPGBP — a failed scoped load reaches an installed `Error` HANDLER.
///
/// `reflect.anthill` declares `operation loaded(...) -> KB effects Error`, and this is
/// the test that the declaration is true rather than decorative. A checker's whole job is
/// to CATCH this and report the diagnostics, so building an `EvalError::Raised` directly
/// — which is what this did before review — would have been a bespoke error the declared
/// effect could never handle. That is the WI-467 / WI-610 defect exactly.
///
/// WHAT FAILS WHEN BACKED OUT: route `kb_loaded`'s failure through a hand-built
/// `EvalError::Raised` again and the handler never fires — `seen` stays empty and the
/// call returns `Raised` instead of the handler's own refusal.
#[test]
fn spgbp_a_failed_load_is_catchable_by_an_error_handler() {
    use anthill_core::eval::effects::HandlerAction;
    use std::cell::RefCell;
    use std::rc::Rc;

    let mut interp = common::interp_for("");
    // The handler records the payload and then RESUMES, which the runtime refuses as
    // non-resumable — a refusal that can only be reached by going through the handler at
    // all, so it doubles as proof the routing happened.
    let seen: Rc<RefCell<Vec<Value>>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&seen);
    interp
        .register_effect_handler(
            "anthill.prelude.Error",
            Box::new(move |_i, _op, args| {
                sink.borrow_mut().extend(args.iter().cloned());
                Ok(HandlerAction::Pure(Value::Unit))
            }),
        )
        .expect("register Error handler");

    let list = interp
        .build_list_value(vec![Value::Str("namespace ( ) ] not anthill".to_string())], &[])
        .expect("build List[String]");
    let _ = interp.call("anthill.reflect.KB.loaded", &[list]);

    let payloads = seen.borrow();
    assert_eq!(
        payloads.len(),
        1,
        "the Error handler must have been invoked exactly once; got {payloads:?}"
    );
    // An ENTITY, not a bare string: a handler that fires must be able to destructure the
    // payload, and `load_failed(diagnostics: List[String])` is what it destructures.
    match &payloads[0] {
        Value::Entity { functor, .. } => assert_eq!(
            interp.kb().qualified_name_of(*functor),
            "anthill.reflect.LoadFailed.load_failed",
            "the payload must be the declared constructor"
        ),
        other => panic!("expected a load_failed entity payload, got {other:?}"),
    }
}

/// WI-SPGBP — a source that does not PARSE is refused before anything is snapshotted.
#[test]
fn spgbp_a_source_that_does_not_parse_raises() {
    let mut interp = common::interp_for("");
    let list = interp
        .build_list_value(vec![Value::Str("namespace ( ) ] not anthill".to_string())], &[])
        .expect("build List[String]");
    let err = interp
        .call("anthill.reflect.KB.loaded", &[list])
        .expect_err("unparseable source must be refused");
    assert!(
        matches!(err, anthill_core::eval::EvalError::Raised { .. }),
        "got {err:?}"
    );
    assert_eq!(interp.layer_depth(), 0);
}

/// WI-SPGBP — `execute(kb(), q)` still means "the ambient KB".
///
/// The ambient sentinel carries no layer, so the pre-ticket spelling keeps working. This
/// is a CONTROL: it passes both with and without this ticket, and exists so that making
/// the `kb` argument real cannot quietly break the argument that was already there.
#[test]
fn spgbp_the_ambient_kb_spelling_is_unchanged() {
    let mut interp = common::interp_for(
        r#"
namespace spgbp.ambient
  sort Widget
    entity gadget(id: Int64)
  end
  fact gadget(id: 3)
end
"#,
    );
    let ambient = interp
        .call("anthill.reflect.KB.kb", &[])
        .expect("kb() is the ambient sentinel");

    let gadget = interp
        .kb()
        .try_resolve_symbol("spgbp.ambient.Widget.gadget")
        .expect("base constructor");
    let pattern_query = interp
        .kb()
        .try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
        .expect("pattern_query");
    let id_field = interp.kb_mut().intern("id");
    let term_field = interp.kb_mut().intern("term");
    let i_sym = interp.kb_mut().intern("i");
    let vi = interp.kb_mut().fresh_var(i_sym);
    let var_i = interp.kb_mut().alloc(Term::Var(Var::Global(vi)));

    let query = Value::Entity {
        functor: pattern_query,
        pos: Vec::new().into(),
        named: vec![(
            term_field,
            Value::Entity {
                functor: gadget,
                pos: Vec::new().into(),
                named: vec![(id_field, Value::term(var_i))].into(),
            },
        )]
        .into(),
    };

    let stream = interp
        .call("anthill.reflect.KB.execute", &[ambient, query])
        .expect("KB.execute over the ambient KB");
    let handle = match stream {
        Value::Stream(h) => h,
        other => panic!("expected a Stream, got {other:?}"),
    };
    assert!(
        interp
            .stream_split_first(&handle)
            .expect("pull")
            .is_some(),
        "the ambient spelling must still answer off the base's own facts"
    );
    assert_eq!(interp.layer_depth(), 0, "`kb()` mints no layer");
}
