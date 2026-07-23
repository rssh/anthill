//! WI-818 — a spec-level `rule` default is a LAW, not executable backing.
//!
//! DECISION (the ticket's option 2, the smaller change): "backed" means
//! EXECUTABLE — a runnable body or a builtin. A `rule` on the spec
//! (`rule tag(?x) = 111`) is a law relating the abstract operation to others:
//! the SLD resolver can use it, but the evaluator cannot dispatch to it (a rule
//! is not a body), so counting it as backing (as WI-363 pinned — that test is
//! REVERSED by this ticket) certified programs that loaded clean and then died
//! at run time. Reasons for (2) over (1) ("make rule defaults executable"):
//! the stdlib already treats laws as non-evaluable specification
//! (`stream.anthill`: "resolvable but not evaluable" — the WI-362 default-body
//! pattern exists precisely because of it); an SLD route for a value-returning
//! op has no sound answer for multiplicity, floundering, or the no-solution
//! case (an empty `head` would still fail at run time, so (1) cannot restore
//! the load-time guarantee the check exists to give); and the one eval→SLD
//! bridge that DOES exist (`eq`, WI-625 gap 4) is predicate-shaped, where
//! "no proof = false" is sound.
//!
//! Shipped alongside, because the load rule now demands executable backing:
//! `Stream.headOption`/`head`/`tail` gained default bodies over `splitFirst`
//! (the `isEmpty` WI-362 pattern; `tail`'s row gained the guarded
//! `Error[EmptyStream]` it always incurred), `List` carries its own
//! `head`/`headOption` (WI-444 override), `Error.raise` bodies type via
//! `Nothing` = bottom, a body may raise a label its row declares GUARDED (the
//! conservatively-present reading), and the override-refinement effects leg
//! aligns impl→spec param names before comparing guarded atoms.
//!
//! Also fixed here (the ticket's second defect): a spec op reached through the
//! `requires` path with no executable backing reports `OperationBodyMissing`
//! with the QUALIFIED name — the same error the direct call reports — instead
//! of degrading to `UnknownOperation { "tag" }` (a name-resolution failure it
//! is not).

use anthill_core::eval::{EvalError, Value};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

// ── The ticket's three variants ─────────────────────────────────────────

/// (A) No backing at all: load is rejected, and the diagnostic names the two
/// conditions the check tests — no (executable) default on the spec, no own
/// op on the carrier.
#[test]
fn variant_a_no_backing_rejected() {
    let src = r#"
namespace wi818.a
  import anthill.prelude.{Int64}
  sort Nameable
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Widget
    entity widget(id: Int64)
    fact Nameable[T = Widget]
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("an unbacked provider op must reject the load");
    let text = errs.join("\n");
    assert!(
        text.contains("backs no operation")
            && text.contains("wi818.a.Nameable.tag")
            && text.contains("no default on")
            && text.contains("no own"),
        "expected (A)'s two-condition diagnostic; got:\n{text}"
    );
}

/// (B) The carrier supplies a real implementation: loads clean, and the value
/// flows both through the direct call and through the `requires` path.
#[test]
fn variant_b_carrier_impl_loads_and_evaluates() {
    let src = r#"
namespace wi818.b
  import anthill.prelude.{Int64}
  sort Nameable
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Widget
    entity widget(id: Int64)
    fact Nameable[T = Widget]
    operation tag(x: Widget) -> Int64 = 111
  end
  sort Box
    sort T = ?
    requires Nameable[T = T]
    operation same(x: T) -> Int64 = tag(x)
  end
end
"#;
    for (op, expect) in [("wi818.b.Widget.tag", 111), ("wi818.b.Box.same", 111)] {
        // Fresh interpreter per call — a trapped call poisons later ones.
        let mut interp = crate::common::interp_for(src);
        let widget = entity(&mut interp, "wi818.b.Widget.widget", &[("id", Value::Int(1))]);
        let got = interp.call(op, &[widget]);
        assert!(
            matches!(got, Ok(Value::Int(n)) if n == expect),
            "{op} must evaluate to {expect}; got {got:?}"
        );
    }
}

/// (C) The spec carries a `rule` default and the carrier supplies nothing:
/// REJECTED AT LOAD with (A)'s message. This is the decision pin — the rule
/// satisfied the old check's "default on the spec" condition while the
/// evaluator could not run it, which is exactly the disagreement WI-818
/// closes. "No default" now means no EXECUTABLE default.
#[test]
fn variant_c_rule_default_rejected_at_load() {
    let src = r#"
namespace wi818.c
  import anthill.prelude.{Int64}
  sort Nameable
    sort T = ?
    operation tag(x: T) -> Int64
    rule tag(?x) = 111
  end
  sort Widget
    entity widget(id: Int64)
    fact Nameable[T = Widget]
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("a rule-only spec default is not executable backing (WI-818); the load passed");
    let text = errs.join("\n");
    assert!(
        text.contains("backs no operation") && text.contains("wi818.c.Nameable.tag"),
        "expected (C) to reject with (A)'s unbacked-op diagnostic; got:\n{text}"
    );
}

/// Review follow-up to (C): a NAMESPACE-LEVEL operation body sharing the spec
/// op's short name is not backing either. No dispatch table (`sort_ops`,
/// instance-fact binding, witness sort) can route a spec-op call to a
/// namespace-level op, so counting it (as the original candidate list did)
/// certified programs that loaded clean and then died at run time with
/// `OperationBodyMissing` — measured by the review's probe before the ns
/// candidate was retired from `op_backed`.
#[test]
fn ns_level_body_is_not_backing() {
    let src = r#"
namespace wi818.ns
  import anthill.prelude.{Int64}
  sort Nameable
    sort T = ?
    operation tag(x: T) -> Int64
  end
  operation tag(x: Widget) -> Int64 = 111
  sort Widget
    entity widget(id: Int64)
    fact Nameable[T = Widget]
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("a namespace-level body must NOT back a spec op (dispatch cannot reach it)");
    let text = errs.join("\n");
    assert!(
        text.contains("backs no operation") && text.contains("wi818.ns.Nameable.tag"),
        "expected the unbacked-op rejection for the ns-level-body shape; got:\n{text}"
    );
}

// ── The error-shape defect: requires path == direct path ────────────────

/// With NO provider anywhere, the load-time backing check has nothing to
/// check, so the unbacked state is still reachable at run time. Both routes to
/// it — the direct call and the `requires`-path dispatch — must report the
/// SAME error: `OperationBodyMissing` naming the op QUALIFIED. Before WI-818
/// the dispatch fall-through degraded to `UnknownOperation { "tag" }` — a
/// name-resolution failure for what is a missing implementation (`tag` is
/// declared on `Nameable`, and `requires Nameable[T]` is precisely what brings
/// it into scope).
#[test]
fn requires_path_reports_missing_body_like_direct_call() {
    let src = r#"
namespace wi818.e
  import anthill.prelude.{Int64}
  sort Nameable
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Thing
    entity thing(id: Int64)
  end
  sort Box
    sort T = ?
    requires Nameable[T = T]
    operation same(x: T) -> Int64 = tag(x)
  end
end
"#;
    for op in ["wi818.e.Nameable.tag", "wi818.e.Box.same"] {
        let mut interp = crate::common::interp_for(src);
        let thing = entity(&mut interp, "wi818.e.Thing.thing", &[("id", Value::Int(1))]);
        let got = interp.call(op, &[thing]);
        match got {
            Err(EvalError::OperationBodyMissing { ref name, .. }) => assert_eq!(
                name, "wi818.e.Nameable.tag",
                "{op}: the missing implementation must be named QUALIFIED"
            ),
            other => panic!(
                "{op}: expected OperationBodyMissing naming wi818.e.Nameable.tag \
                 (the requires path must not degrade to UnknownOperation); got {other:?}"
            ),
        }
    }
}

// ── The stdlib consequence: head/tail/headOption are evaluable ──────────

/// `head(cons(7, nil))` — the call the old world died on with
/// `UnknownOperation { "head" }` — evaluates: `List.head` (the WI-444
/// override, a direct cons read via `headOption`) returns the element, and the
/// spec defaults serve the carriers that supply only `splitFirst`.
#[test]
fn stdlib_stream_reads_evaluate() {
    let src = r#"
namespace wi818.stdlib
  import anthill.prelude.{Int64, Bool, List, Option, EmptyStream}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Stream.{head, tail, headOption, isEmpty}

  sort Use
    operation first() -> Int64 effects Error[EmptyStream] = head(cons(7, nil))
    operation ho() -> Option[T = Int64] = headOption(cons(7, nil))
    operation ho_empty() -> Option[T = Int64] effects Error[EmptyStream] =
      headOption(tail(cons(7, nil)))
    operation third() -> Int64 effects Error[EmptyStream] =
      head(tail(tail(cons(1, cons(2, cons(7, nil))))))
    operation empty() -> Bool = isEmpty(nil)
  end
end
"#;
    let cases: &[(&str, fn(&mut anthill_core::eval::Interpreter, &Result<Value, EvalError>) -> bool)] = &[
        ("first", |_, r| matches!(r, Ok(Value::Int(7)))),
        ("ho", |i, r| entity_functor_is(i, r, "anthill.prelude.Option.some")),
        ("ho_empty", |i, r| entity_functor_is(i, r, "anthill.prelude.Option.none")),
        ("third", |_, r| matches!(r, Ok(Value::Int(7)))),
        ("empty", |_, r| matches!(r, Ok(Value::Bool(true)))),
    ];
    for (op, ok) in cases {
        let mut interp = crate::common::interp_for(src);
        let got = interp.call(&format!("wi818.stdlib.Use.{op}"), &[]);
        assert!(ok(&mut interp, &got), "Use.{op}: unexpected result {got:?}");
    }
}

/// `head` of an empty stream raises the DECLARED `Error[EmptyStream]` — the
/// WI-567 follow-on ("no eval-side raise yet") delivered by the default
/// body's `none` arm. Unhandled, it surfaces as `Raised` carrying the
/// `empty_stream` payload (never the effect dispatcher's no-handler
/// `Internal`).
#[test]
fn stdlib_head_of_empty_raises_empty_stream() {
    let src = r#"
namespace wi818.boom
  import anthill.prelude.{Int64, EmptyStream}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Stream.{head, tail}

  sort Use
    operation boom() -> Int64 effects Error[EmptyStream] = head(tail(cons(7, nil)))
  end
end
"#;
    let mut interp = crate::common::interp_for(src);
    let got = interp.call("wi818.boom.Use.boom", &[]);
    match got {
        Err(EvalError::Raised { ref payload }) => {
            let Value::Entity { functor, .. } = payload else {
                panic!("expected an empty_stream entity payload; got {payload:?}");
            };
            assert_eq!(
                interp.kb().qualified_name_of(*functor),
                "anthill.prelude.EmptyStream.empty_stream",
                "the raise must carry the declared payload"
            );
        }
        other => panic!("head of empty must raise Error[EmptyStream]; got {other:?}"),
    }
}

/// The default bodies run on the carriers that actually INHERIT them —
/// `MappedStream`/`FilteredStream` supply only `splitFirst`, so `head` here is
/// the spec default's frame (List's override never enters), including the
/// default body's raise arm being reachable. Without this, the defaults the
/// backing check certifies for the combinator carriers had zero run-time
/// witness (every other eval fixture's receiver is a List, which overrides).
#[test]
fn stream_defaults_evaluate_on_inheriting_carriers() {
    let src = r#"
namespace wi818.comb
  import anthill.prelude.{Int64, Option, EmptyStream}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Stream.{head, headOption}
  import anthill.prelude.MappedStream.{map}
  import anthill.prelude.FilteredStream.{filter}
  import anthill.prelude.Numeric.{add}
  import anthill.prelude.PartialOrd.{gt}

  sort Use
    operation mh() -> Int64 effects Error[EmptyStream] =
      head(map[EffS = {}](cons(7, nil), lambda (x: Int64) -> add(x, 100)))
    operation fho() -> Option[T = Int64] =
      headOption(filter[EffS = {}](cons(7, nil), lambda (x: Int64) -> gt(x, 100)))
  end
end
"#;
    let mut i1 = crate::common::interp_for(src);
    let got = i1.call("wi818.comb.Use.mh", &[]);
    assert!(
        matches!(got, Ok(Value::Int(107))),
        "head over a MappedStream must run the spec default over MappedStream.splitFirst; got {got:?}"
    );
    let mut i2 = crate::common::interp_for(src);
    let got = i2.call("wi818.comb.Use.fho", &[]);
    assert!(
        entity_functor_is(&mut i2, &got, "anthill.prelude.Option.none"),
        "headOption over a FilteredStream dropping everything must be none; got {got:?}"
    );
}

/// The negative control for the guarded-label admission: a body raising a
/// label the row does NOT declare is still refused — the admission covers
/// exactly the declared guarded atom's own label, nothing wider.
#[test]
fn undeclared_label_under_guarded_row_still_refused() {
    let src = r#"
namespace wi818.neg
  import anthill.prelude.{Int64, List, EmptyStream}
  import anthill.prelude.Stream.{isEmpty}
  import wi818.neg.Boom.{boom}

  sort Boom
    entity boom
  end
  sort Use
    operation f(xs: List) -> Int64 effects { Error[EmptyStream] :- isEmpty(xs) } =
      Error.raise(boom)
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("raising Error[Boom] under a row declaring only guarded Error[EmptyStream] must be refused");
    let text = errs.join("\n");
    assert!(
        text.contains("undeclared effect") && text.contains("Boom"),
        "expected the undeclared-effect rejection naming Boom; got:\n{text}"
    );
}

/// An installed Error handler that RESUMES a raise with a value is refused —
/// `raise -> Nothing` is non-resumable, so the resume surfaces loudly instead
/// of the raise silently evaluating to the handler's value. (The unhandled
/// direction — no handler ⇒ `Raised {{ payload }}` — is pinned by
/// [`stdlib_head_of_empty_raises_empty_stream`].)
#[test]
fn error_handler_resume_is_refused_as_non_resumable() {
    use anthill_core::eval::effects::HandlerAction;
    let src = r#"
namespace wi818.resume
  import anthill.prelude.{Int64, EmptyStream}
  import anthill.prelude.EmptyStream.{empty_stream}
  sort Use
    operation raiser() -> Int64 effects Error[EmptyStream] = Error.raise(empty_stream)
  end
end
"#;
    let mut interp = crate::common::interp_for(src);
    interp
        .register_effect_handler(
            "anthill.prelude.Error",
            Box::new(|_i, _op, _args| Ok(HandlerAction::Pure(Value::Int(0)))),
        )
        .expect("register Error handler");
    let got = interp.call("wi818.resume.Use.raiser", &[]);
    match got {
        Err(EvalError::Internal(ref msg)) => assert!(
            msg.contains("non-resumable"),
            "expected the non-resumable refusal; got Internal({msg})"
        ),
        other => panic!("a resuming Error handler must be refused loudly; got {other:?}"),
    }
}

// ── The SLD world is unchanged — and not doubled ────────────────────────

/// The duplication guard: with the laws AND the new default bodies both in
/// the KB, a `head`/`headOption` goal must still yield EXACTLY one solution —
/// the law and any body-derived view of the body must not each contribute one
/// (a silent multiplicity change every relational consumer would feel).
///
/// Deliberately NOT pinned here: the answers' VALUE. Measured, the law
/// answers for both goals flounder today (`?r` unresolved — the law RHS is an
/// op call, `fst(?p)` / `some(fst(?p))`, and result-position reduction is a
/// pre-existing resolver gap, identical before and after WI-818). Building
/// that reduction is what the ticket's rejected option (1) — executable rule
/// defaults — would have required; option (2) leaves the SLD world exactly
/// where it was.
#[test]
fn sld_head_law_still_proves_once() {
    let src = r#"
namespace wi818.sld
  import anthill.prelude.{Int64}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Stream.{head, headOption, tail, isEmpty}

  rule pick7(?r) :- head(cons(7, nil)) = ?r
  rule pickho(?r) :- headOption(cons(7, nil)) = ?r
  rule picktail(?r) :- tail(cons(7, nil)) = ?r
  rule pickie(?r) :- isEmpty(cons(7, nil)) = ?r
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    for (rule, what) in [
        ("wi818.sld.pick7", "head"),
        ("wi818.sld.pickho", "headOption"),
        ("wi818.sld.picktail", "tail"),
        ("wi818.sld.pickie", "isEmpty"),
    ] {
        let sols = query_unary(&mut kb, rule);
        assert_eq!(
            sols.len(),
            1,
            "{what}'s law+body pair must prove exactly once (no body-derived double); got {sols:?}"
        );
    }
}

// ── Raise-in-body typing (the enabling typer changes) ───────────────────

/// `Error.raise(e)` in tail position types against a concrete return, a
/// projection return (`xs.T` — the shape the Stream defaults need), and as a
/// match-arm join. Pins `anthill.prelude.Nothing` = bottom (the explicit
/// import spelling of the kernel-vocab `Nothing`, `type_head`'s WI-818 alias).
#[test]
fn raise_bodies_typecheck() {
    let cases: &[(&str, &str)] = &[
        ("concrete return", r#"
namespace wi818.q1
  import anthill.prelude.{Int64, EmptyStream}
  import anthill.prelude.EmptyStream.{empty_stream}
  sort Use
    operation f(x: Int64) -> Int64 effects Error[EmptyStream] = Error.raise(empty_stream)
  end
end
"#),
        ("projection return", r#"
namespace wi818.q2
  import anthill.prelude.{List, EmptyStream}
  import anthill.prelude.EmptyStream.{empty_stream}
  sort Use
    operation g(xs: List) -> xs.T effects Error[EmptyStream] = Error.raise(empty_stream)
  end
end
"#),
        ("match-arm join", r#"
namespace wi818.q3
  import anthill.prelude.{Int64, List, Option, Pair, EmptyStream}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.EmptyStream.{empty_stream}
  sort Use
    operation h(xs: List) -> Int64 effects Error[EmptyStream] =
      match List.splitFirst(xs)
        case none() -> Error.raise(empty_stream)
        case some(pair(a, b)) -> 1
  end
end
"#),
    ];
    for (label, src) in cases {
        if let Err(errs) = crate::common::try_load_kb_with(src) {
            panic!("raise body must typecheck ({label}); got:\n{}", errs.join("\n"));
        }
    }
}

// ── helpers ─────────────────────────────────────────────────────────────

/// Build a named-args entity value for `ctor_qn`.
fn entity(
    interp: &mut anthill_core::eval::Interpreter,
    ctor_qn: &str,
    named: &[(&str, Value)],
) -> Value {
    let functor = interp
        .kb_mut()
        .try_resolve_symbol(ctor_qn)
        .unwrap_or_else(|| panic!("resolve {ctor_qn}"));
    let named: Vec<_> = named
        .iter()
        .map(|(n, v)| (interp.kb_mut().intern(n), v.clone()))
        .collect();
    Value::Entity { functor, pos: vec![].into(), named: named.into() }
}

/// Does `r` hold an entity whose functor's qualified name is `qn`?
fn entity_functor_is(
    interp: &mut anthill_core::eval::Interpreter,
    r: &Result<Value, EvalError>,
    qn: &str,
) -> bool {
    matches!(r, Ok(Value::Entity { functor, .. })
        if interp.kb().qualified_name_of(*functor) == qn)
}

/// Solutions of the unary rule `qn(?r)`: (`?r` reified and rendered readably,
/// solution is definite — i.e. no floundered residual).
fn query_unary(kb: &mut KnowledgeBase, qn: &str) -> Vec<(String, bool)> {
    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("resolve {qn}"));
    let r_sym = kb.intern("r");
    let r_vid = kb.fresh_var(r_sym);
    let r_var = kb.alloc(Term::Var(Var::Global(r_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_elem(r_var, 1),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let mut out = Vec::with_capacity(sols.len());
    for sol in &sols {
        let v = kb.reify(r_var, &sol.subst);
        let rendered = match v {
            Value::Int(n) => n.to_string(),
            Value::Entity { functor, .. } => kb.qualified_name_of(functor).to_string(),
            Value::Term { id, .. } => match kb.get_term(id) {
                Term::Const(Literal::Int(n)) => n.to_string(),
                _ => anthill_core::persistence::print::TermPrinter::new(kb).print_term(id),
            },
            other => format!("{other:?}"),
        };
        out.push((rendered, sol.is_definite()));
    }
    out
}
