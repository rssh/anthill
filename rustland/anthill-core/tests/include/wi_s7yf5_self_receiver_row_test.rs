//! S7YF5: self-receiver provisions substitute row parameters at the receiver.
//! The three spec-call regressions fail with the fix backed out. The provider
//! call and bare-parameter provisions reject pure callers either way by design.
//! Declared callers execute the capability and assert its result and effects.
use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::{EvalError, Value};

fn declarations(provision: &str) -> String {
    format!(
        r#"
namespace s7yf5
  import anthill.prelude.{{Int64, Unit, Cell, Modify, Error, String}}
  sort Sp
    import anthill.prelude.{{Int64}}
    effects E = ?
    operation run(s: Self, x: Int64) -> Int64 effects E
    operation twice(s: Self, x: Int64) -> Int64 effects E = run(s, x) + run(s, x)
  end
  sort Box
    import anthill.prelude.{{Int64}}
    import s7yf5.{{Sp}}
    effects BE = ?
    entity box(f: (x: Int64) -> Int64 @ {{BE}})
    provides Sp[E = {provision}]
    operation run(b: Self, x: Int64) -> Int64 effects {{BE}} = match b case box(f) -> f(x)
  end
  import s7yf5.Box.{{box}}
"#
    )
}

fn cell_program(provision: &str, declared: &str, body: &str) -> String {
    format!(
        r#"{}
  operation bump(k: Cell[V = Int64], x: Int64) -> Int64 effects {{Modify[k]}} =
    let u = Cell.set(k, Cell.get(k) + x)
    x
  operation use(k: Cell[V = Int64], v: Box[BE = {{Modify[k]}}]) -> Int64 effects {{{declared}}} = {body}
  operation build(k: Cell[V = Int64]) -> Int64 effects {{Modify[k]}} =
    let v: Box[BE = {{Modify[k]}}] = box(lambda (x: Int64) -> bump(k, x))
    use(k, v)
  operation main() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    let n = build(k)
    n * 100 + Cell.get(k)
end
"#,
        declarations(provision)
    )
}

fn error_program(provision: &str, declared: &str, body: &str) -> String {
    format!(
        r#"{}
  operation fail(x: Int64) -> Int64 effects {{Error[String]}} = Error.raise("boom")
  operation use(v: Box[BE = {{Error[String]}}]) -> Int64 effects {{{declared}}} = {body}
  operation main() -> Int64 effects {{Error[String]}} = use(box(fail))
end
"#,
        declarations(provision)
    )
}

fn check_pure_refusal(provision: &str, body: &str) {
    assert_refused_naming(
        &load_errors_of(&cell_program(provision, "", body)),
        &[
            "use.effects (op-effects)",
            "got undeclared effect: Modify[T = k]",
        ],
        &format!("{body} under {provision}, cell row"),
    );
    assert_refused_naming(
        &load_errors_of(&error_program(provision, "", body)),
        &[
            "use.effects (op-effects)",
            "got undeclared effect: Error[T = String]",
        ],
        &format!("{body} under {provision}, error row"),
    );
}

#[test]
fn s7yf5_dispatch_retains_row_effects() {
    check_pure_refusal("{BE}", "Sp.run(v, 5)");
}

#[test]
fn s7yf5_default_retains_row_effects() {
    check_pure_refusal("{BE}", "Sp.twice(v, 5)");
}

#[test]
fn s7yf5_dot_default_retains_row_effects() {
    check_pure_refusal("{BE}", "v.twice(5)");
}

#[test]
fn s7yf5_controls_reject_pure_callers() {
    for body in ["Sp.run(v, 5)", "Sp.twice(v, 5)", "v.twice(5)"] {
        check_pure_refusal("BE", body);
    }
    check_pure_refusal("{BE}", "Box.run(v, 5)");
}

#[test]
fn s7yf5_declared_callers_execute_effects() {
    for body in [
        "Sp.run(v, 5)",
        "Sp.twice(v, 5)",
        "v.twice(5)",
        "Box.run(v, 5)",
    ] {
        for provision in ["{BE}", "BE"] {
            let mut interp = interp_for(&cell_program(provision, "Modify[k]", body));
            crate::common::register_modify_handler(&mut interp);
            let expected = if body.contains("twice") { 1010 } else { 505 };
            let result = interp.call("s7yf5.main", &[]);
            assert!(
                matches!(result, Ok(Value::Int(n)) if n == expected),
                "{body} under {provision}: {result:?}"
            );

            let mut interp = interp_for(&error_program(provision, "Error[String]", body));
            let result = interp.call("s7yf5.main", &[]);
            assert!(
                matches!(result, Err(EvalError::Raised { payload: Value::Str(ref s) }) if s == "boom"),
                "{body} under {provision}: {result:?}"
            );
        }
    }
}

#[test]
fn s7yf5_merged_provision_retains_each_row() {
    let declarations = declarations("{BE, CE}")
        .replace("effects BE = ?", "effects BE = ?\n    effects CE = ?")
        .replace("@ {BE}", "@ {BE, CE}")
        .replace("effects {BE} = match", "effects {BE, CE} = match");
    for declared in ["", "Modify[a]", "Modify[b]"] {
        let src = format!(
            r#"{declarations}
  operation use(a: Cell[V = Int64], b: Cell[V = Int64],
                v: Box[BE = {{Modify[a]}}, CE = {{Modify[b]}}]) -> Int64 effects {{{declared}}} = Sp.twice(v, 5)
end
"#
        );
        let missing = if declared == "Modify[a]" { "b" } else { "a" };
        assert_refused_naming(
            &load_errors_of(&src),
            &[
                "use.effects (op-effects)",
                &format!("got undeclared effect: Modify[T = {missing}]"),
            ],
            "each receiver row must be retained",
        );
    }
    let src = format!(
        r#"{declarations}
  operation bump(a: Cell[V = Int64], b: Cell[V = Int64], x: Int64) -> Int64 effects {{Modify[a], Modify[b]}} =
    let u = Cell.set(a, Cell.get(a) + x)
    let u = Cell.set(b, Cell.get(b) + 2 * x)
    x
  operation use(a: Cell[V = Int64], b: Cell[V = Int64],
                v: Box[BE = {{Modify[a]}}, CE = {{Modify[b]}}]) -> Int64 effects {{Modify[a], Modify[b]}} = Sp.twice(v, 5)
  operation build(a: Cell[V = Int64], b: Cell[V = Int64]) -> Int64 effects {{Modify[a], Modify[b]}} =
    let v: Box[BE = {{Modify[a]}}, CE = {{Modify[b]}}] = box(lambda (x: Int64) -> bump(a, b, x))
    use(a, b, v)
  operation main() -> Int64 =
    let a: Cell[V = Int64] = Cell.new(0)
    let b: Cell[V = Int64] = Cell.new(0)
    let n = build(a, b)
    n * 10000 + Cell.get(a) * 100 + Cell.get(b)
end
"#
    );
    let mut interp = interp_for(&src);
    crate::common::register_modify_handler(&mut interp);
    let result = interp.call("s7yf5.main", &[]);
    assert!(matches!(result, Ok(Value::Int(101020))), "{result:?}");
}

// These cases expose the hidden cross-sort key collision on the original code:
// a written Car.T and Sp.T share a bare key, but the provision maps the latter
// to List[Car.T]. Matching declarations must run; incompatible ones must fail.
fn provision_program(carrier_param: &str, signature: &str, args: &str) -> String {
    format!(
        r#"
namespace s7yf5provision
  import anthill.prelude.{{Int64, List}}
  sort Sp
    sort T = ?
    operation run(s: Self) -> Int64
  end
  sort Car
    sort {carrier_param} = ?
    entity car(v: {carrier_param})
    provides Sp[T = List[T = {carrier_param}]]
    operation run(c: Self) -> Int64 = 3
  end
  operation accept{signature} -> Int64 = Sp.run(s)
  operation main() -> Int64 =
    let c: Car[{carrier_param} = Int64] = car(v: 1)
    accept({args})
end
"#
    )
}

fn assert_provision_runs(src: &str) {
    let mut interp = interp_for(src);
    let result = interp.call("s7yf5provision.main", &[]);
    assert!(matches!(result, Ok(Value::Int(3))), "{result:?}");
}

#[test]
fn s7yf5_cross_sort_matching_provision_runs() {
    assert_provision_runs(&provision_program("T", "(s: Sp[T = List[T = Int64]])", "c"));
}

#[test]
fn s7yf5_cross_sort_wrong_provision_is_refused() {
    assert_refused_naming(
        &load_errors_of(&provision_program("T", "(s: Sp[T = Int64])", "c")),
        &["accept.s (op-arg)", "expected Sp[T = Int64]"],
        "Car.T must not stand in for the provision's Sp.T",
    );
}

// Renaming the carrier's parameter avoids the original explicit-key collision:
// these controls run/refuse either way, with exactly the same provided type.
#[test]
fn s7yf5_cross_sort_renamed_parameter_controls() {
    assert_provision_runs(&provision_program("U", "(s: Sp[T = List[T = Int64]])", "c"));
    assert_refused_naming(
        &load_errors_of(&provision_program("U", "(s: Sp[T = Int64])", "c")),
        &["accept.s (op-arg)", "expected Sp[T = Int64]"],
        "a differently named carrier parameter provides the same type",
    );
}

// Inference must read the provision too. The argument x DRIVES the inferred A:
// List[Int64] is admitted and an Int64 is refused, regardless of the carrier's
// parameter name. The T-spelled cases fail with the fix backed out.
#[test]
fn s7yf5_cross_sort_inference_reads_the_provision() {
    for carrier_param in ["T", "U"] {
        assert_provision_runs(&provision_program(
            carrier_param,
            "[A](s: Sp[T = A], x: A)",
            "c, [1, 2, 3]",
        ));
        assert_refused_naming(
            &load_errors_of(&provision_program(
                carrier_param,
                "[A](s: Sp[T = A], x: A)",
                "c, 5",
            )),
            &["accept.x (op-arg)", "expected List[T = Int64]"],
            "A is the provided List[Int64], not the carrier's Int64",
        );
    }
}
