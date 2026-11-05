//! Found beside WI-20261014-N2YEK — an arrow NESTED in a slot binds the row parameter it names,
//! as the arrow written at the slot does.
//!
//! `entity box(g: Option[T = (z: Cell[V = Int64]) -> Int64 @ {EB}])` given a bare lambda, and
//! `entity box(g: List[T = (z: …) -> Int64 @ {EB}])` given a list literal, bound nothing to
//! `EB`: the bare lambda met the whole `Option` and the unification failed (the `some` coercion
//! wraps it only at the check), and a hinted literal took the hint as its element type, so its
//! elements' rows reached no variable. The expectation then closed `EB`: `let b: Box[EB = {}] =
//! box(g: lambda (z) -> put(q, 5))` loaded, and applying the payload wrote `q` from an operation
//! declaring nothing — 55, through the `Option` field and through the list (MEASURED). At a
//! call the same shapes were refused "unconstrained", where the spelling the coercion stands
//! for (`some(lambda …)`) ran, and in a rule body a function performing `Clock` handed in a
//! list or bare into an `Option` loaded.
//!
//! Now a value the `some` coercion wraps meets the option's payload, as `some(…)` does
//! (`some_coerced_slot`), and a literal's callable hint holding a variable declares nothing —
//! the literal's element type is its elements' join, each checked against the hint
//! (`hint_declares_the_element`, kernel-language §5.4), in the `cons(…, nil())` spine too.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ──────────────────────────────────
//!
//! Each part made a no-op under an env switch, one build, this file's rows run under each; a row
//! stops at its first failing case, and what the later cases do backed out (in parentheses) was
//! measured on the CLI, on the tree before the change:
//!
//! 1. THE PAYLOAD (`some_coerced_slot` answering `None`). 2 FAIL:
//!    [`a_bare_callable_meets_an_option_slot_at_its_payload`] (the construction refused for an
//!    undeclared `b.EB`, the annotated one running to 55, the calls refused "unconstrained", the
//!    function value's for an undeclared `?_`) and
//!    [`a_rule_body_hands_an_option_its_function`] (loads).
//! 2. THE LITERAL'S JOIN (the hint its element type, as before). 1 FAILS:
//!    [`a_list_literal_at_a_callable_slot_takes_its_elements_join`] (refused for `b.EB`, 55 at
//!    `Box[EB = {}]`, the call refused "unconstrained").
//! 3. THE SPINE'S JOIN (the spine seeded with the hint before its head). 1 FAILS:
//!    [`the_cons_spine_reads_its_head_as_the_literal_does`] (the call refused "unconstrained",
//!    the rule bodies load).
//!
//! PASS EITHER WAY, BY DESIGN: the controls in each row — `some(lambda …)` written, and a
//! literal at a ground element type, which declares; and the pure function a rule body hands
//! over, which loads.

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, run_int64};

/// `{above}` beside `put`, and `use(q)` declaring `{declares}` with `{body}`; `go()` runs `use`
/// over a cell holding 1 and answers `use(c) * 10 + Cell.get(c)`.
fn program(ns: &str, above: &str, declares: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Error, Cell, Modify, List, Option}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation inc(z: Cell[V = Int64]) -> Int64 = 1
{above}
  operation use(q: Cell[V = Int64]) -> Int64{declares} =
{body}
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    use(c) * 10 + Cell.get(c)
end
"#
    )
}

const OPTION_BOX: &str = "  sort Box\n    effects EB = ?\n    entity box(g: Option[T = (z: Cell[V = Int64]) -> Int64 @ {EB}])\n  end\n  \
     operation runOpt[E](p: Cell[V = Int64], o: Option[T = (k: Cell[V = Int64]) -> Int64 @ {E}]) -> Int64 effects {E} =\n    \
     match o\n      case some(w) -> w(p)\n      case none() -> 0\n";
const MATCH_OPTION: &str = "\n    match b.g\n      case some(w) -> w(q)\n      case none() -> 0";

const LIST_BOX: &str = "  sort Box\n    effects EB = ?\n    entity box(g: List[T = (z: Cell[V = Int64]) -> Int64 @ {EB}])\n  end\n  \
     operation eachR[E](p: Cell[V = Int64], fs: List[T = (k: Cell[V = Int64]) -> Int64 @ {E}]) -> Int64 effects {E} =\n    \
     match fs\n      case cons(w, _) -> w(p)\n      case nil() -> 0\n";
const MATCH_LIST: &str = "\n    match b.g\n      case cons(w, _) -> w(q)\n      case nil() -> 0";

/// Each `(name, above, declares, body, value)` runs `go` to `value`.
fn runs(cases: &[(&str, &str, &str, String, i64)]) {
    for (name, above, declares, body, value) in cases {
        let ns = format!("win2yeknest.{name}");
        let src = program(&ns, above, declares, body);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(*value), "{name}");
    }
}

/// A BARE CALLABLE AT AN `Option` SLOT meets the payload, as `some(…)` does: a construction
/// takes `EB = {Modify[q]}` (55), is refused at `Box[EB = {}]` as the arrow written at the field
/// is, and refuses a callback writing its own parameter at the field; a call takes `E` (55) and
/// refuses that callback at the argument; a function value's slot `@ {?}` takes the write (55). The `some(lambda …)` spelling is the control. FAILS
/// under part 1.
#[test]
fn a_bare_callable_meets_an_option_slot_at_its_payload() {
    let writes_q = "lambda (z: Cell[V = Int64]) -> put(q, 5)";
    runs(&[
        (
            "option_box",
            OPTION_BOX,
            " effects Modify[q]",
            format!("    let b = box(g: {writes_q}){MATCH_OPTION}"),
            55,
        ),
        (
            "option_call",
            OPTION_BOX,
            " effects Modify[q]",
            format!("    runOpt(q, {writes_q})"),
            55,
        ),
        (
            "option_function_value",
            "",
            " effects Modify[q]",
            format!(
                "    let app = lambda (o: Option[T = (k: Cell[V = Int64]) -> Int64 @ {{?}}]) -> match o\n      \
                 case some(w) -> w(q)\n      case none() -> 0\n    app({writes_q})"
            ),
            55,
        ),
        (
            "option_call_some",
            OPTION_BOX,
            " effects Modify[q]",
            format!("    runOpt(q, some({writes_q}))"),
            55,
        ),
    ]);
    let src = program(
        "win2yeknest.option_pure",
        OPTION_BOX,
        "",
        &format!("    let b: Box[EB = {{}}] = box(g: {writes_q}){MATCH_OPTION}"),
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["b.annotation (let-binding)", "Box[EB = Modify[T = q]]"],
        "a bare lambda writing `q` at `Box[EB = {}]`",
    );
    let src = program(
        "win2yeknest.option_own",
        OPTION_BOX,
        "",
        &format!("    let b: Box[EB = {{}}] = box(g: lambda (z: Cell[V = Int64]) -> put(z, 5)){MATCH_OPTION}"),
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["box.g (entity-field)", "may not take `Modify[T = z]`"],
        "a bare lambda writing its own parameter at the field",
    );
    let src = program(
        "win2yeknest.option_call_own",
        OPTION_BOX,
        "",
        "    runOpt(q, lambda (z: Cell[V = Int64]) -> put(z, 5))",
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["runOpt.o (op-arg)", "may not take `Modify[T = z]`"],
        "a bare lambda writing its own parameter at the call",
    );
}

/// The rule body of WI-20261013-R1W5A: a function performing `Clock` handed bare into an `Option`
/// slot is refused as the call that performs it, as `some(…)` is. FAILS under part 1.
#[test]
fn a_rule_body_hands_an_option_its_function() {
    let src = r#"
namespace win2yeknest.rule_option
  import anthill.prelude.{String, Option}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Time.{now, Clock}
  operation runOpt[Rho](o: Option[T = () -> String @ {Rho}]) -> String effects {Rho} =
    match o
      case some(f) -> f()
      case none() -> "none"
  rule viaBare(?r) :- runOpt(lambda () -> now(), ?r)
  rule viaSome(?r) :- runOpt(some(lambda () -> now()), ?r)
end
"#;
    let errs = load_errors_of(src);
    for rule in ["viaBare", "viaSome"] {
        assert_refused_naming(
            &errs,
            &[&format!("{rule}.body (rule)"), "which performs `Clock`"],
            rule,
        );
    }
}

/// A LIST LITERAL AT A CALLABLE SLOT HOLDING A VARIABLE is typed by its elements' join, each
/// checked against the slot: a construction takes `EB` from two lambdas (55) and from an
/// operation name lifted beside one (11), is refused at `Box[EB = {}]`, and a call takes `E`
/// (55). A slot whose element type is ground declares, as before. FAILS under part 2.
#[test]
fn a_list_literal_at_a_callable_slot_takes_its_elements_join() {
    let two = "[lambda (z: Cell[V = Int64]) -> put(q, 5), lambda (z: Cell[V = Int64]) -> 2]";
    runs(&[
        (
            "list_box",
            LIST_BOX,
            " effects Modify[q]",
            format!("    let b = box(g: {two}){MATCH_LIST}"),
            55,
        ),
        (
            "list_box_operation",
            LIST_BOX,
            " effects Modify[q]",
            format!(
                "    let b = box(g: [inc, lambda (z: Cell[V = Int64]) -> put(q, 5)]){MATCH_LIST}"
            ),
            11,
        ),
        (
            "list_call",
            LIST_BOX,
            " effects Modify[q]",
            format!("    eachR(q, {two})"),
            55,
        ),
        (
            "list_call_ground",
            LIST_BOX,
            " effects Modify[q]",
            format!("    eachR[E = {{Modify[q]}}](q, {two})"),
            55,
        ),
    ]);
    let src = program(
        "win2yeknest.list_pure",
        LIST_BOX,
        "",
        &format!("    let b: Box[EB = {{}}] = box(g: {two}){MATCH_LIST}"),
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["b.annotation (let-binding)", "Box[EB = Modify[T = q]]"],
        "a list writing `q` at `Box[EB = {}]`",
    );
}

/// THE `cons(…, nil())` SPINE, the literal written as constructors, joins as the literal does:
/// a call takes `E` (55), and a rule body handing a function performing `Clock` in a list — the
/// literal, lowered to the spine there, and the spine written — is refused; a pure one loads.
/// FAILS under part 3.
#[test]
fn the_cons_spine_reads_its_head_as_the_literal_does() {
    runs(&[(
        "spine_call",
        LIST_BOX,
        " effects Modify[q]",
        "    eachR(q, cons(lambda (z: Cell[V = Int64]) -> put(q, 5), nil()))".to_string(),
        55,
    )]);
    let program = |rules: &str| {
        format!(
            r#"
namespace win2yeknest.rule_list
  import anthill.prelude.{{String, List}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Time.{{now, Clock}}
  operation eachL[Rho](fs: List[T = () -> String @ {{Rho}}]) -> String effects {{Rho}} =
    match fs
      case cons(f, _) -> f()
      case nil() -> "none"
{rules}
end
"#
        )
    };
    let errs = load_errors_of(&program(
        "  rule viaList(?r) :- eachL([lambda () -> now()], ?r)\n  \
         rule viaCons(?r) :- eachL(cons(lambda () -> now(), nil()), ?r)",
    ));
    for rule in ["viaList", "viaCons"] {
        assert_refused_naming(
            &errs,
            &[&format!("{rule}.body (rule)"), "which performs `Clock`"],
            rule,
        );
    }
    load_kb_with(&program(
        "  rule viaPure(?r) :- eachL([lambda () -> \"x\"], ?r)",
    ));
}
