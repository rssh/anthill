//! WI-20261023-CX743 (proposal 069 stage 3) — an operation's VALUE parameter declares a
//! default (`operation clamp(x: Int64, low: Int64 = 0, high: Int64 = 100)`, §1.1), and a
//! call that leaves the parameter out takes it (§3): positional arguments fill the next
//! unfilled parameter, named ones fill by name, and the parameters left take their
//! defaults, typed where the call is once its inference is done, so the callee is reached
//! at its declared arity. In a rule-body goal the result column may be named `result:`.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ──────────────────────────────────
//!
//! On the parent tree no program here parses (the grammar has no `= default`). On this
//! tree, each part out alone (MEASURED with a temporary switch per part, over this file):
//!
//! * The loader's record (`Loader::record_operation_param_defaults`): every row — no
//!   default is filed, so every call that leaves a parameter out is refused.
//! * The completion at a call (`complete_defaulted_arguments`): every call row and every
//!   rule row — the call reaches its callee short (an arity fault at run time). The
//!   refusals and the reflect row pass by design.
//! * A call's binding counting a defaulted parameter as filled (`bind_call_arguments`):
//!   every row but the declaration refusals.
//! * The default's typing at its declaration (`check_operation_bodies`): the type, the
//!   type-parameter and the effect rows of the declaration refusals.
//! * Binding a compound argument a default names to a local first
//!   (`bind_arguments_a_default_names`): `rangeOnce`, which then bumps the cell twice.
//! * A mixed call keeping its labels until the completion (`reorder_named_args_in_apply`):
//!   `clampNamedHigh` and `rangeStep`, whose positional rewrite read `10` as `low`.
//! * Eval reading a declaration's name as no local (`names_a_declaration`): the three
//!   shadowed rows.
//! * The member reading the spec's defaults (`call_defaults`): `viaDot` and `viaMember`,
//!   refused at load.
//! * The member's own default refused (`check_override_refinement`): its refusal row.
//! * The `result:` column set aside (`split_result_column`): every rule row — the
//!   `RULES` program is refused as naming no parameter `result`.
//! * A `result:` goal read as a call (`call_dispatch_shape`): `viaResultNamed` and
//!   `viaResultFull`, which then load and answer nothing.
//! * A short goal read as the call (`operation_goal_reading`): the `Bool` short goal,
//!   which answers nothing, and the short-goal refusal, which is not raised.
//! * The short-goal refusal (`short_goal_without_result`): its row.
//! * The reflect row (`Loader::file_operation_param_default`): `a_default_is_reflected`.
//! * The rule-body bracket refusal (`bracketed_call`): its row, which then loads and
//!   drops the bracket.
//! * A call of a function-typed parameter in a default (`splice_default`'s functor arm):
//!   every `OPS` row — `callFLambda`'s call is refused as a call of no operation.
//! * A copied argument searched for the callee's parameters again (`splice_default`'s
//!   own-text flag): the run does not finish — `againFrom4`'s splice replaces `n` by `n`
//!   for ever.
//! * The guard on a default that takes itself (`complete_defaulted_arguments`' `TAKING`):
//!   the run aborts — `a_default_is_refused_at_its_declaration` overflows its stack.
//! * The completed call as what the call's readers past the completion read
//!   (`check_apply_iter`'s rebinding): every `OPS` row — `div2(4)`'s precondition
//!   `neq(b, 0)` is not proved — and the `divz` row, which no longer reads `neq(0, 0)`.
//! * A default's effects judged at the operation's boundary rather than as escaping with
//!   the parameter (`check_operation_bodies`): every `OPS` row — `readFresh`'s default is
//!   refused as an undeclared `Modify[result]`.
//! * The refusal of a default for a parameter the signature reads
//!   (`check_operation_bodies`): its two rows. Before it, a call taking `c`'s default
//!   under `effects Modify[c]` incurred the callee's own `Modify[T = c]`, and one taking
//!   `b`'s under `-> b.V` was refused as a projection off no argument of the call.

use crate::common::{definite_unary, interp_for, load_errors_of, load_kb_with};

/// Operation-body calls.
const OPS: &str = r#"
namespace test.cx743.ops
  import anthill.prelude.{Int64, String, Bool, Option, Type, Cell, Modify}
  import anthill.prelude.Option.{none, some}
  import anthill.reflect.{TypeValue}

  operation clamp(x: Int64, low: Int64 = 0, high: Int64 = 100) -> Int64 =
    if x < low then low else if x > high then high else x
  operation clampHigh() -> Int64 = clamp(120)
  operation clampLow() -> Int64 = clamp(-5)
  operation clampNamedHigh() -> Int64 = clamp(12, high: 10)
  operation clampNamedLow() -> Int64 = clamp(x: -3, low: 5)
  operation clampAll() -> Int64 = clamp(12, 20, 30)
  operation nested() -> Int64 = clamp(clamp(200), 150, 300)

  -- A defaulted parameter need not form a suffix.
  operation connect(host: String = "localhost", port: Int64) -> Int64 =
    port * 100 + String.length(host)
  operation connectByName() -> Int64 = connect(port: 5432)

  -- A default naming an earlier parameter.
  operation range3(first: Int64, last: Int64 = first, step: Int64 = 1) -> Int64 =
    first * 100 + last * 10 + step
  operation rangeDefaults() -> Int64 = range3(7)
  operation rangeStep() -> Int64 = range3(7, step: 3)
  operation bump(c: Cell[V = Int64]) -> Int64 effects Modify[c] =
    let n = Cell.get(c) + 1
    let u = Cell.set(c, n)
    n
  operation rangeOnce() -> Int64 =
    let c = Cell.new(0)
    let r = range3(bump(c))
    r * 1000 + Cell.get(c)

  -- A default holding a lambda over an earlier parameter.
  operation apply1(x: Int64, f: (Int64) -> Int64 = lambda y -> y + x) -> Int64 = f(x)
  operation applyDefault() -> Int64 = apply1(5)

  -- A default calling an earlier function-typed parameter.
  operation callF(f: (Int64) -> Int64, y: Int64 = f(10)) -> Int64 = y
  operation callFLambda() -> Int64 = callF(lambda z -> z * 2)
  -- Beside a variadic capture, which collects the named arguments no parameter takes.
  operation cap[R](p: Int64 = 1, ...rest: R) -> Int64 = p
  operation capNamed() -> Int64 = cap(a: 2, b: 3)
  operation capWritten() -> Int64 = cap(5)

  -- Recursive, and in a constant's value.
  operation countdown(n: Int64, acc: Int64 = 0) -> Int64 =
    if n < 1 then acc else countdown(n - 1, acc + n)
  operation sumTo() -> Int64 = countdown(4)
  -- A call the callee makes of itself passes its own parameter, which is the caller's.
  operation again(n: Int64, last: Int64 = n, depth: Int64 = 0) -> Int64 =
    if depth > 0 then n * 10 + last else again(n, depth: 1)
  operation againFrom4() -> Int64 = again(4)
  const FROM_DEFAULTS: Int64 = clamp(500)
  operation readConst() -> Int64 = FROM_DEFAULTS

  -- A value precondition reads the default the call takes.
  import anthill.prelude.PartialEq.{neq}
  operation div2(a: Int64, b: Int64 = 1) -> Int64 requires neq(b, 0) = a
  operation useDiv() -> Int64 = div2(4)
  -- A default making a fresh value: the parameter's, which the operation does not return.
  operation readFresh(c: Cell[V = Int64] = Cell.new(3)) -> Int64 = Cell.get(c)
  operation useFresh() -> Int64 = readFresh()

  -- An effectful default: its effects are the operation's.
  operation risky() -> Int64 effects {Error} = 7
  operation withRisky(x: Int64 = risky()) -> Int64 effects {Error} = x + 1
  operation callsRisky() -> Int64 effects {Error} = withRisky()

  -- A default's names are the callee's, whatever the caller holds under them.
  const LIMIT: Int64 = 50
  operation lim(x: Int64, m: Int64 = LIMIT) -> Int64 = x + m
  operation shadowedConst() -> Int64 =
    let LIMIT = 3
    lim(1) + LIMIT
  operation base() -> Int64 = 7
  operation withBase(x: Int64 = base()) -> Int64 = x
  operation shadowedOp() -> Int64 =
    let base = lambda () -> 1
    withBase() + base()
  operation withNone(o: Option[T = Int64] = none) -> Int64 =
    match o
      case some(v) -> v
      case none() -> 0
  operation shadowedCtor() -> Int64 =
    let none = some(5)
    withNone()

  -- Stage 2's row with its value default: inference wins over the type default, the
  -- type default answers where nothing binds `T`, a written bracket overrides it.
  operation which[T = String](o: Option[T] = none()) -> Type requires TypeValue[T = T] =
    TypeValue.type_value[T = T]()
  operation whichDefault() -> Type = which()
  operation whichInferred() -> Type = which(some(42))
  operation whichBound() -> Type = which[T = Bool]()
  -- A default naming the operation's type parameter is read at the call's instance.
  operation typeOf[T](x: T, t: Type = TypeValue.type_value[T = T]()) -> Type
    requires TypeValue[T = T] = t
  operation typeOfInt() -> Type = typeOf(1)
  operation typeOfString() -> Type = typeOf("s")
end
"#;

/// A spec's defaults, through the spec and through a provider's member.
const SPEC: &str = r#"
namespace test.cx743.spec
  import anthill.prelude.{Int64}
  sort Scaler
    operation scale(s: Self, k: Int64 = 3) -> Int64
  end
  sort Box
    entity box(n: Int64)
    provides Scaler
    operation scale(s: Self, k: Int64) -> Int64 =
      match s
        case box(n) -> n * k
  end
  operation viaSpec() -> Int64 = Scaler.scale(box(n: 10))
  operation viaSpecWritten() -> Int64 = Scaler.scale(box(n: 10), 5)
  operation viaDot() -> Int64 = box(n: 10).scale()
  operation viaMember() -> Int64 = Box.scale(box(n: 10))
end
"#;

/// Rule-body goals and values.
const RULES: &str = r#"
namespace test.cx743.rules
  import anthill.prelude.{Int64, Bool}
  operation clamp(x: Int64, low: Int64 = 0, high: Int64 = 100) -> Int64 =
    if x < low then low else if x > high then high else x
  operation range3(first: Int64, last: Int64 = first, step: Int64 = 1) -> Int64 =
    first * 100 + last * 10 + step
  operation above(x: Int64, min: Int64 = 10) -> Bool = x > min
  fact num(3)
  fact num(12)
  fact num(40)

  rule viaResult(?r) :- clamp(120, result: ?r)
  rule viaResultNamed(?r) :- clamp(x: 12, high: 10, result: ?r)
  rule viaResultFull(?r) :- clamp(12, 20, 30, result: ?r)
  rule rangeResult(?r) :- range3(7, result: ?r)

  rule viaFunctional(?r) :- clamp(12, 20, 30, ?r)
  rule viaValue(?r) :- ?r <=> clamp(-4)
  rule rangeValue(?r) :- num(?x), ?r <=> range3(?x)

  rule bigs(?x) :- num(?x), above(?x)
  rule bigsFrom2(?x) :- num(?x), above(?x, 2)
end
"#;

fn value_of(program: &str, ns: &str, op: &str) -> anthill_core::eval::value::Value {
    let mut interp = interp_for(program);
    interp
        .call(&format!("{ns}.{op}"), &[])
        .unwrap_or_else(|e| panic!("{op}: {e}"))
}

/// Every row of `rows` read by `read`, the ones that do not answer as they should listed
/// together: a row that panics (its program refused, its call faulted) is one of them.
fn mismatches<W: PartialEq + std::fmt::Debug>(
    rows: &[(&str, W)],
    read: impl Fn(&str) -> W + std::panic::RefUnwindSafe,
) -> Vec<String> {
    rows.iter()
        .filter_map(|(row, want)| {
            let got = std::panic::catch_unwind(|| read(row)).map_err(|_| "panicked");
            (got.as_ref() != Ok(want)).then(|| format!("{row}: {got:?}"))
        })
        .collect()
}

fn int_rows(program: &str, ns: &str, rows: &[(&str, i64)]) -> Vec<String> {
    mismatches(rows, |op| match value_of(program, ns, op) {
        anthill_core::eval::value::Value::Int(n) => n,
        other => panic!("{op}: expected an Int64, got {other:?}"),
    })
}

fn answer_rows(rows: &[(&str, Vec<i64>)]) -> Vec<String> {
    mismatches(rows, |rule| {
        let mut kb = load_kb_with(RULES);
        let mut out: Vec<i64> = definite_unary(&mut kb, &format!("test.cx743.rules.{rule}"))
            .into_iter()
            .map(|v| match v {
                anthill_core::eval::value::Value::Int(n) => n,
                other => panic!("{rule}: expected an Int64, got {other:?}"),
            })
            .collect();
        out.sort();
        out
    })
}

/// A CALL TAKES THE DEFAULTS OF THE PARAMETERS IT LEAVES OUT: positional arguments fill
/// the next unfilled parameter, named ones fill by name, and a defaulted parameter need
/// not form a suffix (`connect(port: 5432)`). A default naming an earlier parameter is
/// the argument the call gives it (`range3(7)` is `range3(7, 7, 1)`); one holding a
/// lambda over an earlier parameter closes over that argument. The call reaches its
/// callee at full arity from a nested call, a recursive one and a constant's value; an
/// effectful default's effects are the operation's, which its caller declares.
#[test]
fn a_call_takes_the_defaults_of_the_parameters_it_leaves_out() {
    let bad = int_rows(
        OPS,
        "test.cx743.ops",
        &[
            ("clampHigh", 100),
            ("clampLow", 0),
            ("clampNamedHigh", 10),
            ("clampNamedLow", 5),
            ("clampAll", 20),
            ("nested", 150),
            ("connectByName", 543209),
            ("rangeDefaults", 771),
            ("rangeStep", 773),
            ("applyDefault", 10),
            ("callFLambda", 20),
            ("capNamed", 1),
            ("capWritten", 5),
            ("sumTo", 10),
            ("againFrom4", 44),
            ("readConst", 100),
            ("callsRisky", 8),
            ("useDiv", 4),
            ("useFresh", 3),
        ],
    );
    assert!(bad.is_empty(), "{bad:#?}");
}

/// A COMPOUND ARGUMENT A DEFAULT NAMES IS EVALUATED ONCE: `range3(bump(c))` under
/// `last = first` bumps the cell once and reads `first = last = 1`; evaluated twice it
/// would be `121002`.
#[test]
fn a_compound_argument_a_default_names_is_evaluated_once() {
    let bad = int_rows(OPS, "test.cx743.ops", &[("rangeOnce", 111001)]);
    assert!(bad.is_empty(), "{bad:#?}");
}

/// A DEFAULT'S NAMES ARE THE CALLEE'S: a constant, an operation and a constructor it
/// writes are what it names at its declaration, whatever a caller holds under the same
/// spelling — `let LIMIT = 3` beside `lim(1)` still takes `LIMIT`'s 50.
#[test]
fn a_default_reads_the_names_it_was_written_with() {
    let bad = int_rows(
        OPS,
        "test.cx743.ops",
        &[("shadowedConst", 54), ("shadowedOp", 8), ("shadowedCtor", 0)],
    );
    assert!(bad.is_empty(), "{bad:#?}");
}

/// THE VALUE DEFAULT IS TYPED AT THE INSTANCE THE CALL FIXED: `which()` leaves `T` to
/// its type default (`String`) and its `o` to `none()`, `which(some(42))` infers `Int64`,
/// `which[T = Bool]()` is what the call writes; a default naming the operation's type
/// parameter (`TypeValue.type_value[T = T]()`) reads it at the call's `T`.
#[test]
fn a_default_is_typed_at_the_calls_instance() {
    let bad = mismatches(
        &[
            ("whichDefault", "String".to_owned()),
            ("whichInferred", "Int64".to_owned()),
            ("whichBound", "Bool".to_owned()),
            ("typeOfInt", "Int64".to_owned()),
            ("typeOfString", "String".to_owned()),
        ],
        |op| {
            let mut interp = interp_for(OPS);
            let v = interp
                .call(&format!("test.cx743.ops.{op}"), &[])
                .unwrap_or_else(|e| panic!("{op}: {e}"));
            anthill_core::kb::typing::type_display_name_value(interp.kb(), &v)
        },
    );
    assert!(bad.is_empty(), "{bad:#?}");
}

/// THE SPEC OWNS ITS DEFAULTS: a call through the spec takes them, and so does a call of
/// the member a provider supplies for it, which declares none (user, 2026-10-24).
#[test]
fn a_spec_default_is_taken_through_the_spec_and_through_its_member() {
    let bad = int_rows(
        SPEC,
        "test.cx743.spec",
        &[
            ("viaSpec", 30),
            ("viaSpecWritten", 50),
            ("viaDot", 30),
            ("viaMember", 30),
        ],
    );
    assert!(bad.is_empty(), "{bad:#?}");
}

/// IN A RULE-BODY GOAL THE RESULT COLUMN IS NAMED `result:`, at any arity: the
/// parameters left out take their defaults, as a call's do.
#[test]
fn a_goal_names_its_result_column() {
    let bad = answer_rows(&[
        ("viaResult", vec![100]),
        ("viaResultNamed", vec![10]),
        ("viaResultFull", vec![20]),
        ("rangeResult", vec![771]),
    ]);
    assert!(bad.is_empty(), "{bad:#?}");
}

/// THE FUNCTIONAL VIEW KEEPS ITS MEANING, with every parameter written
/// (`clamp(12, 20, 30, ?r)`), and a call in a value slot of a rule takes its defaults.
#[test]
fn the_functional_view_and_a_value_call_are_unchanged() {
    let bad = answer_rows(&[
        ("viaFunctional", vec![20]),
        ("viaValue", vec![0]),
        ("rangeValue", vec![331, 1321, 4401]),
    ]);
    assert!(bad.is_empty(), "{bad:#?}");
}

/// A `Bool` OPERATION'S SHORT GOAL IS ITS CALL, with the defaults, and succeeds when it
/// answers `true`.
#[test]
fn a_bool_short_goal_succeeds_on_true() {
    let bad = answer_rows(&[("bigs", vec![12, 40]), ("bigsFrom2", vec![3, 12, 40])]);
    assert!(bad.is_empty(), "{bad:#?}");
}

/// A SHORTER GOAL ON ANY OTHER OPERATION NEEDS `result:`: `clamp(12, ?r)` reads `?r` as
/// `low`, and is refused naming `result:` rather than loaded as either reading.
#[test]
fn a_short_goal_without_result_is_refused() {
    let errs = load_errors_of(
        r#"
namespace test.cx743.short
  import anthill.prelude.{Int64}
  operation clamp(x: Int64, low: Int64 = 0, high: Int64 = 100) -> Int64 = x
  rule bad(?r) :- clamp(12, ?r)
end
"#,
    );
    crate::common::assert_refused_naming(
        &errs,
        &["fills `low`", "write it as `result: ?r`"],
        "the short goal names `result:`",
    );
}

/// Each refusal, in a program of its own, by the words that name it.
fn refusal_rows(rows: &[(&str, &[&str], &str)]) -> Vec<String> {
    let base = r#"
namespace test.cx743.refused
  import anthill.prelude.{Int64}
  operation clamp(x: Int64, low: Int64 = 0, high: Int64 = 100) -> Int64 = x
  operation connect(host: Int64 = 1, port: Int64) -> Int64 = port
  operation risky() -> Int64 effects {Error} = 7
  sort Scaler
    operation scale(s: Self, k: Int64 = 3) -> Int64
  end
"#;
    rows.iter()
        .filter_map(|(body, tokens, why)| {
            let errs = load_errors_of(&format!("{base}{body}\nend\n"));
            (!tokens.iter().all(|t| errs.iter().any(|e| e.contains(t))))
                .then(|| format!("{why}: {errs:?}"))
        })
        .collect()
}

/// AT A CALL: a required parameter declared after a defaulted one is still required; a
/// value precondition is proved of the default the call takes; a function value has none —
/// its arrow is the whole parameter list; and a rule body, which has no channel for a
/// call's bracket, does not take a default that writes one.
#[test]
fn a_call_that_leaves_out_a_parameter_with_no_default_is_refused() {
    let bad = refusal_rows(&[
        (
            "  operation r() -> Int64 = connect()",
            &["no argument fills parameter `port`"],
            "a required parameter after a defaulted one",
        ),
        (
            "  import anthill.prelude.{Type}\n  import anthill.reflect.{TypeValue}\n  operation typeOf[T](x: T, t: Type = TypeValue.type_value[T = T]()) -> Type requires TypeValue[T = T] = t\n  rule r(?t) :- ?t <=> typeOf(1)",
            &["the default of `t` writes `anthill.reflect.TypeValue.type_value[…](…)`, and a rule body has no channel for a call's bracket"],
            "a default writing a call's bracket, taken in a rule body",
        ),
        (
            "  import anthill.prelude.PartialEq.{neq}\n  operation divz(a: Int64, b: Int64 = 0) -> Int64 requires neq(b, 0) = a\n  operation r() -> Int64 = divz(4)",
            &["expected precondition `neq(0, 0)` provable at the call site"],
            "a value precondition the default the call takes refutes",
        ),
        (
            "  operation r() -> Int64 =\n    let f: (Int64, Int64, Int64) -> Int64 = clamp\n    f(12)",
            &["expected 3 arguments — the parameter list this function value declares"],
            "a function value has no defaults",
        ),
    ]);
    assert!(bad.is_empty(), "{bad:#?}");
}

/// AT THE DECLARATION: a default naming its own parameter, a later one or `result`; one
/// not of its parameter's type, at every instance of a type parameter; one whose effect
/// the operation's row does not admit; one for a parameter the signature reads (an effect
/// over it, a projection off it), which a call reads off its argument before it takes a
/// default; one that takes itself, a call it makes leaving its parameter out again; one on
/// a variadic capture; one a provider's member writes.
#[test]
fn a_default_is_refused_at_its_declaration() {
    let bad = refusal_rows(&[
        (
            "  operation r(a: Int64 = b, b: Int64) -> Int64 = a",
            &["names `b`, which is declared after it"],
            "a forward reference",
        ),
        (
            "  operation r(a: Int64 = a) -> Int64 = a",
            &["names `a` itself"],
            "a default naming its own parameter",
        ),
        (
            "  operation r(a: Int64 = result) -> Int64 = a",
            &["names `result`"],
            "a default naming `result`",
        ),
        (
            "  operation r(a: Int64 = \"s\") -> Int64 = a",
            &["r.a (op-arg): expected Int64, got String"],
            "a default of the wrong type",
        ),
        (
            "  operation r[T](a: T, b: T = 42) -> T = a",
            &["r.b (op-arg): expected ?T, got Int64"],
            "a default that does not fit every instance of the type parameter",
        ),
        (
            "  operation r(a: Int64 = risky()) -> Int64 = a",
            &["undeclared effect: Error, incurred by the default of `a`"],
            "a default's effect the operation's row does not admit",
        ),
        (
            "  import anthill.prelude.{Cell, Modify}\n  operation r(c: Cell[V = Int64] = Cell.new(3)) -> Int64 effects Modify[c] = Cell.get(c)",
            &["r.c (op-arg): expected a default for a parameter the signature does not read"],
            "a default for a parameter the operation's row modifies",
        ),
        (
            "  sort Box\n    sort V = ?\n    entity box(v: V)\n  end\n  operation r(b: Box[V = Int64] = box(v: 1)) -> b.V =\n    match b\n      case box(v) -> v",
            &["r.b (op-arg): expected a default for a parameter the signature does not read"],
            "a default for a parameter the return projects off",
        ),
        (
            "  operation r(x: Int64, y: Int64 = r(x)) -> Int64 = y",
            &["the default of `y` takes itself"],
            "a default calling its own operation with its parameter left out",
        ),
        (
            "  operation r(x: Int64 = s()) -> Int64 = x\n  operation s(y: Int64 = r()) -> Int64 = y",
            &["the default of `x` takes itself"],
            "two defaults taking each other",
        ),
        (
            "  operation r(...rest: Int64 = 1) -> Int64 = 0",
            &["takes none of its own"],
            "a variadic capture with a default",
        ),
        (
            "  sort Box\n    entity box(n: Int64)\n    provides Scaler\n    operation scale(s: Self, k: Int64 = 4) -> Int64 = k\n  end",
            &["the spec owns its operation's defaults"],
            "a provider's member redeclaring a default",
        ),
    ]);
    assert!(bad.is_empty(), "{bad:#?}");
}

/// A DEFAULT IS REFLECTED, as `anthill.reflect.OperationParamDefault`: the operation, the
/// parameter, and the expression.
#[test]
fn a_default_is_reflected() {
    use anthill_core::eval::value::Value;
    use anthill_core::persistence::print::TermPrinter;
    let mut kb = load_kb_with(OPS);
    let functor = kb
        .try_resolve_symbol("anthill.reflect.OperationParamDefault")
        .expect("the reflect entity is declared");
    let clamp = kb
        .try_resolve_symbol("test.cx743.ops.clamp")
        .expect("clamp is declared");
    let clamp = kb.make_name_term_from_sym(clamp);
    let field = |head: &Value, name: &str| -> Value {
        let Value::Entity { named, .. } = head else {
            panic!("a reflect row is an entity value: {head:?}")
        };
        named
            .iter()
            .find(|(k, _)| kb.local_name_of(*k) == name)
            .map(|(_, v)| v.clone())
            .unwrap_or_else(|| panic!("no `{name}` in {head:?}"))
    };
    let printer = TermPrinter::new(&kb);
    let mut rows: Vec<(String, String)> = kb
        .rules_by_functor(functor)
        .into_iter()
        .map(|rid| kb.rule_head_value(rid).clone())
        .filter(|head| matches!(field(head, "op"), Value::Term { id, .. } if id == clamp))
        .map(|head| {
            let param = match field(&head, "param") {
                Value::Term { id, .. } => printer.print_term(id),
                other => panic!("`param` is a name: {other:?}"),
            };
            let default = match field(&head, "default") {
                Value::Node(occ) => printer.print_occurrence(&occ),
                other => panic!("`default` is the occurrence: {other:?}"),
            };
            (param.rsplit('.').next().unwrap_or_default().to_owned(), default)
        })
        .collect();
    rows.sort();
    assert_eq!(
        rows,
        vec![
            ("high".to_owned(), "100".to_owned()),
            ("low".to_owned(), "0".to_owned()),
        ]
    );
}
