//! Standard builtins backing stdlib operation signatures.
//!
//! Each entry maps a fully-qualified anthill operation name (as declared
//! in `stdlib/anthill/prelude/`) to a Rust function that consumes evaluated
//! `Value` arguments and returns a result `Value`. Operations defined in the
//! prelude by rules (e.g. `anthill.prelude.List.length`) are not registered
//! here — those need the resolver bridge that arrives with M4.
//!
//! `anthill.prelude.Numeric.zero-val` is a nullary operation returning the
//! additive identity. Dispatch needs a type hint that we don't have inside
//! a zero-arg call, so it's left for the resolver / rule system.
//!
//! `anthill.prelude.Bool.ite(cond, t, e)` is deliberately **not** registered:
//! registering it would eagerly evaluate both branches, silently breaking
//! short-circuit semantics users expect. The `if_expr` form in expression
//! bodies already gives lazy branching; rule-level uses of `ite` are handled
//! by the prelude's rewrite rules during SLD resolution.

use super::{EvalError, Interpreter, Value};

/// Register the standard-library builtins. Symbols that don't resolve in the
/// current KB (stdlib partially loaded, e.g. a minimal test harness) are
/// skipped — every other error is propagated.
pub fn register_standard_builtins(interp: &mut Interpreter) -> Result<(), EvalError> {
    register_if_present(interp, "anthill.prelude.Numeric.add", numeric_add)?;
    register_if_present(interp, "anthill.prelude.Numeric.sub", numeric_sub)?;
    register_if_present(interp, "anthill.prelude.Numeric.mul", numeric_mul)?;

    register_if_present(interp, "anthill.prelude.Int.neg", int_neg)?;
    register_if_present(interp, "anthill.prelude.Int.abs", int_abs)?;
    register_if_present(interp, "anthill.prelude.Int.mod", int_mod)?;
    register_if_present(interp, "anthill.prelude.Int.rem", int_rem)?;
    register_if_present(interp, "anthill.prelude.Int.div", int_div)?;
    register_if_present(interp, "anthill.prelude.Int.divExact", int_div)?;
    register_if_present(interp, "anthill.prelude.Int.sign", int_sign)?;

    register_if_present(interp, "anthill.prelude.Float.div", float_div)?;

    register_if_present(interp, "anthill.prelude.Eq.eq", builtin_eq)?;
    register_if_present(interp, "anthill.prelude.Eq.neq", builtin_neq)?;

    register_if_present(interp, "anthill.prelude.Ordered.compare", ordered_compare)?;
    register_if_present(interp, "anthill.prelude.Ordered.gt", ordered_gt)?;
    register_if_present(interp, "anthill.prelude.Ordered.gte", ordered_gte)?;
    register_if_present(interp, "anthill.prelude.Ordered.lt", ordered_lt)?;
    register_if_present(interp, "anthill.prelude.Ordered.lte", ordered_lte)?;
    register_if_present(interp, "anthill.prelude.Ordered.max", ordered_max)?;
    register_if_present(interp, "anthill.prelude.Ordered.min", ordered_min)?;

    register_if_present(interp, "anthill.prelude.Bool.not", bool_not)?;
    register_if_present(interp, "anthill.prelude.Bool.and", bool_and)?;
    register_if_present(interp, "anthill.prelude.Bool.or", bool_or)?;

    register_if_present(interp, "anthill.prelude.String.concat", string_concat)?;
    register_if_present(interp, "anthill.prelude.String.length", string_length)?;

    register_if_present(interp, "anthill.prelude.BigInt.to_bigint", bigint_to_bigint)?;
    register_if_present(interp, "anthill.prelude.BigInt.to_int", bigint_to_int)?;
    register_if_present(interp, "anthill.prelude.BigInt.to_float", bigint_to_float)?;
    register_if_present(interp, "anthill.prelude.Int.to_float", int_to_float)?;

    register_if_present(interp, "anthill.prelude.Float.isNaN", float_is_nan)?;
    register_if_present(interp, "anthill.prelude.Float.isInfinite", float_is_infinite)?;
    register_if_present(interp, "anthill.prelude.Float.isFinite", float_is_finite)?;

    register_if_present(interp, "anthill.prelude.LogicalStream.splitFirst", logical_stream_split_first)?;
    register_if_present(interp, "anthill.reflect.KB.execute", kb_execute)?;

    register_if_present(interp, "anthill.prelude.Console.print", console_print)?;
    register_if_present(interp, "anthill.prelude.Console.println", console_println)?;
    register_if_present(interp, "anthill.prelude.Console.eprint", console_eprint)?;
    register_if_present(interp, "anthill.prelude.Console.eprintln", console_eprintln)?;
    register_if_present(interp, "anthill.prelude.Console.read_line", console_read_line)?;

    register_if_present(interp, "Modify.get", modify_get)?;
    register_if_present(interp, "Modify.set", modify_set)?;

    Ok(())
}

/// Register a builtin if its qualified name resolves in the KB; silently
/// skip `UnknownOperation` so partial-stdlib test harnesses keep loading.
/// Exposed for downstream crates (e.g. `anthill-stl`) that register their
/// own builtin sets with the same policy.
pub fn register_if_present<F>(interp: &mut Interpreter, qname: &str, f: F) -> Result<(), EvalError>
where
    F: Fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError> + 'static,
{
    match interp.register_builtin(qname, f) {
        Ok(()) => Ok(()),
        Err(EvalError::UnknownOperation { .. }) => Ok(()),
        Err(other) => Err(other),
    }
}

// ── argument helpers ────────────────────────────────────────────

/// Unpack an arg slice into a fixed-size array, enforcing arity.
pub fn expect_args<const N: usize>(op: &'static str, args: &[Value]) -> Result<[Value; N], EvalError> {
    if args.len() != N {
        return Err(EvalError::ArityMismatch { op, expected: N, got: args.len() });
    }
    // `from_fn` + one clone per slot — no intermediate `Vec`s, no try_into.
    Ok(std::array::from_fn(|i| args[i].clone()))
}

fn type_mismatch(expected: &'static str, a: &Value, b: Option<&Value>) -> EvalError {
    let got = match b {
        Some(b) if a.type_name() != b.type_name() => {
            format!("{} and {}", a.type_name(), b.type_name())
        }
        _ => a.type_name().to_string(),
    };
    EvalError::TypeMismatch { expected, got }
}

// ── Numeric: add / sub / mul ────────────────────────────────────
//
// Int uses checked arithmetic — overflow raises `EvalError::Overflow`
// rather than silently wrapping. A spec-oriented language should fail
// loud when a formal property is violated; callers that want wraparound
// can opt in later via a dedicated `WrappingInt` sort.

fn numeric_add(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Numeric.add", args)?;
    match (&a, &b) {
        (Value::Int(x), Value::Int(y)) => x.checked_add(*y)
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Numeric.add" }),
        (Value::BigInt(x), Value::BigInt(y)) => Ok(Value::BigInt(x + y)),
        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x + y)),
        _ => Err(type_mismatch("matching Int, BigInt, or Float", &a, Some(&b))),
    }
}

fn numeric_sub(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Numeric.sub", args)?;
    match (&a, &b) {
        (Value::Int(x), Value::Int(y)) => x.checked_sub(*y)
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Numeric.sub" }),
        (Value::BigInt(x), Value::BigInt(y)) => Ok(Value::BigInt(x - y)),
        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x - y)),
        _ => Err(type_mismatch("matching Int, BigInt, or Float", &a, Some(&b))),
    }
}

fn numeric_mul(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Numeric.mul", args)?;
    match (&a, &b) {
        (Value::Int(x), Value::Int(y)) => x.checked_mul(*y)
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Numeric.mul" }),
        (Value::BigInt(x), Value::BigInt(y)) => Ok(Value::BigInt(x * y)),
        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x * y)),
        _ => Err(type_mismatch("matching Int, BigInt, or Float", &a, Some(&b))),
    }
}

// ── Int-specific ────────────────────────────────────────────────

fn int_neg(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Int.neg", args)?;
    match a {
        Value::Int(x) => x.checked_neg()
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Int.neg" }),
        other => Err(type_mismatch("Int", &other, None)),
    }
}

fn int_abs(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Int.abs", args)?;
    match a {
        Value::Int(x) => x.checked_abs()
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Int.abs" }),
        other => Err(type_mismatch("Int", &other, None)),
    }
}

fn int_mod(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int.mod", args)?;
    match (&a, &b) {
        (Value::Int(_), Value::Int(0)) => Err(EvalError::DivisionByZero { op: "Int.mod" }),
        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x.rem_euclid(*y))),
        _ => Err(type_mismatch("Int", &a, Some(&b))),
    }
}

fn int_rem(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int.rem", args)?;
    match (&a, &b) {
        (Value::Int(_), Value::Int(0)) => Err(EvalError::DivisionByZero { op: "Int.rem" }),
        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x % y)),
        _ => Err(type_mismatch("Int", &a, Some(&b))),
    }
}

/// Truncated integer division. Backs both `anthill.prelude.Int.div` (the
/// primary name that `/` desugars to) and the historical `Int.divExact`
/// alias (kept via stdlib rule `divExact(a, b) = div(a, b)` for
/// compatibility). Semantics are identical — the name change is cosmetic.
fn int_div(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int.div", args)?;
    match (&a, &b) {
        (Value::Int(_), Value::Int(0)) => Err(EvalError::DivisionByZero { op: "Int.div" }),
        (Value::Int(x), Value::Int(y)) => x.checked_div(*y)
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Int.div" }),
        _ => Err(type_mismatch("Int", &a, Some(&b))),
    }
}

/// IEEE floating-point division. NaN / Infinity propagate per the standard;
/// division by 0.0 yields +/-Infinity or NaN rather than an error (users
/// who want strict semantics check explicitly before dividing).
fn float_div(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Float.div", args)?;
    match (&a, &b) {
        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x / y)),
        _ => Err(type_mismatch("Float", &a, Some(&b))),
    }
}

fn int_sign(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Int.sign", args)?;
    match a {
        Value::Int(x) => Ok(Value::Int(x.signum())),
        other => Err(type_mismatch("Int", &other, None)),
    }
}

// ── Eq / Ordered ───────────────────────────────────────────────

fn builtin_eq(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Eq.eq", args)?;
    Ok(Value::Bool(a.structural_eq(&b)))
}

fn builtin_neq(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Eq.neq", args)?;
    Ok(Value::Bool(!a.structural_eq(&b)))
}

/// Total order on primitive scalars. Floats use `total_cmp` so NaN has a
/// well-defined position — `partial_cmp` would lose transitivity.
fn value_compare(a: &Value, b: &Value) -> Result<std::cmp::Ordering, EvalError> {
    Ok(match (a, b) {
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::BigInt(x), Value::BigInt(y)) => x.cmp(y),
        (Value::Float(x), Value::Float(y)) => x.total_cmp(y),
        (Value::Bool(x), Value::Bool(y)) => x.cmp(y),
        (Value::Str(x), Value::Str(y)) => x.cmp(y),
        _ => return Err(EvalError::TypeMismatch {
            expected: "Ordered scalars of matching type",
            got: format!("{} and {}", a.type_name(), b.type_name()),
        }),
    })
}

fn ordered_compare(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Ordered.compare", args)?;
    Ok(Value::Int(match value_compare(&a, &b)? {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }))
}

fn ordered_gt(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Ordered.gt", args)?;
    Ok(Value::Bool(matches!(value_compare(&a, &b)?, std::cmp::Ordering::Greater)))
}

fn ordered_gte(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Ordered.gte", args)?;
    Ok(Value::Bool(!matches!(value_compare(&a, &b)?, std::cmp::Ordering::Less)))
}

fn ordered_lt(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Ordered.lt", args)?;
    Ok(Value::Bool(matches!(value_compare(&a, &b)?, std::cmp::Ordering::Less)))
}

fn ordered_lte(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Ordered.lte", args)?;
    Ok(Value::Bool(!matches!(value_compare(&a, &b)?, std::cmp::Ordering::Greater)))
}

fn ordered_max(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Ordered.max", args)?;
    match value_compare(&a, &b)? {
        std::cmp::Ordering::Less => Ok(b),
        _ => Ok(a),
    }
}

fn ordered_min(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Ordered.min", args)?;
    match value_compare(&a, &b)? {
        std::cmp::Ordering::Greater => Ok(b),
        _ => Ok(a),
    }
}

// ── Bool ───────────────────────────────────────────────────────

fn bool_not(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Bool.not", args)?;
    match a {
        Value::Bool(x) => Ok(Value::Bool(!x)),
        other => Err(type_mismatch("Bool", &other, None)),
    }
}

fn bool_and(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Bool.and", args)?;
    match (&a, &b) {
        (Value::Bool(x), Value::Bool(y)) => Ok(Value::Bool(*x && *y)),
        _ => Err(type_mismatch("Bool", &a, Some(&b))),
    }
}

fn bool_or(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Bool.or", args)?;
    match (&a, &b) {
        (Value::Bool(x), Value::Bool(y)) => Ok(Value::Bool(*x || *y)),
        _ => Err(type_mismatch("Bool", &a, Some(&b))),
    }
}

// ── String ─────────────────────────────────────────────────────

fn string_concat(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("String.concat", args)?;
    match (&a, &b) {
        (Value::Str(x), Value::Str(y)) => {
            let mut out = String::with_capacity(x.len() + y.len());
            out.push_str(x);
            out.push_str(y);
            Ok(Value::Str(out))
        }
        _ => Err(type_mismatch("String", &a, Some(&b))),
    }
}

// ── BigInt conversions ─────────────────────────────────────────

fn bigint_to_bigint(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("BigInt.to_bigint", args)?;
    match a {
        Value::Int(n) => Ok(Value::BigInt(num_bigint::BigInt::from(n))),
        Value::BigInt(n) => Ok(Value::BigInt(n)),
        other => Err(type_mismatch("Int or BigInt", &other, None)),
    }
}

/// BigInt → Option[Int]. Produces `some(n)` if the BigInt fits in i64,
/// `none` otherwise. Relies on `anthill.prelude.List.some` / `.none`
/// being loaded in the KB's symbol table.
fn bigint_to_int(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use num_bigint::ToBigInt;
    let [a] = expect_args::<1>("BigInt.to_int", args)?;
    let n = match a {
        Value::BigInt(n) => n,
        Value::Int(n) => n.to_bigint().unwrap(),
        other => return Err(type_mismatch("BigInt", &other, None)),
    };
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.fields.value;
    use std::convert::TryInto;
    let tmp: Result<i64, _> = (&n).try_into();
    Ok(match tmp {
        Ok(i) => Value::Entity {
            functor: some_sym,
            pos: Vec::new(),
            named: vec![(value_key, Value::Int(i))],
        },
        Err(_) => Value::Entity {
            functor: none_sym,
            pos: Vec::new(),
            named: Vec::new(),
        },
    })
}

// ── Float IEEE predicates ──────────────────────────────────────

fn float_is_nan(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Float.isNaN", args)?;
    match a {
        Value::Float(x) => Ok(Value::Bool(x.is_nan())),
        other => Err(type_mismatch("Float", &other, None)),
    }
}

fn float_is_infinite(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Float.isInfinite", args)?;
    match a {
        Value::Float(x) => Ok(Value::Bool(x.is_infinite())),
        other => Err(type_mismatch("Float", &other, None)),
    }
}

fn float_is_finite(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Float.isFinite", args)?;
    match a {
        Value::Float(x) => Ok(Value::Bool(x.is_finite())),
        other => Err(type_mismatch("Float", &other, None)),
    }
}

/// Int → Float. Exact for |n| < 2^53; rounds to nearest representable
/// double for larger magnitudes (standard IEEE conversion).
fn int_to_float(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Int.to_float", args)?;
    match a {
        Value::Int(n) => Ok(Value::Float(n as f64)),
        other => Err(type_mismatch("Int", &other, None)),
    }
}

/// BigInt → Float. Lossy for values beyond f64 precision; saturates to
/// +/-Infinity for values exceeding Float's range. Total function.
/// Implementation goes via decimal string: num_bigint's Display produces a
/// canonical integer form, and Rust's f64 parser rounds to nearest and
/// returns Infinity on overflow.
fn bigint_to_float(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("BigInt.to_float", args)?;
    let s = match a {
        Value::BigInt(n) => n.to_string(),
        Value::Int(n) => n.to_string(),
        other => return Err(type_mismatch("BigInt or Int", &other, None)),
    };
    let f: f64 = s.parse().unwrap_or(f64::INFINITY);
    Ok(Value::Float(f))
}

fn string_length(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("String.length", args)?;
    match a {
        // Unicode scalar count to match `anthill.prelude.String.length`'s
        // declared character-level semantics (the prelude's rules refer to
        // `length("") = 0`, which is unambiguous either way, but Unicode is
        // the natural choice for user-facing length).
        Value::Str(s) => Ok(Value::Int(s.chars().count() as i64)),
        other => Err(type_mismatch("String", &other, None)),
    }
}

// ── LogicalStream / KB.execute ─────────────────────────────────

use crate::eval::stream::StreamSource;

/// `splitFirst(s: LogicalStream[T]) -> Option[Pair[T, LogicalStream[T]]]`.
/// Pumps the stream one step; yielded substitutions are placeholder
/// `Value::Unit`s for v1 (see `Interpreter::stream_split_first` doc).
fn logical_stream_split_first(
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("LogicalStream.splitFirst", args)?;
    let handle = match arg {
        Value::Stream(h) => h,
        other => return Err(type_mismatch("Stream", &other, None)),
    };
    let pumped = interp.stream_split_first(&handle)?;

    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    match pumped {
        None => Ok(Value::Entity {
            functor: none_sym,
            pos: Vec::new(),
            named: Vec::new(),
        }),
        Some((value, rest)) => {
            let pair_sym = require_symbol(interp, "anthill.prelude.Pair.pair", "pair")?;
            let fst_key = interp.kb.intern("fst");
            let snd_key = interp.kb.intern("snd");
            let value_key = interp.kb.intern("value");
            let pair_value = Value::Entity {
                functor: pair_sym,
                pos: Vec::new(),
                named: vec![(fst_key, value), (snd_key, Value::Stream(rest))],
            };
            Ok(Value::Entity {
                functor: some_sym,
                pos: Vec::new(),
                named: vec![(value_key, pair_value)],
            })
        }
    }
}

/// `KB.execute(kb: KB, q: LogicalQuery) -> Stream[Substitution]`. The KB
/// argument is a sentinel — `Value::Unit` or any placeholder — because the
/// evaluator has no first-class KB values and always uses the interpreter's
/// own KB. The query value is lowered via `KnowledgeBase::execute_logical_query`
/// (proposal 026.1 Q3) and wrapped in `StreamSource::Resolver`.
fn kb_execute(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb_arg, query] = expect_args::<2>("KB.execute", args)?;
    let search = interp.kb.execute_logical_query(&query)
        .map_err(|e| EvalError::Internal(format!("execute_logical_query: {}", e)))?;
    let handle = interp.alloc_stream(StreamSource::Resolver(Some(search)));
    Ok(Value::Stream(handle))
}

/// Resolve a builtin's target symbol. Tries the fully-qualified name first,
/// then falls back to the short name. Exposed so downstream crates that
/// register their own builtins (e.g. `anthill-stl`) error consistently.
pub fn require_symbol(interp: &Interpreter, qualified: &str, short: &str)
    -> Result<crate::intern::Symbol, EvalError>
{
    interp.kb.try_resolve_symbol(qualified)
        .or_else(|| interp.kb.try_resolve_symbol(short))
        .ok_or_else(|| EvalError::Internal(format!("{} not in scope", qualified)))
}

// ── Builtins that route an operation through a registered effect handler.
// Each is identical in shape: resolve the op symbol, invoke the handler
// for a specific effect sort with `(op_sym, args)`. The macro keeps the
// five instances aligned and the wiring grep-friendly.
macro_rules! effect_dispatcher {
    ($fname:ident, $op_qname:literal, $op_short:literal, $effect_qname:literal) => {
        fn $fname(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
            let op_sym = require_symbol(interp, $op_qname, $op_short)?;
            interp.invoke_effect_handler($effect_qname, op_sym, args)
        }
    };
}

effect_dispatcher!(console_print,     "anthill.prelude.Console.print",     "print",     "anthill.prelude.Console.ConsoleOutput");
effect_dispatcher!(console_println,   "anthill.prelude.Console.println",   "println",   "anthill.prelude.Console.ConsoleOutput");
effect_dispatcher!(console_eprint,    "anthill.prelude.Console.eprint",    "eprint",    "anthill.prelude.Console.ConsoleError");
effect_dispatcher!(console_eprintln,  "anthill.prelude.Console.eprintln",  "eprintln",  "anthill.prelude.Console.ConsoleError");
effect_dispatcher!(console_read_line, "anthill.prelude.Console.read_line", "read_line", "anthill.prelude.Console.ConsoleInput");
effect_dispatcher!(modify_get, "Modify.get", "get", "Modify");
effect_dispatcher!(modify_set, "Modify.set", "set", "Modify");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Symbol;

    fn dummy() -> Interpreter {
        Interpreter::new(crate::kb::KnowledgeBase::new())
    }

    #[test]
    fn numeric_add_int() {
        let r = numeric_add(&mut dummy(), &[Value::Int(2), Value::Int(3)]).unwrap();
        assert_eq!(r.as_int(), Some(5));
    }

    #[test]
    fn numeric_add_float() {
        let r = numeric_add(&mut dummy(), &[Value::Float(1.5), Value::Float(2.25)]).unwrap();
        assert!(matches!(r, Value::Float(v) if (v - 3.75).abs() < 1e-9));
    }

    #[test]
    fn numeric_add_overflow_is_error() {
        let err = numeric_add(&mut dummy(), &[Value::Int(i64::MAX), Value::Int(1)]).unwrap_err();
        assert!(matches!(err, EvalError::Overflow { .. }));
    }

    #[test]
    fn numeric_add_mixed_type_shows_both_in_message() {
        let err = numeric_add(&mut dummy(), &[Value::Int(1), Value::Float(2.0)]).unwrap_err();
        match err {
            EvalError::TypeMismatch { got, .. } => {
                assert!(got.contains("Int") && got.contains("Float"), "got = {got}");
            }
            other => panic!("expected TypeMismatch, got {other:?}"),
        }
    }

    #[test]
    fn int_mod_by_zero_is_division_error() {
        let err = int_mod(&mut dummy(), &[Value::Int(5), Value::Int(0)]).unwrap_err();
        assert!(matches!(err, EvalError::DivisionByZero { .. }));
    }

    #[test]
    fn compare_returns_neg1_0_1() {
        let lt = ordered_compare(&mut dummy(), &[Value::Int(1), Value::Int(2)]).unwrap();
        let eq = ordered_compare(&mut dummy(), &[Value::Int(2), Value::Int(2)]).unwrap();
        let gt = ordered_compare(&mut dummy(), &[Value::Int(3), Value::Int(2)]).unwrap();
        assert_eq!(lt.as_int(), Some(-1));
        assert_eq!(eq.as_int(), Some(0));
        assert_eq!(gt.as_int(), Some(1));
    }

    #[test]
    fn eq_on_equal_tuples_is_true() {
        let a = Value::Tuple { pos: vec![Value::Int(1)], named: Vec::new() };
        let b = Value::Tuple { pos: vec![Value::Int(1)], named: Vec::new() };
        let r = builtin_eq(&mut dummy(), &[a, b]).unwrap();
        assert_eq!(r.as_bool(), Some(true));
    }

    #[test]
    fn eq_on_different_tuples_is_false() {
        let a = Value::Tuple { pos: vec![Value::Int(1)], named: Vec::new() };
        let b = Value::Tuple { pos: vec![Value::Int(2)], named: Vec::new() };
        let r = builtin_eq(&mut dummy(), &[a, b]).unwrap();
        assert_eq!(r.as_bool(), Some(false));
    }

    #[test]
    fn eq_on_equal_entities_is_true() {
        let mk = || Value::Entity {
            functor: Symbol::from_raw(7),
            pos: vec![Value::Int(10), Value::Str("x".into())],
            named: vec![(Symbol::from_raw(8), Value::Bool(true))],
        };
        let r = builtin_eq(&mut dummy(), &[mk(), mk()]).unwrap();
        assert_eq!(r.as_bool(), Some(true));
    }

    #[test]
    fn eq_on_entities_differing_functor_is_false() {
        let a = Value::Entity {
            functor: Symbol::from_raw(7),
            pos: vec![Value::Int(1)],
            named: vec![],
        };
        let b = Value::Entity {
            functor: Symbol::from_raw(8),
            pos: vec![Value::Int(1)],
            named: vec![],
        };
        let r = builtin_eq(&mut dummy(), &[a, b]).unwrap();
        assert_eq!(r.as_bool(), Some(false));
    }

    #[test]
    fn string_concat_basic() {
        let r = string_concat(&mut dummy(),
            &[Value::Str("hi ".into()), Value::Str("there".into())]).unwrap();
        assert_eq!(r.as_str(), Some("hi there"));
    }

    #[test]
    fn arity_mismatch_carries_counts() {
        let err = numeric_add(&mut dummy(), &[Value::Int(1)]).unwrap_err();
        assert!(matches!(err, EvalError::ArityMismatch { expected: 2, got: 1, .. }));
    }
}
