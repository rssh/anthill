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
    register_if_present(interp, "anthill.prelude.String.startsWith", string_starts_with)?;
    register_if_present(interp, "anthill.prelude.String.endsWith", string_ends_with)?;
    register_if_present(interp, "anthill.prelude.String.substring", string_substring)?;
    register_if_present(interp, "anthill.prelude.String.toUpper", string_to_upper)?;
    register_if_present(interp, "anthill.prelude.String.toLower", string_to_lower)?;

    register_if_present(interp, "anthill.prelude.BigInt.to_bigint", bigint_to_bigint)?;
    register_if_present(interp, "anthill.prelude.BigInt.to_int", bigint_to_int)?;
    register_if_present(interp, "anthill.prelude.BigInt.to_float", bigint_to_float)?;
    register_if_present(interp, "anthill.prelude.Int.to_float", int_to_float)?;

    register_if_present(interp, "anthill.prelude.Float.isNaN", float_is_nan)?;
    register_if_present(interp, "anthill.prelude.Float.isInfinite", float_is_infinite)?;
    register_if_present(interp, "anthill.prelude.Float.isFinite", float_is_finite)?;

    register_if_present(interp, "anthill.prelude.Map.empty", map_empty)?;
    register_if_present(interp, "anthill.prelude.Map.put", map_put)?;
    register_if_present(interp, "anthill.prelude.Map.get", map_get)?;
    register_if_present(interp, "anthill.prelude.Map.contains", map_contains)?;
    register_if_present(interp, "anthill.prelude.Map.remove", map_remove)?;
    register_if_present(interp, "anthill.prelude.Map.keys", map_keys)?;
    register_if_present(interp, "anthill.prelude.Map.values", map_values)?;
    register_if_present(interp, "anthill.prelude.Map.entries", map_entries)?;
    register_if_present(interp, "anthill.prelude.Map.size", map_size)?;

    register_if_present(interp, "anthill.prelude.LogicalStream.splitFirst", logical_stream_split_first)?;
    register_if_present(interp, "anthill.reflect.KB.kb", kb_ambient)?;
    register_if_present(interp, "anthill.reflect.KB.execute", kb_execute)?;
    register_if_present(interp, "anthill.reflect.KB.facts_of", kb_facts_of)?;
    register_if_present(interp, "anthill.reflect.Substitution.lookup", subst_lookup)?;
    register_if_present(interp, "anthill.reflect.term_functor_name", term_functor_name)?;
    register_if_present(interp, "anthill.reflect.extract", extract_type_builtin)?;
    register_if_present(interp, "anthill.reflect.term_field", term_field)?;
    register_if_present(interp, "anthill.reflect.term_as_string", term_as_string)?;
    register_if_present(interp, "anthill.reflect.term_as_entity", term_as_entity)?;
    register_if_present(interp, "anthill.reflect.as_term", as_term)?;
    register_if_present(interp, "anthill.reflect.fresh_var", reflect_fresh_var)?;
    register_if_present(interp, "anthill.reflect.make_fn", reflect_make_fn)?;
    register_if_present(interp, "anthill.reflect.find_fact", reflect_find_fact)?;
    register_if_present(interp, "anthill.reflect.replace_named_arg", reflect_replace_named_arg)?;
    register_if_present(interp, "anthill.prelude.Time.now", time_now)?;
    register_if_present(interp, "anthill.prelude.Int.to_string", int_to_string)?;

    // Persistence (proposal 007). The operations are declared inside
    // `sort Store { operation persist … }` so their qualified names are
    // `anthill.persistence.Store.<op>`. Stores must be registered via
    // `Interpreter::register_store` before these dispatch.
    register_if_present(interp, "anthill.persistence.Store.persist", persistence_persist)?;
    register_if_present(interp, "anthill.persistence.Store.retract", persistence_retract)?;
    register_if_present(interp, "anthill.persistence.Store.flush",   persistence_flush)?;
    register_if_present(interp, "anthill.persistence.QueryableStore.retrieve",
                        persistence_retrieve)?;

    register_if_present(interp, "anthill.prelude.Console.print", console_print)?;
    register_if_present(interp, "anthill.prelude.Console.println", console_println)?;
    register_if_present(interp, "anthill.prelude.Console.eprint", console_eprint)?;
    register_if_present(interp, "anthill.prelude.Console.eprintln", console_eprintln)?;
    register_if_present(interp, "anthill.prelude.Console.read_line", console_read_line)?;

    register_if_present(interp, "anthill.prelude.ModifyRuntime.get", modify_get)?;
    register_if_present(interp, "anthill.prelude.ModifyRuntime.set", modify_set)?;
    register_if_present(interp, "anthill.prelude.Error.raise", error_raise)?;
    register_if_present(interp, "anthill.prelude.Cell.new", cell_new)?;
    register_if_present(interp, "anthill.prelude.Cell.get", cell_get)?;
    register_if_present(interp, "anthill.prelude.Cell.set", cell_set)?;

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
            pos: Vec::new().into(),
            named: vec![(value_key, Value::Int(i))].into(),
        },
        Err(_) => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
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

fn string_starts_with(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("String.startsWith", args)?;
    match (&a, &b) {
        (Value::Str(s), Value::Str(p)) => Ok(Value::Bool(s.starts_with(p.as_str()))),
        _ => Err(type_mismatch("String", &a, Some(&b))),
    }
}

fn string_ends_with(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("String.endsWith", args)?;
    match (&a, &b) {
        (Value::Str(s), Value::Str(p)) => Ok(Value::Bool(s.ends_with(p.as_str()))),
        _ => Err(type_mismatch("String", &a, Some(&b))),
    }
}

fn string_to_upper(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("String.toUpper", args)?;
    match a {
        Value::Str(s) => Ok(Value::Str(s.to_uppercase())),
        other => Err(type_mismatch("String", &other, None)),
    }
}

fn string_to_lower(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("String.toLower", args)?;
    match a {
        Value::Str(s) => Ok(Value::Str(s.to_lowercase())),
        other => Err(type_mismatch("String", &other, None)),
    }
}

// substring(s, start, end) — character-indexed half-open range, matching
// String.length's Unicode-scalar semantics. Negative or out-of-range indices
// clamp to the string's bounds; reversed ranges produce the empty string.
fn string_substring(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, start, end] = expect_args::<3>("String.substring", args)?;
    let s = match &s { Value::Str(x) => x.clone(), _ => return Err(type_mismatch("String", &s, None)) };
    let start = start.as_int().ok_or_else(|| type_mismatch("Int", &start, None))?;
    let end = end.as_int().ok_or_else(|| type_mismatch("Int", &end, None))?;
    let n = s.chars().count() as i64;
    let lo = start.max(0).min(n) as usize;
    let hi = end.max(0).min(n) as usize;
    if hi <= lo {
        return Ok(Value::Str(String::new()));
    }
    let mut iter = s.chars();
    let prefix: String = iter.by_ref().take(lo).collect();
    drop(prefix);
    let out: String = iter.take(hi - lo).collect();
    Ok(Value::Str(out))
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
            pos: Vec::new().into(),
            named: Vec::new().into(),
        }),
        Some((value, rest)) => {
            let pair_sym = require_symbol(interp, "anthill.prelude.Pair.pair", "pair")?;
            let fst_key = interp.kb.intern("fst");
            let snd_key = interp.kb.intern("snd");
            let value_key = interp.kb.intern("value");
            let pair_value = Value::Entity {
                functor: pair_sym,
                pos: Vec::new().into(),
                named: vec![(fst_key, value), (snd_key, Value::Stream(rest))].into(),
            };
            Ok(Value::Entity {
                functor: some_sym,
                pos: Vec::new().into(),
                named: vec![(value_key, pair_value)].into(),
            })
        }
    }
}

/// `KB.kb() -> KB` — the ambient-knowledge-base accessor. Returns a
/// parameterless entity-shaped value tagged `kb`, so it prints/inspects as `kb`
/// when debugging (and canonicalizes, unlike a bare `Value::Unit`). It is still
/// a singleton sentinel: the evaluator has no first-class KB values and always
/// operates on the interpreter's own KB, so `KB.execute` / `KB.facts_of` treat
/// their `kb` argument as a placeholder, and two `kb()` calls compare equal —
/// one ambient KB. Before WI-313 `kb` was a nullary `entity` and `kb()`
/// constructed this same shape; it is now a zero-arg operation (kernel-language
/// §6.3: a value-producing accessor, not a data constructor), so the
/// construction becomes this builtin.
fn kb_ambient(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    expect_args::<0>("KB.kb", args)?;
    let functor = require_symbol(interp, "anthill.reflect.KB.kb", "kb")?;
    Ok(Value::Entity { functor, pos: Vec::new().into(), named: Vec::new().into() })
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

/// `anthill.reflect.term_functor_name(t: Term) -> Option[String]`.
/// Returns the functor's short name for `Fn` / `Ref` terms; none() otherwise.
/// Anthill code can't construct Symbols cleanly yet, so this surfaces the
/// functor as a String for direct comparison (`eq(name, "Claimed")`).
fn term_functor_name(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("term_functor_name", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    let name: Option<String> = match &arg {
        Value::Term(tid) => match interp.kb.get_term(*tid) {
            crate::kb::term::Term::Fn { functor, .. } => {
                Some(interp.kb.resolve_sym(*functor).to_string())
            }
            crate::kb::term::Term::Ref(sym) | crate::kb::term::Term::Ident(sym) => {
                Some(interp.kb.resolve_sym(*sym).to_string())
            }
            _ => None,
        },
        Value::Entity { functor, .. } => Some(interp.kb.resolve_sym(*functor).to_string()),
        _ => None,
    };

    Ok(match name {
        Some(s) => Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(value_key, Value::Str(s))].into(),
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
        },
    })
}

/// `anthill.reflect.extract(t: Term) -> TypeExtractor`.
///
/// Reify a type term's structure into the transparent, low-level `TypeExtractor`
/// reflection ADT. The classification is the engine-internal [`extract_type`]
/// (kb::typing) — a dual-form reader over both the deep `Type` representation
/// (`sort_ref` / `parameterized` / …) and the term backing (`Ref(S)` /
/// `Fn{S,named}`) it is converging onto (WI-361 stage 2) — and this builtin maps
/// its result into the stdlib `TypeExtractor` value. Total: an unrecognised /
/// malformed form classifies as `Error`.
fn extract_type_builtin(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::term::Term;
    use crate::kb::typing::{extract_type, TypeExtractor};
    let [arg] = expect_args::<1>("extract", args)?;
    let ty = arg.clone();

    let classified = extract_type(&interp.kb, &ty);

    let name_key = interp.kb.intern("name");
    let value_key = interp.kb.intern("value");
    let param_key = interp.kb.intern("param");
    let result_key = interp.kb.intern("result");
    let effects_key = interp.kb.intern("effects");
    let effects_expr_key = interp.kb.intern("effects_expr");
    let term_key = interp.kb.intern("term");
    let base_key = interp.kb.intern("base");
    let bindings_key = interp.kb.intern("bindings");
    let fields_key = interp.kb.intern("fields");
    let type_key = interp.kb.intern("type");
    let member_key = interp.kb.intern("member");

    // A `Symbol` as the `Ref(s)` term the deep field forms carry.
    let sym_ref = |interp: &mut Interpreter, s| Value::Term(interp.kb.alloc(Term::Ref(s)));

    match classified {
        TypeExtractor::SortRef(s) => {
            let name = sym_ref(interp, s);
            ti_entity(interp, "SortRef", vec![(name_key, name)])
        }
        TypeExtractor::TypeVar(s) => {
            let name = sym_ref(interp, s);
            ti_entity(interp, "TypeVar", vec![(name_key, name)])
        }
        TypeExtractor::Nothing => ti_entity(interp, "Nothing", vec![]),
        TypeExtractor::Denoted(v) => ti_entity(interp, "Denoted", vec![(value_key, v)]),
        // WI-376: reify an expression-carried projection — the receiver occurrence
        // (`value`) and the member name as a `Ref(sym)` (`member`).
        TypeExtractor::ExprCarried { value, member } => {
            let member_val = sym_ref(interp, member);
            ti_entity(interp, "ExprCarried", vec![(value_key, value), (member_key, member_val)])
        }
        TypeExtractor::Arrow { param, result, effects } => ti_entity(
            interp,
            "Arrow",
            vec![(param_key, param), (result_key, result), (effects_key, effects)],
        ),
        TypeExtractor::EffectsRows(e) => ti_entity(interp, "EffectsRows", vec![(effects_expr_key, e)]),
        TypeExtractor::Parameterized { base, bindings } => {
            let base_val = sym_ref(interp, base);
            let new_bindings =
                ti_build_records(interp, bindings, "TypeBinding", param_key, value_key)?;
            ti_entity(
                interp,
                "Parameterized",
                vec![(base_key, base_val), (bindings_key, new_bindings)],
            )
        }
        TypeExtractor::NamedTuple(fields) => {
            let new_fields =
                ti_build_records(interp, fields, "NamedTupleElement", name_key, type_key)?;
            ti_entity(interp, "NamedTuple", vec![(fields_key, new_fields)])
        }
        TypeExtractor::Error => ti_entity(interp, "Error", vec![(term_key, ty)]),
    }
}

/// Build a `TypeExtractor` variant entity value (`anthill.prelude.TypeExtractor.<short>`).
fn ti_entity(
    interp: &mut Interpreter,
    short: &str,
    fields: Vec<(crate::intern::Symbol, Value)>,
) -> Result<Value, EvalError> {
    let qname = format!("anthill.prelude.TypeExtractor.{}", short);
    let functor = require_symbol(interp, &qname, short)?;
    Ok(Value::Entity { functor, pos: Vec::new().into(), named: fields.into() })
}

/// Build a standalone `TypeExtractor` helper record (`anthill.prelude.<short>` —
/// `TypeBinding` / `NamedTupleElement`, which live outside the enum).
fn ti_record(
    interp: &mut Interpreter,
    short: &str,
    fields: Vec<(crate::intern::Symbol, Value)>,
) -> Result<Value, EvalError> {
    let qname = format!("anthill.prelude.{}", short);
    let functor = require_symbol(interp, &qname, short)?;
    Ok(Value::Entity { functor, pos: Vec::new().into(), named: fields.into() })
}

/// Build a value list of standalone `key1`/`key2` records (`TypeBinding` /
/// `NamedTupleElement`) from already-classified `(symbol, value)` pairs. The
/// symbol component (binding `param` / element `name`) is re-wrapped as the
/// `Ref(s)` term those fields carry; the value component (binding `value` /
/// element `type`) passes through. `extract_type` did the structural reading.
fn ti_build_records(
    interp: &mut Interpreter,
    items: Vec<(crate::intern::Symbol, Value)>,
    ctor: &str,
    key1: crate::intern::Symbol,
    key2: crate::intern::Symbol,
) -> Result<Value, EvalError> {
    use crate::kb::term::Term;
    let mut out: Vec<Value> = Vec::with_capacity(items.len());
    for (sym, val) in items {
        let sym_val = Value::Term(interp.kb.alloc(Term::Ref(sym)));
        out.push(ti_record(interp, ctor, vec![(key1, sym_val), (key2, val)])?);
    }
    build_value_list(interp, out)
}

/// Build a `List` value (`cons`/`nil`) from element values.
fn build_value_list(interp: &mut Interpreter, elems: Vec<Value>) -> Result<Value, EvalError> {
    let cons_sym = require_symbol(interp, "anthill.prelude.List.cons", "cons")?;
    let nil_sym = require_symbol(interp, "anthill.prelude.List.nil", "nil")?;
    let head_key = interp.kb.intern("head");
    let tail_key = interp.kb.intern("tail");
    let mut list = Value::Entity { functor: nil_sym, pos: Vec::new().into(), named: Vec::new().into() };
    for elem in elems.into_iter().rev() {
        list = Value::Entity {
            functor: cons_sym,
            pos: Vec::new().into(),
            named: vec![(head_key, elem), (tail_key, list)].into(),
        };
    }
    Ok(list)
}

/// `anthill.reflect.term_field(t: Term, name: String) -> Option[Term]`.
/// Look up a named arg on a Fn term by its short name. Mirrors the legacy
/// `extract_named_arg` shim (rustland/anthill-todo/src/main.rs:383) so the
/// anthill side has the same field-extraction primitive without having to
/// thread Symbol values through.
fn term_field(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [term_arg, name_arg] = expect_args::<2>("term_field", args)?;
    let tid = match &term_arg {
        Value::Term(t) => *t,
        other => return Err(type_mismatch("Term", other, None)),
    };
    let name = match &name_arg {
        Value::Str(s) => s.clone(),
        other => return Err(type_mismatch("String", other, None)),
    };
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    let found: Option<crate::kb::term::TermId> = match interp.kb.get_term(tid) {
        crate::kb::term::Term::Fn { named_args, .. } => {
            let named = named_args.clone();
            named.iter()
                .find(|(s, _)| interp.kb.resolve_sym(*s) == name)
                .map(|(_, t)| *t)
        }
        _ => None,
    };

    Ok(match found {
        Some(field_tid) => Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(value_key, Value::Term(field_tid))].into(),
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
        },
    })
}

/// `anthill.reflect.term_as_string(t: Term) -> Option[String]`.
/// Returns `some(s)` when the term is exactly `Const(StringLiteral(_))`;
/// otherwise none(). Used to extract id/description/agent fields after
/// drilling into a fact via `term_field`.
fn term_as_string(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("term_as_string", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    let s: Option<String> = match &arg {
        Value::Term(tid) => match interp.kb.get_term(*tid) {
            crate::kb::term::Term::Const(crate::kb::term::Literal::String(s)) => {
                Some(s.clone())
            }
            _ => None,
        },
        Value::Str(s) => Some(s.clone()),
        _ => None,
    };

    Ok(match s {
        Some(v) => Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(value_key, Value::Str(v))].into(),
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
        },
    })
}

/// `anthill.reflect.term_as_entity(t: Term) -> Option[T = ?E]`.
/// Decodes a `Term::Fn` whose functor is a registered constructor into a
/// typed `Value::Entity`, using `KnowledgeBase::entity_field_types` to
/// recover declared fields. Pairs with `term_as_string` / `term_as_sort`
/// as the entity-decoder side of the family.
///
/// Returns `none()` when `t` is not a `Fn`, when its functor isn't a
/// registered constructor, or when no field-types entry exists for the
/// functor. A `Value::Entity` input is the identity case — both
/// representations inhabit the abstract `reflect.Term` via `TermView`.
fn term_as_entity(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("term_as_entity", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    let materialized: Option<Value> = match arg {
        Value::Term(tid) => materialize_entity(interp, tid),
        Value::Entity { .. } => Some(arg),
        other => return Err(type_mismatch("Term", &other, None)),
    };

    Ok(match materialized {
        Some(value) => Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(value_key, value)].into(),
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
        },
    })
}

/// `anthill.reflect.as_term[E](e: E) -> Term`. The TOTAL value→Term crossing
/// (WI-406) — the explicit partner to `term_as_entity` (partial Term→entity).
/// `Term` is the representation-specific reflected-term sort, not a supertype,
/// so this is a CONVERSION made explicit, not a coercion the typer inserts.
/// At runtime every value carrier already inhabits the abstract `reflect.Term`
/// via `TermView` (a `Value::Entity` is accepted wherever a `Term` is — see
/// `term_as_entity`, the reverse, which takes both), so the value-level
/// operation is the identity; the work is the type-level relabel to `Term`.
///
/// No carrier is rejected — that is not a silent skip but the meaning of TOTAL:
/// `E` is universally quantified, so every value is a valid input and reflects.
/// (Contrast `sort_as_term`, whose arg must be a `Type`/`Term` handle and which
/// therefore loudly rejects a non-`Term` carrier; `as_term` has no ill input to
/// surface.) The `Value::Entity → Term::Fn` materialization a consumer may need
/// happens downstream in `alloc_from_value` at the consumption site (the
/// `pattern_query` lowering, `persist`), NOT here.
fn as_term(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [e] = expect_args::<1>("as_term", args)?;
    Ok(e)
}

fn materialize_entity(interp: &mut Interpreter, tid: crate::kb::term::TermId) -> Option<Value> {
    use crate::intern::Symbol;
    use crate::kb::term::{Term as CoreTerm, TermId};
    use smallvec::SmallVec;
    // Snapshot the (Copy) pieces we need so the kb borrow can be released
    // before we recurse back into &mut interp.
    let (functor, pos_args, named_args): (
        Symbol,
        SmallVec<[TermId; 4]>,
        SmallVec<[(Symbol, TermId); 2]>,
    ) = match interp.kb.get_term(tid) {
        CoreTerm::Fn { functor, pos_args, named_args } =>
            (*functor, pos_args.clone(), named_args.clone()),
        _ => return None,
    };
    // Resolve `functor` to the canonical Symbol that owns the
    // `entity_field_types` entry. Free-standing entities (declared at
    // namespace level rather than `sort … { entity X(...) }`) register
    // fields but no `entity_parent` — `WorkItem` in
    // `anthill-todo/domain.anthill` is the prototypical case — so the
    // probe keys off `entity_field_types`, not `constructor_parent_sort`.
    // The last-resort scan covers a functor that is still an unqualified
    // short name.
    let canonical = if interp.kb.entity_field_types(functor).is_some() {
        functor
    } else {
        let short_name = interp.kb.resolve_sym(functor).to_string();
        interp.kb.symbols.by_qualified_name.iter()
            .find(|(qname, &sym)| {
                qname.rsplit('.').next() == Some(short_name.as_str())
                    && interp.kb.entity_field_types(sym).is_some()
            })
            .map(|(_, &sym)| sym)?
    };
    // WI-342: field types are carrier-agnostic `Value`. Eval only inspects them
    // to default optional fields (see `is_option_type` below); a denoted-bearing
    // (Value::Node) field type is never an `Option`.
    let field_types: Vec<(Symbol, Value)> =
        interp.kb.entity_field_types(canonical)?.to_vec();
    // Default missing `Option[T = …]` fields to `none()` — on-disk facts
    // omit optional named args (a `WorkItem` fact skips
    // `context`/`generates`/`requires_capability`) but the field index
    // still expects them. Required for callers to pattern-match a
    // complete entity.
    let none_sym = interp.kb.try_resolve_symbol("anthill.prelude.Option.none")?;

    let mut named: Vec<(Symbol, Value)> = Vec::with_capacity(field_types.len());
    for (idx, (fname, ftype)) in field_types.iter().enumerate() {
        let field_tid = named_args
            .iter()
            .find(|(s, _)| *s == *fname)
            .map(|(_, t)| *t)
            .or_else(|| pos_args.get(idx).copied());
        let is_opt = ftype.as_term().is_some_and(|t| is_option_type(interp, t));
        match field_tid {
            // The loader's partial-named-arg expansion (kb/load.rs:2752)
            // fills absent slots with a fresh Var so the discrim tree
            // can index the fact uniformly. For materialization those
            // Var-valued Option slots are semantically absent — promote
            // them to none() so reconstruction + re-persistence doesn't
            // bake the synthetic var name into the persisted fact.
            Some(tid)
                if is_opt
                    && matches!(interp.kb.get_term(tid), CoreTerm::Var(_)) =>
            {
                named.push((*fname, Value::Entity {
                    functor: none_sym,
                    pos: Vec::new().into(),
                    named: Vec::new().into(),
                }));
            }
            Some(tid) => named.push((*fname, term_to_value(interp, tid))),
            None if is_opt => {
                named.push((*fname, Value::Entity {
                    functor: none_sym,
                    pos: Vec::new().into(),
                    named: Vec::new().into(),
                }));
            }
            None => return None,
        }
    }

    Some(Value::Entity { functor: canonical, pos: Vec::new().into(), named: named.into() })
}

/// True when `ftype` is `Option` or `Option[T = …]` (qualified or short).
/// Used by `materialize_entity` to decide whether a missing field should
/// default to `none()` rather than aborting the materialization.
fn is_option_type(interp: &Interpreter, ftype: crate::kb::term::TermId) -> bool {
    use crate::kb::term::Term as CoreTerm;
    // WI-361: a field type is term-backed — bare `Ref(Option)` or `Fn{Option, …}`
    // (the base sort IS the functor; no `sort_ref`/`parameterized` wrapper). Read
    // the head sort symbol directly.
    let sym = match interp.kb.get_term(ftype) {
        CoreTerm::Fn { functor, .. } => *functor,
        CoreTerm::Ref(s) => *s,
        _ => return false,
    };
    let name = interp.kb.resolve_sym(sym);
    name == "Option" || name == "anthill.prelude.Option"
}

fn term_to_value(interp: &mut Interpreter, tid: crate::kb::term::TermId) -> Value {
    use crate::intern::Symbol;
    use crate::kb::term::{Literal, Term as CoreTerm};
    // Avoid cloning the whole `Term` when we'll return `Value::Term(tid)`
    // unchanged anyway — the common case for vars and non-ctor refs.
    enum Decision {
        Literal(Literal),
        TryFn(Symbol),
        TryRef(Symbol),
        // WI-109: a logic variable lifts to the kind-typed `Value::Var`,
        // not `Value::Term(tid)` — lossless and structurally reconstructible.
        Var(crate::kb::term::Var),
        AsIs,
    }
    let decision = match interp.kb.get_term(tid) {
        CoreTerm::Const(lit) => Decision::Literal(lit.clone()),
        CoreTerm::Fn { functor, .. } => Decision::TryFn(*functor),
        CoreTerm::Ref(sym) => Decision::TryRef(*sym),
        CoreTerm::Var(v) => Decision::Var(*v),
        _ => Decision::AsIs,
    };
    match decision {
        Decision::Literal(Literal::Int(n)) => Value::Int(n),
        Decision::Literal(Literal::BigInt(b)) => Value::BigInt(b),
        Decision::Literal(Literal::Float(f)) => Value::Float(f.into_inner()),
        Decision::Literal(Literal::Bool(b)) => Value::Bool(b),
        Decision::Literal(Literal::String(s)) => Value::Str(s),
        Decision::Literal(Literal::Handle(_, _)) => Value::Term(tid),
        Decision::TryFn(functor) => {
            if interp.kb.constructor_parent_sort(functor).is_some() {
                materialize_entity(interp, tid).unwrap_or(Value::Term(tid))
            } else {
                Value::Term(tid)
            }
        }
        Decision::TryRef(sym) => {
            if interp.kb.constructor_parent_sort(sym).is_some() {
                Value::Entity { functor: sym, pos: Vec::new().into(), named: Vec::new().into() }
            } else {
                Value::Term(tid)
            }
        }
        Decision::Var(v) => Value::Var(v),
        Decision::AsIs => Value::Term(tid),
    }
}

/// `anthill.reflect.fresh_var[T](name: String) -> T`.
/// Allocate a fresh logical variable wrapped in a `Term::Var(Var::Global(_))`
/// so anthill code can build pattern queries with named holes. WI-406: the
/// surface type is the caller-bound `T` (a `T`-kinded logic var, WI-109), so a
/// hole drops into a typed slot with no value↔Term crossing; the runtime
/// carrier is the same `Term::Var` regardless of `T` (the builtin ignores the
/// type argument — an unbound logic var inhabits every sort until it binds). The display
/// name is used by `Substitution.lookup` callers to recover bindings by
/// name (`lookup(subst, "id")`); two fresh vars with the same name produce
/// distinct `VarId`s — the resolver's identity is the id, not the name.
///
/// Pairs with `pattern_query` + `KB.execute` so anthill code can express
/// goals like `claimable(?id, ?desc)` without needing first-class Symbol
/// construction. WI-182 / proposal 026: the missing piece for cmd_next.
fn reflect_fresh_var(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [name_arg] = expect_args::<1>("fresh_var", args)?;
    let name = match &name_arg {
        Value::Str(s) => s.clone(),
        other => return Err(type_mismatch("String", other, None)),
    };
    let sym = interp.kb.intern(&name);
    let vid = interp.kb.fresh_var(sym);
    let tid = interp.kb.alloc(crate::kb::term::Term::Var(
        crate::kb::term::Var::Global(vid),
    ));
    Ok(Value::Term(tid))
}

/// `anthill.reflect.make_fn(name: String, args: List[Term]) -> Term`.
/// Build a `Term::Fn { functor, pos_args, named_args = [] }` whose functor
/// is resolved by qualified or short name. Companion to `fresh_var`: anthill
/// code constructs pattern goals like `claimable(?id, ?desc)` by
/// `make_fn("anthill.stage0.workflow.claimable", cons(id_var, cons(desc_var, nil())))`.
///
/// The expression-level alternative — writing the constructor call inline
/// in source — only works for names registered as Operations or Entities.
/// Rule-head functors aren't (rule heads are not scanned as definitions),
/// which is why the `cmd_next` port has to construct its goal through this
/// builtin rather than calling `claimable(...)` directly.
fn reflect_make_fn(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::term::{Term, TermId};
    let [name_arg, args_arg] = expect_args::<2>("make_fn", args)?;
    let name = match &name_arg {
        Value::Str(s) => s.clone(),
        other => return Err(type_mismatch("String", other, None)),
    };
    let functor = interp.kb.try_resolve_symbol(&name)
        .ok_or_else(|| EvalError::Internal(format!("make_fn: unknown symbol `{name}`")))?;

    // Walk the cons-chain into Vec<TermId>. Cons cells come in two
    // shapes: `build_list_value` (Rust-side) emits named-arg shape with
    // `head`/`tail` keys; anthill-source `cons(h, t)` emits positional
    // shape (args in `pos`, named empty). Try named first, fall back to
    // positional. Field-name comparison stays string-based — the loader
    // may qualify field symbols, but the canonical short name is
    // `head`/`tail`.
    let cons_sym = interp.reflect.cons;
    let nil_sym = interp.reflect.nil;
    let mut pos_vec: Vec<TermId> = Vec::new();
    let mut cursor = args_arg.clone();
    loop {
        match cursor {
            Value::Entity { functor, pos, named } => {
                if Some(functor) == nil_sym { break; }
                if Some(functor) != cons_sym {
                    let n = interp.kb.resolve_sym(functor);
                    return Err(EvalError::Internal(
                        format!("make_fn: expected cons/nil, got {n}")
                    ));
                }
                let (head, tail) = if !named.is_empty() {
                    let h = named.iter()
                        .find(|(s, _)| interp.kb.resolve_sym(*s) == "head")
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| EvalError::Internal(
                            "make_fn: cons missing head field".into()
                        ))?;
                    let t = named.iter()
                        .find(|(s, _)| interp.kb.resolve_sym(*s) == "tail")
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| EvalError::Internal(
                            "make_fn: cons missing tail field".into()
                        ))?;
                    (h, t)
                } else if pos.len() >= 2 {
                    (pos[0].clone(), pos[1].clone())
                } else {
                    return Err(EvalError::Internal(format!(
                        "make_fn: cons cell shape unrecognized (pos={}, named={})",
                        pos.len(), named.len(),
                    )));
                };
                let tid = match head {
                    Value::Term(t) => t,
                    other => return Err(type_mismatch("Term", &other, None)),
                };
                pos_vec.push(tid);
                cursor = tail;
            }
            other => return Err(type_mismatch("List[Term]", &other, None)),
        }
    }

    let pos_args = smallvec::SmallVec::from_vec(pos_vec);
    let tid = interp.kb.alloc(Term::Fn {
        functor,
        pos_args,
        named_args: smallvec::SmallVec::new(),
    });
    Ok(Value::Term(tid))
}

/// `anthill.reflect.find_fact(t: Term) -> Option[FactId]`.
/// Look up the asserted fact whose head term-id structurally equals `t`,
/// returning a `Term::Const(Literal::Handle(Fact, rule_id))` wrapped in
/// `some(...)`. Used by mutating commands (claim / deliver / verify /
/// update / delete) to obtain a FactId for `Store.retract` after a
/// `facts_of`-style query has yielded the matching head.
///
/// The KB hash-conses term ids, so equality of the head TermId is
/// equality of the head term — no recursive structural compare needed.
fn reflect_find_fact(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::term::{HandleKind, Literal, Term};
    let [term_arg] = expect_args::<1>("find_fact", args)?;
    let target = match &term_arg {
        Value::Term(t) => *t,
        other => return Err(type_mismatch("Term", other, None)),
    };
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    let functor = match interp.kb.get_term(target) {
        Term::Fn { functor, .. } => Some(*functor),
        Term::Ref(sym) => Some(*sym),
        _ => None,
    };
    let found = functor.and_then(|f| {
        interp.kb.rules_by_functor(f).into_iter()
            // A value-fact head (WI-348/WI-366) is not a `TermId`, so it can never
            // equal the ground `target` — skip it (avoids the term-only
            // `rule_head` panic on a value head).
            .find(|rid| matches!(interp.kb.rule_head_value(*rid),
                crate::eval::value::Value::Term(t) if *t == target))
    });

    match found {
        Some(rid) => {
            let handle = interp.kb.alloc(Term::Const(Literal::Handle(
                HandleKind::Fact, rid.raw(),
            )));
            Ok(Value::Entity {
                functor: some_sym,
                pos: Vec::new().into(),
                named: vec![(value_key, Value::Term(handle))].into(),
            })
        }
        None => Ok(Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
        }),
    }
}

/// `anthill.reflect.replace_named_arg(t: Term, name: String, value: Term)
/// -> Term`. Return a fresh `Term::Fn` cloned from `t` with the named arg
/// matching `name` replaced by `value`. If `t` has no such named arg the
/// result is structurally equal to `t`.
///
/// Used by status-transition commands to swap one field on a WorkItem
/// fact (e.g. `status`) without re-typing every other field on the
/// anthill side. Field-name comparison is string-based — the loader may
/// qualify field symbols, but the canonical short name is what callers
/// pass in.
fn reflect_replace_named_arg(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::term::Term;
    let [term_arg, name_arg, value_arg] = expect_args::<3>("replace_named_arg", args)?;
    let tid = match &term_arg {
        Value::Term(t) => *t,
        other => return Err(type_mismatch("Term", other, None)),
    };
    let name = match &name_arg {
        Value::Str(s) => s.clone(),
        other => return Err(type_mismatch("String", other, None)),
    };
    let new_val_tid = interp.kb.alloc_from_value(&value_arg)
        .map_err(|e| EvalError::Internal(format!("replace_named_arg: lower value: {e:?}")))?;

    let (functor, pos_args, mut named_args) = match interp.kb.get_term(tid) {
        Term::Fn { functor, pos_args, named_args } => (*functor, pos_args.clone(), named_args.clone()),
        _ => return Err(EvalError::Internal(
            format!("replace_named_arg: expected Fn term, got {:?}", interp.kb.get_term(tid))
        )),
    };
    for entry in named_args.iter_mut() {
        if interp.kb.resolve_sym(entry.0) == name {
            entry.1 = new_val_tid;
        }
    }
    let new_term = interp.kb.alloc(Term::Fn { functor, pos_args, named_args });
    Ok(Value::Term(new_term))
}

/// `anthill.prelude.Time.now() -> String`.
/// Wall-clock timestamp in RFC-3339-with-Z form (`YYYY-MM-DDTHH:MM:SSZ`),
/// matching the format every legacy `anthill-todo` command writes for
/// status transitions and feedback. Effectful — declared to depend on
/// the `Clock` capability so the typer can flag implicit clock reads.
fn time_now(_interp: &mut Interpreter, _args: &[Value]) -> Result<Value, EvalError> {
    Ok(Value::Str(
        chrono::Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string(),
    ))
}

/// `anthill.prelude.Int.to_string(n: Int) -> String`. Decimal repr, no
/// padding. Negative numbers carry a leading `-`. The CLI port uses this
/// for `"180 work item(s):"` and per-status counts.
fn int_to_string(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("Int.to_string", args)?;
    match arg {
        Value::Int(n) => Ok(Value::Str(n.to_string())),
        other => Err(type_mismatch("Int", &other, None)),
    }
}

/// `anthill.reflect.KB.facts_of(kb: KB, functor: String) -> List[Term]`.
/// Returns every asserted fact whose head functor matches the given short
/// or qualified name. Anthill code uses this as a direct iteration handle
/// (paired with `term_field` / `term_as_string`) when there is no per-field
/// constraint to express via `pattern_query`. The returned list is not
/// streaming — facts are eagerly collected — which is fine for the
/// anthill-todo workitem set (~hundreds of facts).
fn kb_facts_of(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb_arg, sort_arg] = expect_args::<2>("KB.facts_of", args)?;
    // The entity is passed by reference (e.g. `facts_of(kb(), WorkItem)`),
    // resolved to its qualified functor symbol via the caller's import.
    let functor_sym = crate::eval::eval::value_functor(&interp.kb, &sort_arg)
        .ok_or_else(|| type_mismatch("Type (entity reference)", &sort_arg, None))?;

    // WI-348: carrier-agnostic — a fact head may be a value fact (e.g. an
    // `OperationInfo` carrying a `denoted` effect). `rule_head_value` returns the
    // head's `Value` directly (`Value::Term` for the universal hash-consed case),
    // so `facts_of(kb, OperationInfo)` no longer panics on a Node-carrying head.
    let rule_ids = interp.kb.rules_by_functor(functor_sym);
    let elements: Vec<Value> = rule_ids.into_iter()
        .map(|rid| interp.kb.rule_head_value(rid).clone())
        .collect();

    interp.build_list_value(elements, &[])
}

/// `Substitution.lookup(s: Substitution, name: String) -> Option[Term]`.
/// Anthill code can't construct logical variables, so it can't pass them to
/// `Substitution.apply`. `lookup` is the bridge: scan the substitution's
/// bindings for any `VarId` whose short name matches the query string, and
/// return the bound term wrapped in `some(...)`. Variables introduced by
/// query lowering carry the field name from the pattern (e.g. `?status` in
/// `pattern_query(WorkItem(status: ?status))`), so this is the natural way
/// to extract field bindings from a stream solution.
///
/// Multiple bindings share a name — a fresh `?status` is allocated per query
/// invocation. `lookup` returns the first match in the substitution's hash
/// map iteration order; query patterns should use distinct field names per
/// extraction site to keep the result well-defined.
///
/// No KB parameter: `VarId.name()` carries the symbol the loader stamped at
/// pattern build time, so name resolution is a pure read against the
/// substitution. `apply` / `compose` still need kb (term-store walks).
fn subst_lookup(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [subst_val, name_val] = expect_args::<2>("Substitution.lookup", args)?;
    let handle = match subst_val {
        Value::Substitution(h) => h,
        other => return Err(type_mismatch("Substitution", &other, None)),
    };
    let name = match &name_val {
        Value::Str(s) => s.clone(),
        _ => return Err(type_mismatch("String", &name_val, None)),
    };

    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    let arena = interp.subst_arena();
    let bound: Option<Value> = arena.with_subst(&handle, |s| {
        for (vid, val) in s.iter() {
            if interp.kb.resolve_sym(vid.name()) == name {
                return Some(val.clone());
            }
        }
        None
    });

    match bound {
        Some(value) => Ok(Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(value_key, value)].into(),
        }),
        None => Ok(Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
        }),
    }
}

// ── Map builtins (proposal 035) ─────────────────────────────────
//
// `Value::Map(MapHandle)` is the runtime representation of any
// `Map[K = ?, V = ?]`. K and V are erased — heterogeneity only matters to
// the type checker. A user that bypasses the typer and stuffs an
// incompatibly-typed value into a Map gets a silent miss on lookup; the
// runtime won't double-check.
//
// Mutating ops (`put`, `remove`) derive a fresh map from the old one to
// preserve immutability semantics. `MapBody` is a persistent structure
// (see map_arena.rs), so this is O(log N) per write, not a full O(N) copy.

/// Build an `Option[Term=V]` value with the given functor symbols. Helper for
/// `get` to avoid repeating the some/none branch.
fn option_some(some_sym: crate::intern::Symbol, value_key: crate::intern::Symbol, v: Value) -> Value {
    Value::Entity { functor: some_sym, pos: Vec::new().into(), named: vec![(value_key, v)].into() }
}
fn option_none(none_sym: crate::intern::Symbol) -> Value {
    Value::Entity { functor: none_sym, pos: Vec::new().into(), named: Vec::new().into() }
}

fn unsupported_key(v: &Value) -> EvalError {
    EvalError::TypeMismatch {
        expected: "Map key (Int / Bool / String / Term)",
        got: v.type_name().to_string(),
    }
}

fn map_empty(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [] = expect_args::<0>("Map.empty", args)?;
    let handle = interp.alloc_map(super::map_arena::MapBody::new());
    Ok(Value::Map(handle))
}

fn map_put(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg, k_arg, v_arg] = expect_args::<3>("Map.put", args)?;
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let key = super::map_arena::MapKey::try_from_value(&k_arg)
        .ok_or_else(|| unsupported_key(&k_arg))?;
    let mut body = interp.maps.clone_body(&handle);
    body.insert(key, v_arg);
    let new_handle = interp.alloc_map(body);
    Ok(Value::Map(new_handle))
}

fn map_get(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg, k_arg] = expect_args::<2>("Map.get", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let key = match super::map_arena::MapKey::try_from_value(&k_arg) {
        Some(k) => k,
        None => return Err(unsupported_key(&k_arg)),
    };
    let found: Option<Value> = interp.maps.with_body(&handle, |b| b.get(&key).cloned());
    Ok(match found {
        Some(v) => option_some(some_sym, value_key, v),
        None => option_none(none_sym),
    })
}

fn map_contains(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg, k_arg] = expect_args::<2>("Map.contains", args)?;
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let key = match super::map_arena::MapKey::try_from_value(&k_arg) {
        Some(k) => k,
        None => return Err(unsupported_key(&k_arg)),
    };
    let present = interp.maps.with_body(&handle, |b| b.contains_key(&key));
    Ok(Value::Bool(present))
}

fn map_remove(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg, k_arg] = expect_args::<2>("Map.remove", args)?;
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let key = match super::map_arena::MapKey::try_from_value(&k_arg) {
        Some(k) => k,
        None => return Err(unsupported_key(&k_arg)),
    };
    let mut body = interp.maps.clone_body(&handle);
    // `shift_remove` preserves the order of the remaining entries — matches
    // anthill's user-visible semantics that iteration order reflects insertion
    // order (and stays stable across removals).
    body.shift_remove(&key);
    let new_handle = interp.alloc_map(body);
    Ok(Value::Map(new_handle))
}

fn map_keys(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg] = expect_args::<1>("Map.keys", args)?;
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let elements: Vec<Value> = interp.maps.with_body(&handle, |b| {
        b.keys().map(|k| k.to_value()).collect()
    });
    interp.build_list_value(elements, &[])
}

fn map_values(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg] = expect_args::<1>("Map.values", args)?;
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let elements: Vec<Value> = interp.maps.with_body(&handle, |b| {
        b.values().cloned().collect()
    });
    interp.build_list_value(elements, &[])
}

fn map_entries(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg] = expect_args::<1>("Map.entries", args)?;
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let pair_sym = require_symbol(interp, "anthill.prelude.Pair.pair", "pair")?;
    let fst_key = interp.kb.intern("fst");
    let snd_key = interp.kb.intern("snd");
    let elements: Vec<Value> = interp.maps.with_body(&handle, |b| {
        b.iter().map(|(k, v)| Value::Entity {
            functor: pair_sym,
            pos: Vec::new().into(),
            named: vec![(fst_key, k.to_value()), (snd_key, v.clone())].into(),
        }).collect()
    });
    interp.build_list_value(elements, &[])
}

fn map_size(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg] = expect_args::<1>("Map.size", args)?;
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let n = interp.maps.with_body(&handle, |b| b.len());
    Ok(Value::Int(n as i64))
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
effect_dispatcher!(modify_get, "anthill.prelude.ModifyRuntime.get", "get", "anthill.prelude.Modify");
effect_dispatcher!(modify_set, "anthill.prelude.ModifyRuntime.set", "set", "anthill.prelude.Modify");
effect_dispatcher!(error_raise, "anthill.prelude.Error.raise", "raise", "anthill.prelude.Error");

// ── Persistence builtins (proposal 007 §4) ─────────────────────

/// `anthill.persistence.Store.persist(store, fact, meta) -> FactId`.
/// `meta` is accepted but not yet consumed — pass `none()`.
fn persistence_persist(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, fact_val, _meta_val] = expect_args::<3>("persist", args)?;
    let key = interp.store_canonical_key(&store_val)?;

    let fact_term = interp.kb.alloc_from_value(&fact_val)
        .map_err(|e| EvalError::Internal(format!("persist: lower fact: {e:?}")))?;

    let sort = interp.kb.make_name_term("Fact");
    let domain = interp.kb.make_name_term("anthill.todo");
    let rule_id = interp.kb.assert_fact(fact_term, sort, domain, None);

    let store = interp.store_registry.get_mut(&key).ok_or_else(|| {
        EvalError::Internal(format!("persist: no store registered for key `{key}`"))
    })?;
    // The store I/O failure is what `persist`'s `effects Error` declares —
    // deliver it through the Error effect (a custom handler can intercept;
    // default Throws -> Raised). The "no store registered" case above is a
    // host-setup fault not covered by `effects Error`, so it stays Internal.
    let outcome = store.persist(&interp.kb, fact_term, sort, domain, None);
    if let Err(e) = outcome {
        return Err(interp.raise_error(Value::Str(format!("persist failed: {e}"))));
    }

    let handle = interp.kb.alloc(crate::kb::term::Term::Const(
        crate::kb::term::Literal::Handle(crate::kb::term::HandleKind::Fact, rule_id.raw()),
    ));
    Ok(Value::Term(handle))
}

/// `anthill.persistence.Store.retract(store, fact_id) -> Bool`.
/// `Store::retract` must run before `kb.retract` — the store needs the
/// head's canonical printed form, and the rule's TermIds may become
/// invalid after the KB-side retract releases them.
fn persistence_retract(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, id_val] = expect_args::<2>("retract", args)?;
    let key = interp.store_canonical_key(&store_val)?;

    let rule_raw = match &id_val {
        Value::Term(tid) => match interp.kb.get_term(*tid) {
            crate::kb::term::Term::Const(crate::kb::term::Literal::Handle(
                crate::kb::term::HandleKind::Fact,
                raw,
            )) => *raw,
            _ => return Err(EvalError::TypeMismatch {
                expected: "FactId handle",
                got: id_val.type_name().to_string(),
            }),
        },
        _ => return Err(EvalError::TypeMismatch {
            expected: "FactId",
            got: id_val.type_name().to_string(),
        }),
    };
    let rule_id = crate::kb::RuleId::from_raw(rule_raw);

    if !interp.kb.is_rule_alive(rule_id) {
        return Ok(Value::Bool(false));
    }

    {
        let store = interp.store_registry.get_mut(&key).ok_or_else(|| {
            EvalError::Internal(format!("retract: no store registered for key `{key}`"))
        })?;
        let outcome = store.retract(&interp.kb, rule_id);
        if let Err(e) = outcome {
            return Err(interp.raise_error(Value::Str(format!("retract failed: {e}"))));
        }
    }
    interp.kb.retract(rule_id);
    Ok(Value::Bool(true))
}

/// `anthill.persistence.Store.flush(store, delta) -> Bool`.
/// `delta` is accepted for spec conformance but ignored — the FileStore
/// tracks its delta internally via the persist / retract buffers.
fn persistence_flush(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, _delta_val] = expect_args::<2>("flush", args)?;
    let key = interp.store_canonical_key(&store_val)?;

    let store = interp.store_registry.get_mut(&key).ok_or_else(|| {
        EvalError::Internal(format!("flush: no store registered for key `{key}`"))
    })?;
    let outcome = store.flush(&interp.kb);
    if let Err(e) = outcome {
        return Err(interp.raise_error(Value::Str(format!("flush failed: {e}"))));
    }
    Ok(Value::Bool(true))
}

/// `anthill.prelude.Cell.new(initial) -> Cell`. Allocates a fresh slot
/// in the cell arena, seeded with `initial`, and returns a refcounted
/// handle. Each call yields a distinct cell — identity is the slot
/// index, not any value-level structure (per `docs/design/cell-runtime.md`
/// §"Identity scheme"). Cycle prevention is the typer's job; runtime
/// has no walk to do here.
fn cell_new(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [initial] = expect_args::<1>("Cell.new", args)?;
    let handle = interp.alloc_cell(initial);
    Ok(Value::Cell(handle))
}

/// `anthill.prelude.Cell.get(c) -> V`. Reads the current value held in
/// the cell. Type-pure: no `Modify` effect (reading is observation, per
/// proposal 037 §"Read operations").
fn cell_get(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [c] = expect_args::<1>("Cell.get", args)?;
    match c {
        Value::Cell(h) => Ok(interp.read_cell(&h)),
        other => Err(type_mismatch("Cell handle", &other, None)),
    }
}

/// `anthill.prelude.Cell.set(c, v) -> Unit`. Replaces the cell's value
/// with `v`. O(1): a single slot write — no cycle walk (the typer
/// guarantees `v` cannot reach `c`'s Cell type, see design doc).
/// Returns `Unit` per the five forward-compat invariants in proposal 037
/// §"With time-travel" — `set` MUST NOT return the prior value.
fn cell_set(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [c, new_val] = expect_args::<2>("Cell.set", args)?;
    match c {
        Value::Cell(h) => {
            interp.write_cell(&h, new_val);
            Ok(Value::Unit)
        }
        other => Err(type_mismatch("Cell handle", &other, None)),
    }
}

/// `anthill.persistence.QueryableStore.retrieve(store, pattern) -> Stream[Term, Error]`.
fn persistence_retrieve(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, pattern_val] = expect_args::<2>("retrieve", args)?;
    let key = interp.store_canonical_key(&store_val)?;

    let pattern_term = interp.kb.alloc_from_value(&pattern_val)
        .map_err(|e| EvalError::Internal(format!("retrieve: lower pattern: {e:?}")))?;

    let outcome = {
        let store = interp.store_registry.get(&key).ok_or_else(|| {
            EvalError::Internal(format!("retrieve: no store registered for key `{key}`"))
        })?;
        store.retrieve(&interp.kb, pattern_term)
    };
    let hits = match outcome {
        Ok(h) => h,
        Err(e) => return Err(interp.raise_error(Value::Str(format!("retrieve failed: {e}")))),
    };

    let mut iter = hits.into_iter();
    let source = StreamSource::Native(Box::new(move || {
        iter.next().map(Value::Term)
    }));
    let handle = interp.alloc_stream(source);
    Ok(Value::Stream(handle))
}

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
        let a = Value::Tuple { pos: vec![Value::Int(1)].into(), named: Vec::new().into() };
        let b = Value::Tuple { pos: vec![Value::Int(1)].into(), named: Vec::new().into() };
        let r = builtin_eq(&mut dummy(), &[a, b]).unwrap();
        assert_eq!(r.as_bool(), Some(true));
    }

    #[test]
    fn eq_on_different_tuples_is_false() {
        let a = Value::Tuple { pos: vec![Value::Int(1)].into(), named: Vec::new().into() };
        let b = Value::Tuple { pos: vec![Value::Int(2)].into(), named: Vec::new().into() };
        let r = builtin_eq(&mut dummy(), &[a, b]).unwrap();
        assert_eq!(r.as_bool(), Some(false));
    }

    #[test]
    fn eq_on_equal_entities_is_true() {
        let mk = || Value::Entity {
            functor: Symbol::from_raw(7),
            pos: vec![Value::Int(10), Value::Str("x".into())].into(),
            named: vec![(Symbol::from_raw(8), Value::Bool(true))].into(),
        };
        let r = builtin_eq(&mut dummy(), &[mk(), mk()]).unwrap();
        assert_eq!(r.as_bool(), Some(true));
    }

    #[test]
    fn eq_on_entities_differing_functor_is_false() {
        let a = Value::Entity {
            functor: Symbol::from_raw(7),
            pos: vec![Value::Int(1)].into(),
            named: vec![].into(),
        };
        let b = Value::Entity {
            functor: Symbol::from_raw(8),
            pos: vec![Value::Int(1)].into(),
            named: vec![].into(),
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
