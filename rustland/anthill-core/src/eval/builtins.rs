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
    register_if_present(interp, "anthill.prelude.Numeric.neg", numeric_neg)?;

    register_if_present(interp, "anthill.prelude.Int64.neg", int_neg)?;
    register_if_present(interp, "anthill.prelude.Int64.abs", int_abs)?;
    register_if_present(interp, "anthill.prelude.Int64.mod", int_mod)?;
    register_if_present(interp, "anthill.prelude.Int64.rem", int_rem)?;
    register_if_present(interp, "anthill.prelude.Int64.div", int_div)?;
    register_if_present(interp, "anthill.prelude.Int64.divExact", int_div)?;
    register_if_present(interp, "anthill.prelude.Int64.sign", int_sign)?;

    register_if_present(interp, "anthill.prelude.Float.div", float_div)?;

    // WI-644 / proposal 004: eq/neq live on the PartialEq base (Eq is the lawful
    // marker). The semantic `eq`/`neq` are IEEE for Float operands (below),
    // structural otherwise.
    register_if_present(interp, "anthill.prelude.PartialEq.eq", builtin_eq)?;
    register_if_present(interp, "anthill.prelude.PartialEq.neq", builtin_neq)?;
    // WI-615 / proposal 051: `===` (structural identity) is a Bool-returning TEST
    // like `eq` — usable in operation bodies (evaluated), not just rule-body goals.
    // WI-644: it uses the PURELY STRUCTURAL `builtin_struct_eq`, NOT the semantic
    // `builtin_eq` (which is IEEE for a Float pair) — `nan === nan` must stay true.
    register_if_present(interp, "anthill.kernel.struct_eq", builtin_struct_eq)?;

    // WI-644 / proposal 004: gt/lt/gte/lte are the PartialOrd comparison surface
    // (IEEE for Float — a NaN operand answers false); compare/max/min stay on the
    // total Ordered.
    register_if_present(interp, "anthill.prelude.Ordered.compare", ordered_compare)?;
    register_if_present(interp, "anthill.prelude.PartialOrd.gt", ordered_gt)?;
    register_if_present(interp, "anthill.prelude.PartialOrd.gte", ordered_gte)?;
    register_if_present(interp, "anthill.prelude.PartialOrd.lt", ordered_lt)?;
    register_if_present(interp, "anthill.prelude.PartialOrd.lte", ordered_lte)?;
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
    register_if_present(interp, "anthill.prelude.String.repeat", string_repeat)?;

    register_if_present(interp, "anthill.prelude.BigInt.to_bigint", bigint_to_bigint)?;
    register_if_present(interp, "anthill.prelude.BigInt.to_int", bigint_to_int)?;
    register_if_present(interp, "anthill.prelude.BigInt.to_float", bigint_to_float)?;
    register_if_present(interp, "anthill.prelude.Int64.to_float", int_to_float)?;

    register_if_present(interp, "anthill.prelude.Float.isNaN", float_is_nan)?;
    register_if_present(interp, "anthill.prelude.Float.isInfinite", float_is_infinite)?;
    register_if_present(interp, "anthill.prelude.Float.isFinite", float_is_finite)?;

    // WI-532 / proposal 039: special IEEE values exposed as host-supplied
    // term-level constants. These are `SymbolKind::Const` (not operations), but
    // a const's value source is this same builtin map (eval's `force_const`
    // reads `self.builtins.get(&sym)`), so they register here like any builtin.
    register_if_present(interp, "anthill.prelude.Float.infinity", float_infinity)?;
    register_if_present(interp, "anthill.prelude.Float.negativeInfinity", float_negative_infinity)?;
    register_if_present(interp, "anthill.prelude.Float.nan", float_nan)?;

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
    register_if_present(interp, "anthill.reflect.unify", reflect_unify)?;
    register_if_present(interp, "anthill.reflect.term_functor_name", term_functor_name)?;
    register_if_present(interp, "anthill.reflect.extract", extract_type_builtin)?;
    register_if_present(interp, "anthill.reflect.term_field", term_field)?;
    register_if_present(interp, "anthill.reflect.term_as_string", term_as_string)?;
    register_if_present(interp, "anthill.reflect.term_as_int", term_as_int)?;
    register_if_present(interp, "anthill.reflect.term_to_string", reflect_term_to_string)?;
    register_if_present(interp, "anthill.reflect.term_list_items", reflect_term_list_items)?;
    register_if_present(interp, "anthill.reflect.term_as_entity", term_as_entity)?;
    register_if_present(interp, "anthill.reflect.field_access", reflect_field_access)?;
    register_if_present(interp, "anthill.reflect.as_term", as_term)?;
    register_if_present(interp, "anthill.reflect.fresh_var", reflect_fresh_var)?;
    register_if_present(interp, "anthill.reflect.make_fn", reflect_make_fn)?;
    register_if_present(interp, "anthill.reflect.find_fact", reflect_find_fact)?;
    register_if_present(interp, "anthill.reflect.replace_named_arg", reflect_replace_named_arg)?;
    register_if_present(interp, "anthill.prelude.Time.now", time_now)?;
    register_if_present(interp, "anthill.prelude.Int64.to_string", int_to_string)?;

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

    // WI-577 — first-class runtime dispatch values: the anthill face of
    // `Value::Requirement` (a resolved spec-impl dictionary) and `Value::OpRef`
    // (a resolved operation reference). Native views over the RequirementArena.
    register_if_present(interp, "anthill.realization.runtime.Dictionary.impl", dict_impl)?;
    register_if_present(interp, "anthill.realization.runtime.Dictionary.arity", dict_arity)?;
    register_if_present(interp, "anthill.realization.runtime.Dictionary.sub", dict_sub)?;
    register_if_present(interp, "anthill.realization.runtime.Dictionary.resolveOp", dict_resolve_op)?;
    register_if_present(interp, "anthill.realization.runtime.Dictionary.ops", dict_ops)?;
    register_if_present(interp, "anthill.realization.runtime.OpRef.op", opref_op)?;
    register_if_present(interp, "anthill.realization.runtime.OpRef.dict", opref_dict)?;

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

/// WI-279 INC1b: eval-side `field_access` — the runtime twin of the SLD
/// `field_access` builtin (`BuiltinTag::FieldAccess`). The typer rewrites a
/// zero-arg `?x.field` `DotApply` into `field_access(receiver, "field")`; here
/// the receiver has evaluated to a `Value::Entity`, and we return its named
/// field by short name. (The SLD twin projects fields off reflect `Term`s
/// during resolution; eval needs this `Value`-level reader because the
/// rewritten call runs inside an operation body.)
fn reflect_field_access(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [receiver, field] = expect_args::<2>("anthill.reflect.field_access", args)?;
    let field_name = match &field {
        Value::Str(s) => s.clone(),
        other => return Err(EvalError::Internal(format!(
            "field_access: field name must be a string, got {}", other.type_name()))),
    };
    match &receiver {
        Value::Entity { functor, pos, named, .. } => {
            // A field supplied by NAME — match by short name.
            for (sym, val) in named.iter() {
                let full = interp.kb().resolve_sym(*sym);
                let short = full.rsplit('.').next().unwrap_or(full);
                if short == field_name.as_str() {
                    return Ok(val.clone());
                }
            }
            // A field supplied POSITIONALLY (`box(42)`, not `box(value: 42)`):
            // `pos` holds only the positionally-supplied args in source order,
            // so the target field's slot is its RANK among the declared fields
            // NOT supplied by name (a field given by name consumes no `pos`
            // slot) — not its absolute declared index. Walking the declared
            // fields with a cursor that advances only past not-named fields
            // handles every positional/named ordering, not just positional-first.
            let field_syms: Option<Vec<crate::intern::Symbol>> =
                interp.kb().entity_field_names(*functor).map(|f| f.to_vec());
            if let Some(field_syms) = field_syms {
                let mut pos_cursor = 0;
                for f in &field_syms {
                    let short = {
                        let full = interp.kb().resolve_sym(*f);
                        full.rsplit('.').next().unwrap_or(full).to_string()
                    };
                    // A field supplied by name (matched above) consumes no `pos` slot.
                    let supplied_by_name = named.iter().any(|(s, _)| {
                        let nf = interp.kb().resolve_sym(*s);
                        nf.rsplit('.').next().unwrap_or(nf) == short
                    });
                    if supplied_by_name {
                        continue;
                    }
                    if short == field_name.as_str() {
                        if let Some(val) = pos.get(pos_cursor) {
                            return Ok(val.clone());
                        }
                        break;
                    }
                    pos_cursor += 1;
                }
            }
            Err(EvalError::Internal(format!(
                "field_access: entity has no field '{}'", field_name)))
        }
        // WI-638: a NAMED-TUPLE component projection (`(x: A, y: B).x`, or the
        // positional `t._1`). The typer resolved the component against the tuple
        // TYPE and rewrote `t.x` into this call; read the component off the
        // runtime `Value::Tuple`. A named component lives in `named` (by short
        // name); a positional tuple stores its components in `pos`, so a `_N`
        // member (1-based) maps to `pos[N-1]`.
        Value::Tuple { pos, named, .. } => {
            for (sym, val) in named.iter() {
                let full = interp.kb().resolve_sym(*sym);
                let short = full.rsplit('.').next().unwrap_or(full);
                if short == field_name.as_str() {
                    return Ok(val.clone());
                }
            }
            if let Some(idx) = field_name.strip_prefix('_').and_then(|d| d.parse::<usize>().ok()) {
                if let Some(val) = idx.checked_sub(1).and_then(|i| pos.get(i)) {
                    return Ok(val.clone());
                }
            }
            Err(EvalError::Internal(format!(
                "field_access: tuple has no component '{}'", field_name)))
        }
        other => Err(EvalError::Internal(format!(
            "field_access: receiver is not an entity (got {})", other.type_name()))),
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

// WI-529: prefix `-` (`neg`) at the Numeric level — handles every Numeric carrier
// (Int / BigInt / Float), mirroring numeric_add/sub/mul. Int64/Float keep their own
// carrier `neg` builtins too (used when neg dispatches via the carrier override).
fn numeric_neg(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Numeric.neg", args)?;
    match a {
        Value::Int(x) => x.checked_neg()
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Numeric.neg" }),
        Value::BigInt(x) => Ok(Value::BigInt(-x)),
        Value::Float(x) => Ok(Value::Float(-x)),
        other => Err(type_mismatch("Int, BigInt, or Float", &other, None)),
    }
}

// ── Int-specific ────────────────────────────────────────────────

fn int_neg(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Int64.neg", args)?;
    match a {
        Value::Int(x) => x.checked_neg()
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Int64.neg" }),
        other => Err(type_mismatch("Int64", &other, None)),
    }
}

fn int_abs(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Int64.abs", args)?;
    match a {
        Value::Int(x) => x.checked_abs()
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Int64.abs" }),
        other => Err(type_mismatch("Int64", &other, None)),
    }
}

fn int_mod(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int64.mod", args)?;
    match (&a, &b) {
        (Value::Int(_), Value::Int(0)) => Err(i.raise_division_by_zero("Int64.mod")),
        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x.rem_euclid(*y))),
        _ => Err(type_mismatch("Int64", &a, Some(&b))),
    }
}

fn int_rem(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int64.rem", args)?;
    match (&a, &b) {
        (Value::Int(_), Value::Int(0)) => Err(i.raise_division_by_zero("Int64.rem")),
        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x % y)),
        _ => Err(type_mismatch("Int64", &a, Some(&b))),
    }
}

/// Truncated integer division. Backs both `anthill.prelude.Int64.div` (the
/// primary name that `/` desugars to) and the historical `Int64.divExact`
/// alias (kept via stdlib rule `divExact(a, b) = div(a, b)` for
/// compatibility). Semantics are identical — the name change is cosmetic.
fn int_div(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int64.div", args)?;
    match (&a, &b) {
        (Value::Int(_), Value::Int(0)) => Err(i.raise_division_by_zero("Int64.div")),
        (Value::Int(x), Value::Int(y)) => x.checked_div(*y)
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Int64.div" }),
        _ => Err(type_mismatch("Int64", &a, Some(&b))),
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
    let [a] = expect_args::<1>("Int64.sign", args)?;
    match a {
        Value::Int(x) => Ok(Value::Int(x.signum())),
        other => Err(type_mismatch("Int64", &other, None)),
    }
}

// ── Eq / Ordered ───────────────────────────────────────────────

/// WI-644 / proposal 004: the SEMANTIC `PartialEq.eq` on a `Float` operand pair is
/// IEEE `==` — `nan eq nan` is *false*, `-0.0 eq +0.0` is *true* — matching the C++
/// codegen and the stdlib contract (float.anthill). This is what distinguishes the
/// PARTIAL `Float` carrier from the total, structural `Eq` carriers: for any
/// non-Float operand we fall back to the structural compare (`OrderedFloat`-backed),
/// so `Set`/`Map`/entity semantic eq (WI-616 override dispatch) is unchanged and
/// `nan === nan` (`struct_eq`) stays true. Returns `None` unless BOTH operands are
/// raw `Float` scalars.
fn float_ieee_eq(i: &Interpreter, a: &Value, b: &Value) -> Option<bool> {
    match (float_val(i, a), float_val(i, b)) {
        (Some(x), Some(y)) => Some(x == y),
        _ => None,
    }
}

/// The raw `f64` of a Float `Value` — an unboxed `Value::Float` OR a `Literal::Float`
/// inside a `Value::Term` (a reflected / stored-structure operand). Mirrors the
/// resolver's `value_f64` so eval and resolver agree on which operands are floats —
/// otherwise a Term-wrapped float would slip past the IEEE path and read `nan == nan`
/// structurally (via `OrderedFloat`), or make ordering raise a spurious type error.
fn float_val(i: &Interpreter, v: &Value) -> Option<f64> {
    match v {
        Value::Float(f) => Some(*f),
        Value::Term { id, .. } => match i.kb().get_term(*id) {
            crate::kb::term::Term::Const(crate::kb::term::Literal::Float(f)) => Some(f.into_inner()),
            _ => None,
        },
        _ => None,
    }
}

/// `anthill.kernel.struct_eq` (`===`) — the TOTAL, carrier-agnostic STRUCTURAL
/// identity test (proposal 051). Stays on `OrderedFloat` (`nan === nan` is true),
/// unlike the semantic `PartialEq.eq` below: reflection / dedup / hash-consing need
/// structural identity. WI-486: a `Value::Term` operand and its structurally-equal
/// `Value::Node`/`Entity` twin compare equal.
fn builtin_struct_eq(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("struct_eq", args)?;
    Ok(Value::Bool(crate::kb::term_view::views_structurally_equal(i.kb(), &a, &b)))
}

fn builtin_eq(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("PartialEq.eq", args)?;
    Ok(Value::Bool(semantic_equal(i, &a, &b)?))
}

fn builtin_neq(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("PartialEq.neq", args)?;
    Ok(Value::Bool(!semantic_equal(i, &a, &b)?))
}

/// WI-625 (proposal 051 Phase 2, the eval→SLD dual) — eval's SEMANTIC equality,
/// the interpreter mirror of the resolver's `sem_eq_core` (`kb/resolve.rs`).
/// Returns the EQUAL verdict (`neq` negates it). The order matches the resolver
/// exactly so eval, SLD, and the C++ codegen agree on every operand:
///
/// 1. **Float IEEE pair** — the PARTIAL-eq carrier (`nan != nan`,
///    `-0.0 == +0.0`), decided BEFORE the structural reflexivity shortcut
///    (which would read `nan == nan` through `OrderedFloat`).
/// 2. **Reflexivity** — structurally identical operands are equal under any
///    lawful `Eq`; the pre-WI-616 answer, and the hot path.
/// 3. **No override anywhere** — a KB with no eq-dispatch entries takes the
///    structural verdict directly (one flag read; the pre-WI-616 behaviour).
/// 4. **Head-carrier override** — an operand headed by an eq-overriding carrier
///    (`Set`/`Map`, the WI-350/WI-444 short-name convention) with BOTH operands
///    ground: prove `<carrier>.eq(a, b)` by the bounded closed sub-resolution
///    ([`KnowledgeBase::prove_rule_predicate`]) — the SAME evaluator the resolver
///    dispatches through. A non-ground operand is NOT proved (`=` is a test and
///    must not bind — the resolver Delays here; eval falls through to the
///    structural verdict). Truncation of a genuinely huge ground compare
///    surfaces loudly rather than guessing.
/// 5. **Structural** — everything else, including a carrier override BURIED under
///    non-carrier structure (`some({1,2})` vs `some({2,1})`): eval answers
///    structurally, exactly as it did before WI-625. This can be
///    membership-wrong (the resolver merely SUSPENDS such a compare); a complete
///    recursive semantic descent that dispatches at each buried carrier is a
///    WI-625 follow-up. `===` is the explicit structural test.
fn semantic_equal(i: &mut Interpreter, a: &Value, b: &Value) -> Result<bool, EvalError> {
    // 1. Float IEEE pair.
    if let Some(v) = float_ieee_eq(i, a, b) {
        return Ok(v);
    }
    // WI-664: a composite reaching an UNSHIELDED partial (Float) carrier compares
    // FIELD-WISE, not by the structural reflexivity shortcut below (which would
    // launder a nested NaN): `eq(Point(nan,_), Point(nan,_)) = eq(nan,nan) ∧ … =
    // false`, matching the field-wise C++ `operator==`. A lawful-Eq boundary
    // (`TotalFloat`/`Set`/`Map`, own `eq`) is NOT a partial carrier, so its
    // structural / dispatch equality is untouched (`eq(TotalFloat(nan), …)` stays
    // true). Comes BEFORE the reflexivity shortcut.
    if i.kb().value_reaches_partial_carrier(a) || i.kb().value_reaches_partial_carrier(b) {
        if let Some(v) = composite_field_wise_eq(i, a, b)? {
            return Ok(v);
        }
        // Not both same-shape composites (e.g. a bare Float vs an entity — a type
        // mismatch the structural verdict answers `false`): fall through.
    }
    // 2. Reflexivity.
    if crate::kb::term_view::views_structurally_equal(i.kb(), a, b) {
        return Ok(true);
    }
    // 3. No carrier overrides eq at all (the common KB): structural verdict.
    if !i.kb().has_eq_dispatch_entries() {
        return Ok(false);
    }
    // 4. Head-carrier override over GROUND operands ⇒ prove `<carrier>.eq(a, b)`.
    let target = {
        let kb = i.kb();
        kb.sem_eq_dispatch_target(a).or_else(|| kb.sem_eq_dispatch_target(b))
    };
    if let Some(target) = target {
        let ground = {
            let kb = i.kb();
            let empty = crate::kb::subst::Substitution::new();
            kb.value_deep_ground(a, &empty) && kb.value_deep_ground(b, &empty)
        };
        if ground {
            // WI-625 gap 2: a BODIED instance-fact eq op (`fact PartialEq[T = X,
            // eq = myEq]` with `myEq` a match/if/recursive function) is a
            // Bool-valued function, NOT a rule-backed predicate — SLD finds no
            // clause. Decide it through the SAME `bridge_eq_op_to_eval` the resolver
            // uses (so eval and SLD agree). CRUCIAL: it runs an ISOLATED scratch
            // interpreter, NOT `call_op_bridged` — this builtin can execute
            // mid-trampoline (e.g. `List.member`'s inner `eq(head, x)`), where a
            // nested `run()` would corrupt the live activation stack. A body-less
            // rule-backed carrier op (`Set.eq`) still proves via the sub-resolution.
            if crate::kb::typing::op_has_runnable_body(i.kb(), target) {
                return match i.kb_mut().bridge_eq_op_to_eval(target, a.clone(), b.clone()) {
                    Ok(Some(v)) => Ok(v),
                    // UNDECIDED (re-entry cap / a bridge-mode suspend inside the
                    // op): in bridge mode SUSPEND so the resolver residualizes; at
                    // top level surface loudly. An APPLICABLE override that could
                    // not be decided must NOT masquerade as a structural `false`
                    // (that would report equal values unequal — Finding 1). This
                    // mirrors the rule-backed branch below.
                    Ok(None) => {
                        let detail = format!(
                            "instance-fact eq over `{}` could not be decided",
                            i.kb().resolve_sym(target),
                        );
                        Err(if i.bridge_mode() {
                            EvalError::Suspended { detail }
                        } else {
                            EvalError::Internal(detail)
                        })
                    }
                    // The bodied op itself failed (raise/overflow/non-Bool): PROPAGATE
                    // — never a silent structural `false` swallowing the error.
                    Err(e) => Err(e),
                };
            }
            return match i.kb_mut().prove_rule_predicate(target, vec![a.clone(), b.clone()]) {
                crate::kb::resolve::PredicateProof::Proved => Ok(true),
                crate::kb::resolve::PredicateProof::Refuted => Ok(false),
                // Only reachable when a huge ground compare truncates the sub-proof
                // budget (the resolver maps the same case to Delay). Under the
                // resolver→eval bridge (WI-625 gap 1) SUSPEND so the resolver
                // delays; top-level eval has nowhere to suspend to, so it stays a
                // loud error rather than guessing a structural answer.
                crate::kb::resolve::PredicateProof::Undecided => {
                    let detail = format!(
                        "semantic eq over `{}` could not be decided (proof truncated)",
                        i.kb().resolve_sym(target)
                    );
                    Err(if i.bridge_mode() {
                        EvalError::Suspended { detail }
                    } else {
                        EvalError::Internal(detail)
                    })
                }
            };
        }
        // Non-ground operand: `=` never binds — fall through to the structural
        // verdict (the resolver Delays; eval keeps its pre-WI-625 answer).
    }
    // 5. Structural verdict — but a carrier override BURIED under non-overriding
    // structure (`some({1,2})` vs `some({2,1})`) makes it membership-wrong. Under
    // the resolver→eval bridge (WI-625 gap 1) importing that verdict into
    // resolution would be unsound, so SUSPEND — exactly where the resolver's own
    // `builtin_sem_eq` delays (`value_reaches_eq_override`). Top-level eval keeps
    // its documented structural answer.
    if i.bridge_mode()
        && (i.kb().value_has_buried_eq_override(a) || i.kb().value_has_buried_eq_override(b))
    {
        return Err(EvalError::Suspended {
            detail: "structural eq over an eq-overriding carrier buried under \
                     non-overriding structure"
                .to_string(),
        });
    }
    Ok(false)
}

/// WI-664 — field-wise SEMANTIC equality for two composites whose carrier is a
/// derived `NonEq` (field-wise) carrier. Decomposes both to identical shape and
/// ANDs `semantic_equal` over the matching fields, so a nested `Float` follows
/// IEEE (`eq(Point(nan,_), Point(nan,_)) → eq(nan,nan) ∧ … = false`) exactly as
/// the field-wise C++ `operator==`. Returns `Some(false)` on any shape mismatch
/// (different functor / arity / keys), and `None` when the operands are not both
/// functor-headed composites (the caller keeps the structural verdict).
fn composite_field_wise_eq(
    i: &mut Interpreter,
    a: &Value,
    b: &Value,
) -> Result<Option<bool>, EvalError> {
    use crate::kb::eq_derive::FieldPairs;
    // Shared shape-decomposition (releases the kb borrow before the recursion).
    let pairs = match i.kb().same_shape_child_pairs(a, b) {
        FieldPairs::NotComposite => return Ok(None),   // caller keeps the structural verdict
        FieldPairs::Mismatch => return Ok(Some(false)), // shape mismatch ⇒ not equal
        FieldPairs::Pairs(pairs) => pairs,
    };
    for (ca, cb) in &pairs {
        if !semantic_equal(i, ca, cb)? {
            return Ok(Some(false));
        }
    }
    Ok(Some(true))
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

/// WI-644 / proposal 004: the PartialOrd comparison surface (`gt`/`lt`/`gte`/`lte`)
/// on a `Float` operand pair is IEEE — a `NaN` operand is UNORDERED, so every
/// comparison answers `false` (`x > y` etc. are already `false` when either is NaN).
/// This matches the C++ codegen (`>`/`<`) and is the ordering dual of the IEEE `eq`
/// fix. `compare`/`max`/`min` (the total `Ordered` ops) keep `total_cmp` — they are
/// only sound on a total carrier (`TotalFloat`, not raw `Float`). Returns `None`
/// unless BOTH operands are raw `Float` scalars.
fn float_pair(i: &Interpreter, a: &Value, b: &Value) -> Option<(f64, f64)> {
    match (float_val(i, a), float_val(i, b)) {
        (Some(x), Some(y)) => Some((x, y)),
        _ => None,
    }
}

fn ordered_gt(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("PartialOrd.gt", args)?;
    if let Some((x, y)) = float_pair(i, &a, &b) {
        return Ok(Value::Bool(x > y));
    }
    Ok(Value::Bool(matches!(value_compare(&a, &b)?, std::cmp::Ordering::Greater)))
}

fn ordered_gte(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("PartialOrd.gte", args)?;
    if let Some((x, y)) = float_pair(i, &a, &b) {
        return Ok(Value::Bool(x >= y));
    }
    Ok(Value::Bool(!matches!(value_compare(&a, &b)?, std::cmp::Ordering::Less)))
}

fn ordered_lt(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("PartialOrd.lt", args)?;
    if let Some((x, y)) = float_pair(i, &a, &b) {
        return Ok(Value::Bool(x < y));
    }
    Ok(Value::Bool(matches!(value_compare(&a, &b)?, std::cmp::Ordering::Less)))
}

fn ordered_lte(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("PartialOrd.lte", args)?;
    if let Some((x, y)) = float_pair(i, &a, &b) {
        return Ok(Value::Bool(x <= y));
    }
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
            ty: None,
        },
        Err(_) => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
            ty: None,
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

// ── Float IEEE constants (WI-532, host value source for the term-level consts) ──
// Value sources for the bodyless `const infinity/negativeInfinity/nan: Float`
// declared in stdlib float.anthill. `force_const` invokes these with no args.

fn float_infinity(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [] = expect_args::<0>("Float.infinity", args)?;
    Ok(Value::Float(f64::INFINITY))
}

fn float_negative_infinity(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [] = expect_args::<0>("Float.negativeInfinity", args)?;
    Ok(Value::Float(f64::NEG_INFINITY))
}

fn float_nan(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [] = expect_args::<0>("Float.nan", args)?;
    Ok(Value::Float(f64::NAN))
}

/// Int → Float. Exact for |n| < 2^53; rounds to nearest representable
/// double for larger magnitudes (standard IEEE conversion).
fn int_to_float(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Int64.to_float", args)?;
    match a {
        Value::Int(n) => Ok(Value::Float(n as f64)),
        other => Err(type_mismatch("Int64", &other, None)),
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
    let start = start.as_int().ok_or_else(|| type_mismatch("Int64", &start, None))?;
    let end = end.as_int().ok_or_else(|| type_mismatch("Int64", &end, None))?;
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

// repeat(s, n) — n copies of s concatenated; n <= 0 yields the empty string.
// The byte total is checked up front: `str::repeat` PANICS on capacity
// overflow, so an absurd n must surface as a loud EvalError, not a process
// abort (the same defensive stance as substring's bounds clamping).
fn string_repeat(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, n] = expect_args::<2>("String.repeat", args)?;
    let s = match &s { Value::Str(x) => x.clone(), _ => return Err(type_mismatch("String", &s, None)) };
    let n = n.as_int().ok_or_else(|| type_mismatch("Int64", &n, None))?;
    if n <= 0 {
        return Ok(Value::Str(String::new()));
    }
    let fits = usize::try_from(n).ok()
        .and_then(|n| s.len().checked_mul(n))
        .is_some_and(|total| total <= isize::MAX as usize);
    if !fits {
        return Err(EvalError::Overflow { op: "String.repeat" });
    }
    Ok(Value::Str(s.repeat(n as usize)))
}

// ── LogicalStream / KB.execute ─────────────────────────────────

use crate::eval::stream::StreamSource;

/// `splitFirst(s: LogicalStream[T]) -> Option[Pair[T, LogicalStream[T]]]`.
/// Pumps the stream one step. For a resolver stream the yielded element is a
/// reflect `Solution` (`definite(subst)` / `undecided(subst, residual)`,
/// WI-531); it is passed through opaquely here, wrapped in `Pair` with the
/// continuation (see `Interpreter::stream_split_first`).
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
            ty: None,
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
                ty: None,
            };
            Ok(Value::Entity {
                functor: some_sym,
                pos: Vec::new().into(),
                named: vec![(value_key, pair_value)].into(),
                ty: None,
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
    Ok(Value::Entity { functor, pos: Vec::new().into(), named: Vec::new().into(), ty: None })
}

/// `KB.execute(kb: KB, q: LogicalQuery) -> Stream[Solution]` (WI-531; each
/// element is `definite(subst)` or `undecided(subst, residual)`, materialized
/// lazily by `Interpreter::stream_split_first`). The KB argument is a
/// sentinel — `Value::Unit` or any placeholder — because the evaluator has no
/// first-class KB values and always uses the interpreter's own KB. The query
/// value is lowered via `KnowledgeBase::execute_logical_query` (proposal
/// 026.1 Q3) and wrapped in `StreamSource::Resolver`.
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
        Value::Term { id: tid, .. } => match interp.kb.get_term(*tid) {
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
            ty: None,
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
            ty: None,
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
    let sym_ref = |interp: &mut Interpreter, s| Value::term(interp.kb.alloc(Term::Ref(s)));

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
        // WI-428: reify a rigid type-receiver projection — the declaring sort and the
        // member name as `Ref(sym)`s, the subject type term as-is.
        TypeExtractor::RigidTypeProjection { sort, subject, member } => {
            let sort_key = interp.kb.intern("sort");
            let var_key = interp.kb.intern("var");
            let sort_val = sym_ref(interp, sort);
            let member_val = sym_ref(interp, member);
            ti_entity(
                interp,
                "RigidTypeProjection",
                vec![(sort_key, sort_val), (var_key, subject), (member_key, member_val)],
            )
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
    Ok(Value::Entity { functor, pos: Vec::new().into(), named: fields.into(), ty: None })
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
    Ok(Value::Entity { functor, pos: Vec::new().into(), named: fields.into(), ty: None })
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
        let sym_val = Value::term(interp.kb.alloc(Term::Ref(sym)));
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
    let mut list = Value::Entity { functor: nil_sym, pos: Vec::new().into(), named: Vec::new().into(), ty: None };
    for elem in elems.into_iter().rev() {
        list = Value::Entity {
            functor: cons_sym,
            pos: Vec::new().into(),
            named: vec![(head_key, elem), (tail_key, list)].into(),
            ty: None,
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
        Value::Term { id: t, .. } => *t,
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
            named: vec![(value_key, Value::term(field_tid))].into(),
            ty: None,
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
            ty: None,
        },
    })
}

/// `anthill.reflect.term_to_string(t: Term) -> String` — the canonical
/// printed text of a term, via `TermPrinter` (the renderer the persistence
/// layer writes with). Total: any non-Term value lowers through
/// `alloc_from_value` first, so an entity prints as its canonical term.
fn reflect_term_to_string(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [v] = expect_args::<1>("term_to_string", args)?;
    let tid = match &v {
        Value::Term { id: tid, .. } => *tid,
        other => interp
            .kb
            .alloc_from_value(other)
            .map_err(|e| EvalError::Internal(format!("term_to_string: lower: {e:?}")))?,
    };
    let printer = crate::persistence::print::TermPrinter::new(&interp.kb);
    Ok(Value::Str(printer.print_term(tid)))
}

/// `anthill.reflect.term_list_items(t: Term) -> List[Term]` — the element
/// terms of a GROUND cons/nil list term, via the printer's strict spine
/// walker (ONE walker, one semantics: named `cons(head:…, tail:…)` or
/// positional `cons(…, …)` with no extra args, ending in a nullary nil).
/// A non-list or malformed spine (var tail, extra args, non-nil end)
/// yields the EMPTY list — all-or-nothing, never a silently truncated
/// prefix.
fn reflect_term_list_items(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [v] = expect_args::<1>("term_list_items", args)?;
    let tid = match &v {
        Value::Term { id: t, .. } => *t,
        other => interp
            .kb
            .alloc_from_value(other)
            .map_err(|e| EvalError::Internal(format!("term_list_items: lower: {e:?}")))?,
    };
    let printer = crate::persistence::print::TermPrinter::new(&interp.kb);
    let items: Vec<Value> = printer
        .unwrap_list_spine(tid)
        .unwrap_or_default()
        .into_iter()
        .map(Value::term)
        .collect();
    interp
        .build_list_value(items, &[])
        .map_err(|e| EvalError::Internal(format!("term_list_items: build list: {e}")))
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
        Value::Term { id: tid, .. } => match interp.kb.get_term(*tid) {
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
            ty: None,
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
            ty: None,
        },
    })
}

/// `anthill.reflect.term_as_int(t: Term) -> Option[Int64]`.
/// Returns `some(i)` when the term is exactly `Const(IntLiteral(_))` (or an
/// `Int` value carrier); otherwise `none()`. The int-literal partner to
/// `term_as_string`, with the identical carrier handling — used to read a
/// numeric field (e.g. a `StoreFormat` version) after `term_field`.
fn term_as_int(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("term_as_int", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    let i: Option<i64> = match &arg {
        Value::Term { id: tid, .. } => match interp.kb.get_term(*tid) {
            crate::kb::term::Term::Const(crate::kb::term::Literal::Int(i)) => Some(*i),
            _ => None,
        },
        Value::Int(i) => Some(*i),
        _ => None,
    };

    Ok(match i {
        Some(v) => Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(value_key, Value::Int(v))].into(),
            ty: None,
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
            ty: None,
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
        Value::Term { id: tid, .. } => materialize_entity(interp, tid),
        Value::Entity { .. } => Some(arg),
        other => return Err(type_mismatch("Term", &other, None)),
    };

    Ok(match materialized {
        Some(value) => Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(value_key, value)].into(),
            ty: None,
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
            ty: None,
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
        // WI-477: read the field type's head carrier-agnostically — `Value::Term` or
        // `Value::Node` (an occurrence-primary type) alike — via the shared TermView
        // predicate, instead of narrowing to a `TermId` first (which dropped a Node).
        let is_opt = crate::kb::typing::is_option_type(&interp.kb, ftype);
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
                    ty: None,
                }));
            }
            Some(tid) => named.push((*fname, term_to_value(interp, tid))),
            None if is_opt => {
                named.push((*fname, Value::Entity {
                    functor: none_sym,
                    pos: Vec::new().into(),
                    named: Vec::new().into(),
                    ty: None,
                }));
            }
            None => return None,
        }
    }

    Some(Value::Entity { functor: canonical, pos: Vec::new().into(), named: named.into(), ty: None })
}

pub(crate) fn term_to_value(interp: &mut Interpreter, tid: crate::kb::term::TermId) -> Value {
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
        Decision::Literal(Literal::Handle(_, _)) => Value::term(tid),
        Decision::TryFn(functor) => {
            if interp.kb.constructor_parent_sort(functor).is_some() {
                materialize_entity(interp, tid).unwrap_or(Value::term(tid))
            } else {
                Value::term(tid)
            }
        }
        Decision::TryRef(sym) => {
            if interp.kb.constructor_parent_sort(sym).is_some() {
                Value::Entity { functor: sym, pos: Vec::new().into(), named: Vec::new().into(), ty: None }
            } else {
                Value::term(tid)
            }
        }
        Decision::Var(v) => Value::Var(v),
        Decision::AsIs => Value::term(tid),
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
    Ok(Value::term(tid))
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
            Value::Entity { functor, pos, named, .. } => {
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
                    Value::Term { id: t, .. } => t,
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
    Ok(Value::term(tid))
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
        Value::Term { id: t, .. } => *t,
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
                crate::eval::value::Value::Term { id: t, .. } if *t == target))
    });

    match found {
        Some(rid) => {
            let handle = interp.kb.alloc(Term::Const(Literal::Handle(
                HandleKind::Fact, rid.raw(),
            )));
            Ok(Value::Entity {
                functor: some_sym,
                pos: Vec::new().into(),
                named: vec![(value_key, Value::term(handle))].into(),
                ty: None,
            })
        }
        None => Ok(Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
            ty: None,
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
        Value::Term { id: t, .. } => *t,
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
    Ok(Value::term(new_term))
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

/// `anthill.prelude.Int64.to_string(n: Int64) -> String`. Decimal repr, no
/// padding. Negative numbers carry a leading `-`. The CLI port uses this
/// for `"180 work item(s):"` and per-status counts.
fn int_to_string(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("Int64.to_string", args)?;
    match arg {
        Value::Int(n) => Ok(Value::Str(n.to_string())),
        other => Err(type_mismatch("Int64", &other, None)),
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
            ty: None,
        }),
        None => Ok(Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
            ty: None,
        }),
    }
}

/// Build a `Symbol` runtime value for `s` — the reflect representation of an
/// anthill `Symbol` (a nullary `Ref` term). The construction counterpart of
/// reading one back via `Value::Term { id } → Term::Ref(s) | Term::Ident(s)`.
fn symbol_value(kb: &mut crate::kb::KnowledgeBase, s: crate::intern::Symbol) -> Value {
    Value::term(kb.alloc(crate::kb::term::Term::Ref(s)))
}

// ── WI-577 — runtime dictionary / op-ref views ──────────────────────────────
//
// The anthill face of the runtime dispatch values `Value::Requirement` (a
// resolved spec-impl dictionary — `(functor, [sub-dicts])`) and `Value::OpRef`
// (a resolved op symbol + captured dispatch dict). Native VIEWS over the live
// `RequirementArena` handle — the `Substitution`/`Map`/`Cell` model: the value
// stays opaque and these read the arena in place, never a structural copy.
// Design: `docs/design/requirement-dictionaries.md` §2.

/// `Dictionary.impl(d) -> Symbol` — the resolved impl identity (the arena
/// slot's `functor`), surfaced as a `Symbol` value (a `Ref` term).
fn dict_impl(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [d] = expect_args::<1>("Dictionary.impl", args)?;
    match d {
        Value::Requirement(h) => Ok(symbol_value(&mut interp.kb, h.functor())),
        other => Err(type_mismatch("Dictionary", &other, None)),
    }
}

/// `Dictionary.arity(d) -> Int64` — number of sub-requirement dicts.
fn dict_arity(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [d] = expect_args::<1>("Dictionary.arity", args)?;
    match d {
        Value::Requirement(h) => Ok(Value::Int(h.arity() as i64)),
        other => Err(type_mismatch("Dictionary", &other, None)),
    }
}

/// `Dictionary.sub(d, i) -> Dictionary` — project the i-th sub-requirement.
/// No structural copy: `project` bumps the child handle's refcount and wraps
/// the SAME arena slot. A loud out-of-range error (rather than the arena's
/// panic) for an index the anthill caller supplies out of bounds.
fn dict_sub(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [d, idx] = expect_args::<2>("Dictionary.sub", args)?;
    let i = match &idx {
        Value::Int(n) => *n,
        other => return Err(type_mismatch("Int64", other, None)),
    };
    match d {
        Value::Requirement(h) => {
            let n = h.arity();
            if i < 0 || (i as usize) >= n {
                return Err(EvalError::Internal(format!(
                    "Dictionary.sub: index {i} out of range (dict has {n} sub-requirements)"
                )));
            }
            Ok(Value::Requirement(h.project(i as usize)))
        }
        other => Err(type_mismatch("Dictionary", &other, None)),
    }
}

/// `Dictionary.resolveOp(d, specOp: Symbol) -> OpRef` — resolve a spec op
/// against this dict's impl sort into a callable handle. The reflect face of the
/// interpreter's dict-threaded dispatch: [`resolve_op_target`] on
/// `(impl(d), specOp)`, wrapped as `OpRef { op, dict: Some(d) }` — capturing the
/// dispatch dict so the op stays runnable under THIS dict. `specOp` is the SPEC
/// OP symbol — the same key the interpreter dispatches on — and is expected to
/// be a resolved symbol (as minted by `impl` / `op` / reflect `lookup_symbol`).
///
/// The result both INSPECTS (`op` = which op it resolved to, `dict` = its
/// dispatch env — payoff #2) and RUNS: applying the OpRef dispatches `op` under
/// its captured dict (`spread_eta_args` reads a body-less op's arity from its
/// signature, so a native-builtin-backed resolved op like `PartialEq.eq` is callable).
fn dict_resolve_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::term::Term;
    use crate::kb::typing::resolve_op_target;
    let [d, spec_op] = expect_args::<2>("Dictionary.resolveOp", args)?;
    let h = match d {
        Value::Requirement(h) => h,
        other => return Err(type_mismatch("Dictionary", &other, None)),
    };
    let spec_op_sym = match &spec_op {
        Value::Term { id, .. } => match interp.kb.get_term(*id) {
            Term::Ref(s) | Term::Ident(s) => *s,
            _ => return Err(type_mismatch("Symbol", &spec_op, None)),
        },
        other => return Err(type_mismatch("Symbol", other, None)),
    };
    let target = resolve_op_target(&interp.kb, h.functor(), spec_op_sym);
    Ok(Value::OpRef { op: target, dict: Some(h) })
}

/// `Dictionary.ops(d) -> FiniteStream[OpRef]` — all this dict's operations as
/// resolved OpRef handles (the bulk face of `resolveOp`). Each `sort_ops` entry
/// is put through the SAME [`resolve_op_target`] as `resolveOp` — so the two
/// faces agree (an inherited instance-fact placeholder resolves to its bound
/// impl op, not the placeholder) — then wrapped as `OpRef { op, dict: Some(d) }`.
///
/// Returned as an EAGER `List` value: `List provides FiniteStream`, so it
/// satisfies the declared `FiniteStream[OpRef]` return, whereas a bare
/// `Value::Stream` carries as `LogicalStream` (provides only `Stream`). A
/// genuinely lazy carrier is a follow-on; the (already-resolved, finite) set is
/// materialized up front today. Each element is a callable OpRef, same as a
/// `resolveOp` result.
fn dict_ops(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::typing::resolve_op_target;
    let [d] = expect_args::<1>("Dictionary.ops", args)?;
    let h = match d {
        Value::Requirement(h) => h,
        other => return Err(type_mismatch("Dictionary", &other, None)),
    };
    let impl_sym = h.functor();
    let elems: Vec<Value> = interp
        .kb
        .sort_ops_for_impl(impl_sym)
        .into_iter()
        .map(|target| {
            let resolved = resolve_op_target(&interp.kb, impl_sym, target);
            Value::OpRef { op: resolved, dict: Some(h.clone()) }
        })
        .collect();
    build_value_list(interp, elems)
}

/// `OpRef.op(r) -> Symbol` — the resolved operation's identity (a fully-
/// qualified op symbol), surfaced as a `Symbol` value.
fn opref_op(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r] = expect_args::<1>("OpRef.op", args)?;
    match r {
        Value::OpRef { op, .. } => Ok(symbol_value(&mut interp.kb, op)),
        other => Err(type_mismatch("OpRef", &other, None)),
    }
}

/// `OpRef.dict(r) -> Option[Dictionary]` — the captured dispatching dict;
/// none() for a requires-free / namespace-level op.
fn opref_dict(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r] = expect_args::<1>("OpRef.dict", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");
    match r {
        Value::OpRef { dict, .. } => Ok(match dict {
            Some(h) => option_some(some_sym, value_key, Value::Requirement(h)),
            None => option_none(none_sym),
        }),
        other => Err(type_mismatch("OpRef", &other, None)),
    }
}

/// `reflect.unify(a: Term, b: Term, kb: KB) -> Option[Substitution]` — the
/// term-level DATA face of `<=>` (proposal 049, "Two faces of one search").
/// Runs the same `builtin_unify` core over two raw terms and returns the
/// resulting most general unifier as a `Value::Substitution` wrapped in
/// `some(...)`, or `none` when they do not unify. `<=>` is the object-level
/// face (it installs σ into the resolver frame); this face hands σ back as a
/// value, for reflection and the WI-010 self-hosted resolver, which run over
/// raw terms with no typing in scope. The `kb` arg is the ambient-KB sentinel
/// (the `KB.execute` convention) — unification runs on the interpreter's KB.
fn reflect_unify(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a_val, b_val, _kb_arg] = expect_args::<3>("reflect.unify", args)?;
    // A reflect `Term` rides as `Value::Term(TermId)`; a non-`Term` carrier is a
    // type error here (loud, not a silent mismatch).
    let a = match &a_val {
        Value::Term { id: t, .. } => *t,
        _ => return Err(type_mismatch("Term", &a_val, None)),
    };
    let b = match &b_val {
        Value::Term { id: t, .. } => *t,
        _ => return Err(type_mismatch("Term", &b_val, None)),
    };
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");
    match interp.kb.unify_terms(a, b) {
        Some(sigma) => {
            let handle = interp.alloc_subst(sigma);
            Ok(Value::Entity {
                functor: some_sym,
                pos: Vec::new().into(),
                named: vec![(value_key, Value::Substitution(handle))].into(),
                ty: None,
            })
        }
        None => Ok(Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
            ty: None,
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
    Value::Entity { functor: some_sym, pos: Vec::new().into(), named: vec![(value_key, v)].into(), ty: None }
}
fn option_none(none_sym: crate::intern::Symbol) -> Value {
    Value::Entity { functor: none_sym, pos: Vec::new().into(), named: Vec::new().into(), ty: None }
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
            ty: None,
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

// ── Fact monotonicity guard (proposal 053) ─────────────────────
//
// The runtime write paths consult `anthill.reflect.fact_monotonicity(functor)`
// — the SAME reflect predicate the language exposes (single source of truth) —
// before a persist / retract, and refuse the non-monotone step LOUDLY:
//   * retract of a functor that is not `non_monotone` (the SOLE guard — retract
//     is what desyncs re-derived structure and falsifies caches over it);
//   * persist (assert) of a `constant` functor.
// These builtins are the runtime fact-write boundary; they never run during a
// load phase, so the guard cannot trip the loader legitimately establishing
// facts. Factored as a helper so any future in-memory mutation path adopts it.

/// The three fact-monotonicity policies (proposal 053), mirroring the anthill
/// `enum Monotonicity` in `anthill.reflect`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Monotonicity {
    Constant,
    Monotone,
    NonMonotone,
}

/// Reduce `anthill.reflect.fact_monotonicity(functor)` via the simp rewriter
/// and read back the policy, comparing the reduced head by interned SYMBOL
/// identity — not a name string. A user entity sharing a short name (e.g. some
/// `my.pkg.constant`) must not be mistaken for the reflect variant; the repo's
/// representation note requires identity over names.
///
/// The `monotone` DEFAULT is returned for exactly ONE case: the reduced head is
/// still `fact_monotonicity` itself, i.e. no rule fired. reflect.anthill
/// deliberately carries no catch-all rule (under load-order simp firing it would
/// mask every override — most-specific-first is deferred, 043 §4.6), so an
/// unreduced result IS the append-only default. Every OTHER outcome — a missing
/// reflect symbol, a reduction to an unexpected head, or a non-functor carrier —
/// is a LOUD error (repo principle: loud over silent skip), never a silent
/// default that would quietly void the guard.
fn fact_monotonicity_of(
    kb: &mut crate::kb::KnowledgeBase,
    functor: crate::intern::Symbol,
) -> Result<Monotonicity, EvalError> {
    use crate::kb::term::Term;
    // The reflect substrate is loaded whenever the persistence builtins run
    // (persistence imports anthill.reflect), so a missing symbol is a broken /
    // stale setup, not a benign default — surface it.
    let resolve = |kb: &crate::kb::KnowledgeBase, name: &str| -> Result<crate::intern::Symbol, EvalError> {
        kb.try_resolve_symbol(name).ok_or_else(|| EvalError::Internal(format!(
            "fact_monotonicity guard: `{name}` unresolved — the anthill.reflect \
             substrate (proposal 053) must be loaded"
        )))
    };
    let fm_sym = resolve(kb, "anthill.reflect.fact_monotonicity")?;
    let mono_sym = resolve(kb, "anthill.reflect.Monotonicity.monotone")?;
    let non_mono_sym = resolve(kb, "anthill.reflect.Monotonicity.non_monotone")?;
    let const_sym = resolve(kb, "anthill.reflect.Monotonicity.constant")?;

    let functor_ref = kb.alloc(Term::Ref(functor));
    let call = kb.alloc(Term::Fn {
        functor: fm_sym,
        pos_args: smallvec::SmallVec::from_slice(&[functor_ref]),
        named_args: smallvec::SmallVec::new(),
    });
    let (result, _changes) =
        kb.apply_eq_rules(&Value::term(call), 100, &crate::kb::subst::Substitution::new());

    let head = crate::kb::term_view::TermView::head(&result, kb).functor_sym();
    match head {
        Some(s) if s == non_mono_sym => Ok(Monotonicity::NonMonotone),
        Some(s) if s == const_sym => Ok(Monotonicity::Constant),
        Some(s) if s == mono_sym => Ok(Monotonicity::Monotone),
        // Unreduced: head is still the operation itself → no rule matched → the
        // append-only default. This is the ONLY path that yields `monotone`
        // without a rule having said so.
        Some(s) if s == fm_sym => Ok(Monotonicity::Monotone),
        Some(s) => Err(EvalError::Internal(format!(
            "fact_monotonicity({}) reduced to unexpected head `{}` — expected a \
             Monotonicity variant (proposal 053)",
            kb.qualified_name_of(functor),
            kb.qualified_name_of(s),
        ))),
        None => Err(EvalError::Internal(format!(
            "fact_monotonicity({}) reduced to a non-functor carrier (proposal 053)",
            kb.qualified_name_of(functor),
        ))),
    }
}

// ── Persistence builtins (proposal 007 §4) ─────────────────────

/// `anthill.persistence.Store.persist(store, fact, meta) -> FactId`.
/// `meta` is accepted but not yet consumed — pass `none()`.
fn persistence_persist(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, fact_val, _meta_val] = expect_args::<3>("persist", args)?;
    let key = interp.store_canonical_key(&store_val)?;

    let fact_term = interp.kb.alloc_from_value(&fact_val)
        .map_err(|e| EvalError::Internal(format!("persist: lower fact: {e:?}")))?;

    // Proposal 053: refuse asserting a `constant` functor (loud). A monotone
    // (default) or non_monotone functor asserts freely. A fact head must have a
    // functor to key the guard — its absence is a malformed fact, surfaced loud
    // rather than silently asserted past the guard.
    let Some(functor) =
        crate::kb::term_view::TermView::head(&Value::term(fact_term), &interp.kb).functor_sym()
    else {
        return Err(EvalError::Internal(
            "persist: fact head has no functor — cannot apply the monotonicity guard \
             (proposal 053)".into(),
        ));
    };
    if fact_monotonicity_of(&mut interp.kb, functor)? == Monotonicity::Constant {
        let name = interp.kb.qualified_name_of(functor).to_string();
        return Err(interp.raise_error(Value::Str(format!(
            "persist refused: functor `{name}` is constant — no assert (proposal 053)"
        ))));
    }

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
    Ok(Value::term(handle))
}

/// `anthill.persistence.Store.retract(store, fact_id) -> Bool`.
/// `Store::retract` must run before `kb.retract` — the store needs the
/// head's canonical printed form, and the rule's TermIds may become
/// invalid after the KB-side retract releases them.
fn persistence_retract(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, id_val] = expect_args::<2>("retract", args)?;
    let key = interp.store_canonical_key(&store_val)?;

    let rule_raw = match &id_val {
        Value::Term { id: tid, .. } => match interp.kb.get_term(*tid) {
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

    // Proposal 053: retract is the SOLE guard — refuse (loud) unless the functor
    // is `non_monotone`. Retracting a monotone/constant functor's facts at
    // runtime desyncs re-derived structure and falsifies caches. A missing head
    // functor is a malformed rule, surfaced loud rather than silently retracted
    // past the guard.
    let Some(functor) =
        crate::kb::term_view::TermView::head(interp.kb.rule_head_value(rule_id), &interp.kb)
            .functor_sym()
    else {
        return Err(EvalError::Internal(
            "retract: rule head has no functor — cannot apply the monotonicity guard \
             (proposal 053)".into(),
        ));
    };
    if fact_monotonicity_of(&mut interp.kb, functor)? != Monotonicity::NonMonotone {
        let name = interp.kb.qualified_name_of(functor).to_string();
        return Err(interp.raise_error(Value::Str(format!(
            "retract refused: functor `{name}` is not non_monotone (proposal 053)"
        ))));
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
        iter.next().map(Value::term)
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
                assert!(got.contains("Int64") && got.contains("Float"), "got = {got}");
            }
            other => panic!("expected TypeMismatch, got {other:?}"),
        }
    }

    #[test]
    fn int_mod_by_zero_errors_rather_than_returning_a_value() {
        // WI-467: int_mod must DETECT a zero divisor and route it as an error
        // (via `raise_division_by_zero`), never return a bogus remainder. On
        // this bare KB the effects prelude isn't loaded, so building the
        // `division_by_zero` payload fails LOUDLY (`require_symbol` -> Internal
        // "not in scope") rather than fabricating a same-name symbol. The full
        // routed payload (`division_by_zero(op:)` through the Error handler) is
        // covered on a stdlib-loaded KB by
        // `eval_test::{m3_int_division_by_zero, wi467_division_by_zero_routes_through_error_handler}`.
        let err = int_mod(&mut dummy(), &[Value::Int(5), Value::Int(0)]).unwrap_err();
        assert!(
            matches!(&err, EvalError::Internal(m) if m.contains("division_by_zero")),
            "bare KB: expected a loud Internal naming the unresolved payload sort, got {err:?}",
        );
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
        let a = Value::Tuple { pos: vec![Value::Int(1)].into(), named: Vec::new().into(), ty: None };
        let b = Value::Tuple { pos: vec![Value::Int(1)].into(), named: Vec::new().into(), ty: None };
        let r = builtin_eq(&mut dummy(), &[a, b]).unwrap();
        assert_eq!(r.as_bool(), Some(true));
    }

    #[test]
    fn eq_on_different_tuples_is_false() {
        let a = Value::Tuple { pos: vec![Value::Int(1)].into(), named: Vec::new().into(), ty: None };
        let b = Value::Tuple { pos: vec![Value::Int(2)].into(), named: Vec::new().into(), ty: None };
        let r = builtin_eq(&mut dummy(), &[a, b]).unwrap();
        assert_eq!(r.as_bool(), Some(false));
    }

    #[test]
    fn eq_on_equal_entities_is_true() {
        let mk = || Value::Entity {
            functor: Symbol::from_raw(7),
            pos: vec![Value::Int(10), Value::Str("x".into())].into(),
            named: vec![(Symbol::from_raw(8), Value::Bool(true))].into(),
            ty: None,
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
            ty: None,
        };
        let b = Value::Entity {
            functor: Symbol::from_raw(8),
            pos: vec![Value::Int(1)].into(),
            named: vec![].into(),
            ty: None,
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
