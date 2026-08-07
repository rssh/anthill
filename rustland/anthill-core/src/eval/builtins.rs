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
//! bodies already gives lazy branching.
//!
//! WI-884 recorded here that `ite` "reduces NOWHERE", and that has since been RETRACTED
//! twice over, so do not read it as a live measurement. WI-893 found the measurement was
//! a parser artifact — a comment above `ite_true` had silently eaten its `[simp]`, so the
//! probed branch was the untagged one. WI-887 then deleted the `ite` DECLARATION this
//! paragraph pointed at (the reason above stands and is why: an operation evaluates its
//! arguments, so an `ite` operation computes BOTH branches), leaving `ite` defined solely
//! by its two `[simp]` rules. It reduces: driven in `wi884_sibling_backing_test::
//! ite_reduces_under_both_spellings`.
//!
//! WI-894 then scoped that functor to `Bool`, so the name is reached by `import
//! anthill.prelude.Bool.{ite}` or written `Bool.ite(…)` — not by a global name. The
//! non-registration above is unaffected: it is about EVAL, and the reason is strictness,
//! not naming.

use std::rc::Rc;

use super::value::Dictionary;
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
    // (IEEE for Float — a NaN operand answers false); compare/max/min are the total
    // `Ord` surface.
    //
    // WI-876 — NOT REGISTERED HERE. This family is the one whose host
    // implementations are keyed PER CARRIER, from the `operation_map` clause of
    // each `provides <carrier> language rust` block (see
    // [`register_operation_mappings`]). Registered on the SPEC op, one host-scalar
    // implementation served every carrier that never wrote its own — so a
    // STRUCTURAL `Ord` provider was intercepted by code that could not compare
    // its values, on a program that LOADED CLEAN, and the spec's own default bodies
    // could never run. `max`/`min` are in the family too: they are DECLARED on
    // `Ord` (with the default bodies that derive them from `gte`/`lte`), and each
    // total scalar carrier maps them to `ordered_max`/`ordered_min` so the derivation
    // costs no interpreter frame where the host answers in one call. WI-881 — `Float`
    // maps its OWN `max`/`min` to the IEEE pair; the argument is beside `float_max`.

    register_if_present(interp, "anthill.prelude.Bool.not", bool_not)?;
    register_if_present(interp, "anthill.prelude.Bool.and", bool_and)?;
    register_if_present(interp, "anthill.prelude.Bool.or", bool_or)?;

    // WI-884 — HALF OF `String`'S SURFACE IS REGISTERED HERE AND HALF IN ITS BINDING
    // BLOCK, and a reader adding the next one has to know that. These eight are keyed
    // by hardcoded qualified name; `contains`/`indexOf`/`replace`/`trim`/`split`/
    // `isEmpty` are keyed by `rustland/anthill-stl/anthill/string.anthill`'s
    // `operation_map`. Same for `Int64` (nine here, `minValue`/`maxValue` there).
    //
    // NOT the WI-879/WI-880 defect, which is about an operation declared on a SPEC
    // (`Numeric.add`, `Bool.not`) where one registration serves every carrier: these
    // are the CARRIER's own operations, so the qualified name already keys them per
    // carrier and they answer correctly. It is still a split with a cost, and the cost
    // is that the two halves are not equivalent to their READERS —
    // `op_is_interpretable` (kb/typing.rs) counts a host MAPPING and not a hardcoded
    // registration, so `String.contains` reads as backed and `String.concat` does not
    // though one interpreter runs both; `kb.host_op_mappings()`, which is what WI-886
    // wants a second backend to consume, sees six of fourteen; and only the mapped
    // half has its arity checked against the declaration. Unreached today because no
    // spec declares `concat`, which is the same coincidence WI-876's review refused to
    // rely on. Migrating the eight is recorded as feedback on WI-880 — whose acceptance
    // is worded for SPEC ops and so does not currently claim them.
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

    // WI-532 / proposal 039: special IEEE values exposed as host-supplied term-level
    // constants (`SymbolKind::Const`). WI-889 — these are NO LONGER keyed here by
    // hardcoded qualified name. They reach eval as DATA now: the `const_map` clause of
    // `provides Float language rust` emits `ConstMapping` facts, and
    // `register_const_mappings` (below, via `register_operation_mappings`' sibling
    // call) registers each against its const symbol from `HOST_FNS`. A const's value
    // source is still this same builtin map — `force_const` reads `self.builtins.get`
    // and invokes with no args — the registration channel is what changed.

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
    register_if_present(interp, "anthill.prelude.Relation.splitFirst", relation_split_first)?;
    register_if_present(interp, "anthill.prelude.Relation.negate", relation_negate)?;
    register_if_present(interp, "anthill.prelude.Relation.union", relation_union)?;
    register_if_present(interp, "anthill.prelude.Relation.where_run", relation_where_run)?;
    register_if_present(interp, "anthill.prelude.Relation.guarded_of", relation_guarded_of)?;
    register_if_present(interp, "anthill.prelude.Relation.join_run", relation_join_run)?;
    register_if_present(interp, "anthill.prelude.Relation.conjoin_of", relation_conjoin_of)?;
    register_if_present(interp, "anthill.prelude.Relation.project_run", relation_project_run)?;
    register_if_present(interp, "anthill.prelude.Relation.fix", relation_fix)?;
    register_if_present(interp, "anthill.reflect.KB.kb", kb_ambient)?;
    register_if_present(interp, "anthill.reflect.KB.execute", kb_execute)?;
    register_if_present(interp, "anthill.reflect.KB.facts_of", kb_facts_of)?;
    register_if_present(interp, "anthill.reflect.KB.stored_facts_of", kb_stored_facts_of)?;
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
    // WI-722 (043.1) — the occurrence-BUILD side of a compile-time macro. A
    // per-shape occurrence builder returning a spliceable `NodeOccurrence` (not a
    // `Term`, as `make_fn` does). Available wherever eval runs; a macro is the
    // only caller (at compile time, via the `[simp]` fire hook).
    register_if_present(interp, "anthill.reflect.make_apply", reflect_make_apply)?;
    // WI-722 inc 2 (043.1) — the occurrence-READ side of a compile-time macro,
    // the value-domain complement of the resolver's `occurrence_term` /
    // `sub_occurrences` / `type_of` goal handlers (`kb/resolve.rs`). A macro reads
    // its argument occurrences through these (structure via `occurrence_term`,
    // children via `sub_occurrences`, the typer-stamped type via `occurrence_type`)
    // and rebuilds through `make_apply`. Registered on the eval side (surface A) so
    // the macro-eval path (`call_op_bridged`) dispatches them with `Value::Node`
    // args untouched.
    register_if_present(interp, "anthill.reflect.occurrence_term", reflect_occurrence_term)?;
    register_if_present(interp, "anthill.reflect.sub_occurrences", reflect_sub_occurrences)?;
    register_if_present(interp, "anthill.reflect.occurrence_type", reflect_occurrence_type)?;
    register_if_present(interp, "anthill.reflect.is_modifiable", reflect_is_modifiable)?;
    register_if_present(interp, "anthill.reflect.replace_named_arg", reflect_replace_named_arg)?;
    register_if_present(interp, "anthill.prelude.Time.now", time_now)?;
    register_if_present(interp, "anthill.prelude.Int64.to_string", int_to_string)?;

    // Persistence (proposal 007) is NOT here — WI-931 moved its six operations to
    // `HOST_FNS` + the `operation_map` clauses in
    // `rustland/anthill-stl/anthill/persistence.anthill`, so the backing they
    // always had is DECLARED and the load-time provision check can see it. See
    // the `store_*` entries below.

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

    // WI-577 — first-class runtime dispatch values: the anthill face of a
    // requirement dictionary (a resolved spec impl) and `Value::OpRef` (a resolved
    // operation reference). Native readers over the values themselves (WI-1045).
    register_if_present(interp, "anthill.realization.runtime.Dictionary.impl", dict_impl)?;
    register_if_present(interp, "anthill.realization.runtime.Dictionary.arity", dict_arity)?;
    register_if_present(interp, "anthill.realization.runtime.Dictionary.sub", dict_sub)?;
    register_if_present(interp, "anthill.realization.runtime.Dictionary.resolveOp", dict_resolve_op)?;
    register_if_present(interp, "anthill.realization.runtime.Dictionary.ops", dict_ops)?;
    register_if_present(interp, "anthill.realization.runtime.OpRef.op", opref_op)?;
    register_if_present(interp, "anthill.realization.runtime.OpRef.dict", opref_dict)?;
    register_if_present(interp, "anthill.realization.runtime.OpRef.named", opref_named)?;

    // WI-876 — last, because it is the KB-DRIVEN half: everything above is a
    // hardcoded qualified name, this reads what the loaded binding blocks asked
    // for. Registered after, so a mapping and a hardcoded entry naming the same
    // operation resolve to the mapping (nothing does today; the ordering family
    // moved out of the list above entirely).
    register_operation_mappings(interp)?;
    // WI-889 — the const-level peer: register the `const_map` value sources (the Float
    // IEEE specials) against their const symbols, from the same `HOST_FNS` registry.
    register_const_mappings(interp)?;

    Ok(())
}

/// WI-876 — the host functions this runtime exposes to an `operation_map` clause,
/// keyed by the name a binding block spells. A CLOSED list, and that is the point:
/// `host_fn` is a key into this registry, not a symbol resolved by reflection, so
/// the runtime keeps control of what a `.anthill` file can bind to and an unknown
/// key is a refusal rather than a silently unregistered operation.
///
/// Registering here does NOT make an operation dispatchable on its own — the
/// carrier must also DECLARE the operation (`operation compare(a: Int64, b: Int64)
/// -> Int64`, body-less), which is what puts it in the `sort_ops` table both the
/// typer's static pin and the evaluator's value-directed dispatch read.
///
/// WI-884 — a SLICE rather than a `match` on the key, so that the registry can be
/// ITERATED. The arity column is written by hand and
/// [`every_host_fn_key_declares_the_arity_its_function_accepts`] is what checks it,
/// and while the entries lived in a `match` that test had to restate every key in a
/// second hand-written list — which a new entry escapes SILENTLY, one level up from
/// the defect the test exists to catch. Iterating makes it exhaustive by
/// construction. The lookup is a linear scan over a few dozen `&'static str`s, run
/// once per mapping per fresh interpreter, against a stdlib parse.
const HOST_FNS: &[(&str, usize, fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>)] = &[
    // The TOTAL scalar order (`Ord`): `Int64`, `BigInt`, `String`.
    ("ordered_compare", 2, ordered_compare),
    ("ordered_gt", 2, ordered_gt),
    ("ordered_gte", 2, ordered_gte),
    ("ordered_lt", 2, ordered_lt),
    ("ordered_lte", 2, ordered_lte),
    ("ordered_max", 2, ordered_max),
    ("ordered_min", 2, ordered_min),
    // The IEEE partial order (`PartialOrd` on `Float`): a NaN operand is
    // UNORDERED, so every comparison answers false. Its own four functions
    // rather than a carrier test inside the total ones — `Float` names these
    // in its own binding, which is where "Float's order is IEEE" belongs.
    ("float_gt", 2, float_gt),
    ("float_gte", 2, float_gte),
    ("float_lt", 2, float_lt),
    ("float_lte", 2, float_lte),
    // WI-881 — `Float`'s IEEE ARITHMETIC. Every one of these is an `f64`
    // intrinsic; see the section header above the definitions for why they
    // are host functions rather than laws over the other operations.
    ("float_abs", 1, float_abs),
    ("float_neg", 1, float_neg),
    ("float_sqrt", 1, float_sqrt),
    ("float_sin", 1, float_sin),
    ("float_cos", 1, float_cos),
    ("float_tan", 1, float_tan),
    ("float_asin", 1, float_asin),
    ("float_acos", 1, float_acos),
    ("float_atan", 1, float_atan),
    ("float_exp", 1, float_exp),
    ("float_log", 1, float_log),
    ("float_log10", 1, float_log10),
    ("float_log2", 1, float_log2),
    ("float_hypot", 2, float_hypot),
    ("float_fmod", 2, float_fmod),
    ("float_pow", 2, float_pow),
    ("float_atan2", 2, float_atan2),
    ("float_max", 2, float_max),
    ("float_min", 2, float_min),
    ("float_floor", 1, float_floor),
    ("float_ceil", 1, float_ceil),
    ("float_round", 1, float_round),
    ("float_pi", 0, float_pi),
    ("float_e", 0, float_e),
    ("float_tau", 0, float_tau),
    // WI-889 — the three IEEE specials, now reaching eval through `const_map` /
    // `register_const_mappings` like `pi`/`e`/`tau` reach it through `operation_map`.
    // They are `const`s, not operations, but the value function is the same nullary
    // shape (`nullary_const!`), and `force_const` invokes it with no args.
    ("float_infinity", 0, float_infinity),
    ("float_negative_infinity", 0, float_negative_infinity),
    ("float_nan", 0, float_nan),
    // WI-884 — the sibling audit: `Int64`'s BOUNDS and `String`'s search / edit
    // surface, dead in exactly the shape WI-881 found on `Float`. See the two
    // section headers above their definitions for the semantics each one commits
    // to (the index unit, and the empty pattern).
    ("int_min_value", 0, int_min_value),
    ("int_max_value", 0, int_max_value),
    ("string_is_empty", 1, string_is_empty),
    ("string_contains", 2, string_contains),
    ("string_index_of", 2, string_index_of),
    ("string_replace", 3, string_replace),
    ("string_trim", 1, string_trim),
    ("string_split", 2, string_split),
    // WI-931 — PERSISTENCE (proposal 007), the first entries here that are keyed
    // to a SPEC rather than to a scalar carrier. Each takes the store as its
    // first argument and resolves THAT VALUE to its registered mirror, so one
    // host function serves every backend and there is no per-carrier function to
    // name; `rustland/anthill-stl/anthill/persistence.anthill` says why that is
    // not the spec-op registration WI-876 removed. Before WI-931 these six were
    // registered by hardcoded qualified name above, invisible to every load-time
    // reader of "is this operation backed".
    ("store_persist", 3, persistence_persist),
    ("store_flush", 2, persistence_flush),
    ("store_monotonicity", 2, persistence_monotonicity),
    ("store_retract", 2, persistence_retract),
    ("store_update", 3, persistence_update),
    ("store_retrieve", 2, persistence_retrieve),
];

fn host_fn_by_key(key: &str) -> Option<HostFn> {
    HOST_FNS
        .iter()
        .find(|&&(k, _, _)| k == key)
        .map(|&(_, arity, f)| HostFn { arity, f })
}

/// WI-876 — a host function this runtime exposes, with the ARITY it accepts.
///
/// The arity is carried because the registry is CLOSED, so it is known here and
/// nowhere else — and without it a mapping may bind an operation to a host function
/// that cannot take its arguments. MEASURED: `operation squish(a: Widget) -> Int64`
/// mapped to `"ordered_compare"` (which is `expect_args::<2>`) loaded clean, passed
/// `anthill check`, and died `ArityMismatch { expected: 2, got: 1 }` on the first
/// call — a load-time claim of backing that does not imply the operation runs, which
/// is the very defect class this ticket exists to close, one level down.
#[derive(Clone, Copy)]
struct HostFn {
    arity: usize,
    f: fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>,
}

/// WI-876 — register the per-carrier host implementations named by every loaded
/// `operation_map` clause, read from the `anthill.realization.OperationMapping`
/// facts the loader emits.
///
/// LOUD ON BOTH FAILURE MODES, per the repo's no-silent-skip rule — a mapping that
/// registers nothing is invisible until the operation is called, and then it
/// misreports as a missing implementation rather than as the broken binding it is:
///   * an unknown `host_fn` key → [`EvalError::Internal`] naming the key;
///   * a `<carrier>.<operation>` that does not resolve → the carrier did not
///     DECLARE the operation, so nothing could ever dispatch to the registration.
/// This is the reader that CAN complain; `build_host_op_mappings`, which caches the
/// mappings, deliberately does not.
///
/// Mappings for another host language are skipped — a `provides X language cpp`
/// block names cpp functions, which this runtime is right not to know.
fn register_operation_mappings(interp: &mut Interpreter) -> Result<(), EvalError> {
    // Snapshot the cache before registering — `register_builtin_sym` mutates the
    // interpreter. `kb.host_op_mappings()` is built once at load; this function runs
    // for every fresh interpreter, including the one `run_in_bridge_interp` builds
    // per bridged evaluation, so it must not re-walk the facts.
    let mappings: Vec<crate::kb::load::HostOperationMapping> = interp
        .kb()
        .host_op_mappings()
        .iter()
        // WI-886 — the SAME constant `KnowledgeBase::is_interpreter_mapped_op`'s index
        // is built from. That predicate promises this pass registered the operation, so
        // the two filters must be one string.
        .filter(|m| m.lang == crate::kb::load::INTERPRETER_LANG)
        .cloned()
        .collect();
    for crate::kb::load::HostOperationMapping { op, op_qn, host_fn, .. } in mappings {
        let Some(host) = host_fn_by_key(&host_fn) else {
            // Loud, and it stops the whole interpreter — including the short-lived one
            // the resolver builds per bridged evaluation, so an unrelated `[simp]` fire
            // or `eq` dispatch reports this too. That breadth is deliberate: a binding
            // block naming a function the runtime does not have is broken for the whole
            // program, not for one call. The message says so, because the site it
            // surfaces at will often have nothing to do with the mapping.
            return Err(EvalError::Internal(format!(
                "broken binding block: operation_map names host function {host_fn:?} for \
                 {op_qn}, which the rust runtime does not provide. No interpreter can be \
                 built for this program until the binding is fixed — this error may \
                 surface at a call that has nothing to do with {op_qn}."
            )));
        };
        // `op` is `None` only when the loader already refused this mapping (the
        // operation is undeclared, or is not an operation at all), so the load errored
        // and nothing should be registered against it.
        let Some(sym) = op else { continue };
        // The declared operation and the host function must AGREE ON ARITY. Checked
        // at registration, which is the earliest point that knows both: the loader
        // knows the operation's arity but not another language's function set, and
        // this registry is the only thing that knows the host's.
        //
        // Off the CACHED signature (WI-656) rather than `lookup_operation_info`, whose
        // record build clones every per-field `Vec` to be dropped after one `.len()` —
        // the same reason `operation_is_declared` exists beside it. This runs per
        // mapping for every fresh interpreter, including the short-lived one
        // `run_in_bridge_interp` builds per bridged evaluation; the fact-scan fallback
        // is kept for a KB whose signatures are not built yet, where the old reader
        // would still have answered. WI-886 moved both tiers behind `declared_arity`,
        // so cpp-gen's peer check of the same mappings asks the same question the same
        // way — `op_record` being `pub(crate)`, it could not before.
        let declared = crate::kb::op_info::declared_arity(interp.kb(), sym);
        if let Some(n) = declared {
            if n != host.arity {
                return Err(EvalError::Internal(format!(
                    "operation_map maps {op_qn} to {host_fn:?}, but {op_qn} takes {n} \
                     argument(s) and {host_fn:?} takes {}",
                    host.arity
                )));
            }
        }
        // Under BOTH spellings, matching `set_host_op_mappings`' index: a qualified
        // name can be interned under several `Symbol`s, and eval's builtin lookup is a
        // RAW map hit, so whichever spelling reaches dispatch must find the same
        // implementation the predicate promised.
        let canon = interp.kb().canonical_sym(sym);
        interp.register_builtin_sym(sym, host.f);
        if canon != sym {
            interp.register_builtin_sym(canon, host.f);
        }
    }
    Ok(())
}

/// WI-889 — register the per-carrier host VALUE SOURCES named by every loaded
/// `const_map` clause, read from the `anthill.realization.ConstMapping` facts the
/// loader emits. The const-level peer of [`register_operation_mappings`], and it
/// replaces the three hardcoded `register_if_present("anthill.prelude.Float.infinity",
/// …)` lines: the Float IEEE specials now reach eval as DATA, like `pi`/`e`/`tau`.
///
/// LOUD ON BOTH FAILURE MODES, per the repo's no-silent-skip rule, exactly as its
/// operation peer is: an unknown `host_fn` key is an [`EvalError::Internal`] naming the
/// key; a `<carrier>.<const>` the loader already refused (undeclared, or not a const)
/// arrives with `const_sym == None` and registers nothing.
///
/// The function is stored against the const's symbol in the SAME builtin map
/// `force_const` reads (`self.builtins.get(&sym)`), so first demand of the const
/// fetches the host value and caches it — the behavior WI-532 gave these three, now
/// reached by data instead of a hardcoded qualified name.
fn register_const_mappings(interp: &mut Interpreter) -> Result<(), EvalError> {
    // Snapshot the cache before registering — `register_builtin_sym` mutates the
    // interpreter — matching `register_operation_mappings`.
    let mappings: Vec<crate::kb::load::HostConstMapping> = interp
        .kb()
        .host_const_mappings()
        .iter()
        // Only this runtime's language: a cpp `const_map` names a C++ expression, which
        // this runtime is right not to know. Same split as the operation peer.
        .filter(|m| m.lang == crate::kb::load::INTERPRETER_LANG)
        .cloned()
        .collect();
    for crate::kb::load::HostConstMapping { const_sym, const_qn, host_fn, .. } in mappings {
        let Some(host) = host_fn_by_key(&host_fn) else {
            return Err(EvalError::Internal(format!(
                "broken binding block: const_map names host value {host_fn:?} for \
                 {const_qn}, which the rust runtime does not provide. No interpreter can \
                 be built for this program until the binding is fixed."
            )));
        };
        // `const_sym` is `None` only when the loader already refused this mapping (the
        // const is undeclared, or is not a const at all), so the load errored and
        // nothing should be registered against it.
        let Some(sym) = const_sym else { continue };
        // A const's value source is NULLARY — `force_const` invokes it with no args. A
        // host_fn that takes arguments cannot be one; caught here, the earliest point
        // that knows the host function's arity. (The peer check for operations lives in
        // `register_operation_mappings`; here the operation-side "declared arity" is
        // fixed at zero because a const takes none.)
        if host.arity != 0 {
            return Err(EvalError::Internal(format!(
                "const_map maps {const_qn} to {host_fn:?}, but a const's value source \
                 must be NULLARY and {host_fn:?} takes {} argument(s)",
                host.arity
            )));
        }
        // Under BOTH spellings, for the same reason the operation peer does it: eval's
        // const lookup is a RAW `Symbol` map hit, so whichever spelling `force_const`
        // reaches must find the registration.
        let canon = interp.kb().canonical_sym(sym);
        interp.register_builtin_sym(sym, host.f);
        if canon != sym {
            interp.register_builtin_sym(canon, host.f);
        }
    }
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
                let full = interp.kb().local_name_of(*sym);
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
                        let full = interp.kb().local_name_of(*f);
                        full.rsplit('.').next().unwrap_or(full).to_string()
                    };
                    // A field supplied by name (matched above) consumes no `pos` slot.
                    let supplied_by_name = named.iter().any(|(s, _)| {
                        let nf = interp.kb().local_name_of(*s);
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
        // WI-803: the named scan and the WI-790 `_N` fallback both moved into
        // `TupleComponents::by_label`, which is now the ONE owner of "read a tuple
        // component by name" — shared with `match_tuple_pattern`, whose by-label
        // destructuring must resolve a label exactly as `t.x` does or the relation
        // and the reader diverge again (WI-800, WI-805).
        Value::Tuple { .. } => receiver
            .tuple_components()
            .and_then(|c| c.by_label(interp.kb(), field_name.as_str()))
            .cloned()
            .ok_or_else(|| EvalError::Internal(format!(
                "field_access: tuple has no component '{}'", field_name))),
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

// ── Int64 bounds (WI-884) ──────────────────────────────────────
//
// `Int64` declares `minValue()` / `maxValue()` and nothing backed them: both died
// `OperationBodyMissing` on a program that loaded clean, the only two of the sort's
// eighteen declared operations that were dead. The carrier is `i64`, so the bounds
// are its ends and there is nothing to settle here; why they are host-backed rather
// than stated as equations is argued on the declarations in
// `stdlib/anthill/prelude/int64.anthill`.

/// Nullary host constants, over any `Value` constructor: `Int64`'s two bounds here,
/// and `Float`'s mathematical constants plus the IEEE specials below. One macro rather
/// than one per value type — the constructor is the only thing that differed.
macro_rules! nullary_const {
    ($ctor:path; $($fname:ident($op:literal) = $v:expr;)+) => { $(
        fn $fname(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
            let [] = expect_args::<0>($op, args)?;
            Ok($ctor($v))
        }
    )+ };
}

nullary_const! { Value::Int;
    int_min_value("Int64.minValue") = i64::MIN;
    int_max_value("Int64.maxValue") = i64::MAX;
}

// ── Eq / Ord ───────────────────────────────────────────────

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
                    Ok(crate::kb::resolve::BridgeEqOutcome::Decided(v)) => Ok(v),
                    // UNDECIDED (re-entry cap / a bridge-mode suspend inside the
                    // op): in bridge mode SUSPEND so the resolver residualizes; at
                    // top level surface loudly. An APPLICABLE override that could
                    // not be decided must NOT masquerade as a structural `false`
                    // (that would report equal values unequal — Finding 1). This
                    // mirrors the rule-backed branch below. WI-628: THREAD the
                    // `truncated` bit onto the Suspend so a nested truncation
                    // reaching `bridge_eq_op_to_eval` one level up is propagated to
                    // the outer stream, not read as a mere flounder.
                    Ok(crate::kb::resolve::BridgeEqOutcome::Undecided { truncated }) => {
                        let detail = format!(
                            "instance-fact eq over `{}` could not be decided",
                            i.kb().local_name_of(target),
                        );
                        Err(if i.bridge_mode() {
                            EvalError::Suspended { detail, truncated }
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
                // budget, or a floundered sub-proof (the resolver maps the same
                // cases to a truncated / plain `Delay`). Under the resolver→eval
                // bridge (WI-625 gap 1) SUSPEND so the resolver delays; top-level
                // eval has nowhere to suspend to, so it stays a loud error rather
                // than guessing a structural answer. WI-628: THREAD `truncated` onto
                // the Suspend so a genuine depth-truncation propagates through the
                // bridge to the outer stream (a nested `List.member`-style inner eq).
                crate::kb::resolve::PredicateProof::Undecided { truncated } => {
                    let detail = format!(
                        "semantic eq over `{}` could not be decided (proof truncated)",
                        i.kb().local_name_of(target)
                    );
                    Err(if i.bridge_mode() {
                        EvalError::Suspended { detail, truncated }
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
            // A buried override is a flounder (a symbolic operand), not truncation.
            truncated: false,
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
///
/// WI-876 — THE `Float` ARM IS DELIBERATE AND STAYS, though `ordered_gt` & co. no
/// longer guard against reaching it (the `float_pair` test they used to carry moved
/// out to `Float`'s own `float_gt`/`lte`/… , named in its binding). The two families
/// are now selected by the CARRIER, and each is right for the carriers that name it:
/// `ordered_*` is the TOTAL comparison — which for a float-valued TOTAL carrier (the
/// `TotalFloat` shape) must be `total_cmp`, since that is the only float order with
/// transitivity — and `float_*` is IEEE, for the carrier whose order is partial.
/// Deleting this arm would leave a would-be total float carrier with no sound
/// comparison at all; the thing that must not happen is a carrier naming the WRONG
/// family, and that is now a visible line in its `operation_map` rather than a branch
/// buried here.
fn value_compare(a: &Value, b: &Value) -> Result<std::cmp::Ordering, EvalError> {
    Ok(match (a, b) {
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::BigInt(x), Value::BigInt(y)) => x.cmp(y),
        (Value::Float(x), Value::Float(y)) => x.total_cmp(y),
        (Value::Bool(x), Value::Bool(y)) => x.cmp(y),
        (Value::Str(x), Value::Str(y)) => x.cmp(y),
        _ => return Err(EvalError::TypeMismatch {
            expected: "Ord scalars of matching type",
            got: format!("{} and {}", a.type_name(), b.type_name()),
        }),
    })
}

fn ordered_compare(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("compare", args)?;
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
/// fix. The TOTAL `Ord` ops keep `total_cmp` — they are only sound on a total
/// carrier (`TotalFloat`, not raw `Float`).
///
/// WI-876 — these four are `Float`'s OWN host implementations, named by
/// `float.anthill`'s `operation_map`, rather than a `float_pair` test inside the
/// total comparisons. Before, one spec-op registration had to serve both carriers,
/// so "Float's order is IEEE" was a branch buried in shared code; now it is a fact
/// in `Float`'s binding, where the reader looks. Errors on a non-`Float` pair
/// because nothing else can reach them.
fn float_operands(i: &Interpreter, a: &Value, b: &Value) -> Result<(f64, f64), EvalError> {
    match (float_val(i, a), float_val(i, b)) {
        (Some(x), Some(y)) => Ok((x, y)),
        _ => Err(EvalError::TypeMismatch {
            expected: "Float operands",
            got: format!("{} and {}", a.type_name(), b.type_name()),
        }),
    }
}

fn float_gt(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Float.gt", args)?;
    let (x, y) = float_operands(i, &a, &b)?;
    Ok(Value::Bool(x > y))
}

fn float_gte(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Float.gte", args)?;
    let (x, y) = float_operands(i, &a, &b)?;
    Ok(Value::Bool(x >= y))
}

fn float_lt(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Float.lt", args)?;
    let (x, y) = float_operands(i, &a, &b)?;
    Ok(Value::Bool(x < y))
}

fn float_lte(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Float.lte", args)?;
    let (x, y) = float_operands(i, &a, &b)?;
    Ok(Value::Bool(x <= y))
}

fn ordered_gt(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("gt", args)?;
    Ok(Value::Bool(matches!(value_compare(&a, &b)?, std::cmp::Ordering::Greater)))
}

fn ordered_gte(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("gte", args)?;
    Ok(Value::Bool(!matches!(value_compare(&a, &b)?, std::cmp::Ordering::Less)))
}

fn ordered_lt(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("lt", args)?;
    Ok(Value::Bool(matches!(value_compare(&a, &b)?, std::cmp::Ordering::Less)))
}

fn ordered_lte(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("lte", args)?;
    Ok(Value::Bool(!matches!(value_compare(&a, &b)?, std::cmp::Ordering::Greater)))
}

/// `Ord.max`/`min` on a total scalar carrier. `Ord` derives both from
/// `gte`/`lte` by default body, which is what a STRUCTURAL carrier gets — but for a
/// scalar that derivation costs an interpreter frame and a dictionary dispatch where
/// the host answers in one call, so the total carriers map these too. Same reasoning
/// as `gt`/`gte`/`lt`/`lte`, and leaving them out made the surface inconsistent:
/// four of the six keyed to the host and two not.
fn ordered_max(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("max", args)?;
    match value_compare(&a, &b)? {
        std::cmp::Ordering::Less => Ok(b),
        _ => Ok(a),
    }
}

fn ordered_min(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("min", args)?;
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

// ── Float IEEE arithmetic (WI-881) ─────────────────────────────
//
// `Float`'s arithmetic surface, one host function per operation the sort declares,
// keyed per carrier through `float.anthill`'s `operation_map` (WI-876's channel).
// Before this existed the sort declared 32 operations and 8 ran; the other 24 died
// `OperationBodyMissing` on a program that loaded clean, because a host carrier is
// exempt from the load-time backing check wholesale (`check_provider_operations`;
// narrowing that is WI-880).
//
// WHY THE HOST AND NOT A LAW. `float.anthill` states four of them as equations, and
// two of those ARE the definition and are now `[simp]`-tagged so they run as one
// (`recip`, `tau` — see that file). The two here are NOT, and the reason is the same
// both times: IEEE arithmetic distinguishes `+0.0` from `-0.0` while every COMPARISON
// reads them equal, so no ordering- or arithmetic-over-zero law pins the sign bit.
//   * `neg(?a) = sub(0.0, ?a)` is FALSE at `?a = 0.0` — `neg(0.0)` is `-0.0`,
//     `0.0 - 0.0` is `+0.0`, and `recip` tells them apart (`-inf` vs `+inf`).
//   * `abs(?a) = max(?a, neg(?a))` is worse than false, it is UNDEFINED at ±0.0:
//     `f64::max` documents that it may return EITHER input when they compare equal.
// Both are `f64` intrinsics that clear or flip the sign bit directly, and that is
// what the operation means.

/// The single `f64` operand of a unary `Float` host function — [`float_operands`]'
/// arity-1 peer. Reads through the same [`float_val`], so a `Value::Term`-wrapped
/// literal (a reflected / stored-structure operand) is accepted exactly where the
/// comparisons accept one.
fn float_operand(i: &Interpreter, a: &Value) -> Result<f64, EvalError> {
    float_val(i, a).ok_or_else(|| type_mismatch("Float", a, None))
}

/// `Float -> Int64` for `floor` / `ceil` / `round`, which is where the two carriers
/// stop lining up: `f64` has NaN, ±Infinity, and a range far past `i64`, and `as i64`
/// SATURATES them silently (`floor(nan)` would answer `0`, `floor(1e300)` would answer
/// `i64::MAX`). A saturated answer is a wrong answer that looks like a right one, so
/// the out-of-domain operand raises instead — the repo's loud-error rule.
///
/// These three are therefore PARTIAL, which their declarations do not yet say; giving
/// them a guarded `Error` effect row is exactly WI-882's shape and is noted there.
///
/// `Overflow` is this file's variant for "the result cannot be represented in the
/// target" — `String.repeat` already uses it that way, not only for integer
/// arithmetic. Its Display sentence ("integer overflow") is correspondingly loose for
/// a NaN operand; that wording is shared with the arithmetic sites, where it is exact.
fn float_as_int64(op: &'static str, rounded: f64) -> Result<Value, EvalError> {
    // `i64::MIN as f64` is exact (-2^63) and its negation is the first f64 ABOVE the
    // i64 range, so the domain is the HALF-OPEN `[lo, -lo)`. `contains` is false for
    // NaN, which lands in the same arm.
    let lo = i64::MIN as f64;
    if (lo..-lo).contains(&rounded) {
        Ok(Value::Int(rounded as i64))
    } else {
        Err(EvalError::Overflow { op })
    }
}

/// Unary `Float -> Float`. One arm per `f64` intrinsic; the shape is identical and the
/// macro keeps the family aligned and grep-able, as `effect_dispatcher!` does below.
///
/// The `fn(f64) -> f64` annotation is the macro's CONTRACT, not decoration: it makes a
/// wrong-shaped intrinsic a type error at the entry line rather than an arity error
/// inside the expansion — `f64::log` is base-`b` and takes TWO arguments, which is the
/// hazard the `float_log` entry's comment flags.
macro_rules! float_unary {
    ($($fname:ident($op:literal) = $f:expr;)+) => { $(
        fn $fname(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
            let [a] = expect_args::<1>($op, args)?;
            let g: fn(f64) -> f64 = $f;
            Ok(Value::Float(g(float_operand(i, &a)?)))
        }
    )+ };
}

/// Binary `Float -> Float -> Float`.
macro_rules! float_binary {
    ($($fname:ident($op:literal) = $f:expr;)+) => { $(
        fn $fname(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
            let [a, b] = expect_args::<2>($op, args)?;
            let (x, y) = float_operands(i, &a, &b)?;
            let g: fn(f64, f64) -> f64 = $f;
            Ok(Value::Float(g(x, y)))
        }
    )+ };
}

/// Unary `Float -> Int64`, through [`float_as_int64`]'s domain check.
macro_rules! float_rounding {
    ($($fname:ident($op:literal) = $f:expr;)+) => { $(
        fn $fname(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
            let [a] = expect_args::<1>($op, args)?;
            let g: fn(f64) -> f64 = $f;
            float_as_int64($op, g(float_operand(i, &a)?))
        }
    )+ };
}

float_unary! {
    float_abs("Float.abs")     = f64::abs;
    float_neg("Float.neg")     = |x| -x;
    float_sqrt("Float.sqrt")   = f64::sqrt;   // NaN for a negative operand (IEEE)
    float_sin("Float.sin")     = f64::sin;
    float_cos("Float.cos")     = f64::cos;
    float_tan("Float.tan")     = f64::tan;
    float_asin("Float.asin")   = f64::asin;
    float_acos("Float.acos")   = f64::acos;
    float_atan("Float.atan")   = f64::atan;
    float_exp("Float.exp")     = f64::exp;
    float_log("Float.log")     = f64::ln;     // NATURAL log — `f64::log` is base-b
    float_log10("Float.log10") = f64::log10;
    float_log2("Float.log2")   = f64::log2;
}

float_binary! {
    float_hypot("Float.hypot") = f64::hypot;
    float_fmod("Float.fmod")   = |x, y| x % y;  // C fmod: the sign follows the dividend
    float_pow("Float.pow")     = f64::powf;
    float_atan2("Float.atan2") = f64::atan2;
    // IEEE-754 maxNum/minNum: they ABSORB NaN (`max(nan, 1.0) = 1.0`) and are
    // commutative, which a `gte`-derived max is not — MEASURED before this ticket,
    // the derived one answers `1.0` on `(nan, 1.0)` and `nan` on `(1.0, nan)`. That
    // asymmetry is why `Float` exposes the IEEE pair rather than inheriting
    // `Ord`'s derivation, which it could not reach anyway (`Float` provides
    // `PartialOrd`, not `Ord` — so until this ticket there was NO way to take
    // the maximum of two floats at all).
    float_max("Float.max")     = f64::max;
    float_min("Float.min")     = f64::min;
}

float_rounding! {
    float_floor("Float.floor") = f64::floor;
    float_ceil("Float.ceil")   = f64::ceil;
    float_round("Float.round") = f64::round;  // half away from zero
}

// BOTH kinds of host-supplied float value go through [`nullary_const`]: the
// mathematical constants, which are nullary OPERATIONS reaching eval through
// `operation_map`, and the IEEE specials, which are term-level `const`s reaching it
// through the hardcoded registration list (`force_const` invokes those with no args).
// The two differ only in how they are registered — the function is the same shape.
nullary_const! { Value::Float;
    float_pi("Float.pi") = std::f64::consts::PI;
    float_e("Float.e")   = std::f64::consts::E;
    // `tau`'s equation `tau() <=> mul(2.0, pi())` is EXACT (doubling only increments
    // a binary exponent), so it could have been a `[simp]` definition like `recip`'s
    // — and it was, until driving found what inlining cannot do. A `[simp]` head is an
    // APPLICATION; a BARE nullary call site is a `var_ref`, so nothing matches it and
    // `tau` written without parentheses stayed dead while `pi` and `e` — dispatched,
    // not inlined — answered. Three constants of one family must behave alike, so the
    // equation stays as a (true) specification and the host backs the operation.
    float_tau("Float.tau") = std::f64::consts::TAU;

    // The IEEE specials (WI-532): value sources for the bodyless
    // `const infinity/negativeInfinity/nan: Float` declared in stdlib float.anthill.
    // Registered by qualified name, not by `operation_map` — a `const` is not an
    // operation — but the function is the same nullary shape as the three above.
    float_infinity("Float.infinity")                 = f64::INFINITY;
    float_negative_infinity("Float.negativeInfinity") = f64::NEG_INFINITY;
    float_nan("Float.nan")                           = f64::NAN;
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
    // Unicode scalar count to match `anthill.prelude.String.length`'s
    // declared character-level semantics (the prelude's rules refer to
    // `length("") = 0`, which is unambiguous either way, but Unicode is
    // the natural choice for user-facing length).
    Ok(Value::Int(str_operand(&a)?.chars().count() as i64))
}

/// `String.isEmpty` — `str::is_empty`, NOT `length(s) == 0`. The two always agree (a
/// UTF-8 sequence has zero bytes exactly when it has zero scalars) but not on COST:
/// `String.length` counts UNICODE SCALARS (WI-884), so [`string_length`] is O(n).
/// Why the operation is host-backed at all: `rustland/anthill-stl/anthill/string.anthill`.
///
/// BORROWS its argument instead of taking [`expect_args`], which is
/// `std::array::from_fn(|i| args[i].clone())` — and `Value::Str` owns its `String`, so
/// the uniform helper would malloc-and-memcpy the whole subject before the O(1) test
/// ran, leaving this function Θ(|s|) and its reason for existing unfulfilled. Every
/// other string builtin does O(n) work anyway, so there the clone is a constant factor
/// and the uniform shape is right; this is the one where the clone IS the cost. The
/// borrowing arity check is [`error_raise`]'s.
fn string_is_empty(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = args else {
        return Err(EvalError::ArityMismatch { op: "String.isEmpty", expected: 1, got: args.len() });
    };
    Ok(Value::Bool(str_operand(a)?.is_empty()))
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
    Ok(Value::Str(str_operand(&a)?.to_uppercase()))
}

fn string_to_lower(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("String.toLower", args)?;
    Ok(Value::Str(str_operand(&a)?.to_lowercase()))
}

// substring(s, start, end) — character-indexed half-open range, matching
// String.length's Unicode-scalar semantics. Negative or out-of-range indices
// clamp to the string's bounds; reversed ranges produce the empty string.
fn string_substring(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, start, end] = expect_args::<3>("String.substring", args)?;
    let s = str_operand(&s)?.to_string();
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
    let s = str_operand(&s)?.to_string();
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

// ── String search / edit (WI-884) ──────────────────────────────
//
// Five of `String`'s twenty-two declared operations were backed by nothing and died
// `OperationBodyMissing` on a program that loaded clean — WI-881's defect one sort
// over. They are keyed per carrier through `string.anthill`'s `operation_map`
// (WI-876's channel), which is also what checks their arity against the declaration.
//
// WHAT EACH ONE MEANS IS NOT WRITTEN HERE. The index unit, what the empty pattern
// does, which whitespace `trim` takes and why `split` keeps its empty pieces are the
// OPERATIONS' contract, and they are argued on the declarations in
// `stdlib/anthill/prelude/string.anthill`, which is where a reader of the library
// looks and where a second backend has to read them from. This module states only
// what is true of THIS host: which `str` primitive backs each operation, and where
// that primitive's behaviour has to be adjusted to meet the declared contract. There
// is exactly one such adjustment, in `string_index_of`.

/// The `&str` behind a `String` operand — [`float_operand`]'s peer, and the same
/// accessor-plus-[`type_mismatch`] shape `string_substring` and `string_repeat`
/// already use for their `Int64` arguments (`as_int().ok_or_else(…)`).
///
/// The single-operand String builtins that predate this ticket are routed through it
/// too. The three BINARY ones are not: they report `type_mismatch(…, Some(&b))`, which
/// names both operands, and narrowing that message to one is a change to a diagnostic
/// rather than a deduplication.
fn str_operand(v: &Value) -> Result<&str, EvalError> {
    v.as_str().ok_or_else(|| type_mismatch("String", v, None))
}

fn string_contains(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, sub] = expect_args::<2>("String.contains", args)?;
    Ok(Value::Bool(str_operand(&s)?.contains(str_operand(&sub)?)))
}

/// THE ONE PLACE THE HOST PRIMITIVE DISAGREES WITH THE DECLARATION: `str::find`
/// answers in BYTES and `indexOf` is declared in Unicode scalars (see
/// `string.anthill`, which argues the unit and drives the round trip that pins it).
/// The byte offset is converted by counting the characters before it — `find`'s answer
/// is always on a character boundary, so the prefix slice is exact. `-1` when absent.
fn string_index_of(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, sub] = expect_args::<2>("String.indexOf", args)?;
    let (s, sub) = (str_operand(&s)?, str_operand(&sub)?);
    Ok(Value::Int(match s.find(sub) {
        Some(byte) => s[..byte].chars().count() as i64,
        None => -1,
    }))
}

/// `str::replace` — every non-overlapping occurrence, left to right, which is what
/// the declaration specifies.
fn string_replace(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, old, new] = expect_args::<3>("String.replace", args)?;
    let (s, old, new) = (str_operand(&s)?, str_operand(&old)?, str_operand(&new)?);
    Ok(Value::Str(s.replace(old, new)))
}

/// `str::trim`, whose whitespace set is the Unicode `White_Space` property — the
/// declaration says Unicode and not the ASCII subset, so this is `trim` and not
/// `trim_ascii`.
fn string_trim(_i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("String.trim", args)?;
    Ok(Value::Str(str_operand(&s)?.trim().to_string()))
}

/// `str::split`, which keeps the empty pieces the declaration requires.
///
/// The one host function here that BUILDS a structured value rather than a scalar;
/// `bigint_to_int` (which builds an `Option`) is the shape it follows, through the
/// shared [`build_value_list`] so the `cons`/`nil` spine is minted in one place.
fn string_split(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, sep] = expect_args::<2>("String.split", args)?;
    let pieces: Vec<Value> = str_operand(&s)?
        .split(str_operand(&sep)?)
        .map(|p| Value::Str(p.to_string()))
        .collect();
    build_value_list(interp, pieces)
}

// ── LogicalStream / KB.execute ─────────────────────────────────

use crate::eval::stream::StreamSource;

/// `splitFirst(s: LogicalStream[T]) -> Option[Pair[T, LogicalStream[T]]]`.
/// Pumps the stream one step. For a resolver stream the yielded element is a
/// reflect `Solution` (`definite(subst)` / `undecided(subst, residual)`,
/// WI-531); it is passed through opaquely here, wrapped in `Pair` with the
/// continuation (see `Interpreter::stream_split_first`).
///
/// Wrap a pumped stream step as the anthill `Option[Pair[T, Stream]]` value both
/// `splitFirst` builtins return: `none` at end, else `some(pair(fst: value, snd:
/// rest-stream))`. Shared by [`logical_stream_split_first`] and
/// [`relation_split_first`] — the two differ only in how they obtain `pumped`.
fn split_first_result(
    interp: &mut Interpreter,
    pumped: Option<(Value, crate::eval::value::StreamHandle)>,
) -> Result<Value, EvalError> {
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

/// `Relation.splitFirst(r: Relation) -> Option[Pair[A = r.T, B = LogicalStream[T
/// = r.T, E = r.E]]]` — WI-714 (proposal 052). The runtime primitive that makes a
/// `Relation` consumable through `provides LogicalStream`: RUN the relation's
/// query (026.1 `execute_logical_query`), wrap the resolver search in a
/// `MaterializedResolver` over the relation's schema `columns`, and pump ONE
/// solution — materialized onto the free vars as a `T` row (C1
/// `materialize_solution`). The continuation `rest` is a `Value::Stream`, so after
/// the first pull the relation IS an ordinary Stream (the columns ride in the
/// `MaterializedResolver`), and every further `splitFirst`/`head`/`map` goes
/// through `LogicalStream.splitFirst`. Structurally identical to
/// [`logical_stream_split_first`] once the query is run — a runtime op returning a
/// Stream. Empty answer set → `none` (NotFound is the ordinary Stream contract, no
/// bespoke nil arm).
fn relation_split_first(
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("Relation.splitFirst", args)?;
    let (query, columns) = match arg {
        Value::Relation { query, columns } => (query, columns),
        other => return Err(type_mismatch("Relation", &other, None)),
    };
    let search = interp
        .kb
        .execute_logical_query(&query)
        .map_err(|e| EvalError::Internal(format!("Relation.splitFirst execute: {}", e)))?;
    let handle = interp.alloc_stream(StreamSource::MaterializedResolver {
        search: Some(search),
        columns,
    });
    let pumped = interp.stream_split_first(&handle)?;
    split_first_result(interp, pumped)
}

/// `Relation.negate` (WI-714 / proposal 052) — negation-as-failure as a QUERY
/// combinator. Wraps the operand's query in `negation(query: …)` (which the
/// resolver lowers to `not(inner_goals)`) and returns a 0-column membership
/// `Relation` (`Relation[Unit]`): consuming it (e.g. `.isEmpty`) gives an empty
/// stream iff the operand is provable, and a single `unit` iff the operand has NO
/// solution. Combines queries, not streams, so the result stays composable.
fn relation_negate(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("Relation.negate", args)?;
    let (query, columns) = expect_relation(arg)?;
    // Membership guard: negating a relation that still has FREE columns would
    // flounder under NAF (`not p(?x)` with `?x` unbound is undecidable), reading a
    // floundered residual as a spurious solution. Reject it loudly — as a runtime
    // TYPE error (the operand is the wrong shape), NOT an engine-internal error —
    // rather than return a silently-wrong result. `columns` empty ⟺ every head slot
    // is bound, the ground-goal precondition for every relation built from surface
    // code; it is an APPROXIMATION of "the goal atom is ground" — a free logic var
    // supplied as an argument VALUE (constructible only via reflect/metaprogramming,
    // not plain code) is not reflected in `columns` and would slip through. Ideally
    // this is load-time; see the stdlib note on why the signature can't carry the
    // `T = Unit` constraint with `E` open.
    if !columns.is_empty() {
        let names: Vec<String> = columns
            .iter()
            .map(|(s, _)| interp.kb.local_name_of(*s).to_string())
            .collect();
        return Err(EvalError::TypeMismatch {
            expected: "a membership Relation (Relation[Unit]; all columns bound)",
            got: format!(
                "a relation with free column(s): {} — negating it would flounder under \
                 negation-as-failure; close the columns first (bind via application, or project)",
                names.join(", ")
            ),
        });
    }
    // Combine at the QUERY level (shared builder, same one `build_relation_value`
    // uses); `columns` is the operand's already-empty set — reuse it for the result.
    let neg = interp.build_logical_query_value("negation", vec![("query", (*query).clone())])?;
    Ok(Value::Relation { query: std::rc::Rc::new(neg), columns })
}

/// Destructure a `Value::Relation` into `(query, columns)`, or a loud type error.
/// Shared by the relational-algebra builtins (`negate` / `union` / …), which all
/// take `Relation` operands.
type RelationParts =
    (std::rc::Rc<Value>, std::rc::Rc<[(crate::intern::Symbol, crate::kb::term::VarId)]>);
fn expect_relation(v: Value) -> Result<RelationParts, EvalError> {
    match v {
        Value::Relation { query, columns } => Ok((query, columns)),
        other => Err(type_mismatch("Relation", &other, None)),
    }
}

/// Rewrite the free column variables of a relation `query` value (WI-714 `union`)
/// under σ, which maps one operand's column `VarId`s to the other's — so a
/// `disjunction` of two INDEPENDENTLY-built relations binds ONE shared result column
/// set (both `or` branches bind the same vars → materialization is correct). This
/// walks the structural spine (`Value::Entity` — the LogicalQuery constructors and
/// goal atoms) and renames each term leaf via the canonical `apply_subst`, which
/// descends compound terms too — so a column var nested inside a compound goal arg
/// (as a future `where` / `join` → `guarded` / `conjunction` will emit) is renamed,
/// not silently missed. Ground scalar / opaque arg values carry no free column var
/// and pass through; a `Value::Node` occurrence or a value-level `Var` never appears
/// in an eval-built query, so it is surfaced loudly rather than cloned through (which
/// could silently drop a var that must be aligned).
fn rename_query_vars(
    kb: &mut crate::kb::KnowledgeBase,
    v: &Value,
    sigma: &crate::kb::subst::Substitution,
) -> Result<Value, EvalError> {
    match v {
        Value::Entity { functor, pos, named } => {
            let mut pos2 = Vec::with_capacity(pos.len());
            for c in pos.iter() {
                pos2.push(rename_query_vars(kb, c, sigma)?);
            }
            let mut named2 = Vec::with_capacity(named.len());
            for (k, c) in named.iter() {
                named2.push((*k, rename_query_vars(kb, c, sigma)?));
            }
            Ok(Value::Entity { functor: *functor, pos: pos2.into(), named: named2.into() })
        }
        Value::Term { id } => Ok(Value::term(kb.apply_subst(*id, sigma))),
        // A carrier-neutral logic-variable leaf (`Value::Var`, WI-714/WI-348):
        // resolve it through σ — the placeholder→column alignment `where_run` (and
        // `union`) builds — instead of rejecting it. A `Global` column var maps to
        // its σ-image (`resolve_as_value`); a var σ does not bind, or a
        // `DeBruijn`/`Rigid` (no query σ touches those), rides through unchanged.
        // This is what makes `rename_query_vars` genuinely carrier-neutral rather
        // than assuming a var only ever rides interned inside a `Value::Term`.
        Value::Var(crate::kb::term::Var::Global(vid)) => Ok(match sigma.resolve_as_value(*vid) {
            Some(bound) => bound.clone(),
            None => v.clone(),
        }),
        Value::Var(_) => Ok(v.clone()),
        // A `Value::Node` occurrence never appears in an eval-built query; if one
        // does, surface it loudly rather than silently cloning a var that must align.
        Value::Node(_) => Err(EvalError::Internal(format!(
            "relation query alignment: unexpected {} carrier in a relation query",
            v.type_name()
        ))),
        _ => Ok(v.clone()),
    }
}

/// `Relation.union` (WI-714 / proposal 052) — the bag union of two relations as a
/// QUERY combinator. Builds `disjunction(left: a.query, right: b.query)` — a new
/// LogicalQuery (the resolver lowers it to `or(...)`) — so the result stays a
/// composable Relation. The operands' independently-minted column variables are
/// aligned (b's rewritten to a's via σ) so both `or` branches bind the ONE result
/// column set; without that a right-branch solution would leave a's columns unbound.
/// Combines queries, not streams.
fn relation_union(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Relation.union", args)?;
    let (qa, cols_a) = expect_relation(a)?;
    let (qb, cols_b) = expect_relation(b)?;
    // Same-schema requirement. The typer normally rejects a mismatch at LOAD — union's
    // two `Relation` params share the sort's `T`, so `Relation[String]` ∪
    // `Relation[Int64]` binds `T` inconsistently (op-type-params tie). This runtime
    // arity check is the REACHABLE backstop for the T-collapse corner the type sees as
    // consistent: a 0-column `Relation[Unit]` vs a 1-column relation over a `Unit`
    // column, or a 1-column relation whose element is a tuple vs the matching 2-column
    // relation — and for a relation built past the typer (reflect). A loud error, never
    // a silent misalignment (the length-mismatched `zip` below would drop columns).
    if cols_a.len() != cols_b.len() {
        return Err(EvalError::TypeMismatch {
            expected: "two relations with the same schema (union)",
            got: format!(
                "relations of differing arity: {} column(s) vs {} column(s)",
                cols_a.len(),
                cols_b.len()
            ),
        });
    }
    // σ maps b's column vars to a's (positionally); `apply_subst` (in the walker) then
    // rewrites them in b's query so both disjunction branches bind the SAME result
    // columns (a's).
    let mut sigma = crate::kb::subst::Substitution::new();
    for ((_, vb), (_, va)) in cols_b.iter().zip(cols_a.iter()) {
        let va_term = interp.kb.alloc(crate::kb::term::Term::Var(crate::kb::term::Var::Global(*va)));
        sigma.bind(&interp.kb, *vb, va_term);
    }
    let qb_aligned = rename_query_vars(&mut interp.kb, &qb, &sigma)?;
    let disj = interp.build_logical_query_value(
        "disjunction",
        vec![("left", (*qa).clone()), ("right", qb_aligned)],
    )?;
    Ok(Value::Relation { query: std::rc::Rc::new(disj), columns: cols_a })
}

/// `Relation.where_run` (WI-714 / proposal 052) — the RUNTIME back-end of `where`.
/// The `guarded_of` macro has already compiled the row lambda into `cond`, a
/// `LogicalQuery` recipe whose column references are HOLES: `Var::Global` variables
/// named by the schema field symbol (`c.x` → a var named `x`). Fill each hole with
/// `r`'s real column variable of that name and CONJOIN the filled condition onto
/// `r`'s query — a new LogicalQuery, so the result stays a composable Relation over
/// `r`'s UNCHANGED schema. Same query-combining shape as `negate`/`union`; the
/// hole-fill is the `where`-specific seam.
///
/// `conjunction(left: r.query, right: <condition>)` rather than `guarded(query,
/// condition)`: a `guarded`'s condition is a single goal LEAF, which is all the atomic
/// first increment produced. A WI-730 condition is a query TREE (the `&&`/`||`/`!`
/// spine maps onto conjunction/disjunction/negation), so it composes at the QUERY
/// level. The two coincide on that atomic case — `conjunction(q, pattern_query(a))`
/// and `guarded(q, a)` both lower to `lower(q) ++ [a]` (kb/execute.rs) — so this is
/// the same query it always built, generalized. `left` FIRST is load-bearing: the
/// lowered goal list keeps `r`'s goals ahead of the condition, so every column is
/// BOUND before a guard reads it — which is what keeps a `!` (negation-as-failure)
/// from floundering on a free column variable.
fn relation_where_run(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r, cond] = expect_args::<2>("Relation.where_run", args)?;
    let (query, columns) = expect_relation(r)?;
    // The whole-row sentinel symbol (if `compile_operand` ever minted one) — resolved
    // ONCE here, not per `Var::Global` node in the recipe walk.
    let whole_row = interp.kb.lookup_symbol(WHOLE_ROW_HOLE);
    let condition = fill_column_holes(&interp.kb, &cond, &columns, whole_row)?;
    let filtered = interp.build_logical_query_value(
        "conjunction",
        vec![("left", (*query).clone()), ("right", condition)],
    )?;
    Ok(Value::Relation { query: std::rc::Rc::new(filtered), columns })
}

/// Reserved hole name for a bare-binder (WHOLE-ROW) reference `c` in a `where`
/// condition over a 1-collapse (single-column) relation — `eq(c, 30)`. `where_run`
/// maps it to the relation's sole column. A dunder name that cannot clash with a user
/// field (column names are head-variable names, never dunders).
const WHOLE_ROW_HOLE: &str = "__anthill_where_whole_row__";

/// Replace each column HOLE in a `LogicalQuery` recipe `Value` — a `Var::Global`
/// variable whose NAME is a schema field symbol (`guarded_of` mints it from `c.x`) —
/// with `r`'s real column variable of that name (WI-714 `where_run`). The walk is over
/// the whole recipe, so it reaches the atoms nested under a WI-730 `&&`/`||`/`!` spine
/// exactly as it reached the lone atom of the first increment. Matching is by the
/// interned field/column `Symbol`: the SAME symbol names the lambda's field access
/// and the relation's column, so this is exact canonical equality, NOT a
/// cross-scope short-name compare (WI-672). Every `Var::Global` in a `guarded_of`
/// goal is a column hole (the translation introduces vars only for columns), so a
/// hole naming no column — or a `Value::Node` occurrence, which never appears in an
/// eval-built goal — is a loud error, never a silent drop.
fn fill_column_holes(
    kb: &crate::kb::KnowledgeBase,
    v: &Value,
    columns: &[(crate::intern::Symbol, crate::kb::term::VarId)],
    whole_row: Option<crate::intern::Symbol>,
) -> Result<Value, EvalError> {
    use crate::kb::term::Var;
    match v {
        Value::Entity { functor, pos, named } => {
            let mut pos2 = Vec::with_capacity(pos.len());
            for c in pos.iter() {
                pos2.push(fill_column_holes(kb, c, columns, whole_row)?);
            }
            let mut named2 = Vec::with_capacity(named.len());
            for (k, c) in named.iter() {
                named2.push((*k, fill_column_holes(kb, c, columns, whole_row)?));
            }
            Ok(Value::Entity { functor: *functor, pos: pos2.into(), named: named2.into() })
        }
        Value::Var(Var::Global(hole)) => {
            let name = hole.name();
            // A WHOLE-ROW hole (bare binder `c`, e.g. `eq(c, 30)`) refers to the entire
            // row, which is a single column ONLY for a 1-collapse (single-column)
            // relation. Over a multi-column relation the whole row is a named tuple with
            // no eq column — a USER error, not a compiler invariant break: `eq(c, c)`
            // type-checks for a multi-column row (named-tuple `eq`), so this IS reachable
            // (compile_operand can't see the arity — only the runtime schema can).
            if whole_row == Some(name) {
                return match columns {
                    [(_, vid)] => Ok(Value::Var(Var::Global(*vid))),
                    _ => Err(EvalError::TypeMismatch {
                        expected: "a single-column relation for a whole-row `where` condition \
                                   (compare a specific column `c.field` over a multi-column row)",
                        got: format!("a bare whole-row binder `c` over a {}-column relation", columns.len()),
                    }),
                };
            }
            let (_, vid) = columns.iter().find(|(cn, _)| *cn == name).ok_or_else(|| {
                EvalError::Internal(format!(
                    "where_run: the compiled condition references column `{}`, which is not \
                     in the relation's schema",
                    kb.local_name_of(name)
                ))
            })?;
            Ok(Value::Var(Var::Global(*vid)))
        }
        Value::Node(_) => Err(EvalError::Internal(format!(
            "where_run: unexpected {} carrier in a goal recipe",
            v.type_name()
        ))),
        _ => Ok(v.clone()),
    }
}

/// WI-757 — a row-lambda macro's REJECTION of its input, on the macro diagnostic
/// channel ([`EvalError::MacroRejected`]): the condition the author wrote is
/// definitively not goal-expressible, so the macro reports WHY instead of declining
/// and leaving the residual `guarded_of` template's type error to speak for it.
///
/// `at` is the OFFENDING occurrence — the one atom / operand / lambda that does not
/// translate, not the whole `where` call — so the load error points at the text the
/// author must change. Every rejection below passes one; only an invariant break (a
/// non-occurrence argument, which the macro classifier makes unreachable) stays an
/// ordinary [`type_mismatch`] DECLINE.
///
/// The `expected …, got …` phrasing is built HERE — the channel itself carries one
/// rendered `detail`, because its other producer is an anthill macro's `raise`,
/// whose payload has no such structure (proposal 043.1 §3.6).
fn macro_rejects(
    expected: &str,
    got: String,
    at: &std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
) -> EvalError {
    EvalError::MacroRejected {
        detail: format!("expected {expected}, got {got}"),
        span: Some(at.span),
    }
}

/// `Relation.guarded_of` (WI-714 / proposal 052) — the compile-time MACRO behind
/// `where` (occurrence→occurrence, so the `[simp]` engine fires it at compile time,
/// WI-722). It reads the row lambda `cond` and compiles its body — AS SYNTAX, never
/// applied — into a `LogicalQuery` recipe, then splices `where_run(r, <recipe>)`.
///
/// The condition is any nesting of atomic predicates under `and`/`or`/`not`
/// (WI-730; the first increment took the single atom alone) — see
/// [`compile_condition`] for the tree→query mapping. A field access `c.x` on the
/// binder becomes a column HOLE: a fresh var NAMED by the field symbol `x`, which
/// `where_run` fills with `r`'s real column of that name (canonical `Symbol` match,
/// not a short-name compare). A literal becomes its value. Anything else is a loud
/// compile error (LINQ's "cannot translate").
fn relation_guarded_of(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence::{Expr, Pattern};
    use std::rc::Rc;
    let [r_arg, cond_arg] = expect_args::<2>("Relation.guarded_of", args)?;
    let r_occ = match &r_arg {
        Value::Node(o) => Rc::clone(o),
        other => return Err(type_mismatch("NodeOccurrence", other, None)),
    };
    let cond_occ = match &cond_arg {
        Value::Node(o) => Rc::clone(o),
        other => return Err(type_mismatch("NodeOccurrence", other, None)),
    };

    // The condition must be a ROW LAMBDA `c -> <body>`; its binder scopes the
    // columns. A non-lambda (e.g. a raw logic-variable goal) is rejected — that
    // belongs in a rule, not the functional `where` (052 division of labour).
    let (binder, body) = match cond_occ.as_expr() {
        Some(Expr::Lambda { param, body }) => {
            let binder = match param.as_pattern() {
                Some(Pattern::Var { name, .. }) => *name,
                _ => {
                    return Err(macro_rejects(
                        "a row lambda with a single binder (`c -> …`)",
                        "a lambda whose parameter is not a plain binder".to_string(),
                        param,
                    ))
                }
            };
            (binder, Rc::clone(body))
        }
        _ => {
            return Err(macro_rejects(
                "a row lambda (`c -> eq(c.x, …)`) as `where`'s condition",
                "a non-lambda condition (a logic-variable goal belongs in a rule)".to_string(),
                &cond_occ,
            ))
        }
    };

    // Compile the lambda body, as syntax, into a query recipe (column refs → holes),
    // then splice `where_run(r, <recipe>)` — the runtime back-end.
    let recipe = compile_condition(interp, &body, &[binder])?;
    splice_query_runner(interp, "anthill.prelude.Relation.where_run", &[r_occ], recipe)
}

/// Splice a `<runner>(<relation…>, <recipe>)` call for a row-lambda macro — the shared
/// tail of `guarded_of` → `where_run` (one row) and `conjoin_of` → `join_run` (two
/// rows). The compiled `recipe` rides an `Expr::Spliced` leaf STAMPED
/// `anthill.reflect.LogicalQuery` (the `runner`'s `cond: LogicalQuery` slot); the
/// relation occurrences pass through positionally ahead of it. The result is a normal
/// runtime call the typer re-types (via the macro-expand splice) and eval runs.
fn splice_query_runner(
    interp: &mut Interpreter,
    runner_qn: &str,
    relations: &[std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>],
    recipe: Value,
) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence::{Expr, NodeOccurrence};
    use std::rc::Rc;
    // The first relation occurrence anchors the synthesized nodes' source/owner.
    let anchor = relations.first().ok_or_else(|| {
        EvalError::Internal("WI-714: query-runner splice with no relation operand".into())
    })?;
    let pass = interp.kb.register_pass("anthill.kb.passes.macro_expand");
    let owner = anchor.owner;
    let spliced =
        NodeOccurrence::synthesized_expr(Expr::Spliced(recipe), Rc::clone(anchor), pass, owner);
    // STAMP the spliced leaf's type. The `Expr::Spliced` typer arm reads a synthesized
    // leaf's type from `inferred_type` else the position's `expected` — and errors
    // `BottomExpr` when both are absent. `synthesized_expr` resets `inferred_type` to
    // None, so the constructor (this macro) supplies it: the recipe fills the runner's
    // `cond: LogicalQuery` slot, so its type is the reflect `LogicalQuery` sort (the
    // carrier design's "type from the constructor", WI-714 / carrier leaf).
    // `make_sort_ref_by_name` SILENTLY interns an Unresolved sort if the name is
    // missing (kb/mod.rs), and the `Expr::Spliced` typer arm reads `inferred_type`
    // OVER `expected` — so a phantom sort would override the runner's real `cond:
    // LogicalQuery` hint. Resolve loudly instead. (reflect.anthill always loads before
    // user code types, so this never fires — a belt for a hostile load order.)
    if interp.kb.try_resolve_symbol("anthill.reflect.LogicalQuery").is_none() {
        return Err(EvalError::Internal(format!(
            "WI-714 {runner_qn} lowering: anthill.reflect.LogicalQuery is not resolvable"
        )));
    }
    let query_ty = Value::term(interp.kb.make_sort_ref_by_name("anthill.reflect.LogicalQuery"));
    spliced.set_inferred_type(query_ty);
    let runner = interp
        .kb
        .try_resolve_symbol(runner_qn)
        .ok_or_else(|| EvalError::Internal(format!("WI-714: {runner_qn} unresolved")))?;
    let mut pos_args: Vec<Rc<NodeOccurrence>> = relations.to_vec();
    pos_args.push(spliced);
    let call = NodeOccurrence::synthesized_expr(
        Expr::Apply { functor: runner, pos_args, named_args: Vec::new(), type_args: Vec::new() },
        Rc::clone(anchor),
        pass,
        owner,
    );
    Ok(Value::Node(call))
}

/// `Relation.conjoin_of` (WI-714 / proposal 052) — the compile-time MACRO behind
/// `join` (occurrence→occurrence, WI-722). It reads the TWO-row lambda `cond` and
/// compiles its body — AS SYNTAX, never applied — into a goal recipe over BOTH rows'
/// columns, then splices `join_run(r1, r2, <recipe>)`.
///
/// The condition is a two-binder lambda `(c, q) -> <body>` — a tuple pattern whose two
/// sub-binders name the two rows. A field access `c.x` / `q.y` on either binder becomes
/// a column HOLE named by the field symbol (the same `compile_condition` the single-row
/// `where` uses, given both binders); `join_run` fills each hole from the merged column
/// set, whose names are disjoint across the two rows in this increment. The condition
/// admits the same `and`/`or`/`not` nesting `where` does (WI-730), for the same reason:
/// one shared compiler.
fn relation_conjoin_of(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence::{Expr, Pattern};
    use std::rc::Rc;
    let [r1_arg, r2_arg, cond_arg] = expect_args::<3>("Relation.conjoin_of", args)?;
    let as_occ = |v: &Value| match v {
        Value::Node(o) => Ok(Rc::clone(o)),
        other => Err(type_mismatch("NodeOccurrence", other, None)),
    };
    let r1_occ = as_occ(&r1_arg)?;
    let r2_occ = as_occ(&r2_arg)?;
    let cond_occ = as_occ(&cond_arg)?;

    // The condition must be a TWO-ROW lambda `(c, q) -> <body>`: a lambda whose single
    // parameter is a tuple pattern binding the two rows. A single-binder lambda (one
    // row) or a non-lambda is rejected — `join` combines two rows.
    let (binders, body) = match cond_occ.as_expr() {
        Some(Expr::Lambda { param, body }) => {
            let binders = match param.as_pattern() {
                Some(Pattern::Tuple { positional, .. }) => {
                    let mut bs: Vec<crate::intern::Symbol> = Vec::with_capacity(positional.len());
                    for sub in positional {
                        match sub.as_pattern() {
                            Some(Pattern::Var { name, .. }) => bs.push(*name),
                            _ => {
                                return Err(macro_rejects(
                                    "a two-row lambda `(c, q) -> …` binding two plain rows",
                                    "a join lambda whose tuple binder nests a non-plain sub-pattern"
                                        .to_string(),
                                    sub,
                                ))
                            }
                        }
                    }
                    bs
                }
                _ => {
                    return Err(macro_rejects(
                        "a two-row lambda `(c, q) -> eq(c.x, q.y)` as `join`'s condition",
                        "a `join` condition that is not a two-row tuple lambda".to_string(),
                        param,
                    ))
                }
            };
            (binders, Rc::clone(body))
        }
        _ => {
            return Err(macro_rejects(
                "a two-row lambda `(c, q) -> eq(c.x, q.y)` as `join`'s condition",
                "a non-lambda condition (a logic-variable goal belongs in a rule)".to_string(),
                &cond_occ,
            ))
        }
    };
    // First increment: exactly two rows. A different arity is a clean user-facing error.
    if binders.len() != 2 {
        return Err(macro_rejects(
            "a `join` row lambda binding exactly two rows `(c, q) -> …`",
            format!("a join row lambda binding {} rows", binders.len()),
            &cond_occ,
        ));
    }
    let recipe = compile_condition(interp, &body, &binders)?;
    splice_query_runner(interp, "anthill.prelude.Relation.join_run", &[r1_occ, r2_occ], recipe)
}

/// `Relation.join_run` (WI-714 / proposal 052) — the RUNTIME back-end of `join`, a
/// query combinator like `union`. Given `r1`, `r2` and the compiled goal recipe (whose
/// column references are HOLES named by the schema field symbol), it:
///   1. freshens `r2`'s column variables (like `union` aligns operands) so a self-join
///      `r.join(r, …)` does not accidentally unify the two copies' columns;
///   2. fills each recipe hole with the real column variable of that name, over the
///      MERGED column set `r1.columns ++ r2'.columns` (disjoint names in this increment,
///      so the field name alone identifies the column — a collision is a loud error);
///   3. wraps `guarded(conjunction(r1.query, r2'.query), <goal>)` — a new LogicalQuery
///      (`conjunction` conjoins the two queries, `guarded` adds the join predicate) — so
///      the result stays a composable `Relation` over the merged schema.
fn relation_join_run(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r1, r2, cond] = expect_args::<3>("Relation.join_run", args)?;
    let (q1, cols1) = expect_relation(r1)?;
    let (q2, cols2) = expect_relation(r2)?;

    // Freshen r2's column variables (map each to a fresh var of the same name) and
    // rewrite r2's query accordingly — so r1 and r2 never share a column variable
    // (a self-join `r.join(r, …)` would otherwise force the two copies equal). Same
    // alignment `union` performs, one operand.
    let mut sigma = crate::kb::subst::Substitution::new();
    let cols2_fresh: std::rc::Rc<[(crate::intern::Symbol, crate::kb::term::VarId)]> = cols2
        .iter()
        .map(|(name, vid)| {
            let fresh = interp.kb.fresh_var(*name);
            let fresh_term =
                interp.kb.alloc(crate::kb::term::Term::Var(crate::kb::term::Var::Global(fresh)));
            sigma.bind(&interp.kb, *vid, fresh_term);
            (*name, fresh)
        })
        .collect();
    let q2_fresh = rename_query_vars(&mut interp.kb, &q2, &sigma)?;

    // The merged column set — r1's columns then r2's (freshened). Column NAMES must be
    // DISJOINT across the two rows in this increment: the recipe's holes are filled by
    // name over this merged set, and a materialized row is a named tuple keyed by these
    // names, so a clash is ambiguous both ways. A loud error (the typer's `concat`
    // enforces this at LOAD; this backstops a relation built past the typer via reflect).
    let mut merged: Vec<(crate::intern::Symbol, crate::kb::term::VarId)> =
        Vec::with_capacity(cols1.len() + cols2_fresh.len());
    merged.extend(cols1.iter().copied());
    for (name, vid) in cols2_fresh.iter() {
        if cols1.iter().any(|(n, _)| n == name) {
            return Err(EvalError::TypeMismatch {
                expected: "two relations with DISJOINT column names (join)",
                got: format!(
                    "column `{}` appears in both rows — a shared join-column name is not yet \
                     supported (rename one, or project); qualified merge is a follow-up",
                    interp.kb.local_name_of(*name)
                ),
            });
        }
        merged.push((*name, *vid));
    }
    let merged: std::rc::Rc<[(crate::intern::Symbol, crate::kb::term::VarId)]> = merged.into();

    // Fill the recipe's column holes over the merged set, then conjoin: the two rows'
    // queries (the cartesian product) and then the join condition — a query TREE since
    // WI-730, conjoined exactly as `where_run` conjoins its own (see the note there on
    // why this is `conjunction` and not `guarded`). Condition LAST, so both rows'
    // columns are bound before it runs.
    let whole_row = interp.kb.lookup_symbol(WHOLE_ROW_HOLE);
    let condition = fill_column_holes(&interp.kb, &cond, &merged, whole_row)?;
    let product = interp.build_logical_query_value(
        "conjunction",
        vec![("left", (*q1).clone()), ("right", q2_fresh)],
    )?;
    let joined = interp.build_logical_query_value(
        "conjunction",
        vec![("left", product), ("right", condition)],
    )?;
    Ok(Value::Relation { query: std::rc::Rc::new(joined), columns: merged })
}

/// WI-787: read a column-keyed SPEC record (`Relation.project_run`'s projection
/// map, `Relation.fix`'s restriction record) — the `named` half of a tuple, with
/// a POSITIONAL component refused loudly rather than ignored.
///
/// These two builtins are the tuple readers that legitimately want `named`
/// ALONE: every entry is `column-name ↦ …`, and a positional component carries
/// no column name, so there is nothing it could restrict or select. But reading
/// one half and dropping the other is exactly the WI-787 defect, and here it
/// would degrade silently — a spec whose components all landed in `pos` reads as
/// the EMPTY record, which both builtins treat as the identity, so the filter
/// vanishes and the query returns unrestricted rows.
///
/// No source program reaches this — `project_run`'s spec is built by the typer
/// with `pos` hardcoded empty, and `fix`'s is rejected upstream by the `Without`
/// reduction, which refuses a key naming no column (MEASURED: `fix(_1: 3)`,
/// where `_1` is the synthetic positional label for index 0 and so is hoisted
/// into `pos`, fails to LOAD). The guard is for a programmatically-built spec,
/// and it is a loud error rather than a `debug_assert` because the silent
/// reading is a WRONG ANSWER, not a crash.
fn spec_record_fields<'a>(
    spec: &'a Value,
    what: &'static str,
) -> Result<&'a [(crate::intern::Symbol, Value)], EvalError> {
    match spec {
        Value::Tuple { pos, named } if pos.is_empty() => Ok(named),
        Value::Tuple { pos, .. } => Err(EvalError::TypeMismatch {
            expected: what,
            got: format!(
                "a spec with {} POSITIONAL component(s), which name no column — every entry \
                 must be `column-name ↦ value`",
                pos.len()
            ),
        }),
        other => Err(type_mismatch(what, other, None)),
    }
}

/// `Relation.project_run` (WI-714 / proposal 052) — the RUNTIME back-end of `project`
/// (the distribute-dot `r.(f1, f2)`), a column restriction rather than a query
/// combinator. `spec` is the compile-time projection map the typer spliced: a
/// `Value::Tuple` whose named fields are `result-key ↦ Str(source-column-name)`.
/// Rebuild `columns` as `[(result-key, r's column variable of source-name)]` —
/// SELECTING (and RENAMING, when a result key differs from its source) — while leaving
/// `r.query` UNCHANGED: `projected` is a resolver pass-through (kb/execute.rs), so 052
/// applies the restriction HERE at materialization. Only the kept columns are read into
/// each answer row; a dropped column is still SOLVED, so the row multiplicity is the
/// source relation's (bag projection, OQ6). Source names match `r`'s columns by INTERNED
/// symbol — the same canonical seam `where_run` fills holes on, NOT a short-name compare
/// (WI-672). A source naming no column is a loud error, never a silent drop.
fn relation_project_run(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r, spec] = expect_args::<2>("Relation.project_run", args)?;
    let (query, columns) = expect_relation(r)?;
    let pairs = spec_record_fields(&spec, "a projection spec tuple (result-key ↦ source-column-name)")?;
    let mut projected: Vec<(crate::intern::Symbol, crate::kb::term::VarId)> =
        Vec::with_capacity(pairs.len());
    for (result_key, source) in pairs.iter() {
        let source_name = match source {
            Value::Str(s) => s.as_str(),
            other => {
                return Err(EvalError::TypeMismatch {
                    expected: "a source column name (String) in the projection spec",
                    got: other.type_name().to_string(),
                })
            }
        };
        // Resolve the source name to its canonical interned `Symbol`, then match `r`'s column
        // by SYMBOL equality — a column's name symbol is the canonical intern-map entry for
        // its short name (`rule_head_var_slots` names positional columns by the head var's
        // `.name()` and named columns by the head field key, both global-interned), so
        // `lookup_symbol` round-trips to exactly the column symbol. This is the same
        // interned-symbol seam `where_run` fills holes on (its holes carry the field symbol
        // `guarded_of` interned at compile time), NOT a short-name compare (WI-672). A source
        // that resolves to no column is a loud error (typer already verified the column
        // exists in the schema, so this only fires on a programmatically-built spec).
        let vid = interp
            .kb
            .lookup_symbol(source_name)
            .and_then(|sy| find_column(&columns, sy))
            .ok_or_else(|| {
                EvalError::Internal(format!(
                    "project_run: the projection selects column `{source_name}`, which is not \
                     in the relation's schema"
                ))
            })?;
        projected.push((*result_key, vid));
    }
    Ok(Value::Relation { query, columns: projected.into() })
}

/// `Relation.fix` (WI-714 / proposal 052 §"`fix` is sugar"; WI-727 / proposal 056) — the
/// RUNTIME back-end of `fix(p, x: 1, z: 2)`: RESTRICT relation columns to constants and
/// DROP them. `fix` is an ORDINARY operation (proposal 056 §2.1) — no compile-time macro,
/// no typer recognizer keyed on its name: the variadic capture folded its dynamic column
/// arguments into `spec`, an ordinary `Value::Tuple` record `(column-name ↦ constant)`,
/// which reaches this builtin as a plain argument. For each `(col, const)`: wrap
/// `guarded(query, eq(col's variable, const))` — the same query-combining step
/// `where`/`negate`/`union` perform, with `eq` the resolver's equality connective
/// (`PartialEq.eq`, as `where`'s guards use) restricting the column to the constant — then
/// DROP that column from `columns`. The column variable stays in the query (still SOLVED),
/// so a dropped column keeps the source relation's row multiplicity (bag semantics, OQ6,
/// exactly as `project`). Columns match `spec` keys by canonical interned symbol (the same
/// seam `project_run`/`where_run` use), NOT a short-name compare (WI-672). A key naming no
/// column is a loud error; an empty record (`r.fix()`) is the identity.
fn relation_fix(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [p, spec] = expect_args::<2>("Relation.fix", args)?;
    let (query, columns) = expect_relation(p)?;
    let fixes = spec_record_fields(&spec, "a fix record (column-name ↦ constant) captured named tuple")?;
    let eq_sym = interp
        .kb
        .try_resolve_symbol("anthill.prelude.PartialEq.eq")
        .ok_or_else(|| {
            EvalError::Internal("fix: `anthill.prelude.PartialEq.eq` is unresolvable".to_string())
        })?;
    let mut query: Value = (*query).clone();
    for (col_name, const_val) in fixes.iter() {
        // The relation's real column variable of this name — matched by canonical interned
        // `Symbol` (a column's name IS the intern-map entry for its short name), the same
        // seam `project_run` uses. The typer's `Without` reduction already verified the
        // column exists in the schema, so this only fires on a programmatically-built spec.
        let vid = find_column(&columns, *col_name).ok_or_else(|| {
            EvalError::Internal(format!(
                "fix: restricts column `{}`, which is not in the relation's schema",
                interp.kb.local_name_of(*col_name)
            ))
        })?;
        // The restrict guard `eq(?col, const)` — a goal atom the resolver conjoins with the
        // query (guarded), pinning `?col` to the constant on the surviving solutions.
        let guard = Value::Entity {
            functor: eq_sym,
            pos: std::rc::Rc::from(vec![
                Value::Var(crate::kb::term::Var::Global(vid)),
                const_val.clone(),
            ]),
            named: std::rc::Rc::from(Vec::new()),
        };
        query = interp
            .build_logical_query_value("guarded", vec![("query", query), ("condition", guard)])?;
    }
    // Drop the restricted columns from the materialized schema, KEEPING the query — the
    // dropped column is still solved (bag semantics), exactly as `project`. A handful of
    // columns, so a linear scan against the (equally tiny) `fixes` — no set needed.
    let kept: Vec<(crate::intern::Symbol, crate::kb::term::VarId)> = columns
        .iter()
        .filter(|(cn, _)| !fixes.iter().any(|(fn_name, _)| fn_name == cn))
        .copied()
        .collect();
    Ok(Value::Relation { query: std::rc::Rc::new(query), columns: kept.into() })
}

/// WI-714 — the relation column variable named `sym`, matched by canonical interned
/// `Symbol` (a column's name IS the intern-map entry for its short name — the same seam
/// `where_run` fills holes on, NOT a WI-672 short-name compare). Shared by the relation
/// back-ends that select a column by name (`fix`, `project_run`).
fn find_column(
    columns: &[(crate::intern::Symbol, crate::kb::term::VarId)],
    sym: crate::intern::Symbol,
) -> Option<crate::kb::term::VarId> {
    columns.iter().find(|(cn, _)| *cn == sym).map(|(_, v)| *v)
}

/// The `LogicalQuery` constructor each boolean CONNECTIVE lowers to, with that
/// constructor's field names in operand order — proposal 052's tree→query table
/// (`&&`/`||`/`!` ⇒ conjunction/disjunction/negation), WI-730. Matched by CANONICAL
/// operation name, never a short name (WI-672); a user operation that merely shares
/// the short name `and` is a different symbol and falls through to the atom path.
const BOOLEAN_CONNECTIVES: [(&str, &str, &[&str]); 3] = [
    ("anthill.prelude.Bool.and", "conjunction", &["left", "right"]),
    ("anthill.prelude.Bool.or", "disjunction", &["left", "right"]),
    ("anthill.prelude.Bool.not", "negation", &["query"]),
];

/// Compile a row-lambda condition body into a `LogicalQuery` goal recipe `Value`, as
/// syntax (never applied) — proposal 052 §"Compiling a row lambda into a query", the
/// LINQ `IQueryable` expression-tree translation with the `LogicalQuery` ADT as the
/// backend. Each node of the `Bool`-valued tree maps to one query constructor:
///
/// | lambda expression                | `LogicalQuery`                     |
/// |----------------------------------|------------------------------------|
/// | atomic predicate `eq(c.x, 1)`    | `pattern_query(term: <goal atom>)` |
/// | `and(a, b)`                      | `conjunction(left, right)`         |
/// | `or(a, b)`                       | `disjunction(left, right)`         |
/// | `not(a)`                         | `negation(query)`                  |
///
/// All four are already wired in the `kb/execute.rs` lowerer, which is what makes
/// nesting free: it flattens a conjunction into a goal LIST and lifts a MULTI-goal
/// `or`/`not` branch through a synthesized conjunction rule (`_synth_N(?vars) :-
/// goals`, proposal 033 §M4). So `or(and(a, b), c)` needs no new machinery here — only
/// the tree walk. (WI-730; the first `where`/`join` increments compiled the atom
/// alone.)
///
/// The recursion is bounded by the SOURCE nesting of a hand-written condition, the
/// same bound the operand walk below already runs under.
fn compile_condition(
    interp: &mut Interpreter,
    body: &std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
    binders: &[crate::intern::Symbol],
) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence::Expr;
    let Some(Expr::Apply { functor, pos_args, named_args, .. }) = body.as_expr() else {
        return Err(macro_rejects(
            "a goal-expressible row-lambda condition — a predicate \
             (`eq(c.x, …)`) or an `and`/`or`/`not` of them",
            "a condition that does not translate to a query goal (an `if`, a \
             `match`, a literal — compute it with `.map` on the stream instead)"
                .to_string(),
            body,
        ));
    };
    // A boolean CONNECTIVE — recurse over the spine into the matching query
    // constructor. Its operands are conditions in their own right, so any depth of
    // `&&`/`||`/`!` nesting composes with no extra case.
    if let Some((op_qn, ctor, fields)) = BOOLEAN_CONNECTIVES
        .iter()
        .find(|(op_qn, _, _)| interp.kb.try_resolve_symbol(op_qn) == Some(*functor))
    {
        // The connectives are declared with POSITIONAL parameters; a call spelled with
        // labels (`and(a: p, b: q)`) would have to be matched to them by name, which is
        // not wired. Refuse it loudly rather than read the operands in the wrong order.
        if pos_args.len() != fields.len() || !named_args.is_empty() {
            return Err(macro_rejects(
                "a boolean connective applied to positional operands \
                 (`and(p, q)` / `or(p, q)` / `not(p)`)",
                format!(
                    "`{op_qn}` applied to {} positional and {} named argument(s)",
                    pos_args.len(),
                    named_args.len()
                ),
                body,
            ));
        }
        let mut operands = Vec::with_capacity(fields.len());
        for (field, arg) in fields.iter().zip(pos_args) {
            operands.push((*field, compile_condition(interp, arg, binders)?));
        }
        return interp.build_logical_query_value(ctor, operands);
    }
    // A FIELD ACCESS is an OPERAND form, never a condition: `c.ok` NAMES a column, it
    // does not state a predicate ABOUT one. It reaches condition position as a bare
    // `Bool` column (`where(λ c -> c.ok)`) or a nested projection (`c.a.b`), both of
    // which type-check — and `anthill.reflect.field_access` is itself a registered
    // builtin, so the head check below would wave it through and compile a projection
    // into GOAL position, where it means nothing. Refuse, and name the spelling that
    // works. Recognized through the shared `field_access_parts` contract, the same one
    // `compile_operand` reads a column reference by (no second copy of the desugaring).
    if crate::kb::body_specialize::field_access_parts(&interp.kb, *functor, pos_args).is_some() {
        return Err(macro_rejects(
            "a predicate as a row-lambda condition — COMPARE the column \
             (`eq(c.ok, true)`), do not merely name it",
            "a bare column projection in condition position".to_string(),
            body,
        ));
    }
    // An ATOM. The predicate FUNCTOR is kept verbatim — the lambda's `eq`
    // (`PartialEq.eq`) IS the resolver's eq connective, so there is no value→goal
    // mapping — but it must actually BE a goal the resolver can run: a registered
    // builtin (`eq`/`neq`/`lt`/…) or a RULE cited as a predicate (`adult(c.age)`).
    // Any other `Bool`-valued call — `ite(…)`, an ordinary operation — would compile
    // to an atom nothing can prove, and the filtered relation would come back
    // silently EMPTY. Reject it here instead: 052's "cannot translate to SQL".
    // Checked BEFORE the operands so the diagnostic names the untranslatable head
    // rather than whatever it was applied to.
    //
    // WI-898 — `ite(…)` IS THE EXAMPLE ABOVE, and this set is what decides it. While
    // an equation-introduced functor shared `SymbolKind::Goal` (WI-894), `ite` passed
    // this gate: it named no clauses under itself, so the compiled atom was
    // unprovable and the `where` came back silently empty — precisely the failure the
    // rejection is written to prevent. `EquationFunctor` is deliberately excluded,
    // which restores it.
    if interp.kb.builtin_of(*functor).is_none() && !interp.kb.cites_a_relation(*functor) {
        return Err(macro_rejects(
            "a goal-expressible predicate (a builtin such as `eq`/`neq`/`lt`, \
             or a rule) as a row-lambda condition atom",
            format!(
                "`{}`, which is neither — it has no meaning as a query goal \
                 (compute it with `.map` on the stream instead)",
                interp.kb.qualified_name_of(*functor)
            ),
            body,
        ));
    }
    let mut pos = Vec::with_capacity(pos_args.len());
    for a in pos_args {
        pos.push(compile_operand(interp, a, binders)?);
    }
    let mut named = Vec::with_capacity(named_args.len());
    for (k, a) in named_args {
        named.push((*k, compile_operand(interp, a, binders)?));
    }
    let atom = Value::Entity { functor: *functor, pos: pos.into(), named: named.into() };
    interp.build_logical_query_value("pattern_query", vec![("term", atom)])
}

/// Compile one predicate operand: a column field-access `c.x` on a binder becomes a
/// HOLE (a fresh var named `x`, filled by `where_run`/`join_run`); a literal becomes
/// its value. `binders` holds the one (`where`) or two (`join`) row binders.
fn compile_operand(
    interp: &mut Interpreter,
    occ: &std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
    binders: &[crate::intern::Symbol],
) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence::Expr;
    use crate::kb::term::{Literal, Var};
    // A column reference `c.x` on a binder becomes a HOLE: a fresh var NAMED by the
    // field symbol, which `where_run`/`join_run` fills with the real column of that name.
    if let Some(field) = binder_field_access(interp, occ, binders) {
        let hole = interp.kb.fresh_var(field);
        return Ok(Value::Var(Var::Global(hole)));
    }
    // A BARE binder reference `c` is the WHOLE ROW. For a 1-collapse (single-column)
    // relation it IS the sole column (`eq(c, 30)`); over a multi-column row a whole-row
    // comparison has no single eq column. The arity is NOT visible here (only the
    // runtime schema is) and a multi-column `eq(c, c)` DOES type-check (named-tuple eq),
    // so the single-column check is deferred to `where_run` when it fills the hole.
    if is_binder_ref(occ, binders) {
        let sole = interp.kb.intern(WHOLE_ROW_HOLE);
        let hole = interp.kb.fresh_var(sole);
        return Ok(Value::Var(Var::Global(hole)));
    }
    match occ.as_expr() {
        Some(Expr::Const(lit)) => Ok(match lit {
            Literal::Int(n) => Value::Int(*n),
            Literal::Float(f) => Value::Float(f.0),
            Literal::Bool(b) => Value::Bool(*b),
            Literal::String(s) => Value::Str(s.clone()),
            other => {
                return Err(macro_rejects(
                    "an Int/Float/Bool/String literal in the `where` condition",
                    format!("an unsupported literal kind: {other:?}"),
                    occ,
                ))
            }
        }),
        _ => Err(macro_rejects(
            "a column (`c.x`) or a literal in the `where` condition",
            "an operand that is neither a row column nor a literal".to_string(),
            occ,
        )),
    }
}

/// Recognize a column reference `c.x` on the row-lambda binder and return the field
/// SYMBOL (which names the query HOLE `where_run` later fills). Post-typing, `c.x` is
/// lowered to the reflect form `field_access(c, "x")` (WI-638 / WI-681) — an `Apply`,
/// NOT a `DotApply` — so the column is read through the SAME `field_access_parts`
/// contract the op-body specializer uses (no third copy of the desugaring; the field
/// string is interned to the canonical `Symbol`, so `where_run`'s hole/column match
/// is exact-symbol, not a WI-672 short-name compare). A raw zero-arg `DotApply` (the
/// pre-lowering shape) is accepted as a defensive fallback. `None` for any operand
/// that is not a binder field access.
fn binder_field_access(
    interp: &mut Interpreter,
    occ: &std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
    binders: &[crate::intern::Symbol],
) -> Option<crate::intern::Symbol> {
    use crate::kb::node_occurrence::Expr;
    match occ.as_expr()? {
        // Post-typing form (the real one): `c.x` → `field_access(c, "x")`.
        Expr::Apply { functor, pos_args, named_args, .. } if named_args.is_empty() => {
            let (receiver, field) =
                crate::kb::body_specialize::field_access_parts(&interp.kb, *functor, pos_args)?;
            is_binder_ref(&receiver, binders).then(|| interp.kb.intern(&field))
        }
        // Pre-lowering fallback: `c.x` as a zero-arg `DotApply`.
        Expr::DotApply { receiver, name, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() && is_binder_ref(receiver, binders) =>
        {
            Some(*name)
        }
        _ => None,
    }
}

/// Is `occ` a reference to one of the row-lambda binders? A binder reference lowers
/// to `var_ref(name)` (WI-552); accept the plain `Ref`/`Ident` forms defensively.
/// `binders` is a slice so a `where` single-row lambda (`[c]`) and a `join` two-row
/// lambda (`[c, q]`) share the recognizer — a field access on EITHER binder yields the
/// field name, which `*_run` fills from the merged column set (disjoint across the two
/// rows in the first `join` increment, so the field name alone identifies the column).
fn is_binder_ref(
    occ: &std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
    binders: &[crate::intern::Symbol],
) -> bool {
    use crate::kb::node_occurrence::Expr;
    matches!(
        occ.as_expr(),
        Some(Expr::VarRef { name }) | Some(Expr::Ref(name)) | Some(Expr::Ident(name)) if binders.contains(name)
    )
}

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
    split_first_result(interp, pumped)
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

    // One head read replaces the `Fn` / `Ref` / `Ident` / `Entity` nest this
    // hand-matched, via the reader that keeps ALL of those spellings —
    // `functor_sym` alone has no `Ident` arm and silently dropped it.
    //
    // IT IS NOT A PURE EQUIVALENCE, and an earlier version of this comment
    // claimed it was. The replaced outer match ended `_ => None`, so a
    // `Value::Node` answered `none()`; a head read answers the occurrence's own
    // functor. That is the right answer — an occurrence carrying `Apply{f, …}`
    // has functor `f` whatever holds it — but it does flip `none()` to
    // `some(name)` for any caller that was using this op to discriminate a
    // term-carrier from an occurrence. No caller in the corpus does; nothing
    // pins it either way.
    let name: Option<String> = interp
        .kb
        .value_head_symbol(&arg)
        .map(|s| interp.kb.local_name_of(s).to_string());

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
    let arity_key = interp.kb.intern("arity");
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
        // WI-791: `arity` reifies alongside the other three. A program that
        // `case`s over an `Arrow` needs it to tell a one-tuple-parameter arrow
        // from an n-parameter one — the same distinction the typer needs — and
        // dropping it here would make `extract` lossy against the stdlib
        // `entity Arrow(param, result, effects, arity)` it is defined to mirror.
        TypeExtractor::Arrow { param, result, effects, arity } => {
            // `arity` arrives decoded; re-mint the `Const(Int)` the stdlib entity's
            // `arity: Int64` field holds, through the same builder the typer uses so
            // a reified arrow is structurally identical to the one it came from.
            let arity_val = Value::term(interp.kb.make_arity_term(arity));
            ti_entity(
                interp,
                "Arrow",
                vec![
                    (param_key, param),
                    (result_key, result),
                    (effects_key, effects),
                    (arity_key, arity_val),
                ],
            )
        }
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
                .find(|(s, _)| interp.kb.local_name_of(*s) == name)
                .map(|(_, t)| *t)
        }
        _ => None,
    };

    Ok(match found {
        Some(field_tid) => Value::Entity {
            functor: some_sym,
            pos: Vec::new().into(),
            named: vec![(value_key, Value::term(field_tid))].into(),
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
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
        },
        None => Value::Entity {
            functor: none_sym,
            pos: Vec::new().into(),
            named: Vec::new().into(),
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
        Value::Term { id: tid, .. } => materialize_entity(interp, tid),
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
    // probe keys off `entity_field_types`, not `strict_parent_sort`.
    // The last-resort scan covers a functor that is still an unqualified
    // short name.
    let canonical = if interp.kb.entity_field_types(functor).is_some() {
        functor
    } else {
        let short_name = interp.kb.local_name_of(functor).to_string();
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
        // `sort_of_constructor`, NOT `strict_parent_sort` (WI-937). The
        // question here is "is this an entity constructor", and the strict view
        // answers `None` for an EPONYMOUS one — `entity_parent[Vec3] == Vec3`, so
        // its `.filter(|&p| p != functor)` drops it. That is right for a walker
        // climbing to a parent and wrong here: it made every §6.3 free-standing /
        // eponymous entity fail to materialize, so a bodied op reading `a.x` off
        // one got `Value::Term` and died `field_access: receiver is not an entity`
        // — a debug_assert abort in `bridge_op_to_eval`, a silent residual in
        // release. The accessor's own doc says to prefer the total view when the
        // question is "which sort does this belong to"; this is that question.
        Decision::TryFn(functor) => {
            if interp.kb.sort_of_constructor(functor).is_some() {
                materialize_entity(interp, tid).unwrap_or(Value::term(tid))
            } else {
                Value::term(tid)
            }
        }
        Decision::TryRef(sym) => {
            if interp.kb.sort_of_constructor(sym).is_some() {
                Value::Entity { functor: sym, pos: Vec::new().into(), named: Vec::new().into() }
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

/// Walk a reflect cons-list `Value` into a `Vec`, applying `extract` to each
/// element. Cons cells come in two shapes: `build_list_value` (Rust-side) emits
/// named `head`/`tail` keys; anthill-source `cons(h, t)` emits positional args —
/// try named first, fall back to positional. Field-name comparison stays
/// string-based (the loader may qualify field symbols; the canonical short name
/// is `head`/`tail`). A non-cons/nil cell or a malformed cons is a LOUD error,
/// never a silently-dropped element. `ctx` prefixes the internal-error messages;
/// `list_type` names the expected element list for the non-list `type_mismatch`.
/// Shared by `make_fn` (element → `TermId`) and `make_apply` (element → occurrence).
fn reflect_cons_to_vec<T>(
    interp: &Interpreter,
    list: Value,
    ctx: &str,
    list_type: &'static str,
    mut extract: impl FnMut(Value) -> Result<T, EvalError>,
) -> Result<Vec<T>, EvalError> {
    let cons_sym = interp.reflect.cons;
    let nil_sym = interp.reflect.nil;
    let mut out: Vec<T> = Vec::new();
    let mut cursor = list;
    loop {
        match cursor {
            Value::Entity { functor, pos, named, .. } => {
                if Some(functor) == nil_sym {
                    break;
                }
                if Some(functor) != cons_sym {
                    let n = interp.kb.local_name_of(functor);
                    return Err(EvalError::Internal(format!("{ctx}: expected cons/nil, got {n}")));
                }
                let (head, tail) = if !named.is_empty() {
                    let h = named
                        .iter()
                        .find(|(s, _)| interp.kb.local_name_of(*s) == "head")
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| EvalError::Internal(format!("{ctx}: cons missing head field")))?;
                    let t = named
                        .iter()
                        .find(|(s, _)| interp.kb.local_name_of(*s) == "tail")
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| EvalError::Internal(format!("{ctx}: cons missing tail field")))?;
                    (h, t)
                } else if pos.len() >= 2 {
                    (pos[0].clone(), pos[1].clone())
                } else {
                    return Err(EvalError::Internal(format!(
                        "{ctx}: cons cell shape unrecognized (pos={}, named={})",
                        pos.len(),
                        named.len(),
                    )));
                };
                out.push(extract(head)?);
                cursor = tail;
            }
            other => return Err(type_mismatch(list_type, &other, None)),
        }
    }
    Ok(out)
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

    let pos_vec: Vec<TermId> =
        reflect_cons_to_vec(interp, args_arg, "make_fn", "List[Term]", |v| match v {
            Value::Term { id, .. } => Ok(id),
            other => Err(type_mismatch("Term", &other, None)),
        })?;

    let pos_args = smallvec::SmallVec::from_vec(pos_vec);
    let tid = interp.kb.alloc(Term::Fn {
        functor,
        pos_args,
        named_args: smallvec::SmallVec::new(),
    });
    Ok(Value::term(tid))
}

/// WI-722 (proposal 043.1) — `anthill.reflect.make_apply(name: String,
/// args: List[NodeOccurrence], from: NodeOccurrence) -> NodeOccurrence`.
///
/// The occurrence-BUILD side of a compile-time macro: build a synthesized
/// `Expr::Apply` occurrence whose functor is resolved from `name` and whose
/// positional argument occurrences are the `args` list — each reused in place, so
/// an input occurrence keeps its own identity and span. Unlike `make_fn` (which
/// builds a flat `Term`), this returns a spliceable `NodeOccurrence`, so a macro's
/// result can carry child occurrences (a reused argument, later a lambda body)
/// that a `Term` cannot represent. `from` is the source occurrence the built node
/// points at for diagnostics — the `Synthesized.from` (043.1 §3.5).
///
/// The node is stamped with a dedicated `macro_expand` pass, so a macro-built
/// occurrence is distinguishable from a template-substituted one and the simp
/// engine's `Synthesized.from` ancestor-loop check (043 §4.5) sees it. The
/// spliced subtree is RE-TYPED by the typer's `push_visit` continuation, so this
/// builder leaves `inferred_type` unset (as `synthesized_expr` does).
fn reflect_make_apply(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence::{Expr, NodeOccurrence};
    use std::rc::Rc;
    let [name_arg, args_arg, from_arg] = expect_args::<3>("make_apply", args)?;
    let name = match &name_arg {
        Value::Str(s) => s.clone(),
        other => return Err(type_mismatch("String", other, None)),
    };
    let functor = interp
        .kb
        .try_resolve_symbol(&name)
        .ok_or_else(|| EvalError::Internal(format!("make_apply: unknown symbol `{name}`")))?;

    // Reuse each argument occurrence in place (identity + span preserved). A
    // non-occurrence element is a LOUD error, never a silently-dropped node.
    let pos_args: Vec<Rc<NodeOccurrence>> =
        reflect_cons_to_vec(interp, args_arg, "make_apply", "List[NodeOccurrence]", |v| match v {
            Value::Node(occ) => Ok(occ),
            other => Err(type_mismatch("NodeOccurrence", &other, None)),
        })?;

    let from = match &from_arg {
        Value::Node(occ) => Rc::clone(occ),
        other => return Err(type_mismatch("NodeOccurrence", other, None)),
    };
    let pass = interp.kb.register_pass("anthill.kb.passes.macro_expand");
    let owner = from.owner;
    let expr = Expr::Apply { functor, pos_args, named_args: Vec::new(), type_args: Vec::new() };
    Ok(Value::Node(NodeOccurrence::synthesized_expr(expr, from, pass, owner)))
}

/// WI-722 inc 2 (proposal 043.1) — `anthill.reflect.occurrence_term(occ:
/// NodeOccurrence) -> Term`.
///
/// The occurrence-READ side of a compile-time macro: reflect the argument
/// occurrence as its hash-consed `Term` twin (via the shared
/// [`try_occurrence_to_term`] reification — `apply` → `Fn`, an arg-less `dot_apply`
/// → its `dot_apply` term, a literal → `Const`, …), so a macro can inspect a
/// node's head + shape through the existing `Term` reflect surface
/// (`term_functor_name`, `term_field`, `term_list_items`). This is the value-domain
/// complement of the resolver's `occurrence_term` GOAL handler, which unifies a
/// reflect PATTERN against the occurrence; a macro wants the term as a VALUE.
///
/// A child-bearing / binder-scoping form (`lambda`/`if`/`let`/`match`/…) has no
/// flat goal-term shape — `try_occurrence_to_term` returns `None` — so this reads
/// `Bottom` for it (`⊥`, matching `occurrence_to_term`'s own sentinel). That is not
/// an error but the documented signal to navigate such a form STRUCTURALLY via
/// [`reflect_sub_occurrences`] instead (e.g. a `where`/`join` row lambda: read its
/// `[param, body]` children, then `occurrence_term` the applicative body).
///
/// Precondition: the reflect meta-constructors (`Expr.dot_apply`, `ListLiteral`,
/// `Pattern.*`, …) `try_occurrence_to_term` resolves must be interned — the same
/// prelude-loaded-KB precondition its existing callers rely on
/// (`node_occurrence.rs`). This holds whenever the builtin is reachable:
/// `register_if_present` only registers it once `anthill.reflect.occurrence_term`
/// resolves, and that name is scanned together with its sibling constructors from
/// the one `reflect.anthill` module.
fn reflect_occurrence_term(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::term::Term;
    let [occ_arg] = expect_args::<1>("occurrence_term", args)?;
    let occ = match &occ_arg {
        Value::Node(o) => std::rc::Rc::clone(o),
        other => return Err(type_mismatch("NodeOccurrence", other, None)),
    };
    let tid = crate::kb::node_occurrence::try_occurrence_to_term(&mut interp.kb, &occ)
        .unwrap_or_else(|| interp.kb.alloc(Term::Bottom));
    Ok(Value::term(tid))
}

/// WI-722 inc 2 (proposal 043.1) — `anthill.reflect.sub_occurrences(occ:
/// NodeOccurrence) -> List[NodeOccurrence]`.
///
/// The occurrence's direct child occurrences, in a fixed per-form order
/// ([`node_occurrence::for_each_child`] — the same order the resolver's
/// `sub_occurrences` goal handler shows). The children keep their identity (the
/// existing `Rc`s), so a macro can navigate INTO a child-bearing form (a lambda
/// body, an `if` branch) that `occurrence_term` reads as `Bottom`, and then reuse a
/// child in place when it rebuilds via [`reflect_make_apply`]. The list SPINE is
/// the eval-side `Value::Entity` cons ([`build_value_list`]) — the representation
/// `make_apply`'s cons-walk consumes and the interpreter itself produces — not the
/// resolver's `Value::Node` occurrence-cons.
///
/// Only an `Expr`-kind occurrence has expression children; a `Pattern` / `Type` /
/// `EffectExpr` occurrence yields the empty list (as the resolver handler does).
fn reflect_sub_occurrences(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence;
    use std::rc::Rc;
    let [occ_arg] = expect_args::<1>("sub_occurrences", args)?;
    let occ = match &occ_arg {
        Value::Node(o) => Rc::clone(o),
        other => return Err(type_mismatch("NodeOccurrence", other, None)),
    };
    let mut children: Vec<Value> = Vec::new();
    if let Some(expr) = occ.as_expr() {
        node_occurrence::for_each_child(expr, |c| children.push(Value::Node(Rc::clone(c))));
    }
    build_value_list(interp, children)
}

/// WI-722 inc 2 (proposal 043.1) — `anthill.reflect.occurrence_type(occ:
/// NodeOccurrence) -> Option[Type]`.
///
/// The typer-stamped [`inferred_type`](crate::kb::node_occurrence::NodeOccurrence::inferred_type)
/// of the occurrence, or `none()` when it is untyped (a rule head, a not-yet-typed
/// or ill-typed node). A macro runs AFTER its arguments are typed (the typer-side
/// rewriter is bottom-up), so `where`/`join` read a relation argument's schema —
/// which lives in its *type*, not its syntax (043.1 §3.4) — through this reader.
/// The type rides as a carrier-agnostic `Value` (WI-342/WI-502): a ground type is
/// `Value::Term`, a denoted-bearing one `Value::Node`; either way it is wrapped
/// verbatim in `some(value: …)`.
fn reflect_occurrence_type(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [occ_arg] = expect_args::<1>("occurrence_type", args)?;
    let occ = match &occ_arg {
        Value::Node(o) => std::rc::Rc::clone(o),
        other => return Err(type_mismatch("NodeOccurrence", other, None)),
    };
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    match occ.inferred_type() {
        Some(ty) => {
            let value_key = interp.kb.intern("value");
            Ok(Value::Entity {
                functor: some_sym,
                pos: Vec::new().into(),
                named: vec![(value_key, ty)].into(),
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
        if interp.kb.local_name_of(entry.0) == name {
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

/// `anthill.reflect.KB.stored_facts_of(kb, sort) -> List[StoredRef[Term]]`.
/// The capability-carrying companion to [`kb_facts_of`]: each visible row is
/// paired with the source-neutral reference its owner minted, so callers can
/// later pass `.reference` to retract/update without rediscovering identity.
fn kb_stored_facts_of(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [_kb_arg, sort_arg] = expect_args::<2>("KB.stored_facts_of", args)?;
    let functor_sym = crate::eval::eval::value_functor(&interp.kb, &sort_arg)
        .ok_or_else(|| type_mismatch("Type (entity reference)", &sort_arg, None))?;
    let rows = interp
        .kb
        .read_stored_facts(functor_sym, crate::kb::extent::BodiedRulePolicy::Refuse)
        .map_err(|e| EvalError::Internal(format!("stored_facts_of: {e}")))?;
    let elements = rows
        .into_iter()
        .map(|row| stored_ref_value(interp, row))
        .collect::<Result<Vec<_>, _>>()?;
    interp.build_list_value(elements, &[])
}

/// Materialize the declared `StoredRef[T]` pair around an extent-seam row.
/// `FactRef` itself stays a native opaque carrier — it is never lowered into a
/// `Term` or a resident-only handle literal.
fn stored_ref_value(interp: &mut Interpreter, row: crate::kb::extent::StoredRow)
    -> Result<Value, EvalError>
{
    let stored_ref = require_symbol(
        interp,
        "anthill.reflect.StoredRef.stored_ref",
        "stored_ref",
    )?;
    Ok(Value::Entity {
        functor: stored_ref,
        pos: Vec::new().into(),
        named: vec![
            (interp.fields.value, row.row),
            (interp.fields.reference, Value::FactRef(row.reference)),
        ].into(),
    })
}

/// `anthill.reflect.is_modifiable(t: Type) -> Bool` (WI-206). True iff `t`'s head
/// sort is admitted by a `Modifiable[T = …]` fact — the marker proposal 037 Rule 8
/// demands before `Modify[t]` may appear in an effect row.
///
/// The test is on the HEAD SORT, so a parameterized instance answers as its base
/// does: `fact Modifiable[T = Cell]` (cell.anthill) makes `Cell` and `Cell[V =
/// Int64]` alike modifiable. A literal `Modifiable[T = t]` KB query could not do
/// that — the fact's `T` is the bare `Ref(Cell)`, which does not unify with the
/// parameterized `Cell[V = Int64]`.
///
/// Reads the fact set through `region::is_modifiable_sort`, the same reader the
/// typer's region analysis uses, so reflection and the kernel cannot disagree
/// about what is modifiable.
fn reflect_is_modifiable(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [ty] = expect_args::<1>("is_modifiable", args)?;
    let sort = crate::eval::eval::value_functor(&interp.kb, &ty)
        .ok_or_else(|| type_mismatch("Type (a sort reference)", &ty, None))?;
    Ok(Value::Bool(crate::kb::region::is_modifiable_sort(
        &interp.kb, sort,
    )))
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
            if interp.kb.local_name_of(vid.name()) == name {
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

/// Build a `Symbol` runtime value for `s` — the reflect representation of an
/// anthill `Symbol` (a `Value::SymbolRef`). The construction counterpart of
/// reading one back via [`KnowledgeBase::value_symbol`].
///
/// WI-1016 FLIPPED THIS to the value-level carrier, which is what made
/// `Value::SymbolRef` live: `Dictionary.impl`, `OpRef.op` and `OpRef.named` are
/// its only producers, and each answers a question about a value the KB already
/// holds — interning a `Term::Ref` to hand one symbol back is a store write for a
/// read, and it PINS that node for the KB's lifetime. It takes no `KnowledgeBase`
/// for exactly that reason: a function that still demanded `&mut` on the store
/// would advertise the write this change exists to remove.
///
/// NOT the other minters (`lookup_symbol`, `scope`, the resolver's
/// `builtin_lookup_symbol`), and deliberately so: they build a `Symbol` out of a
/// string, so they must intern something anyway, and leaving them on the
/// `Term::Ref` carrier keeps BOTH spellings of one symbol in circulation. That is
/// the state every cross-carrier seam has to survive — `MapKey`, `values_equal`,
/// the discrim keys, the printer — so keeping it is what tests those seams rather
/// than avoiding them.
fn symbol_value(s: crate::intern::Symbol) -> Value {
    Value::SymbolRef(s)
}

// ── WI-577 — runtime dictionary / op-ref views ──────────────────────────────
//
// The anthill face of the runtime dispatch values: a requirement dictionary
// (`Dictionary(sub₀ … subₙ₋₁, impl: S)`) and `Value::OpRef` (a resolved op
// symbol + captured dispatch dict).
//
// WI-1045 — a dictionary is now an ORDINARY value, so these are not views over
// a second store any more: `impl` reads the named child, `arity` is the
// positional arity, `sub` is positional child `k`. What each one still owns is
// the BOUNDARY CHECK — an anthill caller may pass any value, so
// [`Dictionary::from_value`] is what turns "some value" into a dictionary here,
// and it is the only place in the crate that test runs.
// Design: `docs/design/requirement-dictionaries.md` §2,
// `docs/design/requirement-channel.md` §9.

/// The dictionary an anthill caller passed, or the declared `type_mismatch`.
/// ONE owner for the four faces' boundary check, so they cannot come to accept
/// different things under one sort name.
fn expect_dictionary(interp: &Interpreter, v: &Value) -> Result<Dictionary, EvalError> {
    Dictionary::from_value(&interp.kb, v).ok_or_else(|| type_mismatch("Dictionary", v, None))
}

/// `Dictionary.impl(d) -> Symbol` — the resolved impl identity, surfaced as a
/// `Symbol` value.
fn dict_impl(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [d] = expect_args::<1>("Dictionary.impl", args)?;
    Ok(symbol_value(expect_dictionary(interp, &d)?.impl_sort()))
}

/// `Dictionary.arity(d) -> Int64` — number of sub-requirement dicts.
fn dict_arity(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [d] = expect_args::<1>("Dictionary.arity", args)?;
    Ok(Value::Int(expect_dictionary(interp, &d)?.arity() as i64))
}

/// `Dictionary.sub(d, i) -> Dictionary` — project the i-th sub-requirement.
/// No structural copy: the child rides an `Rc`, so this is a refcount bump. A
/// loud out-of-range error for an index the anthill caller supplies out of
/// bounds.
fn dict_sub(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [d, idx] = expect_args::<2>("Dictionary.sub", args)?;
    let i = match &idx {
        Value::Int(n) => *n,
        other => return Err(type_mismatch("Int64", other, None)),
    };
    let dict = expect_dictionary(interp, &d)?;
    let sub = usize::try_from(i).ok().and_then(|k| dict.sub(k)).ok_or_else(|| {
        EvalError::Internal(format!(
            "Dictionary.sub: index {i} out of range (dict has {} sub-requirements)",
            dict.arity(),
        ))
    })?;
    Ok(sub.into_value())
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
    use crate::kb::typing::resolve_op_target_checked;
    let [d, spec_op] = expect_args::<2>("Dictionary.resolveOp", args)?;
    let h = expect_dictionary(interp, &d)?;
    let Some(spec_op_sym) = interp.kb.value_symbol(&spec_op) else {
        return Err(type_mismatch("Symbol", &spec_op, None));
    };
    // WI-857: refuses a `NoProvider` marker — `resolveOp` MINTS A CALLABLE, so it is
    // a dispatch face, and letting it hand back an `OpRef` on the spec op is the
    // silent fall-through the marker exists to prevent.
    let target = resolve_op_target_checked(&interp.kb, h.impl_sort(), spec_op_sym)
        .map_err(|detail| EvalError::UnpinnedRequirement { detail })?;
    // WI-857: `target` is the RESOLVED member; `h` is a dictionary for the spec
    // `spec_op_sym` belongs to, whose layout has that spec's chain as its prefix.
    // Carry the named op so applying this ref measures `h` against the right layout —
    // reading it off `target` alone measures a spec dictionary against the provider's
    // own chain, which for a chain-free witness is 0 and rejects a valid dict.
    Ok(Value::OpRef { op: target, dict: Some(Rc::new(h)), named: Some(spec_op_sym) })
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
    use crate::kb::typing::resolve_op_target_checked;
    let [d] = expect_args::<1>("Dictionary.ops", args)?;
    let h = Rc::new(expect_dictionary(interp, &d)?);
    let impl_sym = h.impl_sort();
    // WI-857: refuse the marker UP FRONT, not per element. A marker's
    // `sort_ops_for_impl` is EMPTY, so a per-element check never runs and the bulk
    // face would answer `nil` — "this dictionary has no operations" — for a
    // dictionary that pins no provider at all. That is the silent skip the marker
    // exists to prevent, one level quieter than the one `resolveOp` refuses.
    if let Err(detail) = crate::kb::typing::marker_refusal(&interp.kb, impl_sym) {
        return Err(EvalError::UnpinnedRequirement { detail });
    }
    let elems: Vec<Value> = interp
        .kb
        .sort_ops_for_impl(impl_sym)
        .into_iter()
        .map(|target| {
            resolve_op_target_checked(&interp.kb, impl_sym, target)
                .map(|resolved| Value::OpRef {
                    op: resolved,
                    dict: Some(h.clone()),
                    // The table row IS the op named here, pre-resolution.
                    named: Some(target),
                })
                .map_err(|detail| EvalError::UnpinnedRequirement { detail })
        })
        .collect::<Result<Vec<Value>, EvalError>>()?;
    build_value_list(interp, elems)
}

/// `OpRef.op(r) -> Symbol` — the resolved operation's identity (a fully-
/// qualified op symbol), surfaced as a `Symbol` value.
fn opref_op(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r] = expect_args::<1>("OpRef.op", args)?;
    match r {
        Value::OpRef { op, .. } => Ok(symbol_value(op)),
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
            Some(h) => option_some(some_sym, value_key, h.as_value().clone()),
            None => option_none(none_sym),
        }),
        other => Err(type_mismatch("OpRef", &other, None)),
    }
}

/// `OpRef.named(r) -> Option[Symbol]` — the op the CALL named, when that differs
/// from the resolved `op` (WI-857); none() means "the same".
///
/// WI-1019 declared it because it is part of the value's identity, and the
/// accessor set claimed to expose everything the value holds while omitting it.
fn opref_named(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r] = expect_args::<1>("OpRef.named", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");
    match r {
        Value::OpRef { named, .. } => Ok(match named {
            Some(sym) => option_some(some_sym, value_key, symbol_value(sym)),
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
            })
        }
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

/// The `MapKey` a builtin's key argument addresses, or the loud type error.
///
/// One owner for the four `Map` builtins, which all ask the same question and
/// used to spell it two different ways (one `ok_or_else`, three four-line
/// `match`es). WI-1016 had to thread a `&KnowledgeBase` through every one of
/// them — `try_from_value` canonicalizes the two carriers of a symbol — which is
/// the second time this sequence was edited in lockstep.
fn map_key(
    kb: &crate::kb::KnowledgeBase,
    v: &Value,
) -> Result<super::map_arena::MapKey, EvalError> {
    super::map_arena::MapKey::try_from_value(kb, v).ok_or_else(|| EvalError::TypeMismatch {
        expected: "Map key (Int / Bool / String / Symbol / Term)",
        got: v.type_name().to_string(),
    })
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
    let key = map_key(&interp.kb, &k_arg)?;
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
    let key = map_key(&interp.kb, &k_arg)?;
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
    let key = map_key(&interp.kb, &k_arg)?;
    let present = interp.maps.with_body(&handle, |b| b.contains_key(&key));
    Ok(Value::Bool(present))
}

fn map_remove(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg, k_arg] = expect_args::<2>("Map.remove", args)?;
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let key = map_key(&interp.kb, &k_arg)?;
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

// `Error.raise` deliberately does NOT use the generic dispatcher. An unhandled
// Console/Modify effect is a missing-capability `Internal` fault, but an
// unhandled `Error` DEFAULTS to Throw — [`Interpreter::raise_error`]'s
// no-handler arm is `Raised { payload }` (WI-467: the payload is never lost),
// the same channel a native builtin's declared `effects Error` takes. The
// generic dispatcher's no-handler `Internal` became reachable from surface
// code the moment `Stream.head`'s default body raised (WI-818).
fn error_raise(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [payload] = args else {
        return Err(EvalError::ArityMismatch { op: "Error.raise", expected: 1, got: args.len() });
    };
    Err(interp.raise_error(payload.clone()))
}

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

use crate::persistence::Monotonicity;

/// Reduce `anthill.reflect.fact_monotonicity(functor)` via the simp rewriter
/// and read back the policy, comparing the reduced head by interned SYMBOL
/// identity — not a name string. A user entity sharing a short name (e.g. some
/// `my.pkg.constant`) must not be mistaken for the reflect variant; the repo's
/// representation note requires identity over names.
///
/// Returns `Ok(None)` for exactly ONE case: the reduced head is still
/// `fact_monotonicity` itself, i.e. NO in-memory reflect rule fired.
/// reflect.anthill deliberately carries no catch-all rule (under load-order
/// simp firing it would mask every override — most-specific-first is deferred,
/// 043 §4.6), so an unreduced result means the in-memory KB is silent and the
/// caller falls back to the owning store's policy, then the `monotone` default
/// ([`Interpreter::resolve_fact_monotonicity`]). Every OTHER non-variant
/// outcome — a missing reflect symbol, a reduction to an unexpected head, or a
/// non-functor carrier — is a LOUD error (repo principle: loud over silent
/// skip), never a silent default that would quietly void the guard.
fn reflect_fact_monotonicity(
    kb: &mut crate::kb::KnowledgeBase,
    functor: crate::intern::Symbol,
) -> Result<Option<Monotonicity>, EvalError> {
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
    let mono_sym = resolve(kb, Monotonicity::Monotone.reflect_variant_qname())?;
    let non_mono_sym = resolve(kb, Monotonicity::NonMonotone.reflect_variant_qname())?;
    let const_sym = resolve(kb, Monotonicity::Constant.reflect_variant_qname())?;

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
        Some(s) if s == non_mono_sym => Ok(Some(Monotonicity::NonMonotone)),
        Some(s) if s == const_sym => Ok(Some(Monotonicity::Constant)),
        Some(s) if s == mono_sym => Ok(Some(Monotonicity::Monotone)),
        // Unreduced: head is still the operation itself → no in-memory rule
        // matched → defer to the store fallback / default.
        Some(s) if s == fm_sym => Ok(None),
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

impl Interpreter {
    /// The single authority for a functor's write policy (proposal 053 /
    /// 007 §2), consulted by the persist / retract guards and the
    /// `Store.monotonicity` query. Precedence, per 007's 1-to-1 routing (a
    /// functor is owned by exactly one store, so these never overlap):
    ///   1. an in-memory `fact_monotonicity` reflect rule ("by reflect rule in
    ///      memory"), then
    ///   2. the owning external store's materialized policy ("by its API
    ///      externally"; resolved and materialized in `kb.extents` at
    ///      `register_mirror`), then
    ///   3. the `monotone` append-only default.
    fn resolve_fact_monotonicity(
        &mut self,
        functor: crate::intern::Symbol,
    ) -> Result<Monotonicity, EvalError> {
        if let Some(m) = reflect_fact_monotonicity(&mut self.kb, functor)? {
            return Ok(m);
        }
        // No in-memory rule: the owning mirror's policy, looked up by the SYMBOL
        // registration resolved its declared name to. Asking by name here — rendering
        // this resolved functor back to text — is what made rung 3 ambiguous: a store
        // whose spelling did not match read exactly like a store that declared nothing
        // (WI-919). A miss now means only what rung 3 says it means.
        Ok(self.kb.mirror_monotonicity(functor).unwrap_or(Monotonicity::Monotone))
    }
}

// ── Persistence builtins (proposal 007 §4) ─────────────────────

/// `anthill.persistence.Store.persist(store, fact, meta) -> StoredRef[Term]`.
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
    if interp.resolve_fact_monotonicity(functor)? == Monotonicity::Constant {
        let name = interp.kb.qualified_name_of(functor).to_string();
        return Err(interp.raise_error(Value::Str(format!(
            "persist refused: functor `{name}` is constant — no assert (proposal 053)"
        ))));
    }

    // The KB seam owns mirror-before-resident ordering and mints the
    // source-neutral reference that future writes must carry.
    let row = interp.kb.persist_mirrored(&key, Value::term(fact_term), None)
        .map_err(|e| interp.raise_error(Value::Str(format!("persist failed: {e}"))))?;
    stored_ref_value(interp, row)
}

/// `anthill.persistence.Store.monotonicity(store, functor) -> Monotonicity`.
///
/// The write-policy QUERY (proposal 053 / 007 §2): answers a functor's policy
/// so the system can plan (persist iff `!= constant`, retract iff
/// `non_monotone`) WITHOUT attempting a write and catching the failure. The
/// answer is the owning store's authority — an in-memory reflect rule, else the
/// store's materialized policy, else the `monotone` default
/// ([`Interpreter::resolve_fact_monotonicity`]). The `store` argument selects
/// nothing here (1-to-1 routing already binds the functor to its store); it is
/// part of the operation's shape and validated as a store-shaped value so a
/// stray carrier is loud rather than silently answered.
fn persistence_monotonicity(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, functor_val] = expect_args::<2>("monotonicity", args)?;
    // Validate the first arg is a store-shaped value (loud on a stray carrier),
    // even though the policy is keyed by functor — 1-to-1 routing already binds
    // the functor to its store. Keeps the op honest to its signature.
    let _key = interp.store_canonical_key(&store_val)?;

    let Some(functor) =
        crate::kb::term_view::TermView::head(&functor_val, &interp.kb).functor_sym()
        .or_else(|| match &functor_val {
            // A functor passed as its raw name string.
            Value::Str(name) => interp.kb.try_resolve_symbol(name),
            _ => None,
        })
    else {
        return Err(EvalError::TypeMismatch {
            expected: "Symbol (functor)",
            got: functor_val.type_name().to_string(),
        });
    };

    let mono = interp.resolve_fact_monotonicity(functor)?;
    let variant = mono.reflect_variant_qname();
    let functor_sym = interp.kb.try_resolve_symbol(variant).ok_or_else(|| {
        EvalError::Internal(format!(
            "monotonicity: `{variant}` unresolved — the anthill.reflect substrate \
             (proposal 053) must be loaded"
        ))
    })?;
    Ok(Value::Entity {
        functor: functor_sym,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    })
}

/// `anthill.persistence.NonMonotonicStore.retract(store, reference) -> Bool`.
fn persistence_retract(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, id_val] = expect_args::<2>("retract", args)?;
    let key = interp.store_canonical_key(&store_val)?;

    let reference = match id_val {
        Value::FactRef(reference) => reference,
        other => return Err(EvalError::TypeMismatch {
            expected: "FactRef",
            got: other.type_name().to_string(),
        }),
    };

    // An external owner receives its native key through the KB seam. For a
    // mirrored resident row, the reference also carries the mirror it came
    // from; accepting a different `store` argument would silently route a
    // mutation to the wrong durable extent.
    let Some(rule_id) = reference.resident_rule() else {
        let outcome = interp.kb.retract_persistent(&reference)
            .map_err(|e| EvalError::Internal(format!("retract: {e}")))?;
        return Ok(Value::Bool(outcome));
    };

    if reference.resident_mirror() != Some(key.as_str()) {
        return Err(EvalError::Internal(
            "retract: FactRef does not belong to the supplied store".into(),
        ));
    }

    if !interp.kb.is_rule_alive(rule_id) {
        return Ok(Value::Bool(false));
    }
    let head = interp.kb.rule_head_value(rule_id).clone();
    if let Err(error) = interp.kb.check_fact_mutation_target(&head) {
        return Err(interp.raise_error(Value::Str(error.to_string())));
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
    if interp.resolve_fact_monotonicity(functor)? != Monotonicity::NonMonotone {
        let name = interp.kb.qualified_name_of(functor).to_string();
        return Err(interp.raise_error(Value::Str(format!(
            "retract refused: functor `{name}` is not non_monotone (proposal 053)"
        ))));
    }

    let outcome = interp.kb.retract_persistent(&reference)
        .map_err(|e| interp.raise_error(Value::Str(format!("retract failed: {e}"))))?;
    Ok(Value::Bool(outcome))
}

/// `anthill.persistence.NonMonotonicStore.update(store, reference, new) ->
/// Option[StoredRef[Term]]`.
///
/// Both mounted owners and resident mirrors implement this through the KB's
/// single update seam; callers never compose retract and persist themselves.
fn persistence_update(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, reference_val, new] = expect_args::<3>("update", args)?;
    let key = interp.store_canonical_key(&store_val)?;
    let reference = match reference_val {
        Value::FactRef(reference) => reference,
        other => return Err(EvalError::TypeMismatch {
            expected: "FactRef",
            got: other.type_name().to_string(),
        }),
    };
    if let Some(rule_id) = reference.resident_rule() {
        if reference.resident_mirror() != Some(key.as_str()) {
            return Err(EvalError::Internal(
                "update: FactRef does not belong to the supplied store".into(),
            ));
        }
        if !interp.kb.is_rule_alive(rule_id) {
            let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
            return Ok(option_none(none_sym));
        }
        let old = interp.kb.rule_head_value(rule_id).clone();
        if let Err(error) = interp.kb.check_fact_mutation_target(&old) {
            return Err(interp.raise_error(Value::Str(error.to_string())));
        }
        let Some(functor) = crate::kb::term_view::TermView::head(&old, &interp.kb).functor_sym() else {
            return Err(EvalError::Internal(
                "update: rule head has no functor — cannot apply the monotonicity guard (proposal 053)".into(),
            ));
        };
        if interp.resolve_fact_monotonicity(functor)? != Monotonicity::NonMonotone {
            let name = interp.kb.qualified_name_of(functor).to_string();
            return Err(interp.raise_error(Value::Str(format!(
                "update refused: functor `{name}` is not non_monotone (proposal 053)"
            ))));
        }
    }
    let row = interp
        .kb
        .update_persistent(&reference, new, None)
        .map_err(|e| interp.raise_error(Value::Str(format!("update failed: {e}"))))?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    Ok(match row {
        Some(row) => option_some(some_sym, interp.fields.value, stored_ref_value(interp, row)?),
        None => option_none(none_sym),
    })
}

/// `anthill.persistence.Store.flush(store, delta) -> Bool`.
/// `delta` is accepted for spec conformance but ignored — the FileStore
/// tracks its delta internally via the persist / retract buffers.
fn persistence_flush(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, _delta_val] = expect_args::<2>("flush", args)?;
    let key = interp.store_canonical_key(&store_val)?;

    let mut store = interp.kb.take_mirror(&key).ok_or_else(|| {
        EvalError::Internal(format!("flush: no store registered for key `{key}`"))
    })?;
    let outcome = store.flush(&interp.kb);
    interp.kb.put_mirror(key, store);
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
        let store = interp.kb.mirror(&key).ok_or_else(|| {
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

    /// WI-881 — every `host_fn_by_key` entry's declared ARITY is the arity its function
    /// actually accepts.
    ///
    /// The registry writes that number by hand, a second time, beside a function whose
    /// `expect_args::<N>` already fixed it. A disagreement is SILENT where it matters:
    /// `register_operation_mappings` compares the column against the *anthill*
    /// declaration, so a wrong column paired with a matching declaration passes
    /// registration and dies `ArityMismatch` at the first call — which is exactly the
    /// defect class WI-876 added that check to close, one level down, and the ticket
    /// that opened 25 new chances to hit it is the one that owes the check.
    ///
    /// Probed rather than proved: call each function with `arity` placeholder operands
    /// and assert it did not answer `ArityMismatch`. Operand TYPES are wrong on purpose
    /// — a `TypeMismatch` (or any other error, or a value) all mean the arity was
    /// accepted, which is the only thing under test.
    ///
    /// WI-884 — driven off [`HOST_FNS`] itself. It used to restate every key in a
    /// second hand-written list here, which a newly registered function escapes
    /// SILENTLY: the omission is invisible, and the entry it would have caught is one
    /// whose wrong arity survives registration and dies at the first call. A test
    /// against a hand-copied roster of the thing under test checks the copy.
    #[test]
    fn every_host_fn_key_declares_the_arity_its_function_accepts() {
        for (key, _, _) in HOST_FNS {
            let host = host_fn_by_key(key).unwrap_or_else(|| panic!("{key} is registered"));
            let args = vec![Value::Float(1.0); host.arity];
            if let Err(EvalError::ArityMismatch { expected, got, .. }) =
                (host.f)(&mut dummy(), &args)
            {
                panic!(
                    "host_fn_by_key says {key} takes {}, but the function wants {expected} \
                     (it was given {got})",
                    host.arity
                );
            }
        }
        assert!(
            host_fn_by_key("no_such_host_function").is_none(),
            "the control: the registry is CLOSED, so an unknown key has no entry",
        );
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
