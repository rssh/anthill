//! Standard builtins backing stdlib operation signatures.
//!
//! Each entry maps a fully-qualified anthill operation name (as declared
//! in `stdlib/anthill/prelude/`) to a Rust function that consumes evaluated
//! `Value` arguments and returns a result `Value`. Operations defined in the
//! prelude by rules (e.g. `anthill.prelude.List.length`) are not registered
//! here — those need the resolver bridge that arrives with M4.
//!
//! `anthill.prelude.Additive.zero` is a nullary operation returning the
//! additive identity. Dispatch needs a type hint that we don't have inside
//! a zero-arg call, so it's left for the resolver / rule system. (It was
//! `Numeric.zero-val` until WI-20260825-1WBZT split the syntax categories out;
//! `Multiplicative.one` is the same shape and is unregistered for the same reason.)
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
// WI-20260827-2YHZ3 — the carrier-neutral operand accessors (`as_int64`, `as_bool`, …)
// every scalar builtin below reads its arguments through.
use crate::kb::term_view::TermView;

/// Register the standard-library builtins. Symbols that don't resolve in the
/// current KB (stdlib partially loaded, e.g. a minimal test harness) are
/// skipped — every other error is propagated.
pub fn register_standard_builtins(interp: &mut Interpreter) -> Result<(), EvalError> {
    // WI-880 — `Additive.add`/`sub`/`neg` and `Multiplicative.mul` are NOT REGISTERED
    // HERE. They were, keyed by the SPEC op, which is WI-876's defect A stated for the
    // arithmetic family: one host-scalar implementation was the backing for every
    // carrier that never wrote its own, and `op_backed`'s `kb.is_builtin` leg certified
    // it as backed for all of them. Each carrier names its own in its binding block's
    // `operation_map` (`int_add` / `float_add` / `bigint_add`, …); `Additive.sub` gains
    // the DEFAULT BODY that `arithmetic.anthill`'s `sub_def` law always stated, which is
    // what a structural carrier inherits now that nothing shadows it.
    //
    // WI-20260825-1WBZT put the declarations on the OPERATOR'S OWN CATEGORY
    // (`stdlib/anthill/prelude/arithmetic.anthill`), which `Numeric` reaches by
    // `provides`; that is the address the carriers' declarations now shadow per carrier.

    // WI-644 / proposal 004: eq/neq live on the PartialEq base (Eq is the lawful
    // marker). The semantic `eq`/`neq` are IEEE for Float operands (below),
    // structural otherwise.
    //
    // WI-880 — THE ONE SPEC-OP REGISTRATION THAT STAYS, and the ticket that removed the
    // others is where the reason is argued. `builtin_eq` is not the defect shape its
    // siblings were: it does not decide by testing its operands and then answer wrongly
    // for a carrier it cannot handle — it DISPATCHES, through `semantic_equal`, to the
    // head carrier's own `eq` before deciding anything structurally, which is exactly
    // why `eq` already worked on a structural carrier when `compare` did not (WI-876's
    // asymmetry).
    //
    // AND IT CANNOT SIMPLY BE RE-KEYED, which is the part that makes this a design and
    // not a leftover. Equality fires from UNIFICATION as well as from a call — an `=`
    // goal in a rule body reaches `sem_eq_dispatch` (kb/resolve.rs), where there is no
    // call site and therefore no requirement dictionary to select a provider with
    // (058 §3.7). A value-directed step has to exist for that path whatever the
    // registration says, so keying `eq` per carrier would ADD a channel rather than
    // replace one. It would also cost each scalar carrier a declared `eq` member, and
    // every one of them imports `PartialEq.{eq}` for its own laws and constraints —
    // which 059 R4 then refuses as a capture (measured on `Float.mul`, this ticket).
    //
    // A dispatching builtin is still a workaround for a missing key rather than a
    // design, and WI-880's own note says so. What would retire it is a value-directed
    // entry that is not spelled as a spec-op registration; nothing owns that yet.
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

    // WI-884 FOUND HALF OF `String`'S AND `Int64`'S HOST SURFACE REGISTERED HERE BY
    // HARDCODED QUALIFIED NAME AND HALF IN ITS BINDING BLOCK. WI-880 MIGRATED THE
    // REST, and the whole block is gone: `concat`/`length`/`startsWith`/`endsWith`/
    // `substring`/`toUpper`/`toLower`/`repeat`, `Int64`'s `abs`/`mod`/`rem`/`div`/
    // `divExact`/`sign`/`to_float`/`to_string`, `Float`'s `div`/`isNaN`/`isInfinite`/
    // `isFinite` and `BigInt`'s three conversions are all `operation_map` entries now.
    //
    // THESE WERE NEVER THE SPEC-OP DEFECT — they are the CARRIER's own operations, so
    // the qualified name already keyed them per carrier and they answered correctly.
    // The cost was that THE TWO HALVES WERE NOT EQUIVALENT TO THEIR READERS, and each
    // of the three is closed by the move: `op_is_interpretable` (kb/typing.rs) counts
    // a host MAPPING and not a hardcoded registration, so `String.contains` read as
    // backed while `String.concat` did not though one interpreter ran both;
    // `kb.host_op_mappings()` — what WI-886 wants a second backend to consume — saw
    // six of `String`'s fourteen; and only the mapped half had its arity checked
    // against the anthill declaration. kernel-language.md §8.7 recorded the first as a
    // SOUNDNESS gap rather than an incompleteness: `:- String.concat("a", "b") = "ab"`
    // answered 0 as a rule-body goal, DECIDED false rather than suspended, so `not(…)`
    // over it answered 1.

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

    register_if_present(
        interp,
        "anthill.prelude.LogicalStream.splitFirst",
        logical_stream_split_first,
    )?;
    register_if_present(
        interp,
        "anthill.prelude.Relation.splitFirst",
        relation_split_first,
    )?;
    register_if_present(interp, "anthill.prelude.Relation.negate", relation_negate)?;
    register_if_present(interp, "anthill.prelude.Relation.union", relation_union)?;
    register_if_present(
        interp,
        "anthill.prelude.Relation.where_run",
        relation_where_run,
    )?;
    register_if_present(
        interp,
        "anthill.prelude.Relation.guarded_of",
        relation_guarded_of,
    )?;
    register_if_present(
        interp,
        "anthill.prelude.Relation.join_run",
        relation_join_run,
    )?;
    register_if_present(
        interp,
        "anthill.prelude.Relation.conjoin_of",
        relation_conjoin_of,
    )?;
    register_if_present(
        interp,
        "anthill.prelude.Relation.project_run",
        relation_project_run,
    )?;
    register_if_present(interp, "anthill.prelude.Relation.fix", relation_fix)?;
    register_if_present(interp, "anthill.prelude.Relation.rename", relation_rename)?;

    register_if_present(interp, "anthill.prelude.Time.now", time_now)?;

    // Persistence (proposal 007) is NOT here — WI-931 moved its six operations to
    // `HOST_FNS` + the `operation_map` clauses in
    // `rustland/anthill-stl/anthill/persistence.anthill`, so the backing they
    // always had is DECLARED and the load-time provision check can see it. See
    // the `store_*` entries below.

    register_if_present(interp, "anthill.prelude.Console.print", console_print)?;
    register_if_present(interp, "anthill.prelude.Console.println", console_println)?;
    register_if_present(interp, "anthill.prelude.Console.eprint", console_eprint)?;
    register_if_present(interp, "anthill.prelude.Console.eprintln", console_eprintln)?;
    register_if_present(
        interp,
        "anthill.prelude.Console.read_line",
        console_read_line,
    )?;

    register_if_present(interp, "anthill.prelude.ModifyRuntime.get", modify_get)?;
    register_if_present(interp, "anthill.prelude.ModifyRuntime.set", modify_set)?;
    register_if_present(interp, "anthill.prelude.Error.raise", error_raise)?;
    register_if_present(interp, "anthill.prelude.Cell.new", cell_new)?;
    register_if_present(interp, "anthill.prelude.Cell.get", cell_get)?;
    register_if_present(interp, "anthill.prelude.Cell.set", cell_set)?;

    // WI-577 — first-class runtime dispatch values: the anthill face of a
    // requirement dictionary (a resolved spec impl) and `Value::OpRef` (a resolved
    // operation reference). Native readers over the values themselves (WI-1045).
    register_if_present(
        interp,
        "anthill.realization.runtime.Dictionary.impl",
        dict_impl,
    )?;
    register_if_present(
        interp,
        "anthill.realization.runtime.Dictionary.arity",
        dict_arity,
    )?;
    register_if_present(
        interp,
        "anthill.realization.runtime.Dictionary.sub",
        dict_sub,
    )?;
    register_if_present(
        interp,
        "anthill.realization.runtime.Dictionary.resolveOp",
        dict_resolve_op,
    )?;
    register_if_present(
        interp,
        "anthill.realization.runtime.Dictionary.ops",
        dict_ops,
    )?;
    register_if_present(interp, "anthill.realization.runtime.OpRef.op", opref_op)?;
    register_if_present(interp, "anthill.realization.runtime.OpRef.dict", opref_dict)?;
    register_if_present(
        interp,
        "anthill.realization.runtime.OpRef.named",
        opref_named,
    )?;
    register_if_present(
        interp,
        "anthill.realization.runtime.OpRef.spreadLabels",
        opref_spread_labels,
    )?;
    register_if_present(
        interp,
        "anthill.realization.runtime.OpRef.opRequirements",
        opref_op_requirements,
    )?;

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
const HOST_FNS: &[(
    &str,
    usize,
    fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>,
)] = &[
    // The TOTAL scalar order (`Ord`): `Int64`, `BigInt`, `String`.
    ("ordered_compare", 2, ordered_compare),
    ("ordered_gt", 2, ordered_gt),
    ("ordered_gte", 2, ordered_gte),
    ("ordered_lt", 2, ordered_lt),
    ("ordered_lte", 2, ordered_lte),
    ("ordered_max", 2, ordered_max),
    ("ordered_min", 2, ordered_min),
    // WI-880 — THE ARITHMETIC FAMILY, one key per (carrier, operation). These are the
    // entries that replaced the four spec-op registrations `register_standard_builtins`
    // used to make; the section header above their definitions carries the measurement
    // and the overflow table that is the argument for keying them apart.
    ("int_add", 2, int_add),
    ("int_sub", 2, int_sub),
    ("int_mul", 2, int_mul),
    ("int_neg", 1, int_neg),
    ("float_add", 2, float_add),
    ("float_sub", 2, float_sub),
    ("float_mul", 2, float_mul),
    ("bigint_add", 2, bigint_add),
    ("bigint_sub", 2, bigint_sub),
    ("bigint_mul", 2, bigint_mul),
    ("bigint_neg", 1, bigint_neg),
    // WI-20260824-VT8CF — `BigInt`'s division with remainder, named by its own binding's
    // `operation_map`.
    ("bigint_div", 2, bigint_div),
    ("bigint_mod", 2, bigint_mod),
    ("bigint_rem", 2, bigint_rem),
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
    // WI-880 — the CARRIER-OWNED surface WI-884 left registered by hardcoded qualified
    // name. Nothing about these operations changed; they are keyed through the same
    // channel as their siblings now, so a reader asking "what does the host implement
    // for this carrier" gets one answer instead of two halves. See the deleted block
    // in `register_standard_builtins` for the three readers that were split.
    ("int_abs", 1, int_abs),
    ("int_mod", 2, int_mod),
    ("int_rem", 2, int_rem),
    // `div` and `divExact` are ONE function under two names — `Int64.divExact` is a
    // historical alias a stdlib rule rewrites to `div`, and the mapping says so
    // outright where the two `register_if_present` lines said it by repetition.
    ("int_div", 2, int_div),
    ("int_sign", 1, int_sign),
    ("int_to_float", 1, int_to_float),
    ("int_to_string", 1, int_to_string),
    ("float_div", 2, float_div),
    ("float_is_nan", 1, float_is_nan),
    ("float_is_infinite", 1, float_is_infinite),
    ("float_is_finite", 1, float_is_finite),
    ("bigint_to_bigint", 1, bigint_to_bigint),
    ("bigint_to_int", 1, bigint_to_int),
    ("bigint_to_float", 1, bigint_to_float),
    ("string_concat", 2, string_concat),
    ("string_length", 1, string_length),
    ("string_starts_with", 2, string_starts_with),
    ("string_ends_with", 2, string_ends_with),
    ("string_substring", 3, string_substring),
    ("string_to_upper", 1, string_to_upper),
    ("string_to_lower", 1, string_to_lower),
    ("string_repeat", 2, string_repeat),
    // WI-20260826-VPEWK — `Bool`'s three under their MAPPED spelling, so that the
    // readers of `is_interpreter_mapped_op` can see them. They keep their hardcoded
    // `register_if_present` registration below as well, and that is deliberate: the
    // mapping is declared in `rustland/anthill-stl/anthill/bool.anthill`, so a KB
    // loaded from `stdlib/` ALONE has no `operation_map` clause to register from and
    // would otherwise lose `and`/`or`/`not` entirely. `register_builtin` inserts, so
    // the two registrations are the same function under the same symbol.
    //
    // This is WI-884's split closing for ONE sort, not the whole migration WI-880
    // owns: the eight `String`/`Int64` hardcoded names above are still unmapped, and
    // `String.concat("a", "b") = "ab"` still answers 0 at an operand for that reason.
    ("bool_and", 2, bool_and),
    ("bool_or", 2, bool_or),
    ("bool_not", 1, bool_not),
    ("string_is_empty", 1, string_is_empty),
    ("string_contains", 2, string_contains),
    ("string_index_of", 2, string_index_of),
    ("string_replace", 3, string_replace),
    ("string_trim", 1, string_trim),
    ("string_split", 2, string_split),
    // WI-1121 — the two primitives a content-derived id is minted from (§6.5).
    ("string_slug", 2, string_slug),
    ("string_digest_base32", 2, string_digest_base32),
    // WI-880 — THE REFLECTION SURFACE, keyed through the same channel as everything
    // else the host implements. These twenty-six were registered by hardcoded qualified
    // name, which answered correctly from an operation body and was INVISIBLE to every
    // reader of "is this operation host-backed" — so a rule could not read a term at
    // all, and `not(...)` over an accessor answered 1 out of a call that never ran
    // (kernel-language.md §5.2's decided-false decline). The binding block is
    // `rustland/anthill-stl/anthill/reflect.anthill`; it also records why twenty of them
    // take a NAMESPACE target rather than a carrier one.
    ("term_functor_name", 1, term_functor_name),
    ("term_field", 2, term_field),
    ("term_as_string", 1, term_as_string),
    ("term_as_int", 1, term_as_int),
    ("term_as_entity", 1, term_as_entity),
    ("term_to_string", 1, reflect_term_to_string),
    ("term_list_items", 1, reflect_term_list_items),
    ("reflect_field_access", 2, reflect_field_access),
    ("extract_type_builtin", 1, extract_type_builtin),
    ("as_term", 1, as_term),
    ("reflect_fresh_var", 1, reflect_fresh_var),
    ("reflect_make_fn", 2, reflect_make_fn),
    // WI-722 (043.1) — the occurrence-BUILD side of a compile-time macro: a per-shape
    // occurrence builder returning a spliceable `NodeOccurrence` (not a `Term`, as
    // `make_fn` does). Available wherever eval runs; a macro is the only caller, at
    // compile time via the `[simp]` fire hook.
    ("reflect_make_apply", 3, reflect_make_apply),
    ("reflect_replace_named_arg", 3, reflect_replace_named_arg),
    ("reflect_unify", 3, reflect_unify),
    // WI-722 (043.1) — the occurrence-READ side of a compile-time macro, the
    // value-domain complement of the resolver's `occurrence_term` / `sub_occurrences` /
    // `type_of` goal handlers (`kb/resolve.rs`). A macro reads its argument occurrences
    // through these (structure via `occurrence_term`, children via `sub_occurrences`,
    // the typer-stamped type via `occurrence_type`) and rebuilds through `make_apply`.
    // Reached on the eval side (surface A) so the macro-eval path (`call_op_bridged`)
    // dispatches them with `Value::Node` args untouched.
    //
    // WI-880 moved these two paragraphs here with the registrations they describe. Left
    // where they were, they sat directly above `register_if_present("…Time.now")` and
    // read as documentation of `Time.now` — found by /code-review.
    ("reflect_occurrence_term", 1, reflect_occurrence_term),
    ("reflect_occurrence_type", 1, reflect_occurrence_type),
    ("reflect_sub_occurrences", 1, reflect_sub_occurrences),
    (
        "reflect_sub_occurrence_labels",
        1,
        reflect_sub_occurrence_labels,
    ),
    ("reflect_is_modifiable", 1, reflect_is_modifiable),
    ("kb_ambient", 0, kb_ambient),
    ("kb_loaded", 1, kb_loaded),
    // WI-5XBBQ — the layer DELTA, as operations rather than as facts. A fact is a
    // channel the loaded candidate can write (measured: it can hand-write any reflect
    // row), so a gate reading a relation about its own subject reads a channel that
    // subject controls. These read Rust-side marks outside the clause store.
    ("kb_layer_symbols", 1, kb_layer_symbols),
    ("kb_layer_clauses", 1, kb_layer_clauses),
    ("kb_execute", 2, kb_execute),
    ("kb_facts_of", 2, kb_facts_of),
    ("kb_stored_facts_of", 2, kb_stored_facts_of),
    ("subst_lookup", 2, subst_lookup),
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

/// The function `key` names, from EITHER half of the registry: this runtime's own
/// [`HOST_FNS`], then WI-1122's embedder table on the KB.
///
/// `HOST_FNS` is consulted first, but the order is not a precedence rule — a key
/// cannot be in both, because `KnowledgeBase::register_host_fn` refuses to register
/// one this runtime already ships. The order is just the cheap check first.
///
/// A miss in BOTH is still the WI-876 refusal at the caller, not a silent skip.
fn host_fn_by_key(kb: &crate::kb::KnowledgeBase, key: &str) -> Option<HostFn> {
    if let Some(hit) = HOST_FNS
        .iter()
        .find(|&&(k, _, _)| k == key)
        .map(|&(_, arity, f)| HostFn {
            arity,
            f: HostFnImpl::Static(f),
        })
    {
        return Some(hit);
    }
    kb.host_fn_registry().get(key)
}

/// WI-1122 — is `key` one this runtime ships? Asked by
/// `KnowledgeBase::register_host_fn` so an embedder cannot shadow a built-in entry.
/// The one reader of [`HOST_FNS`] outside this module, which is why it is a predicate
/// over the key rather than an accessor handing out the table.
pub(crate) fn is_builtin_host_fn_key(key: &str) -> bool {
    HOST_FNS.iter().any(|&(k, _, _)| k == key)
}

// WI-876's `HostFn` — the function plus the ARITY it accepts — now lives in
// `kb::host_fns`, because WI-1122's embedder table stores the same type and that
// table has to live on the KB. The arity rationale moved with it; what matters here
// is that BOTH halves of the registry yield this one type, so the arity check in
// `register_operation_mappings` cannot tell which half an entry came from and applies
// to an embedder entry unchanged.
use crate::kb::host_fns::{HostFn, HostFnImpl};

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
    // WI-880 — DERIVED ONCE PER KB, not once per interpreter. This function runs for
    // every fresh interpreter, and `run_in_bridge_interp` builds one per bridged
    // evaluation; everything below the `register_on` calls is a pure function of the KB,
    // so it belongs on the KB. See `KnowledgeBase::host_op_registrations`' field for the
    // per-crossing cost it removes.
    //
    // The list is CLONED out before registering: `register_builtin_sym` needs
    // `&mut Interpreter` and the cache is borrowed from `interp.kb()`. A `HostFn` clone
    // is a `usize` plus a function pointer (or an `Arc::clone` for an embedder entry) —
    // the three `String` clones, the key scan, the arity lookup and the `canonical_sym`
    // hash that used to ride here are all gone.
    let registrations: Vec<(crate::intern::Symbol, crate::kb::host_fns::HostFn)> = interp
        .kb()
        .host_op_registrations(|| build_host_op_registrations(interp.kb()))
        .map_err(EvalError::Internal)?
        .to_vec();
    for (sym, host) in registrations {
        host.register_on(interp, sym);
    }
    Ok(())
}

/// WI-880 — resolve every `operation_map` entry this runtime is responsible for to the
/// `(Symbol, HostFn)` pairs an interpreter registers, refusing both failure modes.
/// Memoized by [`KnowledgeBase::host_op_registrations`]; see that field for why.
///
/// A pure function of the KB, which is what makes memoizing it sound: the mappings, the
/// two host-function registries and the declared arities are all fixed by the time
/// `set_host_op_mappings` runs, and that call `seal`s the embedder table.
fn build_host_op_registrations(
    kb: &crate::kb::KnowledgeBase,
) -> Result<Vec<(crate::intern::Symbol, crate::kb::host_fns::HostFn)>, String> {
    let mut out = Vec::new();
    for m in kb.host_op_mappings() {
        // WI-886 — the SAME constant `KnowledgeBase::is_interpreter_mapped_op`'s index
        // is built from. That predicate promises this pass registered the operation, so
        // the two filters must be one string.
        if m.lang != crate::kb::load::INTERPRETER_LANG {
            continue;
        }
        let Some(host) = host_fn_by_key(kb, &m.host_fn) else {
            // Loud, and it stops the whole interpreter — including the short-lived one
            // the resolver builds per bridged evaluation, so an unrelated `[simp]` fire
            // or `eq` dispatch reports this too. That breadth is deliberate: a binding
            // block naming a function the runtime does not have is broken for the whole
            // program, not for one call. The message says so, because the site it
            // surfaces at will often have nothing to do with the mapping.
            return Err(format!(
                "broken binding block: operation_map names host function {:?} for \
                 {}, which the rust runtime does not provide. No interpreter can be \
                 built for this program until the binding is fixed — this error may \
                 surface at a call that has nothing to do with {}.",
                m.host_fn, m.op_qn, m.op_qn
            ));
        };
        // `op` is `None` only when the loader already refused this mapping (the
        // operation is undeclared, or is not an operation at all), so the load errored
        // and nothing should be registered against it.
        let Some(sym) = m.op else { continue };
        // The declared operation and the host function must AGREE ON ARITY. Checked
        // at registration, which is the earliest point that knows both: the loader
        // knows the operation's arity but not another language's function set, and
        // this registry is the only thing that knows the host's.
        //
        // Off the CACHED signature (WI-656) rather than `lookup_operation_info`, whose
        // record build clones every per-field `Vec` to be dropped after one `.len()` —
        // the same reason `operation_is_declared` exists beside it. WI-886 moved both
        // tiers behind `declared_arity`, so cpp-gen's peer check of the same mappings
        // asks the same question the same way — `op_record` being `pub(crate)`, it
        // could not before. The fact-scan fallback inside it is kept for a KB whose
        // signatures are not built yet, where the old reader would still have answered.
        if let Some(n) = crate::kb::op_info::declared_arity(kb, sym) {
            if n != host.arity {
                return Err(format!(
                    "operation_map maps {} to {:?}, but {} takes {n} \
                     argument(s) and {:?} takes {}",
                    m.op_qn, m.host_fn, m.op_qn, m.host_fn, host.arity
                ));
            }
        }
        // Under BOTH spellings, matching `set_host_op_mappings`' index: a qualified
        // name can be interned under several `Symbol`s, and eval's builtin lookup is a
        // RAW map hit, so whichever spelling reaches dispatch must find the same
        // implementation the predicate promised.
        let canon = kb.canonical_sym(sym);
        if canon != sym {
            out.push((canon, host.clone()));
        }
        out.push((sym, host));
    }
    Ok(out)
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
    for crate::kb::load::HostConstMapping {
        const_sym,
        const_qn,
        host_fn,
        ..
    } in mappings
    {
        let Some(host) = host_fn_by_key(interp.kb(), &host_fn) else {
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
        host.register_on(interp, sym);
        if canon != sym {
            host.register_on(interp, canon);
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
    use crate::kb::term_view::{TermView, ViewHead};
    let [receiver, field] = expect_args::<2>("anthill.reflect.field_access", args)?;
    // The SELECTOR reads carrier-neutrally too (WI-20260827-3ZNBC): the typer
    // splices it as a literal today, but `make_apply`-built reflect calls can hand
    // this a term-carried name, and a selector is a string on every carrier.
    let field_name = str_operand(interp.kb(), &field)
        .map_err(|_| {
            EvalError::Internal(format!(
                "field_access: field name must be a string, got {}",
                field.type_name()
            ))
        })?
        .into_owned();
    // WI-20260827-2YHZ3 — READ THE RECEIVER THROUGH `TermView`, so this one arm
    // serves every carrier an entity can arrive on. It used to match
    // `Value::Entity` alone and refuse the rest, which made `row.x.v` die
    // "receiver is not an entity (got Node)" the moment a relation column carried
    // its answer as an occurrence — and a `Value::Term`-carried entity was in the
    // same position. `Value::Entity`, `Value::Term` and `Value::Node` all view as
    // `ViewHead::Functor` (term_view.rs), so the collapse REMOVES a case rather
    // than adding one: the arm below is the old entity arm with its three reads —
    // functor, named args, positional args — asked of the view instead of the
    // variant.
    let receiver_functor = match receiver.head(interp.kb()) {
        ViewHead::Functor {
            functor: Some(f), ..
        } => Some(f),
        ViewHead::Ref(sym) => Some(sym),
        _ => None,
    };
    match (&receiver, receiver_functor) {
        (_, Some(functor)) if !matches!(receiver, Value::Tuple { .. }) => {
            let functor = &functor;
            // A field supplied by NAME — match by short name.
            for sym in receiver.named_keys(interp.kb()) {
                let full = interp.kb().local_name_of(sym);
                let short = full.rsplit('.').next().unwrap_or(full);
                if short == field_name.as_str() {
                    let val = receiver
                        .named_arg(interp.kb(), sym)
                        .map(|c| c.to_value())
                        .expect("a key from `named_keys` reads back");
                    return absent_option_as_none(interp, *functor, field_name.as_str(), Some(val));
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
                    let supplied_by_name = receiver.named_keys(interp.kb()).iter().any(|s| {
                        let nf = interp.kb().local_name_of(*s);
                        nf.rsplit('.').next().unwrap_or(nf) == short
                    });
                    if supplied_by_name {
                        continue;
                    }
                    if short == field_name.as_str() {
                        let val = receiver
                            .pos_arg(interp.kb(), pos_cursor)
                            .map(|v| v.to_value());
                        return absent_option_as_none(interp, *functor, field_name.as_str(), val);
                    }
                    pos_cursor += 1;
                }
            }
            absent_option_as_none(interp, *functor, field_name.as_str(), None)
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
        (Value::Tuple { .. }, _) => receiver
            .tuple_components()
            .and_then(|c| c.by_label(interp.kb(), field_name.as_str()))
            .cloned()
            .ok_or_else(|| {
                EvalError::Internal(format!(
                    "field_access: tuple has no component '{}'",
                    field_name
                ))
            }),
        (other, _) => Err(EvalError::Internal(format!(
            "field_access: receiver is not an entity (got {})",
            other.type_name()
        ))),
    }
}

/// A DECLARED `Option[T]` field the value does not actually supply reads as `none()`.
///
/// WI-20260827-3ZNBC — this used to live one layer away and only on one carrier.
/// `materialize_entity` did it while REIFYING a term into a `Value::Entity`, so a
/// relation column over an entity arrived with its optional slots already filled and
/// `row.item.context` answered `none()`. With the drain handing the column through on
/// its own carrier the reification is gone, and without this the same read answers the
/// loader's synthetic Var — which matches neither `case some(v)` nor `case none()` and
/// raises `MatchFailed`, i.e. the same program stops working depending on how its
/// value was proved. Moving the defaulting to the READ is what makes it carrier-blind:
/// `Value::Entity`, `Value::Term` and `Value::Node` receivers now all answer `none()`,
/// where before only the first did (and only because something else had filled it in).
///
/// TWO SPELLINGS OF "does not supply it", both from the loader's own encoding:
///  * the slot is ABSENT (`supplied` is `None`) — a hand-built or partial value; and
///  * the slot is PRESENT but holds a VAR. On-disk facts omit optional named args, and
///    `kb/load.rs`'s partial-named-arg expansion fills the gap with a fresh var so the
///    discrim tree can index the fact uniformly. Those are semantically absent, which
///    is exactly the rule `materialize_entity` states at its own Var arm.
///
/// A field that is NOT declared `Option[T]` is untouched in both directions: absent
/// stays the loud "entity has no field" error, and a var-valued slot is handed back as
/// the var it is. Widening that would turn a missing REQUIRED field into `none()`,
/// which is the silent-wrong-answer this function exists to avoid, not to create.
fn absent_option_as_none(
    interp: &mut Interpreter,
    functor: crate::intern::Symbol,
    field_name: &str,
    supplied: Option<Value>,
) -> Result<Value, EvalError> {
    use crate::kb::term_view::{TermView, ViewHead};
    let is_absent = match &supplied {
        None => true,
        Some(v) => matches!(v.head(interp.kb()), ViewHead::Var(_)),
    };
    if is_absent {
        // Keyed by SHORT name, as the two scans above are: `entity_field_types` holds
        // the declared field symbols, which may be qualified.
        let declared_option = interp
            .kb
            .entity_field_types(functor)
            .map(|fields| fields.to_vec())
            .into_iter()
            .flatten()
            .find(|(fname, _)| {
                let full = interp.kb().local_name_of(*fname);
                full.rsplit('.').next().unwrap_or(full) == field_name
            })
            .is_some_and(|(_, ftype)| crate::kb::typing::is_option_type(interp.kb(), &ftype));
        if declared_option {
            let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
            return Ok(Value::Entity {
                functor: none_sym,
                pos: Vec::new().into(),
                named: Vec::new().into(),
            });
        }
    }
    supplied.ok_or_else(|| {
        EvalError::Internal(format!("field_access: entity has no field '{field_name}'"))
    })
}

// ── argument helpers ────────────────────────────────────────────

/// Unpack an arg slice into a fixed-size array, enforcing arity.
pub fn expect_args<const N: usize>(
    op: &'static str,
    args: &[Value],
) -> Result<[Value; N], EvalError> {
    if args.len() != N {
        return Err(EvalError::ArityMismatch {
            op,
            expected: N,
            got: args.len(),
        });
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
//
// WI-880 — THESE FOUR ARE NO LONGER REGISTERED, and the per-carrier functions
// below them are what replaced the registration. They remain as the shared
// SEMANTICS the three carriers agree on, invoked through the carrier wrappers, so
// that "Int64 addition is checked" is written once. What moved is only the KEY.
//
// WHY THE KEY WAS THE DEFECT. Registered on `anthill.prelude.Additive.add`, ONE
// function was the implementation for every carrier that never wrote its own — and
// the function then had to TEST ITS OPERANDS to discover which arithmetic it was
// being asked for. That is a dispatch table written as a match, with no carrier
// dimension anywhere a reader could see it: `op_backed`'s `kb.is_builtin` leg
// certified `Additive.add` as backed for EVERY provider, and a structural carrier
// that omitted an operation loaded clean and died here. MEASURED before the change,
// on a `Money(cents: Int64)` carrier providing `Numeric` with its own `add`/`neg`/
// `mul`/`zero`/`one` and no `sub`: `Additive.sub(cents(700), cents(25))` died
// "expected matching Int, BigInt, or Float, got Entity" — the arm below.
//
// THE OVERFLOW COLUMN IS THE ARGUMENT MADE CONCRETE. `Int64.add` raises `Overflow`,
// `Float.add` saturates to an infinity, `BigInt.add` cannot overflow at all: three
// different operations under one name, chosen by an operand test. Each carrier now
// names its own in its binding block's `operation_map`.

/// WI-880 — `op` IS THE CALLER'S OWN NAME, not this function's.
///
/// These four are no longer registered against anything: their only callers are the
/// per-carrier wrappers below, which is what "the key moved" means. So the label that
/// reaches `EvalError::Overflow` has to come from the caller — otherwise an `Int64`
/// overflow reports `op: "Numeric.add"`, naming a spec operation this ticket stopped
/// implementing, in exactly the diagnostic the per-carrier split exists to sharpen.
/// Found by /code-review; the section header below argued the refusal names its carrier
/// and only the type-mismatch arm did.
///
/// `&'static str` because [`EvalError::Overflow`]'s field is one — the labels are all
/// literals at the call sites, so this costs nothing.
fn numeric_add(op: &'static str, a: &Value, b: &Value) -> Result<Value, EvalError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x
            .checked_add(*y)
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op }),
        (Value::BigInt(x), Value::BigInt(y)) => Ok(Value::BigInt(x + y)),
        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x + y)),
        _ => Err(type_mismatch("matching Int, BigInt, or Float", a, Some(b))),
    }
}

/// `op` is the caller's — see [`numeric_add`].
fn numeric_sub(op: &'static str, a: &Value, b: &Value) -> Result<Value, EvalError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x
            .checked_sub(*y)
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op }),
        (Value::BigInt(x), Value::BigInt(y)) => Ok(Value::BigInt(x - y)),
        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x - y)),
        _ => Err(type_mismatch("matching Int, BigInt, or Float", a, Some(b))),
    }
}

/// `op` is the caller's — see [`numeric_add`].
fn numeric_mul(op: &'static str, a: &Value, b: &Value) -> Result<Value, EvalError> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x
            .checked_mul(*y)
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op }),
        (Value::BigInt(x), Value::BigInt(y)) => Ok(Value::BigInt(x * y)),
        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x * y)),
        _ => Err(type_mismatch("matching Int, BigInt, or Float", a, Some(b))),
    }
}

// WI-529: prefix `-` (`neg`) at the Numeric level — handles every Numeric carrier
// (Int / BigInt / Float), mirroring numeric_add/sub/mul. Int64/Float keep their own
// carrier `neg` builtins too (used when neg dispatches via the carrier override).
/// `op` is the caller's — see [`numeric_add`].
fn numeric_neg(op: &'static str, a: &Value) -> Result<Value, EvalError> {
    match a {
        Value::Int(x) => x
            .checked_neg()
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op }),
        Value::BigInt(x) => Ok(Value::BigInt(-x)),
        Value::Float(x) => Ok(Value::Float(-x)),
        other => Err(type_mismatch("Int, BigInt, or Float", other, None)),
    }
}

// ── the per-carrier arithmetic (WI-880) ─────────────────────────
//
// One wrapper per (carrier, operation), each NARROWED to its own carrier's values
// and each named by that carrier's `operation_map`. The narrowing is the point and
// not an accident of the refactor: `int_add` accepting only a pair of `Int`s is
// what makes "this is `Int64`'s addition" a checkable claim rather than a comment.
// A wrapper reached with foreign operands is a REFUSAL naming the carrier, where
// the shared function's message could only name the union of the three.
//
// `neg` is not repeated here: `Int64.neg` and `Float.neg` were already carrier-keyed
// (`int_neg` / `float_neg`), and `bigint_neg` is added below beside `BigInt`'s own
// operations. `zero` / `one` stay unregistered in EITHER spelling — a nullary
// operation has no operand to dispatch on, which is this module's header note and is
// unchanged by moving the key.

/// `Int64`'s addition — checked, so an overflow is `EvalError::Overflow` rather than
/// a wrap. Named by `rustland/anthill-stl/anthill/int64.anthill`'s `operation_map`.
fn int_add(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int64.add", args)?;
    // Operands read through `TermView::literal_int64` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_int64(i.kb()), b.literal_int64(i.kb())) {
        (Some(x), Some(y)) => numeric_add("Int64.add", &Value::Int(x), &Value::Int(y)),
        _ => Err(type_mismatch("Int64", &a, Some(&b))),
    }
}

/// `Int64`'s subtraction — checked. See [`int_add`].
fn int_sub(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int64.sub", args)?;
    // Operands read through `TermView::literal_int64` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_int64(i.kb()), b.literal_int64(i.kb())) {
        (Some(x), Some(y)) => numeric_sub("Int64.sub", &Value::Int(x), &Value::Int(y)),
        _ => Err(type_mismatch("Int64", &a, Some(&b))),
    }
}

/// `Int64`'s multiplication — checked. See [`int_add`].
fn int_mul(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int64.mul", args)?;
    // Operands read through `TermView::literal_int64` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_int64(i.kb()), b.literal_int64(i.kb())) {
        (Some(x), Some(y)) => numeric_mul("Int64.mul", &Value::Int(x), &Value::Int(y)),
        _ => Err(type_mismatch("Int64", &a, Some(&b))),
    }
}

/// `Float`'s addition — IEEE, so it SATURATES to an infinity where `Int64`'s raises.
/// That difference is the reason the two are separate keys.
fn float_add(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Float.add", args)?;
    // Operands read through `TermView::literal_f64` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_f64(i.kb()), b.literal_f64(i.kb())) {
        (Some(x), Some(y)) => numeric_add("Float.add", &Value::Float(x), &Value::Float(y)),
        _ => Err(type_mismatch("Float", &a, Some(&b))),
    }
}

/// `Float`'s subtraction — IEEE. See [`float_add`].
fn float_sub(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Float.sub", args)?;
    // Operands read through `TermView::literal_f64` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_f64(i.kb()), b.literal_f64(i.kb())) {
        (Some(x), Some(y)) => numeric_sub("Float.sub", &Value::Float(x), &Value::Float(y)),
        _ => Err(type_mismatch("Float", &a, Some(&b))),
    }
}

/// `Float`'s multiplication — IEEE. See [`float_add`].
fn float_mul(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Float.mul", args)?;
    // Operands read through `TermView::literal_f64` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_f64(i.kb()), b.literal_f64(i.kb())) {
        (Some(x), Some(y)) => numeric_mul("Float.mul", &Value::Float(x), &Value::Float(y)),
        _ => Err(type_mismatch("Float", &a, Some(&b))),
    }
}

/// `BigInt`'s addition — UNBOUNDED, so it has no overflow arm at all. The third
/// column of the table in this section's header.
fn bigint_add(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("BigInt.add", args)?;
    // Operands read through `TermView::literal_big_int` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_big_int(i.kb()), b.literal_big_int(i.kb())) {
        (Some(x), Some(y)) => numeric_add("BigInt.add", &Value::BigInt(x), &Value::BigInt(y)),
        _ => Err(type_mismatch("BigInt", &a, Some(&b))),
    }
}

/// `BigInt`'s subtraction — unbounded. See [`bigint_add`].
fn bigint_sub(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("BigInt.sub", args)?;
    // Operands read through `TermView::literal_big_int` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_big_int(i.kb()), b.literal_big_int(i.kb())) {
        (Some(x), Some(y)) => numeric_sub("BigInt.sub", &Value::BigInt(x), &Value::BigInt(y)),
        _ => Err(type_mismatch("BigInt", &a, Some(&b))),
    }
}

/// `BigInt`'s multiplication — unbounded. See [`bigint_add`].
fn bigint_mul(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("BigInt.mul", args)?;
    // Operands read through `TermView::literal_big_int` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_big_int(i.kb()), b.literal_big_int(i.kb())) {
        (Some(x), Some(y)) => numeric_mul("BigInt.mul", &Value::BigInt(x), &Value::BigInt(y)),
        _ => Err(type_mismatch("BigInt", &a, Some(&b))),
    }
}

/// `BigInt`'s negation — unbounded, so unlike [`int_neg`] it cannot fail on
/// `i64::MIN`. `Int64` and `Float` already had their own; this completes the three.
fn bigint_neg(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("BigInt.neg", args)?;
    // Operand read through `TermView::literal_big_int` — the carrier-neutral question,
    // so the read IS the guard. This was the last unary member of the sort still
    // matching `Value::BigInt` by variant, beside an `add`/`sub`/`mul` that had been
    // widened (WI-20260827-2YHZ3 / -3ZNBC).
    //
    // NOT `big_int_operand`, which additionally accepts an `Int64` — that widening is
    // a SORT one and belongs to the CONVERSIONS (`to_bigint` / `to_int` / `to_float`),
    // which have always taken either. `neg` refused an `Int64` before this ticket and
    // still does: smuggling a sort widening in with a carrier widening would make
    // `BigInt.neg(5)` answer `-5` where it used to raise (found by /code-review).
    let x = {
        use crate::kb::term_view::TermView;
        a.literal_big_int(i.kb())
            .ok_or_else(|| type_mismatch("BigInt", &a, None))?
    };
    numeric_neg("BigInt.neg", &Value::BigInt(x))
}

// ── Int-specific ────────────────────────────────────────────────

fn int_neg(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Int64.neg", args)?;
    // Operand read through `TermView::literal_int64` — the carrier-neutral question, so the
    // read IS the guard (WI-20260827-2YHZ3).
    match a.literal_int64(i.kb()) {
        Some(x) => x
            .checked_neg()
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Int64.neg" }),
        None => Err(type_mismatch("Int64", &a, None)),
    }
}

fn int_abs(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Int64.abs", args)?;
    // Operand read through `TermView::literal_int64` — the carrier-neutral question, so the
    // read IS the guard (WI-20260827-2YHZ3).
    match a.literal_int64(i.kb()) {
        Some(x) => x
            .checked_abs()
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Int64.abs" }),
        None => Err(type_mismatch("Int64", &a, None)),
    }
}

fn int_mod(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int64.mod", args)?;
    // Operands read through `TermView::literal_int64` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_int64(i.kb()), b.literal_int64(i.kb())) {
        (Some(_), Some(0)) => Err(i.raise_division_by_zero("Int64.mod")),
        (Some(x), Some(y)) => Ok(Value::Int(x.rem_euclid(y))),
        _ => Err(type_mismatch("Int64", &a, Some(&b))),
    }
}

fn int_rem(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int64.rem", args)?;
    // Operands read through `TermView::literal_int64` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_int64(i.kb()), b.literal_int64(i.kb())) {
        (Some(_), Some(0)) => Err(i.raise_division_by_zero("Int64.rem")),
        (Some(x), Some(y)) => Ok(Value::Int(x % y)),
        _ => Err(type_mismatch("Int64", &a, Some(&b))),
    }
}

/// Truncated integer division. Backs both `anthill.prelude.Int64.div` (the
/// primary name that `/` desugars to) and the historical `Int64.divExact`
/// alias (kept via stdlib rule `divExact(a, b) = div(a, b)` for
/// compatibility). Semantics are identical — the name change is cosmetic.
fn int_div(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Int64.div", args)?;
    // Operands read through `TermView::literal_int64` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_int64(i.kb()), b.literal_int64(i.kb())) {
        (Some(_), Some(0)) => Err(i.raise_division_by_zero("Int64.div")),
        (Some(x), Some(y)) => x
            .checked_div(y)
            .map(Value::Int)
            .ok_or(EvalError::Overflow { op: "Int64.div" }),
        _ => Err(type_mismatch("Int64", &a, Some(&b))),
    }
}

/// IEEE floating-point division. NaN / Infinity propagate per the standard;
/// division by 0.0 yields +/-Infinity or NaN rather than an error (users
/// who want strict semantics check explicitly before dividing).
fn float_div(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Float.div", args)?;
    // Operands read through `TermView::literal_f64` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_f64(i.kb()), b.literal_f64(i.kb())) {
        (Some(x), Some(y)) => Ok(Value::Float(x / y)),
        _ => Err(type_mismatch("Float", &a, Some(&b))),
    }
}

// ── BigInt: division with remainder ─────────────────────────────────────
//
// WI-20260824-VT8CF — `BigInt` provides `EuclideanDomain`, and until this ticket it
// declared NO division at all: eighteen ordering and conversion operations and not one
// of `div` / `mod` / `rem`. The RESOLVER already computed all three
// (`Self::bigint_checked_div`, `Self::bigint_rem_euclid` — the BigInt slots of
// `BuiltinTag::Div` / `Mod`), so a rule-body `div` over BigInt answered while the same
// division in an operation body had nothing to dispatch to. These three close that, with
// the same semantics as the resolver's slots and as `Int64`'s: `div` truncates, `mod` is
// Euclidean (never negative), `rem`'s sign follows the dividend.
//
// NO OVERFLOW ARM, unlike `Int64`'s: `num_bigint::BigInt` is unbounded, so the zero
// divisor is the only partiality — which is also why `num_bigint`'s own `/` and `%`
// PANIC there rather than returning, making the guard load-bearing rather than
// defensive.

fn bigint_div(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("BigInt.div", args)?;
    // Operands read through `TermView::literal_big_int` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_big_int(i.kb()), b.literal_big_int(i.kb())) {
        (Some(_), Some(y)) if y.sign() == num_bigint::Sign::NoSign => {
            Err(i.raise_division_by_zero("BigInt.div"))
        }
        (Some(x), Some(y)) => Ok(Value::BigInt(x / y)),
        _ => Err(type_mismatch("BigInt", &a, Some(&b))),
    }
}

/// Euclidean remainder — always non-negative, matching `Int64.mod`'s `rem_euclid`.
/// `num_bigint`'s `%` follows the DIVIDEND's sign, so a negative result is lifted by
/// `|b|`; the divisor's own sign decides which way, which is why the inner test is on
/// `b` and not on `r` alone.
fn bigint_mod(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("BigInt.mod", args)?;
    // Operands read through `TermView::literal_big_int` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_big_int(i.kb()), b.literal_big_int(i.kb())) {
        (Some(_), Some(y)) if y.sign() == num_bigint::Sign::NoSign => {
            Err(i.raise_division_by_zero("BigInt.mod"))
        }
        (Some(x), Some(y)) => {
            let r = &x % &y;
            Ok(Value::BigInt(if r.sign() == num_bigint::Sign::Minus {
                if y.sign() == num_bigint::Sign::Minus {
                    r - y
                } else {
                    r + y
                }
            } else {
                r
            }))
        }
        _ => Err(type_mismatch("BigInt", &a, Some(&b))),
    }
}

/// Truncated remainder — sign follows the dividend, the partner `div` satisfies
/// `b * div(a, b) + rem(a, b) = a` with (`EuclideanDomain`'s `euclid_div` law).
fn bigint_rem(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("BigInt.rem", args)?;
    // Operands read through `TermView::literal_big_int` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_big_int(i.kb()), b.literal_big_int(i.kb())) {
        (Some(_), Some(y)) if y.sign() == num_bigint::Sign::NoSign => {
            Err(i.raise_division_by_zero("BigInt.rem"))
        }
        (Some(x), Some(y)) => Ok(Value::BigInt(x % y)),
        _ => Err(type_mismatch("BigInt", &a, Some(&b))),
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

/// The raw `f64` a Float operand DENOTES, on whatever carrier it rides — an unboxed
/// `Value::Float`, a `Literal::Float` inside a hash-consed `Value::Term`, or one
/// inside a `Value::Node` occurrence. Mirrors the resolver's `value_f64` so eval and
/// resolver agree on which operands are floats — otherwise a handle-wrapped float
/// would slip past the IEEE path and read `nan == nan` structurally (via
/// `OrderedFloat`), or make ordering raise a spurious type error.
///
/// WI-20260827-3ZNBC — THE OCCURRENCE CARRIER IS THE HALF THIS WAS MISSING while its
/// doc already claimed the mirror. `value_f64` gained it in WI-685; this kept a
/// hand-rolled two-arm match, so once the SLD→eval bridge stopped normalizing its
/// operands, `Vec3(x: a.x + b.x, …)` inside a bridged `vec_add` read its field off a
/// rule-body occurrence, got `Value::Node(Const(1.0))`, and `Float.add` refused —
/// the whole goal RESIDUALIZED rather than erroring, which is how a missing carrier
/// arm hides. One [`TermView::literal_f64`] call is the entire mirror, and asking the
/// carrier-neutral question is what keeps the two from drifting apart again.
/// (Control: `vec3_ops_test::every_member_answers_relationally` and
/// `::the_imported_short_name_answers_through_the_derived_view` fail without it.)
fn float_val(i: &Interpreter, v: &Value) -> Option<f64> {
    use crate::kb::term_view::TermView;
    v.literal_f64(i.kb())
}

/// `anthill.kernel.struct_eq` (`===`) — the TOTAL, carrier-agnostic STRUCTURAL
/// identity test (proposal 051). Stays on `OrderedFloat` (`nan === nan` is true),
/// unlike the semantic `PartialEq.eq` below: reflection / dedup / hash-consing need
/// structural identity. WI-486: a `Value::Term` operand and its structurally-equal
/// `Value::Node`/`Entity` twin compare equal.
fn builtin_struct_eq(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("struct_eq", args)?;
    Ok(Value::Bool(crate::kb::term_view::views_structurally_equal(
        i.kb(),
        &a,
        &b,
    )))
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
        kb.sem_eq_dispatch_target(a)
            .or_else(|| kb.sem_eq_dispatch_target(b))
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
            //
            // WI-880 — THE BODY QUESTION, ASKED DELIBERATELY, not the executability one.
            // The branch is "is this a Bool-valued FUNCTION to run, or a PREDICATE to
            // prove", and only a body answers it. `op_is_executable` /
            // `op_is_interpretable` answer "can the interpreter INVOKE it", which is a
            // different question and would be the wrong one here: their host-mapping leg
            // would be true for an `eq` no rule backs and no body defines.
            //
            // THAT DIVERGENCE IS NOT REACHABLE TODAY AND ITS BOUNDARY IS EXACT: no
            // carrier's `eq` is `operation_map`ped anywhere in the tree, because
            // `PartialEq.eq` is the ONE spec-op registration WI-880 kept (see
            // `register_standard_builtins` for the argument). The day an `eq` IS
            // host-mapped, a host-mapped-and-body-less one would take the `else` branch
            // below, find no clauses, and Refute — EQUAL VALUES REPORTED UNEQUAL, which
            // is the failure this whole function exists to prevent. Whoever maps an `eq`
            // owns this line and its twin in `resolve.rs`'s `sem_eq_dispatch`.
            if crate::kb::typing::op_has_runnable_body(i.kb(), target) {
                return match i
                    .kb_mut()
                    .bridge_eq_op_to_eval(target, a.clone(), b.clone())
                {
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
            return match i
                .kb_mut()
                .prove_rule_predicate(target, vec![a.clone(), b.clone()])
            {
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
                // WI-1092 — the operands' carrier DECLARES this `eq` member and
                // nothing defines it. NOT `Ok(false)`, and not the structural verdict
                // either: the carrier said its equality is `target`, so answering
                // structurally would report a verdict it disowned. Loud through the
                // shared WI-818 classifier at top level, and under the resolver→eval
                // bridge a Suspend (never truncated — no branch was cut) so the
                // resolver residualizes exactly as its own `sem_eq_dispatch` does for
                // the same target.
                crate::kb::resolve::PredicateProof::Undefined => {
                    if i.bridge_mode() {
                        // Its own sentence rather than the classifier's rendering: a
                        // `detail` rides inside a residual, where the classifier's
                        // remedy paragraph and backtrace are noise.
                        return Err(EvalError::Suspended {
                            detail: format!(
                                "carrier eq `{}` is declared with no definition",
                                i.kb().qualified_name_of(target)
                            ),
                            truncated: false,
                        });
                    }
                    Err(i.unrunnable_target_error(target))
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
        FieldPairs::NotComposite => return Ok(None), // caller keeps the structural verdict
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
fn value_compare(
    kb: &crate::kb::KnowledgeBase,
    a: &Value,
    b: &Value,
) -> Result<std::cmp::Ordering, EvalError> {
    use crate::kb::term::Literal;
    use crate::kb::term_view::TermView;
    // Both operands read through `TermView::as_literal` first (WI-20260827-2YHZ3),
    // so an `Ord` comparison decides the same on a hash-consed `Value::Term`, a
    // `Value::Node` occurrence and a native scalar. Backs `ordered_compare` and
    // every `gt`/`gte`/`lt`/`lte`, which is why leaving it on the native match
    // while widening `add`/`sub`/`mul` was the incoherence /code-review named:
    // `Int64.add(handle, 1)` succeeded where `Int64.gt(handle, 1)` refused.
    // ONE reader, not two. WI-20260827-2YHZ3 added the `as_literal` pair above a
    // native `match (a, b)` fallback and left the fallback in place; every pair it
    // could still answer — two `Value::Int`s, two `Value::Str`s — reads as
    // `ViewHead::Const` up here, so the only arm it could ever REACH was its own
    // error (WI-20260827-3ZNBC). Two spellings of one comparison is how the halves
    // drift apart, which is the defect this function was widened to remove.
    let (Some(la), Some(lb)) = (a.as_literal(kb), b.as_literal(kb)) else {
        return Err(EvalError::TypeMismatch {
            expected: "Ord scalars of matching type",
            got: format!("{} and {}", a.type_name(), b.type_name()),
        });
    };
    Ok(match (la, lb) {
        (Literal::Int(x), Literal::Int(y)) => x.cmp(&y),
        (Literal::BigInt(x), Literal::BigInt(y)) => x.cmp(&y),
        (Literal::Float(x), Literal::Float(y)) => x.into_inner().total_cmp(&y.into_inner()),
        (Literal::Bool(x), Literal::Bool(y)) => x.cmp(&y),
        (Literal::String(x), Literal::String(y)) => x.cmp(&y),
        // MISMATCHED literal sorts, e.g. `compare(1, "a")`. Same refusal as a
        // non-literal operand — an `Ord` comparison across sorts has no answer.
        _ => {
            return Err(EvalError::TypeMismatch {
                expected: "Ord scalars of matching type",
                got: format!("{} and {}", a.type_name(), b.type_name()),
            })
        }
    })
}

fn ordered_compare(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("compare", args)?;
    Ok(Value::Int(match value_compare(i.kb(), &a, &b)? {
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

fn ordered_gt(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("gt", args)?;
    Ok(Value::Bool(matches!(
        value_compare(i.kb(), &a, &b)?,
        std::cmp::Ordering::Greater
    )))
}

fn ordered_gte(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("gte", args)?;
    Ok(Value::Bool(!matches!(
        value_compare(i.kb(), &a, &b)?,
        std::cmp::Ordering::Less
    )))
}

fn ordered_lt(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("lt", args)?;
    Ok(Value::Bool(matches!(
        value_compare(i.kb(), &a, &b)?,
        std::cmp::Ordering::Less
    )))
}

fn ordered_lte(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("lte", args)?;
    Ok(Value::Bool(!matches!(
        value_compare(i.kb(), &a, &b)?,
        std::cmp::Ordering::Greater
    )))
}

/// `Ord.max`/`min` on a total scalar carrier. `Ord` derives both from
/// `gte`/`lte` by default body, which is what a STRUCTURAL carrier gets — but for a
/// scalar that derivation costs an interpreter frame and a dictionary dispatch where
/// the host answers in one call, so the total carriers map these too. Same reasoning
/// as `gt`/`gte`/`lt`/`lte`, and leaving them out made the surface inconsistent:
/// four of the six keyed to the host and two not.
fn ordered_max(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("max", args)?;
    match value_compare(i.kb(), &a, &b)? {
        std::cmp::Ordering::Less => Ok(b),
        _ => Ok(a),
    }
}

fn ordered_min(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("min", args)?;
    match value_compare(i.kb(), &a, &b)? {
        std::cmp::Ordering::Greater => Ok(b),
        _ => Ok(a),
    }
}

// ── Bool ───────────────────────────────────────────────────────

fn bool_not(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Bool.not", args)?;
    // Operand read through `TermView::literal_bool` — the carrier-neutral question, so the
    // read IS the guard (WI-20260827-2YHZ3).
    match a.literal_bool(i.kb()) {
        Some(x) => Ok(Value::Bool(!x)),
        None => Err(type_mismatch("Bool", &a, None)),
    }
}

fn bool_and(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Bool.and", args)?;
    // Operands read through `TermView::literal_bool` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_bool(i.kb()), b.literal_bool(i.kb())) {
        (Some(x), Some(y)) => Ok(Value::Bool(x && y)),
        _ => Err(type_mismatch("Bool", &a, Some(&b))),
    }
}

fn bool_or(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("Bool.or", args)?;
    // Operands read through `TermView::literal_bool` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_bool(i.kb()), b.literal_bool(i.kb())) {
        (Some(x), Some(y)) => Ok(Value::Bool(x || y)),
        _ => Err(type_mismatch("Bool", &a, Some(&b))),
    }
}

// ── String ─────────────────────────────────────────────────────

fn string_concat(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("String.concat", args)?;
    // Operands read through `TermView::literal_string` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_string(i.kb()), b.literal_string(i.kb())) {
        (Some(x), Some(y)) => {
            let mut out = String::with_capacity(x.len() + y.len());
            out.push_str(&x);
            out.push_str(&y);
            Ok(Value::Str(out))
        }
        _ => Err(type_mismatch("String", &a, Some(&b))),
    }
}

// ── BigInt conversions ─────────────────────────────────────────

fn bigint_to_bigint(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("BigInt.to_bigint", args)?;
    Ok(Value::BigInt(big_int_operand(i.kb(), &a, "Int or BigInt")?))
}

/// BigInt → Option[Int]. Produces `some(n)` if the BigInt fits in i64,
/// `none` otherwise. Relies on `anthill.prelude.List.some` / `.none`
/// being loaded in the KB's symbol table.
fn bigint_to_int(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("BigInt.to_int", args)?;
    let n = big_int_operand(interp.kb(), &a, "BigInt")?;
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

// Read through `float_operand` like every other `Float` host function
// (WI-20260827-3ZNBC): the three predicates were the only members of the sort
// still matching `Value::Float` by variant, so `Float.add(handle, 1.0)` decided
// while `Float.isNaN(handle)` refused the same operand.
fn float_is_nan(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Float.isNaN", args)?;
    Ok(Value::Bool(float_operand(i, &a)?.is_nan()))
}

fn float_is_infinite(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Float.isInfinite", args)?;
    Ok(Value::Bool(float_operand(i, &a)?.is_infinite()))
}

fn float_is_finite(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Float.isFinite", args)?;
    Ok(Value::Bool(float_operand(i, &a)?.is_finite()))
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
fn int_to_float(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("Int64.to_float", args)?;
    Ok(Value::Float(int_operand(i.kb(), &a)? as f64))
}

/// BigInt → Float. Lossy for values beyond f64 precision; saturates to
/// +/-Infinity for values exceeding Float's range. Total function.
/// Implementation goes via decimal string: num_bigint's Display produces a
/// canonical integer form, and Rust's f64 parser rounds to nearest and
/// returns Infinity on overflow.
fn bigint_to_float(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("BigInt.to_float", args)?;
    let s = big_int_operand(i.kb(), &a, "BigInt or Int")?.to_string();
    let f: f64 = s.parse().unwrap_or(f64::INFINITY);
    Ok(Value::Float(f))
}

fn string_length(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("String.length", args)?;
    // Unicode scalar count to match `anthill.prelude.String.length`'s
    // declared character-level semantics (the prelude's rules refer to
    // `length("") = 0`, which is unambiguous either way, but Unicode is
    // the natural choice for user-facing length).
    Ok(Value::Int(str_operand(i.kb(), &a)?.chars().count() as i64))
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
fn string_is_empty(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = args else {
        return Err(EvalError::ArityMismatch {
            op: "String.isEmpty",
            expected: 1,
            got: args.len(),
        });
    };
    Ok(Value::Bool(str_operand(i.kb(), &a)?.is_empty()))
}

fn string_starts_with(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("String.startsWith", args)?;
    // Operands read through `TermView::literal_string` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_string(i.kb()), b.literal_string(i.kb())) {
        (Some(s), Some(p)) => Ok(Value::Bool(s.starts_with(p.as_str()))),
        _ => Err(type_mismatch("String", &a, Some(&b))),
    }
}

fn string_ends_with(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a, b] = expect_args::<2>("String.endsWith", args)?;
    // Operands read through `TermView::literal_string` — the carrier-neutral
    // question, so the read IS the guard (WI-20260827-2YHZ3).
    match (a.literal_string(i.kb()), b.literal_string(i.kb())) {
        (Some(s), Some(p)) => Ok(Value::Bool(s.ends_with(p.as_str()))),
        _ => Err(type_mismatch("String", &a, Some(&b))),
    }
}

fn string_to_upper(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("String.toUpper", args)?;
    Ok(Value::Str(str_operand(i.kb(), &a)?.to_uppercase()))
}

fn string_to_lower(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [a] = expect_args::<1>("String.toLower", args)?;
    Ok(Value::Str(str_operand(i.kb(), &a)?.to_lowercase()))
}

// substring(s, start, end) — character-indexed half-open range, matching
// String.length's Unicode-scalar semantics. Negative or out-of-range indices
// clamp to the string's bounds; reversed ranges produce the empty string.
fn string_substring(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, start, end] = expect_args::<3>("String.substring", args)?;
    let s = str_operand(i.kb(), &s)?.to_string();
    let start = int_operand(i.kb(), &start)?;
    let end = int_operand(i.kb(), &end)?;
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
fn string_repeat(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, n] = expect_args::<2>("String.repeat", args)?;
    let s = str_operand(i.kb(), &s)?.to_string();
    let n = int_operand(i.kb(), &n)?;
    if n <= 0 {
        return Ok(Value::Str(String::new()));
    }
    let fits = usize::try_from(n)
        .ok()
        .and_then(|n| s.len().checked_mul(n))
        .is_some_and(|total| total <= isize::MAX as usize);
    if !fits {
        return Err(EvalError::Overflow {
            op: "String.repeat",
        });
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
/// A `String` operand, on any carrier — `Cow` so the native case still BORROWS.
///
/// WI-20260827-2YHZ3. The naive widening (`literal_string`, which returns an owned
/// `String`) would allocate on every read, and these back `contains` / `indexOf` /
/// `split` inside filters over long streams — /code-review flagged exactly that cost.
/// A native `Value::Str` borrows as before; only a handle carrier — a `Value::Term`
/// or a `Value::Node` occurrence, which is what a rule-body-bound answer rides on
/// (WI-246) — pays a clone, and that carrier had no reading at all before.
fn str_operand<'a>(
    kb: &crate::kb::KnowledgeBase,
    v: &'a Value,
) -> Result<std::borrow::Cow<'a, str>, EvalError> {
    use crate::kb::term_view::TermView;
    if let Value::Str(s) = v {
        return Ok(std::borrow::Cow::Borrowed(s.as_str()));
    }
    v.literal_string(kb)
        .map(std::borrow::Cow::Owned)
        .ok_or_else(|| type_mismatch("String", v, None))
}

/// An `Int64` operand, on any carrier — [`str_operand`]'s integer peer, and the
/// reader every builtin that CONSUMES an integer goes through.
///
/// WI-20260827-3ZNBC. There was no such reader, so the sites that consume an int
/// beside a string — `String.substring`'s bounds, `repeat`'s count, `slug`'s cap,
/// `digestBase32`'s width, `Dictionary.sub`'s index — read the string through
/// `str_operand` and the integer through the INHERENT `Value::as_int`, which sees
/// the native variant alone. So one operand of one call decided carrier-neutrally
/// and the next refused, which is the half-widened set /code-review named on
/// WI-20260827-2YHZ3 reappearing one layer out. No clone to weigh here (`i64` is
/// `Copy`), so unlike `str_operand` there is no native fast path to keep.
fn int_operand(kb: &crate::kb::KnowledgeBase, v: &Value) -> Result<i64, EvalError> {
    use crate::kb::term_view::TermView;
    v.literal_int64(kb)
        .ok_or_else(|| type_mismatch("Int64", v, None))
}

/// A `BigInt` operand, on any carrier. Accepts an `Int64` too — the `BigInt`
/// conversions have always widened an `Int` operand, and that is a SORT question
/// (`Int64` embeds in `BigInt`) independent of the carrier one this reader answers.
/// Borrows nothing: `BigInt` is owned either way.
fn big_int_operand(
    kb: &crate::kb::KnowledgeBase,
    v: &Value,
    expected: &'static str,
) -> Result<num_bigint::BigInt, EvalError> {
    use crate::kb::term::Literal;
    use crate::kb::term_view::TermView;
    match v.as_literal(kb) {
        Some(Literal::BigInt(b)) => Ok(b),
        Some(Literal::Int(n)) => Ok(num_bigint::BigInt::from(n)),
        _ => Err(type_mismatch(expected, v, None)),
    }
}

fn string_contains(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, sub] = expect_args::<2>("String.contains", args)?;
    Ok(Value::Bool(
        str_operand(i.kb(), &s)?.contains(str_operand(i.kb(), &sub)?.as_ref()),
    ))
}

/// THE ONE PLACE THE HOST PRIMITIVE DISAGREES WITH THE DECLARATION: `str::find`
/// answers in BYTES and `indexOf` is declared in Unicode scalars (see
/// `string.anthill`, which argues the unit and drives the round trip that pins it).
/// The byte offset is converted by counting the characters before it — `find`'s answer
/// is always on a character boundary, so the prefix slice is exact. `-1` when absent.
fn string_index_of(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, sub] = expect_args::<2>("String.indexOf", args)?;
    let (s, sub) = (str_operand(i.kb(), &s)?, str_operand(i.kb(), &sub)?);
    Ok(Value::Int(match s.find(sub.as_ref()) {
        Some(byte) => s[..byte].chars().count() as i64,
        None => -1,
    }))
}

/// `str::replace` — every non-overlapping occurrence, left to right, which is what
/// the declaration specifies.
fn string_replace(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, old, new] = expect_args::<3>("String.replace", args)?;
    let (s, old, new) = (
        str_operand(i.kb(), &s)?,
        str_operand(i.kb(), &old)?,
        str_operand(i.kb(), &new)?,
    );
    Ok(Value::Str(s.replace(old.as_ref(), new.as_ref())))
}

/// `str::trim`, whose whitespace set is the Unicode `White_Space` property — the
/// declaration says Unicode and not the ASCII subset, so this is `trim` and not
/// `trim_ascii`.
fn string_trim(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s] = expect_args::<1>("String.trim", args)?;
    Ok(Value::Str(str_operand(i.kb(), &s)?.trim().to_string()))
}

// ── slug / digest (WI-1121) ────────────────────────────────────
//
// The two host primitives a locally-minted, content-derived identifier needs
// (`anthill-todo/docs/design/backend-github-coordination.md` §6.5). Both are
// declared on `anthill.prelude.String` and argued there; what is host-specific
// — and therefore lives here — is only that neither is expressible in anthill:
// `slug` classifies CHARACTERS, and `digestBase32` needs integer bit
// arithmetic over bytes.

/// `String.slug(s, cap)` — the total, deterministic reduction of prose to
/// `[a-z0-9-]` the design's §6.5 specifies: lowercase, keep `[a-z0-9]`,
/// collapse every other run to a single `-`, cut at a word boundary at `cap`
/// characters, drop a trailing `-`.
///
/// TOTAL, AND THE EMPTY ANSWER IS LEGAL — a description written entirely in a
/// non-ASCII script (this project writes Ukrainian) or entirely in punctuation
/// keeps nothing, and the caller omits the segment. That is why a slug can
/// never be load-bearing: it is a rendering, not an identity.
///
/// CUT AT A WORD BOUNDARY means: take the last `-` at or before `cap` and cut
/// there, unless there is none, in which case cut at `cap` exactly — so a
/// single long word yields a truncated word rather than nothing. `cap <= 0`
/// yields "".
fn string_slug(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, cap] = expect_args::<2>("String.slug", args)?;
    let s = str_operand(i.kb(), &s)?;
    let cap = int_operand(i.kb(), &cap)?;
    Ok(Value::Str(slug(s.as_ref(), cap)))
}

/// The slug rule itself, split out so it is unit-testable without a `Value`.
fn slug(s: &str, cap: i64) -> String {
    if cap <= 0 {
        return String::new();
    }
    // Lowercase first: `to_lowercase` can change the character COUNT (`İ` →
    // `i̇`), so classifying before it would count a different string than the
    // one that gets cut.
    let lowered = s.to_lowercase();
    let mut out = String::new();
    for c in lowered.chars() {
        if c.is_ascii_lowercase() || c.is_ascii_digit() {
            out.push(c);
        } else if !out.ends_with('-') && !out.is_empty() {
            // A run of anything else is ONE `-`, and a leading run is dropped
            // outright — a slug never starts with the separator.
            out.push('-');
        }
    }
    let cap = cap as usize;
    if out.chars().count() > cap {
        // `out` is ASCII by construction, so byte and character indices agree
        // and `[..cap]` cannot split a scalar.
        let head = &out[..cap];
        // A `-` sitting exactly AT the cap means the head already ends on a word
        // boundary — keep it whole. Without this test the cut retreats to the
        // PREVIOUS boundary and throws away a word that fit exactly, which is
        // how a 30-character cap yielded 20 characters.
        out = if out.as_bytes()[cap] == b'-' {
            head.to_string()
        } else {
            match head.rfind('-') {
                Some(at) => head[..at].to_string(),
                None => head.to_string(),
            }
        };
    }
    out.trim_end_matches('-').to_string()
}

/// Crockford base32 — `0123456789ABCDEFGHJKMNPQRSTVWXYZ`, i.e. 0–9 and A–Z
/// without `I`, `L`, `O` and `U`. Uppercase, which is the ONE canonical case
/// §6.5 requires: the digest lands in a filename, and on a case-insensitive
/// filesystem (APFS by default) two spellings that differ only in case are one
/// file, so minting must never produce two.
const CROCKFORD: &[u8; 32] = b"0123456789ABCDEFGHJKMNPQRSTVWXYZ";

/// `String.digestBase32(s, chars)` — a deterministic digest of `s`, rendered as
/// `chars` Crockford base32 characters (5 bits each).
///
/// NOT A CHECKSUM AND NOT CRYPTOGRAPHIC. §6.5 is explicit that the id it feeds
/// is OPAQUE — a minting rule, not an integrity check — because one of the hash
/// inputs (a work item's description) is edited for months afterwards, so no
/// later recomputation can reproduce it. What the digest owes its caller is
/// exactly two properties: the same input gives the same output (which is what
/// makes a retried `add` idempotent rather than duplicating an item), and
/// different inputs spread evenly (which is what keeps collisions at the
/// birthday bound rather than clustered).
///
/// FNV-1a over the UTF-8 bytes, finished with a splitmix64 avalanche. FNV-1a
/// alone has weak diffusion in its high bits, and a 25-bit answer is a SLICE of
/// the word — so the avalanche is not decoration, it is what makes the slice
/// uniform.
fn string_digest_base32(i: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, chars] = expect_args::<2>("String.digestBase32", args)?;
    let s = str_operand(i.kb(), &s)?;
    let chars = int_operand(i.kb(), &chars)?;
    // 12 characters is 60 bits, the most a `u64` digest can render without
    // padding the top with a constant — which would look like width the answer
    // does not have. Refused rather than clamped: a caller asking for 16 is
    // asking for entropy this cannot supply, and quietly handing back 60 bits
    // dressed as 80 is the silent degradation the repo's rules forbid.
    if chars <= 0 || chars > 12 {
        return Err(EvalError::TypeMismatch {
            expected: "String.digestBase32 width: an Int64 in 1..=12 (the digest is 64 bits \
                       wide, and 5 bits go into each base32 character)",
            got: chars.to_string(),
        });
    }
    Ok(Value::Str(digest_base32(s.as_ref(), chars as u32)))
}

/// The digest itself, split out so it is unit-testable without a `Value`.
fn digest_base32(s: &str, chars: u32) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325; // FNV-1a 64 offset basis
    for b in s.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3); // FNV-1a 64 prime
    }
    // splitmix64 finalizer.
    h ^= h >> 30;
    h = h.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    h ^= h >> 27;
    h = h.wrapping_mul(0x94d0_49bb_1331_11eb);
    h ^= h >> 31;
    // Most significant group first, so a PREFIX of a wider digest is the
    // narrower digest of the same input — which is what lets §6.5 widen the
    // hash later without renumbering anything.
    (0..chars)
        .map(|i| {
            let shift = 64 - 5 * (i + 1);
            CROCKFORD[((h >> shift) & 0x1f) as usize] as char
        })
        .collect()
}

/// `str::split`, which keeps the empty pieces the declaration requires.
///
/// The one host function here that BUILDS a structured value rather than a scalar;
/// `bigint_to_int` (which builds an `Option`) is the shape it follows, through the
/// shared [`build_value_list`] so the `cons`/`nil` spine is minted in one place.
fn string_split(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [s, sep] = expect_args::<2>("String.split", args)?;
    let (s, sep) = (
        str_operand(interp.kb(), &s)?.into_owned(),
        str_operand(interp.kb(), &sep)?.into_owned(),
    );
    let pieces: Vec<Value> = s
        .split(sep.as_str())
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
fn relation_split_first(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
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
    // not plain code) is not reflected in `columns` and would slip through.
    //
    // WI-728 moved the ORDINARY verdict to LOAD time: `negate`'s return is now
    // `Relation[T = Membership[T = r.T], …]`, and `Membership` is the type-level
    // predicate the ctor-reduction boundary evaluates (kb/typing.rs). This guard is
    // NOT thereby dead — it reads the VALUE's own `columns`, a different population
    // from the SCHEMA the typer sees. TWO ways it is still reached, only the first DRIVEN
    // (in `wi728_membership_operand_test`):
    //   * a schema never known statically — the WI-734 abstract-operand rule leaves the
    //     assertion symbolic, and a wrapper widening its own return to a bare `Relation`
    //     lets that residual escape unreduced (`…_abstract_schema_defers_to_the_runtime_-
    //     guard`).
    //   * a relation built through reflect rather than from surface code. NOT driven —
    //     there is no reflect LogicalQuery BUILD interface yet (see `guarded_of`'s note
    //     in relation.anthill), so no test can construct one. Stated so a later reader
    //     weighing this guard's removal knows which of the two is argued and which is
    //     merely asserted.
    //
    // A THIRD WAY IS GONE (WI-20260818-YQB1Y): a ONE-column relation whose column type is
    // `Unit` used to 1-collapse to the same `Unit` a zero-column relation gets, so no
    // type-level check could see the column and only this guard could. Its schema is now
    // `(t: Unit)` and `Membership` refuses it at LOAD, which is where WI-728's recorded
    // limit went. That was the SHARPEST of the three — it needed no generic code at all —
    // so this guard's case is now weaker than it was, and rests on the two above.
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
    Ok(Value::Relation {
        query: std::rc::Rc::new(neg),
        columns,
    })
}

/// Destructure a `Value::Relation` into `(query, columns)`, or a loud type error.
/// Shared by the relational-algebra builtins (`negate` / `union` / …), which all
/// take `Relation` operands.
type RelationParts = (
    std::rc::Rc<Value>,
    std::rc::Rc<[(crate::intern::Symbol, crate::kb::term::VarId)]>,
);
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
        Value::Entity {
            functor,
            pos,
            named,
        } => {
            let mut pos2 = Vec::with_capacity(pos.len());
            for c in pos.iter() {
                pos2.push(rename_query_vars(kb, c, sigma)?);
            }
            let mut named2 = Vec::with_capacity(named.len());
            for (k, c) in named.iter() {
                named2.push((*k, rename_query_vars(kb, c, sigma)?));
            }
            Ok(Value::Entity {
                functor: *functor,
                pos: pos2.into(),
                named: named2.into(),
            })
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
        let va_term = interp
            .kb
            .alloc(crate::kb::term::Term::Var(crate::kb::term::Var::Global(
                *va,
            )));
        sigma.bind(&interp.kb, *vb, va_term);
    }
    let qb_aligned = rename_query_vars(&mut interp.kb, &qb, &sigma)?;
    let disj = interp.build_logical_query_value(
        "disjunction",
        vec![("left", (*qa).clone()), ("right", qb_aligned)],
    )?;
    Ok(Value::Relation {
        query: std::rc::Rc::new(disj),
        columns: cols_a,
    })
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
    let [r, cond, params] = expect_args::<3>("Relation.where_run", args)?;
    let (query, columns) = expect_relation(r)?;
    let params = spec_record_fields(&params, "a where-condition parameter record")?;
    let condition = fill_recipe_holes(&interp.kb, &cond, &columns, params)?;
    let filtered = interp.build_logical_query_value(
        "conjunction",
        vec![("left", (*query).clone()), ("right", condition)],
    )?;
    Ok(Value::Relation {
        query: std::rc::Rc::new(filtered),
        columns,
    })
}

/// WI-1127 — name prefix for a PARAMETER hole in a row-condition recipe: the operand
/// that is neither a column nor a literal (`eq(c.age, v)`, `eq(c.age, thirty())`).
/// `compile_operand` mints `<prefix>N__` for the Nth such operand and hands the
/// EXPRESSION to the runner as a captured argument under that SAME label, so
/// `where_run`/`join_run` fill the hole by exact interned-`Symbol` match — the seam a
/// column hole already uses. A dunder, so it cannot clash with a user field (column names
/// are head-variable names).
const PARAM_HOLE_PREFIX: &str = "__anthill_row_param_";

/// Replace each HOLE in a `LogicalQuery` recipe `Value` with what fills it. A hole is a
/// `Var::Global` variable minted by the row-lambda compiler and identified by its NAME
/// symbol; there are TWO kinds, and the name space is disjoint by construction:
/// a COLUMN hole named by a schema field symbol (`guarded_of` mints it from `c.x`) takes
/// `r`'s real column variable of that name (WI-714), and a PARAMETER hole (WI-1127) takes
/// the value its captured operand evaluated to.
///
/// WI-20260818-YQB1Y — THE THIRD KIND IS GONE. A bare binder `c` used to mint a WHOLE-ROW
/// sentinel that this function filled with the sole column of a 1-collapse relation. With
/// the collapse dropped, a row is a named tuple at every arity and no column variable
/// carries it, so `compile_operand` refuses a bare binder outright and no such hole is
/// ever minted.
///
/// The walk is over the whole recipe, so it reaches the atoms nested under a WI-730
/// `&&`/`||`/`!` spine exactly as it reached the lone atom of the first increment.
/// Matching is by the interned `Symbol` in both cases: the SAME symbol names the
/// lambda's field access and the relation's column, and the SAME symbol names a parameter
/// hole and its capture-record field — exact canonical equality, NOT a cross-scope
/// short-name compare (WI-672). Every `Var::Global` in a `guarded_of` goal is one of the
/// two (the translation introduces vars for nothing else), so a hole matching neither —
/// or a `Value::Node` occurrence, which never appears in a MACRO-BUILT recipe — is a loud
/// error, never a silent drop.
///
/// That `Value::Node` rule is about the RECIPE's own structure and NOT about what a
/// parameter carries: a captured operand's value is arbitrary runtime data, spliced in
/// verbatim without inspection, exactly as `relation_fix` splices its argument. A
/// reflect-valued column compared against a reflect-valued operand therefore puts a
/// `Value::Node` in the goal legitimately, through both constructs alike; the guard below
/// is not weakened by that, because it never governed values in the first place.
fn fill_recipe_holes(
    kb: &crate::kb::KnowledgeBase,
    v: &Value,
    columns: &[(crate::intern::Symbol, crate::kb::term::VarId)],
    params: &[(crate::intern::Symbol, Value)],
) -> Result<Value, EvalError> {
    use crate::kb::term::Var;
    match v {
        Value::Entity {
            functor,
            pos,
            named,
        } => {
            let mut pos2 = Vec::with_capacity(pos.len());
            for c in pos.iter() {
                pos2.push(fill_recipe_holes(kb, c, columns, params)?);
            }
            let mut named2 = Vec::with_capacity(named.len());
            for (k, c) in named.iter() {
                named2.push((*k, fill_recipe_holes(kb, c, columns, params)?));
            }
            Ok(Value::Entity {
                functor: *functor,
                pos: pos2.into(),
                named: named2.into(),
            })
        }
        Value::Var(Var::Global(hole)) => {
            let name = hole.name();
            // WI-1127 — a PARAMETER hole: the compiler could not fold this operand (it is
            // neither a column nor a literal), so it left a hole and captured the
            // EXPRESSION as an argument; the value arrived here already evaluated, in the
            // caller's scope. Keyed by the same interned `Symbol` on both ends (the hole's
            // name IS the capture record's field label), so this is the exact-symbol match
            // a column hole gets, not a name compare. Tried FIRST: a parameter label is a
            // dunder (`__anthill_row_param_N__`), which no column and no user field can
            // spell, so the three hole kinds cannot collide.
            if let Some((_, val)) = params.iter().find(|(p, _)| *p == name) {
                return Ok(val.clone());
            }
            let (_, vid) = columns.iter().find(|(cn, _)| *cn == name).ok_or_else(|| {
                let local = kb.local_name_of(name);
                // A dunder-named hole that reached here is a PARAMETER hole the capture
                // record does not carry — a compile/runtime channel desync, not a schema
                // question, so it says so rather than blaming the schema.
                if local.starts_with(PARAM_HOLE_PREFIX) {
                    return EvalError::Internal(format!(
                        "where_run: the compiled condition references parameter hole `{local}`, \
                         which the capture record does not carry ({} parameter(s) passed)",
                        params.len()
                    ));
                }
                EvalError::Internal(format!(
                    "where_run: the compiled condition references column `{local}`, which is \
                     not in the relation's schema"
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
/// not a short-name compare). A literal becomes its value. Any other operand that does
/// not READ the row becomes a PARAMETER hole, its expression captured as an argument of
/// the spliced `where_run` call (WI-1127, [`compile_operand`]). An operand that does read
/// the row, and a condition outside the goal-expressible `Bool` subset, are loud compile
/// errors (LINQ's "cannot translate").
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
    // then splice `where_run(r, <recipe>, <captured params>)` — the runtime back-end.
    let mut params = Vec::new();
    let recipe = compile_condition(interp, &body, &[binder], &mut params)?;
    splice_query_runner(
        interp,
        "anthill.prelude.Relation.where_run",
        &[r_occ],
        recipe,
        params,
    )
}

/// Splice a `<runner>(<relation…>, <recipe>)` call for a row-lambda macro — the shared
/// tail of `guarded_of` → `where_run` (one row) and `conjoin_of` → `join_run` (two
/// rows). The compiled `recipe` rides an `Expr::Spliced` leaf STAMPED
/// `anthill.reflect.LogicalQuery` (the `runner`'s `cond: LogicalQuery` slot); the
/// relation occurrences pass through positionally ahead of it. The result is a normal
/// runtime call the typer re-types (via the macro-expand splice) and eval runs.
///
/// WI-1127 — `params` are the condition's row-independent operand OCCURRENCES, one per
/// PARAMETER hole `compile_operand` minted, riding as NAMED arguments labelled by the
/// hole's own symbol. They fill the runner's trailing variadic capture (`...params: P`,
/// proposal 056), which the typer folds into one named-tuple record — so the runner
/// reads `(hole-label ↦ value)` and matches it against the recipe's holes by exactly the
/// interned symbol both sides were minted from. The occurrences are re-typed HERE, in
/// the caller's scope, which is the whole point: their meaning (`v`, `thirty()`) exists
/// at the call and not inside the lambda the macro read as syntax.
///
/// It is not the only synthesizer of an `Expr::Apply` carrying NAMED arguments —
/// `substitute_to_occurrence` (kb/simp_rewrite.rs) copies parse-checked keys, and
/// `normalize_variadic_capture` itself rebuilds one from a call's own labels. It is the
/// only one that MINTS its labels rather than carrying labels an author wrote, which is
/// what the WI-805 duplicate-label guard's reachability note turns on (typing.rs): a
/// running counter cannot repeat, so the guard stays unreachable through this path.
fn splice_query_runner(
    interp: &mut Interpreter,
    runner_qn: &str,
    relations: &[std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>],
    recipe: Value,
    params: Vec<(
        crate::intern::Symbol,
        std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
    )>,
) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence::{Expr, NodeOccurrence};
    use std::rc::Rc;
    // The first relation occurrence anchors the synthesized nodes' source/owner.
    let anchor = relations.first().ok_or_else(|| {
        EvalError::Internal("WI-714: query-runner splice with no relation operand".into())
    })?;
    let pass = crate::kb::occurrence::macro_expand_pass(&mut interp.kb);
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
    //
    // WI-913: through the FALLIBLE form, not a `try_resolve_symbol` pre-check ahead of
    // the infallible one. That pre-check was total only while the two spellings asked
    // the same question, and routing the mint through the name ladder made them differ
    // — the ladder is strictly narrower (a field, an `internal` name), so the guard
    // could admit a name the mint then interned as the very phantom it exists to stop.
    // One lookup, and the guard IS the mint.
    let query_ty = Value::term(
        interp
            .kb
            .try_make_sort_ref_by_name("anthill.reflect.LogicalQuery")
            .ok_or_else(|| {
                EvalError::Internal(format!(
                    "WI-714 {runner_qn} lowering: anthill.reflect.LogicalQuery is not resolvable"
                ))
            })?,
    );
    spliced.set_inferred_type(query_ty);
    let runner = interp
        .kb
        .try_resolve_symbol(runner_qn)
        .ok_or_else(|| EvalError::Internal(format!("WI-714: {runner_qn} unresolved")))?;
    let mut pos_args: Vec<Rc<NodeOccurrence>> = relations.to_vec();
    pos_args.push(spliced);
    let call = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: runner,
            pos_args,
            named_args: params,
            type_args: Vec::new(),
        },
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
                            _ => return Err(macro_rejects(
                                "a two-row lambda `(c, q) -> …` binding two plain rows",
                                "a join lambda whose tuple binder nests a non-plain sub-pattern"
                                    .to_string(),
                                sub,
                            )),
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
    let mut params = Vec::new();
    let recipe = compile_condition(interp, &body, &binders, &mut params)?;
    splice_query_runner(
        interp,
        "anthill.prelude.Relation.join_run",
        &[r1_occ, r2_occ],
        recipe,
        params,
    )
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
///
/// WI-1128 / WI-20260818-YQB1Y — THE TYPE CAUGHT UP WITH THIS SIDE. A relation VALUE has
/// always carried `(name, VarId)` for every column, so the merge below was already correct
/// for a one-column operand while the schema TYPE could not state the merged result and
/// `Concat` refused it. Dropping the 1-collapse (`relation_schema_type`, kb/typing.rs) gives
/// the type the same column names the value has, so a one-column operand now merges at both
/// levels and the refusal is gone.
fn relation_join_run(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r1, r2, cond, params] = expect_args::<4>("Relation.join_run", args)?;
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
                interp
                    .kb
                    .alloc(crate::kb::term::Term::Var(crate::kb::term::Var::Global(
                        fresh,
                    )));
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
    let params = spec_record_fields(&params, "a join-condition parameter record")?;
    let condition = fill_recipe_holes(&interp.kb, &cond, &merged, params)?;
    let product = interp.build_logical_query_value(
        "conjunction",
        vec![("left", (*q1).clone()), ("right", q2_fresh)],
    )?;
    let joined = interp
        .build_logical_query_value("conjunction", vec![("left", product), ("right", condition)])?;
    Ok(Value::Relation {
        query: std::rc::Rc::new(joined),
        columns: merged,
    })
}

/// WI-787: read a NAME-KEYED record — `Relation.project_run`'s projection map,
/// `Relation.fix`'s restriction record, and (WI-1127) `where_run`/`join_run`'s
/// captured condition parameters — as the `named` half of a tuple, with a
/// POSITIONAL component refused loudly rather than ignored.
///
/// These are the tuple readers that legitimately want `named` ALONE: every entry
/// is `name ↦ …` (a column for the first two, a recipe hole for the third), and a
/// positional component carries no name, so there is nothing it could restrict,
/// select or fill. But reading one half and dropping the other is exactly the
/// WI-787 defect, and here it would degrade silently — a record whose components
/// all landed in `pos` reads as EMPTY, which every caller treats as "nothing to
/// do", so the filter vanishes and the query returns unrestricted rows.
///
/// No source program reaches this. `project_run`'s spec is built by the typer
/// with `pos` hardcoded empty; `fix`'s is rejected upstream by the `Without`
/// reduction, which refuses a key naming no column (MEASURED: `fix(_1: 3)`,
/// where `_1` is the synthetic positional label for index 0 and so is hoisted
/// into `pos`, fails to LOAD); and the condition parameters are minted by
/// `compile_operand` as NAMED arguments alone, so the capture has no positional
/// leftover to bind. The guard is for a programmatically-built record, and it is
/// a loud error rather than a `debug_assert` because the silent reading is a
/// WRONG ANSWER, not a crash.
fn spec_record_fields<'a>(
    spec: &'a Value,
    what: &'static str,
) -> Result<&'a [(crate::intern::Symbol, Value)], EvalError> {
    match spec {
        Value::Tuple { pos, named } if pos.is_empty() => Ok(named),
        Value::Tuple { pos, .. } => Err(EvalError::TypeMismatch {
            expected: what,
            got: format!(
                "a record with {} POSITIONAL component(s), which name nothing — every entry \
                 must be `name ↦ value`",
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
    let pairs = spec_record_fields(
        &spec,
        "a projection spec tuple (result-key ↦ source-column-name)",
    )?;
    let mut projected: Vec<(crate::intern::Symbol, crate::kb::term::VarId)> =
        Vec::with_capacity(pairs.len());
    for (result_key, source) in pairs.iter() {
        // The source NAME reads carrier-neutrally (WI-20260827-3ZNBC), like every
        // other string read in this file. The typer splices this spec with native
        // `Value::Str` entries today, so nothing drives the other carriers — but a
        // name is a string on all of them, and this was the one native-variant string
        // read left after the pass (found by /code-review).
        let source_name =
            str_operand(interp.kb(), source).map_err(|_| EvalError::TypeMismatch {
                expected: "a source column name (String) in the projection spec",
                got: source.type_name().to_string(),
            })?;
        let source_name = source_name.as_ref();
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
    Ok(Value::Relation {
        query,
        columns: projected.into(),
    })
}

/// `Relation.rename` (WI-731) — the RUNTIME back-end of `r.rename(who: r.name)`: re-key some
/// of the relation's columns IN PLACE, keeping the rest and keeping the ORDER. An ordinary
/// operation with a variadic capture (proposal 056 §2.1, `fix`'s shape) — no compile-time
/// macro, and nothing keyed on `rename`'s identity in the typer.
///
/// `spec` is the captured record `(result-key ↦ the one-column relation naming the source)`.
/// The source column arrives as a RELATION VALUE rather than a name, which is the same thing
/// its TYPE carries at the reduction boundary ([`rename_schema_type`]) — one surface, read
/// twice, and neither reading invents a channel the other lacks.
///
/// MATCHED BY THE COLUMN'S NAME **AND** ITS VARIABLE — see the note at the check itself. The
/// name selects the column (names are distinct within a schema); the variable checks that the
/// source came from THIS relation, which no type can state. `r.rename(who: other.name)` is
/// therefore caught here, loudly, rather than renaming `r`'s own `name` behind the author's
/// back — and a receiver carrying one variable in two columns still re-keys exactly one.
fn relation_rename(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r, spec] = expect_args::<2>("Relation.rename", args)?;
    let (query, columns) = expect_relation(r)?;
    let pairs = spec_record_fields(
        &spec,
        "a rename spec record (result-key \u{21a6} the one-column relation naming the source)",
    )?;
    let mut map: Vec<(crate::intern::Symbol, crate::intern::Symbol)> =
        Vec::with_capacity(pairs.len());
    for (result_key, source) in pairs.iter() {
        let key_name = interp.kb.local_name_of(*result_key).to_string();
        let (_src_query, src_columns) = expect_relation(source.clone())?;
        let [(src_name, src_vid)] = src_columns.as_ref() else {
            return Err(EvalError::Internal(format!(
                "Relation.rename: entry `{key_name}` names {} columns; a rename's source is \
                 exactly one column (the typer's `Rename` reduction refuses every other \
                 arity, so this is a programmatically-built spec)",
                src_columns.len()
            )));
        };
        // BOTH HALVES, and each answers a different question. The NAME selects which of the
        // receiver's columns is meant — names are distinct within a schema (§4.5), so the
        // name is the key, and it is the same key `rename_schema_type` resolved against `T`.
        // The VARIABLE then checks PROVENANCE: `r.name` projects `r`'s own column and carries
        // `r`'s `VarId`, so a source lifted from a DIFFERENT relation fails here even when the
        // two columns share a name — which no TYPE can see, since `Relation[T = (name: …)]`
        // states none.
        //
        // THE VARIABLE ALONE IS NOT A KEY, and that was this function's first cut. A relation
        // may carry ONE `VarId` in TWO columns — `r.(a: id, b: id)` is a legal projection, and
        // `keep_spec_projections` refuses only duplicate RESULT keys, never a duplicate source
        // — so `p.rename(z: p.a)` re-keyed BOTH of them and returned a row with two `z`
        // columns and no `b`: a wrong row, disagreeing with the type `Rename` had computed,
        // and unanswerable to `row.b` downstream.
        let Some(_) = columns.iter().find(|(n, v)| n == src_name && v == src_vid) else {
            let src = interp.kb.local_name_of(*src_name).to_string();
            return Err(EvalError::TypeMismatch {
                // A PROGRAM error, not an evaluator-invariant one, so NOT `Internal` — the
                // resolver bridge `debug_assert`s on that variant (kb/resolve.rs), which
                // would abort a debug build and silently residualize a release one on an
                // ordinary user mistake. The same reading `UnpinnedRequirement` records.
                expected: "a column of the relation being renamed",
                got: format!(
                    "`{src}`, which is a column of a DIFFERENT relation (entry `{key_name}`). \
                     A rename re-keys the receiver's own columns, so write the source off the \
                     receiver: `r.rename({key_name}: r.{src})`"
                ),
            });
        };
        map.push((*src_name, *result_key));
    }
    // `columns` IN ORDER — a renamed column keeps its position, the VALUE half of the
    // in-place rule `rename_schema_type` states for the TYPE.
    let renamed: Vec<(crate::intern::Symbol, crate::kb::term::VarId)> = columns
        .iter()
        .map(|(name, vid)| {
            let key = map
                .iter()
                .find_map(|(s, k)| (s == name).then_some(*k))
                .unwrap_or(*name);
            (key, *vid)
        })
        .collect();
    Ok(Value::Relation {
        query,
        columns: renamed.into(),
    })
}

/// `Relation.fix` (WI-714 / proposal 052 §"`fix` is sugar"; WI-727 / proposal 056) — the
/// RUNTIME back-end of `fix(p, x: 1, z: 2)`: RESTRICT relation columns to given VALUES and
/// DROP them. `fix` is an ORDINARY operation (proposal 056 §2.1) — no compile-time macro,
/// no typer recognizer keyed on its name: the variadic capture folded its dynamic column
/// arguments into `spec`, an ordinary `Value::Tuple` record `(column-name ↦ value)`,
/// which reaches this builtin as a plain argument. For each `(col, val)`: wrap
/// `guarded(query, eq(col's variable, val))` — the same query-combining step
/// `where`/`negate`/`union` perform, with `eq` the resolver's equality connective
/// (`PartialEq.eq`, as `where`'s guards use) restricting the column to that value — then
/// DROP that column from `columns`. The column variable stays in the query (still SOLVED),
/// so a dropped column keeps the source relation's row multiplicity (bag semantics, OQ6,
/// exactly as `project`). Columns match `spec` keys by canonical interned symbol (the same
/// seam `project_run`/`where_run` use), NOT a short-name compare (WI-672). A key naming no
/// column is a loud error; an empty record (`r.fix()`) is the identity.
///
/// "CONSTANT" IN 052's PROSE MEANS ROW-INDEPENDENT — one value for the whole restriction,
/// as against `where`'s per-ROW predicate — and NOT a literal, NOT a compile-time constant.
/// The argument is an ORDINARY expression of the column's type, evaluated ONCE at the call
/// before `fix` is applied, so an operation result, a `let`-bound value, or the caller's own
/// parameter all restrict identically; the guard is a semantic `eq` over whatever `Value`
/// arrived, and there is no constant check in the typer or here to relax. WI-735 asked to
/// relax a gate that does not exist here, and was rejected; the `wi727_fix_value_may_be_*`
/// tests pin it, the runtime-parameter one being the control a literal-only `fix` could
/// not pass.
///
/// SAME OPERAND SET AS `where` (WI-1127), by two different routes. `fix` takes its value
/// as an ORDINARY ARGUMENT, already evaluated when it arrives here; `where`'s condition is
/// a row lambda compiled AS SYNTAX by the `guarded_of` macro, which cannot fold a value
/// that does not exist yet — so it CAPTURES the operand expression as a recipe parameter
/// and `where_run` fills it with the same evaluated `Value` this builtin receives.
///
/// Until WI-1127 that was NOT so, and the header's `fix ≡ where(…) + project` was simply
/// FALSE for every non-literal `v`: `compile_operand` admitted a column or a literal and
/// refused the rest, so the `where` spelling of `fix(x: v)` did not load. The equivalence
/// is stated here because it now holds, not because it always did — and that literal-only
/// diagnostic is what WI-735 read and mis-attributed to `fix`, through this very claim.
fn relation_fix(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [p, spec] = expect_args::<2>("Relation.fix", args)?;
    let (query, columns) = expect_relation(p)?;
    let fixes = spec_record_fields(
        &spec,
        "a fix record (column-name ↦ value) captured named tuple",
    )?;
    let eq_sym = interp
        .kb
        .try_resolve_symbol("anthill.prelude.PartialEq.eq")
        .ok_or_else(|| {
            EvalError::Internal("fix: `anthill.prelude.PartialEq.eq` is unresolvable".to_string())
        })?;
    let mut query: Value = (*query).clone();
    for (col_name, fixed_val) in fixes.iter() {
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
        // The restrict guard `eq(?col, val)` — a goal atom the resolver conjoins with the
        // query (guarded), pinning `?col` to that value on the surviving solutions. `val` is
        // whatever the argument evaluated to (see the header): no constant-ness is asked of
        // it here or anywhere upstream.
        let guard = Value::Entity {
            functor: eq_sym,
            pos: std::rc::Rc::from(vec![
                Value::Var(crate::kb::term::Var::Global(vid)),
                fixed_val.clone(),
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
    Ok(Value::Relation {
        query: std::rc::Rc::new(query),
        columns: kept.into(),
    })
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
    (
        "anthill.prelude.Bool.and",
        "conjunction",
        &["left", "right"],
    ),
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
/// `params` collects the atoms' captured OPERANDS — see [`compile_operand`]. It is
/// threaded through the connective recursion rather than gathered per atom, so the whole
/// tree's parameters share one index space and one capture record.
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
    params: &mut Vec<(
        crate::intern::Symbol,
        std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
    )>,
) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence::Expr;
    let Some(Expr::Apply {
        functor,
        pos_args,
        named_args,
        ..
    }) = body.as_expr()
    else {
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
            operands.push((*field, compile_condition(interp, arg, binders, params)?));
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
        pos.push(compile_operand(interp, a, binders, params)?);
    }
    let mut named = Vec::with_capacity(named_args.len());
    for (k, a) in named_args {
        named.push((*k, compile_operand(interp, a, binders, params)?));
    }
    let atom = Value::Entity {
        functor: *functor,
        pos: pos.into(),
        named: named.into(),
    };
    interp.build_logical_query_value("pattern_query", vec![("term", atom)])
}

/// Compile one predicate operand: a column field-access `c.x` on a binder becomes a
/// HOLE (a fresh var named `x`, filled by `where_run`/`join_run`); a literal becomes
/// its value. `binders` holds the one (`where`) or two (`join`) row binders.
///
/// WI-1127 — ANY OTHER operand that does not mention a row binder becomes a second kind
/// of hole: a PARAMETER. The macro reads the lambda as SYNTAX, at load time, so a
/// `let`-bound name or an operation call has no value yet to fold — but it has no
/// dependence on the row either, so it is one value for the whole restriction, exactly
/// what `fix` already takes as an ordinary argument. It is pushed onto `params` under a
/// freshly-minted dunder label and re-emitted by [`splice_query_runner`] as a captured
/// argument of the runner, which evaluates it in the CALLER's scope and fills the hole.
///
/// A ROW-DEPENDENT operand (`plus(c.age, 1)`) stays a loud rejection: there is no single
/// value to capture, and computing per row is not what a query goal does — 052's "cannot
/// translate". Recognized by [`mentions_binder`] — a read of one of THESE binder symbols
/// anywhere in the subtree, nested lambda bodies included.
fn compile_operand(
    interp: &mut Interpreter,
    occ: &std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
    binders: &[crate::intern::Symbol],
    params: &mut Vec<(
        crate::intern::Symbol,
        std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
    )>,
) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence::Expr;
    use crate::kb::term::{Literal, Var};
    // A column reference `c.x` on a binder becomes a HOLE: a fresh var NAMED by the
    // field symbol, which `where_run`/`join_run` fills with the real column of that name.
    if let Some(field) = binder_field_access(interp, occ, binders) {
        let hole = interp.kb.fresh_var(field);
        return Ok(Value::Var(Var::Global(hole)));
    }
    // A BARE binder reference `c` is the WHOLE ROW, and WI-20260818-YQB1Y made that a
    // loud rejection rather than a hole. It used to mint a WHOLE-ROW sentinel that
    // `where_run` filled with the relation's sole column, which was only ever correct
    // because a one-column relation's row WAS its column under the 1-collapse. With the
    // collapse gone a row is a named tuple at every arity — `(age: 30)`, never `30` — so
    // no column variable carries it and there is nothing honest to fill the hole with.
    //
    // A REFUSAL AND NOT A TUPLE-BUILDING FILL: a query goal compares columns, and
    // reconstructing the row as a tuple TERM would put a shape in the goal that the
    // resolver has no column to unify against. The remedy is one dot — `eq(c.age, 30)`
    // for `where`, `eq(c.age, q.age)` for `join` — which is also what the row's own type
    // now says. This is where the sentinel's OTHER defect went too: one symbol was minted
    // for a bare `c` and a bare `q`, so in a join condition the hole could say neither
    // which row it meant nor match the sole-column arm over the MERGED column list
    // (WI-1128 recorded it as a second, independent blocker with no drivable control).
    // Deleting the sentinel closes both at once — there is no per-binder keying to get
    // right when there is no whole-row hole.
    if is_binder_ref(occ, binders) {
        return Err(macro_rejects(
            "a COLUMN of the row (`c.age`) as a condition operand",
            "a bare row binder, which is the WHOLE row — a named tuple of every column, \
             not a value a query goal can compare. Name the column you mean (`c.age`)"
                .to_string(),
            occ,
        ));
    }
    // A LITERAL folds into the recipe directly — no capture, no runtime argument.
    // (Only the four scalar kinds; any other `Const` takes the parameter channel below,
    // where it is evaluated like any other expression rather than refused.)
    if let Some(Expr::Const(lit)) = occ.as_expr() {
        match lit {
            Literal::Int(n) => return Ok(Value::Int(*n)),
            Literal::Float(f) => return Ok(Value::Float(f.0)),
            Literal::Bool(b) => return Ok(Value::Bool(*b)),
            Literal::String(s) => return Ok(Value::Str(s.clone())),
            _ => {}
        }
    }
    // ROW-DEPENDENT: nothing to capture — the operand's value differs per row.
    if mentions_binder(occ, binders) {
        return Err(macro_rejects(
            "a row-INDEPENDENT operand — a column (`c.x`), a literal, or any expression \
             that does not read the row (it is captured and evaluated once, at the call)",
            "an operand that COMPUTES over the row binder — a query goal compares columns, \
             it does not evaluate expressions per row (compute it with `.map` on the \
             stream instead)"
                .to_string(),
            occ,
        ));
    }
    // A PARAMETER: hole + captured expression, keyed by one freshly-minted label.
    let label = interp
        .kb
        .intern(&format!("{PARAM_HOLE_PREFIX}{}__", params.len()));
    params.push((label, std::rc::Rc::clone(occ)));
    let hole = interp.kb.fresh_var(label);
    Ok(Value::Var(Var::Global(hole)))
}

/// WI-1127 — does `occ` read a row binder anywhere in its subtree? The test that splits
/// a row-INDEPENDENT operand (capturable as a recipe parameter, evaluated once at the
/// call) from a row-DEPENDENT one (a loud rejection). Walks the occurrence children
/// through the canonical [`for_each_child`]; a non-`Expr` child (a nested lambda's
/// Pattern) binds names rather than reading them.
///
/// The match is on the binder SYMBOLS, not their spelling, and both halves of that are
/// driven by `wi1127_binder_matching_is_symbol_exact_and_descends`. It DESCENDS into a
/// nested lambda's body, so `apply1(lambda z -> c.age, 1)` is caught — stopping at the
/// operand's top node would compile a per-row read into a goal that cannot mean it. And
/// an inner binder that merely REUSES the row binder's spelling (`apply1(lambda c -> c,
/// 30)`) is a DIFFERENT symbol, reads no row, and is captured — MEASURED, and correct:
/// refusing it would reject an operand whose value is perfectly row-independent.
fn mentions_binder(
    occ: &std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
    binders: &[crate::intern::Symbol],
) -> bool {
    if is_binder_ref(occ, binders) {
        return true;
    }
    let Some(expr) = occ.as_expr() else {
        return false;
    };
    let mut found = false;
    crate::kb::node_occurrence::for_each_child(expr, |child| {
        found = found || mentions_binder(child, binders);
    });
    found
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
///
/// THE FIELD NAME ALONE IDENTIFIES THE COLUMN — an INVARIANT, not a property of this
/// function, and WI-731 documents it here rather than changing anything. The returned symbol
/// discards WHICH BINDER the access came from, so in a two-row `join` condition
/// `eq(c.name, q.name)` both operands mint a hole named `name` and `fill_recipe_holes` maps
/// both to the SAME column variable: the condition degrades to `eq(?x, ?x)`, vacuously true,
/// and EVERY pair of rows joins. That is a silently unfiltered cartesian product, not an
/// error.
///
/// IT IS UNREACHABLE, BY TWO ENFORCEMENT SITES, and both are named because the invariant is
/// upheld elsewhere and nothing here would notice if they stopped:
///  * `concat_named_tuple_types` (kb/typing.rs) refuses a merged schema whose operands share
///    a field name, at LOAD — so no program in which both holes could exist ever loads;
///  * `join_run`'s own merged-name guard (below) fires before `fill_recipe_holes` on the
///    reflect path, which the typer does not gate.
///
/// SO WI-731 DELIBERATELY DID NOT "FIX" IT. Keying a hole by `(binder, field)` would be a
/// change with no drivable control — a test would pass with and without it, since the
/// program that needs it cannot load (the WI-1078 shape). What WI-731 shipped instead is the
/// `rename` operator, which is how an author gets PAST the refusal: renaming one side leaves
/// the two holes distinct by construction, so the fix removes the collision rather than
/// teaching the holes to live with it. It is the AUTOMATIC-QUALIFICATION design — merging
/// `c.name`/`q.name` into `left.name`/`right.name` behind the author's back — that would have
/// made this live, which is the strongest reason the collision surface and this invariant had
/// to be decided together.
fn binder_field_access(
    interp: &mut Interpreter,
    occ: &std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>,
    binders: &[crate::intern::Symbol],
) -> Option<crate::intern::Symbol> {
    use crate::kb::node_occurrence::Expr;
    match occ.as_expr()? {
        // Post-typing form (the real one): `c.x` → `field_access(c, "x")`.
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        } if named_args.is_empty() => {
            let (receiver, field) =
                crate::kb::body_specialize::field_access_parts(&interp.kb, *functor, pos_args)?;
            is_binder_ref(&receiver, binders).then(|| interp.kb.intern(&field))
        }
        // Pre-lowering fallback: `c.x` as a zero-arg `DotApply`.
        Expr::DotApply {
            receiver,
            name,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() && is_binder_ref(receiver, binders) => {
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
    Ok(Value::Entity {
        functor,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    })
}

/// WI-SPGBP — `KB.loaded(sources: List[String]) -> KB`, the scoped load.
///
/// Loads each source text as a DISCARDABLE LAYER over the interpreter's own KB and
/// returns the layer as a first-class `KB` value. The ticket's form, unchanged:
/// `execute(loaded(sources), q)` — no bracket, no second KB, no goal-as-a-name.
///
/// WHY A LAYER AND NOT A SEPARATE KB. The goal handed to `execute` is an arbitrary
/// LOGICAL TERM, and its symbols are the CALLER's. A separate KB with its own tables
/// would make that term meaningless on the far side and force the goal to be a NAME
/// resolved there — the short-name identity matching WI-672 / WI-897 removed. Sharing
/// the caller's term store and symbol table is what keeps a goal written at the call site
/// legal in the result.
///
/// FAILURE IS THE ANSWER, NOT AN INTERNAL ERROR. A candidate program that does not parse
/// or does not load is exactly what a checker is asking about, so both are `raise`d as an
/// `Error` payload carrying the diagnostics — and the layer is unwound first, so a failed
/// `loaded` leaves the KB exactly as it found it. That unwind is why the snapshot is
/// taken here and handed to the arena only on success (see
/// [`crate::eval::layer_arena::LayerArenaRef::push`]).
fn kb_loaded(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [sources_arg] = expect_args::<1>("KB.loaded", args)?;
    let texts = expect_string_list(interp, &sources_arg)?;

    // Parse BEFORE snapshotting: a parse fault touches no KB state, so there is nothing
    // to unwind and the diagnostic is not entangled with a restore.
    let mut parsed = Vec::with_capacity(texts.len());
    for (i, text) in texts.iter().enumerate() {
        match crate::parse::parse(text) {
            Ok(file) => parsed.push(file),
            Err(errors) => {
                // Located `line:col: message`, built off ONE `LineIndex` for the whole
                // batch — `ParseError` has no `Display` precisely so a caller cannot
                // re-index the source per error (see `ParseError::all_located`). There
                // is no path to render: a scoped source is a String the caller supplied.
                let loc = crate::span::LineIndex::new(text);
                let detail: Vec<String> = errors
                    .iter()
                    .map(|e| format!("source {i}: {}", e.format_at(&loc)))
                    .collect();
                return Err(interp.raise_load_failed(detail));
            }
        }
    }

    let snapshot = interp.kb.snapshot_scoped();
    let refs: Vec<&crate::parse::ir::ParsedFile> = parsed.iter().collect();
    match crate::kb::load::load_incremental(&mut interp.kb, &refs, &crate::kb::load::NullResolver) {
        Ok(_) => {
            // The layer can OVERRIDE what the base declared, so the interpreter's memos
            // have to go on the way IN as well as on the way out (`sweep_layers` clears
            // them again on the discard). `op_body_cache` and `const_cache` are keyed by
            // `Symbol` and are not touched by `load_incremental` — a base operation whose
            // body was cached before the layer would otherwise keep running the base's
            // version of a definition the layer just replaced.
            //
            // The KB's OWN caches are the loader's business, not this function's: a layer
            // load IS `load_incremental`, which every embedder already runs against a
            // live KB, so whatever invalidation it does is the established contract here
            // too. These two are the pair no loader ever sees.
            interp.op_body_cache.clear();
            // Same rule as the discard side (`Interpreter::sweep_layers`): an in-flight
            // `Forcing` sentinel is control state, not a memo, and dropping it disables
            // const-cycle detection for a const whose body is being evaluated right now.
            interp
                .const_cache
                .retain(|_, entry| matches!(entry, crate::eval::ConstCacheEntry::Forcing));
            // WI-5XBBQ — the DECLARATION half of the layer delta, copied NOW. The
            // ledger it reads is per-scan, so this is the only instant at which it
            // still describes THIS load; see `declared_symbols_of_last_scan`.
            let declared = interp.kb.declared_symbols_of_last_scan();
            let handle = interp.layers.push(snapshot, declared);
            Ok(Value::Kb(handle))
        }
        Err(errors) => {
            // Unwind FIRST. A caller that catches this must see the KB it had, not a
            // half-loaded one — a partially applied layer is the state the ticket calls
            // worse than none.
            interp.kb.restore_scoped(snapshot);
            // Rendered through the loader's OWN batch renderer, not a `to_string()` loop:
            // it locates each error against a per-file `LineIndex` built once, which is
            // the whole reason `render_all` exists (WI-745 / WI-852). These diagnostics
            // are the answer a checker reports, so they should read the way the CLI's do.
            let detail: Vec<String> = crate::kb::load::LoadError::render_all(&errors).collect();
            Err(interp.raise_load_failed(detail))
        }
    }
}

/// WI-5XBBQ — the `KB` argument of a layer-delta reader, as the LAYER it names.
///
/// Two refusals, both loud, because either would otherwise answer a plausible lie:
///
/// * `kb()` — the ambient sentinel — names no layer, so it has no delta. Answering the
///   empty list there would report every candidate as having contributed nothing.
/// * A layer with another layer applied ON TOP of it. The KB the delta is measured
///   against is the one as it stands, which includes the inner layer, so an outer
///   handle's marks would attribute the inner layer's symbols and clauses to the outer
///   one. This is the same fact `LayerArenaRef::retain_innermost` is built on.
fn expect_innermost_layer(
    interp: &Interpreter,
    arg: &Value,
    op: &'static str,
) -> Result<crate::eval::layer_arena::KbHandle, EvalError> {
    let handle = match arg {
        Value::Kb(h) => h.clone(),
        other => {
            return Err(EvalError::Internal(format!(
                "KB.{op}: the layer delta is a question about a SCOPED LOAD, and `{}` names \
                 no layer — pass the value `KB.loaded(sources)` returned",
                other.type_name()
            )))
        }
    };
    if !interp.layers.is_innermost(&handle) {
        return Err(EvalError::Internal(format!(
            "KB.{op}: this layer is not the innermost one, and its delta would be measured \
             against a knowledge base that still has a later layer applied — let the inner \
             layer be DISCARDED first (releasing it is not enough: a released layer stays \
             applied until the interpreter sweeps it)"
        )));
    }
    Ok(handle)
}

/// WI-5XBBQ — `KB.layer_symbols(kb) -> List[LayerSymbol]`, the DEFINITION half of a
/// scoped load's delta.
///
/// Two answers in one row, because neither subsumes the other and a gate needs both:
///
/// * `minted` — the layer created this symbol. The mint mark decides it, and the mark
///   is exact because `SymbolTable::defs` is append-only under a layer.
/// * `declared` — the layer wrote a `sort` / `enum` / `entity` / `operation` / `const` /
///   type-parameter declaration at this name. MEASURED, and it is the reason this
///   half exists: a scoped load can write `sort guardians.Triage` — a name the BASE
///   owns — and the load re-enters the same symbol rather than minting a second, so
///   `minted` is false and the mark alone never sees the redeclaration.
///
/// A symbol can be both (an ordinary new declaration), minted only (a predicate a
/// `rule` head brought into existence — §8.6 says a rule head is resolved, not
/// declared, so it has no declaration ledger entry), or declared only (the
/// redeclaration above).
///
/// UNRESOLVED SYMBOLS ARE SKIPPED. A load interns strings that name nothing — a
/// positional field label, a parse-time short name that never resolved — and they
/// have no qualified name for a policy to read or a diagnostic to print.
fn kb_layer_symbols(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [kb_arg] = expect_args::<1>("KB.layer_symbols", args)?;
    let handle = expect_innermost_layer(interp, &kb_arg, "layer_symbols")?;
    let (mark, declared) = interp
        .layers
        .with_delta(&handle, |d| (d.symbol_mark(), d.declared().to_vec()));
    let declared_set: std::collections::HashSet<crate::intern::Symbol> =
        declared.iter().copied().collect();

    // Minted first, in mint order; then the redeclarations, which the mark cannot see.
    let mut rows: Vec<(crate::intern::Symbol, bool, bool)> = Vec::new();
    for raw in mark..interp.kb.symbols.symbol_count() {
        let sym = crate::intern::Symbol::from_raw(raw);
        if !interp.kb.symbols.is_resolved(sym) {
            continue;
        }
        rows.push((sym, true, declared_set.contains(&sym)));
    }
    for sym in declared {
        // The SAME `is_resolved` guard as the minted loop above, and it has to be the
        // same one: a declaration ledger entry naming an unresolved symbol would fall
        // back to its bare intern string in `qualified_name_of`, and the naming rule
        // would then refuse a candidate citing a name that denotes nothing.
        if sym.index() < mark && interp.kb.symbols.is_resolved(sym) {
            rows.push((sym, false, true));
        }
    }

    let ctor = require_symbol(interp, "anthill.reflect.LayerSymbol", "LayerSymbol")?;
    let f_symbol = interp.kb_mut().intern("symbol");
    let f_minted = interp.kb_mut().intern("minted");
    let f_declared = interp.kb_mut().intern("declared");
    let elements: Vec<Value> = rows
        .into_iter()
        .map(|(sym, minted, declared)| {
            let name = interp.kb_mut().alloc(crate::kb::term::Term::Ref(sym));
            Value::Entity {
                functor: ctor,
                pos: Vec::new().into(),
                named: vec![
                    (f_symbol, Value::term(name)),
                    (f_minted, Value::Bool(minted)),
                    (f_declared, Value::Bool(declared)),
                ]
                .into(),
            }
        })
        .collect();
    interp.build_list_value(elements, &[])
}

/// WI-5XBBQ — `KB.layer_clauses(kb) -> List[LayerClause]`, the ASSERTION half.
///
/// EVERY CLAUSE THE LAYER'S SOURCE TEXT WROTE, and nothing the loader derived — see
/// [`crate::kb::ClauseOrigin`] for why the two must be told apart and why a
/// head-namespace exemption cannot do it. Without the filter this answer would include
/// the reflect metadata row the loader banks for an ordinary `provides` clause, and a
/// containment rule over it would refuse every well-formed candidate.
///
/// Retracted slots are skipped: they include the TOMBSTONES an inner layer's discard
/// left behind (`KnowledgeBase::tombstone_layer_rules`), which are not this layer's
/// clauses in any sense a policy means.
fn kb_layer_clauses(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [kb_arg] = expect_args::<1>("KB.layer_clauses", args)?;
    let handle = expect_innermost_layer(interp, &kb_arg, "layer_clauses")?;
    let mark = interp.layers.with_delta(&handle, |d| d.clause_mark());

    let rows = interp.kb.layer_source_clauses(mark);

    let ctor = require_symbol(interp, "anthill.reflect.LayerClause", "LayerClause")?;
    let f_functor = interp.kb_mut().intern("functor");
    let f_head = interp.kb_mut().intern("head");
    let f_bodied = interp.kb_mut().intern("bodied");
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let f_value = interp.kb_mut().intern("value");
    let mut elements = Vec::with_capacity(rows.len());
    for (functor, head, bodied) in rows {
        // A DENIAL — `rule ⊥ :- …` — heads at the kernel's bottom, which interns no
        // symbol, so this really is `none` rather than a shape that cannot occur. It is
        // REPORTED and not skipped: a clause a policy cannot see is a clause it cannot
        // refuse, and a denial installed over the base by an untrusted program is
        // exactly the kind a policy wants to refuse.
        let functor = match functor {
            Some(sym) => {
                let name = interp.kb_mut().alloc(crate::kb::term::Term::Ref(sym));
                Value::Entity {
                    functor: some_sym,
                    pos: Vec::new().into(),
                    named: vec![(f_value, Value::term(name))].into(),
                }
            }
            None => Value::Entity {
                functor: none_sym,
                pos: Vec::new().into(),
                named: Vec::new().into(),
            },
        };
        elements.push(Value::Entity {
            functor: ctor,
            pos: Vec::new().into(),
            named: vec![
                (f_functor, functor),
                (f_head, head),
                (f_bodied, Value::Bool(bodied)),
            ]
            .into(),
        });
    }
    interp.build_list_value(elements, &[])
}

/// Read a `List[String]` argument STRICTLY.
///
/// [`crate::kb::typing::value_list_elements`] is deliberately tolerant — a malformed
/// spine reads as the empty list — which is right for a typer walk and wrong here: an
/// empty scoped load that silently succeeded would report a candidate program as clean
/// because nothing was loaded at all. So an empty result is accepted only when the
/// argument really is `nil`, and every element must be a `Str`.
fn expect_string_list(interp: &Interpreter, arg: &Value) -> Result<Vec<String>, EvalError> {
    // Walk the spine HERE rather than through `typing::value_list_elements`, which stops
    // at the first non-`cons` cell and returns the prefix with no signal. That tolerance
    // is right for a typer walk and wrong here: a malformed or partial spine
    // (`["a", "b" | ?rest]`) would load a SUBSET of the requested sources and report the
    // candidate clean on the strength of text that never reached the KB — the exact
    // silent-skip this function's strictness exists to prevent.
    let mut out = Vec::new();
    let mut cell = arg.clone();
    loop {
        match list_cell_kind(interp, &cell) {
            ListCell::Nil => return Ok(out),
            ListCell::Cons => {}
            ListCell::Neither => return Err(type_mismatch("List[String]", arg, None)),
        }
        let head = named_child(interp, &cell, "head")
            .ok_or_else(|| type_mismatch("List[String]", arg, None))?;
        out.push(str_operand(interp.kb(), &head)?.into_owned());
        cell = named_child(interp, &cell, "tail")
            .ok_or_else(|| type_mismatch("List[String]", arg, None))?;
    }
}

/// Which end of a `List` spine `v` is — or neither.
enum ListCell {
    Cons,
    Nil,
    Neither,
}

/// Classify a list cell CARRIER-AGNOSTICALLY, by its head functor.
///
/// Two spellings have to be read here, and missing either one breaks a real case:
///
/// * The CARRIER. A `cons` cell reaches this through `TermView` whatever holds it, so a
///   list read out of the KB (a `Value::Term`, a `Solution` binding, a reified term)
///   walks fine — but matching `Value::Entity` structurally would not have recognised
///   that list's `nil`, and an EMPTY such list would be refused as "not a list".
///   `loaded(sources_from_a_query(...))` returning no rows is exactly that case.
/// * The WI-511 / WI-436 CANON, via [`ViewHead::functor_sym`] rather than a `Functor`
///   match. `nil` is a NULLARY constructor, and `functor_view_head` canonicalizes a
///   0-ary application of a registered constructor to the bare [`ViewHead::Ref`]. So
///   `cons` (two named args) heads as `Functor` while `nil` heads as `Ref`, and a
///   `Functor`-only match sees every list as unterminated. `functor_sym` is the reader
///   that spans both, which is why it exists.
fn list_cell_kind(interp: &Interpreter, v: &Value) -> ListCell {
    use crate::kb::term_view::TermView;
    match v.head(&interp.kb).functor_sym() {
        Some(f) => match interp.kb.qualified_name_of(f) {
            "anthill.prelude.List.cons" => ListCell::Cons,
            "anthill.prelude.List.nil" => ListCell::Nil,
            _ => ListCell::Neither,
        },
        None => ListCell::Neither,
    }
}

/// One named child of a value, through the SAME projection the typer uses
/// ([`crate::kb::typing::named_child_value`]) so the two cannot disagree about what a
/// named child is. `None` when the name was never interned — which, for `head`/`tail`,
/// means no list was ever built in this KB.
fn named_child(interp: &Interpreter, v: &Value, name: &str) -> Option<Value> {
    let key = interp.kb.lookup_symbol(name)?;
    crate::kb::typing::named_child_value(&interp.kb, v, key)
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
    // WI-SPGBP — the KB argument is REAL now, and this is what it buys: the search this
    // builds is RETAINED against the scope it was built in. `execute` returns a
    // `StreamSource::Resolver` that `splitFirst` pumps LATER, so a layer whose last
    // holder went away between the two would be discarded out from under a search still
    // running against it — exactly the bug a bracket form would have had, and the reason
    // the ticket settled on a KB VALUE.
    //
    // WHAT IS PINNED IS THE INNERMOST LIVE LAYER, NOT THE ARGUMENT, and the difference
    // is load-bearing. The search reads the KB AS IT STANDS — every layer applied, not
    // just the one named here — so pinning the argument would leave `execute(kb(), q)`
    // under a live layer holding nothing at all, and `execute(A, q)` with a `B` on top
    // holding only `A` while reading `A + B`. One innermost handle pins the whole stack,
    // because layers unwind innermost-first. See `LayerArenaRef::retain_innermost`.
    //
    // SO WHAT IS THE ARGUMENT FOR, given this reads `_kb_arg`? Not what it was before
    // WI-SPGBP, when it meant nothing anywhere: `kb()` answered a zero-field entity and
    // every `kb`-taking builtin ignored it. It is real now because `loaded(sources)`
    // genuinely APPLIES a layer, and because holding the value it returns is what keeps
    // that layer applied across statements — `execute(loaded(s), q)` works precisely
    // because the value exists and is owned. What the argument is not is the mechanism
    // that keeps THIS stream sound; that has to be the innermost layer, for the reason
    // above. Retaining the argument as well would be redundant, since the innermost
    // handle already pins everything below it.
    let layer = interp.layers.retain_innermost();
    let search = interp
        .kb
        .execute_logical_query(&query)
        .map_err(|e| EvalError::Internal(format!("execute_logical_query: {}", e)))?;
    let handle = interp.alloc_stream(StreamSource::Resolver {
        search: Some(search),
        layer,
    });
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
    let id_key = interp.kb.intern("id");

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
        // WI-1079: the engine's two variable forms, reified with the IDENTITY (`id`, the
        // `VarId`) beside the rendering (`name`). `id` rides as an unboxed `Value::Int` — it
        // is a number, not a term, and the entity declares it `Int64`.
        TypeExtractor::FlexVar { name, id } => {
            let name_val = sym_ref(interp, name);
            ti_entity(
                interp,
                "FlexVar",
                vec![(name_key, name_val), (id_key, Value::Int(i64::from(id)))],
            )
        }
        TypeExtractor::Skolem { name, id } => {
            let name_val = sym_ref(interp, name);
            ti_entity(
                interp,
                "Skolem",
                vec![(name_key, name_val), (id_key, Value::Int(i64::from(id)))],
            )
        }
        TypeExtractor::Nothing => ti_entity(interp, "Nothing", vec![]),
        TypeExtractor::Denoted(v) => ti_entity(interp, "Denoted", vec![(value_key, v)]),
        // WI-376: reify an expression-carried projection — the receiver occurrence
        // (`value`) and the member name as a `Ref(sym)` (`member`).
        TypeExtractor::ExprCarried { value, member } => {
            let member_val = sym_ref(interp, member);
            ti_entity(
                interp,
                "ExprCarried",
                vec![(value_key, value), (member_key, member_val)],
            )
        }
        // WI-428: reify a rigid type-receiver projection — the declaring sort and the
        // member name as `Ref(sym)`s, the subject type term as-is.
        TypeExtractor::RigidTypeProjection {
            sort,
            subject,
            member,
        } => {
            let sort_key = interp.kb.intern("sort");
            let var_key = interp.kb.intern("var");
            let sort_val = sym_ref(interp, sort);
            let member_val = sym_ref(interp, member);
            ti_entity(
                interp,
                "RigidTypeProjection",
                vec![
                    (sort_key, sort_val),
                    (var_key, subject),
                    (member_key, member_val),
                ],
            )
        }
        // WI-791: `arity` reifies alongside the other three. A program that
        // `case`s over an `Arrow` needs it to tell a one-tuple-parameter arrow
        // from an n-parameter one — the same distinction the typer needs — and
        // dropping it here would make `extract` lossy against the stdlib
        // `entity Arrow(param, result, effects, arity)` it is defined to mirror.
        TypeExtractor::Arrow {
            param,
            result,
            effects,
            arity,
        } => {
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
        TypeExtractor::EffectsRows(e) => {
            ti_entity(interp, "EffectsRows", vec![(effects_expr_key, e)])
        }
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
        // WI-1083: `binders` is a `List[Term]` of BARE variable terms — no wrapper
        // record, so it builds through `build_value_list` directly rather than through
        // `ti_build_records` (a binder IS a term, and giving it a one-field record
        // would invent structure the entity does not declare).
        TypeExtractor::PolyType { binders, body } => {
            let binder_list = build_value_list(interp, binders)?;
            let binders_key = interp.kb.intern("binders");
            let body_key = interp.kb.intern("body");
            ti_entity(
                interp,
                "PolyType",
                vec![(binders_key, binder_list), (body_key, body)],
            )
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
    Ok(Value::Entity {
        functor,
        pos: Vec::new().into(),
        named: fields.into(),
    })
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
    Ok(Value::Entity {
        functor,
        pos: Vec::new().into(),
        named: fields.into(),
    })
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
    let mut list = Value::Entity {
        functor: nil_sym,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
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
    let name = str_operand(interp.kb(), &name_arg)?.into_owned();
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    let found: Option<crate::kb::term::TermId> = match interp.kb.get_term(tid) {
        crate::kb::term::Term::Fn { named_args, .. } => {
            let named = named_args.clone();
            named
                .iter()
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
/// Returns `some(s)` when the argument DENOTES a string literal — on any carrier:
/// a hash-consed `Term::Const(String)`, a `Value::Node` occurrence of one, or a
/// native `Value::Str`; otherwise `none()`. Used to extract id/description/agent
/// fields after drilling into a fact via `term_field`.
///
/// WI-20260827-3ZNBC: the carrier list used to be written out by hand and was
/// missing the OCCURRENCE, which is the carrier a rule-body-bound answer rides on
/// (WI-246) — so the one reflect operation whose whole job is "read the string this
/// term denotes" answered `none()` for a term that plainly denoted one. Asking
/// [`TermView::literal_string`] is the same question with no list to keep in step.
fn term_as_string(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("term_as_string", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    let s: Option<String> = {
        use crate::kb::term_view::TermView;
        arg.literal_string(&interp.kb)
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
/// Returns `some(i)` when the argument DENOTES an int literal, on any carrier;
/// otherwise `none()`. The int-literal partner to `term_as_string`, with the
/// identical carrier handling (see there) — used to read a numeric field (e.g. a
/// `StoreFormat` version) after `term_field`.
fn term_as_int(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("term_as_int", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    let i: Option<i64> = {
        use crate::kb::term_view::TermView;
        arg.literal_int64(&interp.kb)
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

    // A `Value::Node` occurrence is admitted alongside `Value::Term` — this doc's
    // own claim ("both representations inhabit the abstract `reflect.Term` via
    // `TermView`") that the carrier match used to contradict, and which
    // `materialize_entity` can now honour because it reads through `TermView`
    // (WI-20260827-2YHZ3). A carrier that is NOT a term handle still refuses
    // LOUDLY rather than falling through to `none()`: `term_as_entity(5)` is a
    // caller mistake, not an absent entity.
    let materialized: Option<Value> = match arg {
        Value::Entity { .. } => Some(arg),
        Value::Term { .. } | Value::Node(_) => materialize_entity(interp, &arg),
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

fn materialize_entity(interp: &mut Interpreter, v: &Value) -> Option<Value> {
    use crate::intern::Symbol;
    use crate::kb::term_view::{TermView, ViewHead};
    // Snapshot functor + children so the `&kb` borrow is released before we
    // recurse back into `&mut interp`. The children are read through `TermView`
    // and snapshotted as owned `Value`s, which is what makes this work on a
    // `Value::Node` occurrence and a hash-consed `Value::Term` alike.
    let (functor, pos_args, named_args): (Symbol, Vec<Value>, Vec<(Symbol, Value)>) = {
        let kb = &interp.kb;
        let ViewHead::Functor {
            functor: Some(functor),
            pos_arity,
            ..
        } = v.head(kb)
        else {
            return None;
        };
        // A positional slot BELOW the arity that does not read back is a view
        // inconsistency, not an absent field: collecting with `filter_map` would
        // slide every later argument down one slot and materialize it into the
        // WRONG declared field below — a silently wrong entity rather than an
        // error (found by /code-review).
        let mut pos: Vec<Value> = Vec::with_capacity(pos_arity);
        for i in 0..pos_arity {
            pos.push(v.pos_arg(kb, i)?.to_value());
        }
        let named: Vec<(Symbol, Value)> = v
            .named_keys(kb)
            .into_iter()
            .filter_map(|k| v.named_arg(kb, k).map(|c| (k, c.to_value())))
            .collect();
        (functor, pos, named)
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
        interp
            .kb
            .symbols
            .by_qualified_name
            .iter()
            .find(|(qname, &sym)| {
                qname.rsplit('.').next() == Some(short_name.as_str())
                    && interp.kb.entity_field_types(sym).is_some()
            })
            .map(|(_, &sym)| sym)?
    };
    // WI-342: field types are carrier-agnostic `Value`. Eval only inspects them
    // to default optional fields (see `is_option_type` below); a denoted-bearing
    // (Value::Node) field type is never an `Option`.
    let field_types: Vec<(Symbol, Value)> = interp.kb.entity_field_types(canonical)?.to_vec();
    // Default missing `Option[T = …]` fields to `none()` — on-disk facts
    // omit optional named args (a `WorkItem` fact skips
    // `context`/`generates`/`requires_capability`) but the field index
    // still expects them. Required for callers to pattern-match a
    // complete entity.
    let none_sym = interp
        .kb
        .try_resolve_symbol("anthill.prelude.Option.none")?;

    let mut named: Vec<(Symbol, Value)> = Vec::with_capacity(field_types.len());
    for (idx, (fname, ftype)) in field_types.iter().enumerate() {
        let field_val: Option<Value> = named_args
            .iter()
            .find(|(s, _)| *s == *fname)
            .map(|(_, val)| val.clone())
            .or_else(|| pos_args.get(idx).cloned());
        // WI-477: read the field type's head carrier-agnostically — `Value::Term` or
        // `Value::Node` (an occurrence-primary type) alike — via the shared TermView
        // predicate, instead of narrowing to a `TermId` first (which dropped a Node).
        let is_opt = crate::kb::typing::is_option_type(&interp.kb, ftype);
        match field_val {
            // The loader's partial-named-arg expansion (kb/load.rs:2752)
            // fills absent slots with a fresh Var so the discrim tree
            // can index the fact uniformly. For materialization those
            // Var-valued Option slots are semantically absent — promote
            // them to none() so reconstruction + re-persistence doesn't
            // bake the synthetic var name into the persisted fact.
            // Var-ness read through `TermView`, so an occurrence-carried slot
            // answers the same question as a term-carried one.
            Some(ref fv) if is_opt && matches!(fv.head(&interp.kb), ViewHead::Var(_)) => {
                named.push((
                    *fname,
                    Value::Entity {
                        functor: none_sym,
                        pos: Vec::new().into(),
                        named: Vec::new().into(),
                    },
                ));
            }
            Some(ref fv) => {
                let converted = value_to_native(interp, fv);
                named.push((*fname, converted));
            }
            None if is_opt => {
                named.push((
                    *fname,
                    Value::Entity {
                        functor: none_sym,
                        pos: Vec::new().into(),
                        named: Vec::new().into(),
                    },
                ));
            }
            None => return None,
        }
    }

    Some(Value::Entity {
        functor: canonical,
        pos: Vec::new().into(),
        named: named.into(),
    })
}

/// Materialize a KB HANDLE into the interpreter's native value.
///
/// **NOT A BOUNDARY, and two earlier drafts of this family wrongly made it one.**
/// WI-20260827-2YHZ3 normalized every relation column through here, and the SLD→eval
/// bridge normalized every operand, both on the premise that the interpreter's value
/// operations are native-only "and are not meant to be" carrier-neutral. That premise
/// was false in both halves: reflect `Term` values already flow through anthill code
/// as `Value::Term`, and the operations that refused a handle — `Int64.add`,
/// `field_access` — were simply MISSING AN ARM. They read their operands through
/// `TermView` now ([`TermView::literal_int64`] and its siblings,
/// `reflect_field_access`), so WI-20260827-3ZNBC removed both normalizations and this
/// function is on neither path.
///
/// THE ONE CALLER LEFT is [`materialize_entity`], converting a decoded entity's
/// FIELDS — and it is here because that function's product is a `Value::Entity`,
/// i.e. a value whose whole point is to be pattern-matched natively by the anthill
/// `case` that asked for it. `term_as_entity` is the reflect operation whose job IS
/// Term → Entity; handing back an entity whose fields were still handles would make
/// the decode half-done, and would reintroduce exactly the incoherence
/// WI-20260827-3ZNBC set out to remove — a field read answering native or handle
/// depending on how the receiver arrived.
///
/// Every question it asks — is this a literal, a constructor application, a bare
/// constructor, a variable — goes through [`TermView::head`], so it answers the same
/// for a `Value::Term` and a `Value::Node`. That is what let `term_as_entity` stop
/// refusing an occurrence while its own doc claimed to accept one.
///
/// An ALREADY-NATIVE value is returned untouched — not an optimization: an
/// external extent row binds a `Value::Entity` the resolver never built from a
/// term, and re-materializing it would re-run the Option-field defaulting over an
/// entity that is already complete.
fn value_to_native(interp: &mut Interpreter, v: &Value) -> Value {
    match v {
        Value::Term { .. } | Value::Node(_) => handle_to_native(interp, v),
        already_native => already_native.clone(),
    }
}

fn handle_to_native(interp: &mut Interpreter, v: &Value) -> Value {
    use crate::intern::Symbol;
    use crate::kb::term::Literal;
    use crate::kb::term_view::{TermView, ViewHead};
    // Decide from the HEAD alone, then drop the `&kb` borrow before recursing
    // back through `&mut interp` — the same shape the `TermId` version used, for
    // the same reason.
    enum Decision {
        Literal(Literal),
        TryFn(Symbol),
        TryRef(Symbol),
        // WI-109: a logic variable lifts to the kind-typed `Value::Var`,
        // not the raw carrier — lossless and structurally reconstructible.
        Var(crate::kb::term::Var),
        AsIs,
    }
    let decision = match v.head(&interp.kb) {
        ViewHead::Const(lit) => Decision::Literal(lit),
        ViewHead::Functor {
            functor: Some(f), ..
        } => Decision::TryFn(f),
        ViewHead::Ref(sym) => Decision::TryRef(sym),
        ViewHead::Var(var) => Decision::Var(var),
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
                materialize_entity(interp, v).unwrap_or_else(|| v.clone())
            } else {
                v.clone()
            }
        }
        Decision::TryRef(sym) => {
            if interp.kb.sort_of_constructor(sym).is_some() {
                Value::Entity {
                    functor: sym,
                    pos: Vec::new().into(),
                    named: Vec::new().into(),
                }
            } else {
                v.clone()
            }
        }
        Decision::Var(var) => Value::Var(var),
        Decision::AsIs => v.clone(),
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
    let name = str_operand(interp.kb(), &name_arg)?.into_owned();
    let sym = interp.kb.intern(&name);
    let vid = interp.kb.fresh_var(sym);
    let tid = interp
        .kb
        .alloc(crate::kb::term::Term::Var(crate::kb::term::Var::Global(
            vid,
        )));
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
            Value::Entity {
                functor,
                pos,
                named,
                ..
            } => {
                if Some(functor) == nil_sym {
                    break;
                }
                if Some(functor) != cons_sym {
                    let n = interp.kb.local_name_of(functor);
                    return Err(EvalError::Internal(format!(
                        "{ctx}: expected cons/nil, got {n}"
                    )));
                }
                let (head, tail) = if !named.is_empty() {
                    let h = named
                        .iter()
                        .find(|(s, _)| interp.kb.local_name_of(*s) == "head")
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| {
                            EvalError::Internal(format!("{ctx}: cons missing head field"))
                        })?;
                    let t = named
                        .iter()
                        .find(|(s, _)| interp.kb.local_name_of(*s) == "tail")
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| {
                            EvalError::Internal(format!("{ctx}: cons missing tail field"))
                        })?;
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
/// is resolved through [`resolve_host_name`]. Companion to `fresh_var`: anthill
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
    let name = str_operand(interp.kb(), &name_arg)?.into_owned();
    let functor = resolve_host_name(interp, "make_fn", &name)?;

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
    let name = str_operand(interp.kb(), &name_arg)?.into_owned();
    let functor = resolve_host_name(interp, "make_apply", &name)?;

    // Reuse each argument occurrence in place (identity + span preserved). A
    // non-occurrence element is a LOUD error, never a silently-dropped node.
    let pos_args: Vec<Rc<NodeOccurrence>> = reflect_cons_to_vec(
        interp,
        args_arg,
        "make_apply",
        "List[NodeOccurrence]",
        |v| match v {
            Value::Node(occ) => Ok(occ),
            other => Err(type_mismatch("NodeOccurrence", &other, None)),
        },
    )?;

    let from = match &from_arg {
        Value::Node(occ) => Rc::clone(occ),
        other => return Err(type_mismatch("NodeOccurrence", other, None)),
    };
    let pass = crate::kb::occurrence::macro_expand_pass(&mut interp.kb);
    let owner = from.owner;
    let expr = Expr::Apply {
        recv_type: None,
        functor,
        pos_args,
        named_args: Vec::new(),
        type_args: Vec::new(),
    };
    Ok(Value::Node(NodeOccurrence::synthesized_expr(
        expr, from, pass, owner,
    )))
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

/// WI-1129 (proposal 056 §2.3) — `anthill.reflect.sub_occurrence_labels(occ:
/// NodeOccurrence) -> List[String]`.
///
/// The COMPONENT NAMES of the occurrence's direct children, in the same order and
/// of the same length as [`reflect_sub_occurrences`] — the two are read as a pair.
/// A child with no label of its own reads as its `_1`-based positional label (§4.5),
/// so the pairing is total.
///
/// This is the reader 056 §2.3 names alongside `sub_occurrences`, and it is what
/// makes the rule-head capture usable: the captured labels are the CALLER's names
/// (`r.rename(who: r.name)` — a column name no macro can know in advance), so a
/// macro must enumerate them, which neither `sub_occurrences` (children, no names)
/// nor `term_field` (one name you must already have) can do. Reading the labels off
/// `occurrence_term`'s Fn twin is not an alternative for the same reason, and it
/// additionally goes `Bottom` the moment one component is a child-bearing form.
///
/// Only an `Expr`-kind occurrence has children; a `Pattern` / `Type` / `EffectExpr`
/// one yields the empty list, as `sub_occurrences` does.
fn reflect_sub_occurrence_labels(
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    use crate::kb::node_occurrence;
    let [occ_arg] = expect_args::<1>("sub_occurrence_labels", args)?;
    let occ = match &occ_arg {
        Value::Node(o) => std::rc::Rc::clone(o),
        other => return Err(type_mismatch("NodeOccurrence", other, None)),
    };
    let labels: Vec<Value> = match occ.as_expr() {
        Some(expr) => {
            let mut count = 0usize;
            node_occurrence::for_each_child(expr, |_| count += 1);
            let labels = node_occurrence::child_labels(&interp.kb, expr, count);
            debug_assert_eq!(
                labels.len(),
                count,
                "WI-1129: `child_labels` must stay parallel to `for_each_child`",
            );
            labels.into_iter().map(Value::Str).collect()
        }
        None => Vec::new(),
    };
    build_value_list(interp, labels)
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
    let name = str_operand(interp.kb(), &name_arg)?.into_owned();
    let new_val_tid = interp
        .kb
        .alloc_from_value(&value_arg)
        .map_err(|e| EvalError::Internal(format!("replace_named_arg: lower value: {e:?}")))?;

    let (functor, pos_args, mut named_args) = match interp.kb.get_term(tid) {
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => (*functor, pos_args.clone(), named_args.clone()),
        _ => {
            return Err(EvalError::Internal(format!(
                "replace_named_arg: expected Fn term, got {:?}",
                interp.kb.get_term(tid)
            )))
        }
    };
    for entry in named_args.iter_mut() {
        if interp.kb.local_name_of(entry.0) == name {
            entry.1 = new_val_tid;
        }
    }
    let new_term = interp.kb.alloc(Term::Fn {
        functor,
        pos_args,
        named_args,
    });
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
fn int_to_string(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [arg] = expect_args::<1>("Int64.to_string", args)?;
    Ok(Value::Str(int_operand(interp.kb(), &arg)?.to_string()))
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
    let elements: Vec<Value> = rule_ids
        .into_iter()
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
fn stored_ref_value(
    interp: &mut Interpreter,
    row: crate::kb::extent::StoredRow,
) -> Result<Value, EvalError> {
    let stored_ref = require_symbol(interp, "anthill.reflect.StoredRef.stored_ref", "stored_ref")?;
    Ok(Value::Entity {
        functor: stored_ref,
        pos: Vec::new().into(),
        named: vec![
            (interp.fields.value, row.row),
            (interp.fields.reference, Value::FactRef(row.reference)),
        ]
        .into(),
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
    let name = str_operand(interp.kb(), &name_val)?.into_owned();

    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");

    // WI-20260827-2YHZ3 — two steps, and the split is the fix. The scan finds the
    // VarId; `answer_binding` then reads it, because a raw `val.clone()` here
    // truncated exactly as `print_solutions` did: a var bound by a rule-body
    // BUILTIN sits behind an uncompressed link, so anthill code asking for a field
    // binding got back `some(<an unbound var>)` — a `some` that looks like an
    // answer. `subst_arena()` exists for this shape (its doc: borrow a
    // substitution through the arena "while also mutably borrowing `kb`").
    //
    // KNOWN, PRE-EXISTING, AND NOT WIDENED HERE: the NAME scan is `s.iter()`,
    // which is this level's bindings only, while `answer_binding`'s read walks the
    // parent chain. So a name held only in a parent frame is still not FOUND —
    // a separate gap from the one this ticket closes, in a by-name lookup whose
    // doc above already records that it resolves loosely (first match, hash order).
    // Making the scan walk parents would change which binding a live consumer
    // (anthill-todo's `pattern_query`) finds, and that wants its own measurement.
    let arena = interp.subst_arena();
    let found: Option<crate::kb::term::VarId> = arena.with_subst(&handle, |s| {
        s.iter()
            .find(|(vid, _)| interp.kb.local_name_of(vid.name()) == name)
            .map(|(vid, _)| *vid)
    });
    let bound: Option<Value> =
        found.and_then(|vid| arena.with_subst(&handle, |s| interp.kb_mut().answer_binding(vid, s)));

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
    let i = int_operand(interp.kb(), &idx)?;
    let dict = expect_dictionary(interp, &d)?;
    let sub = usize::try_from(i)
        .ok()
        .and_then(|k| dict.sub(k))
        .ok_or_else(|| {
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
    Ok(Value::OpRef {
        // WI-1087: not an ETA site — `Dictionary.resolveOp` mints this from a
        // dictionary, with no `Function[A]` slot to read a parameter-list mapping off.
        spread_labels: None,
        op: target,
        dict: Some(Rc::new(h)),
        named: Some(spec_op_sym),
        // WI-1091: and no call site either, so nothing here could have BUILT an
        // op-scoped slot. A resolved member whose own `requires` clause the body reads
        // therefore enters unsupplied and raises at the read, naming the frame — the
        // same answer this route gave before the channel existed.
        op_reqs: None,
    })
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
                    // WI-1087 / WI-1091: not an eta site — see the sibling mint above
                    // for both halves.
                    spread_labels: None,
                    op: resolved,
                    dict: Some(h.clone()),
                    // The table row IS the op named here, pre-resolution.
                    named: Some(target),
                    op_reqs: None,
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

/// `OpRef.spreadLabels(r) -> Option[List[Symbol]]` — the eta-site parameter mapping
/// (`A`'s component labels in declared order); none() at every non-eta mint.
///
/// WI-1088 declared it for the reason WI-1019 declared `named`: it is part of the
/// value's identity ([`crate::kb::term_view`]'s `opref_shape`), and the accessor set
/// claimed to expose everything the value holds while omitting it.
///
/// The STRUCTURAL VIEW spells the same field as a positional TUPLE of symbols and this
/// accessor as a `List` — two renderings of one field, not two representations of the
/// mapping. Neither is derived from the other and they never meet: the view is internal
/// machinery (equality, `goal_fingerprint`, discrim keys), where a `cons` chain would be
/// an allocation per child read on the hot path; the `List` is the anthill surface, where
/// a tuple of statically-unknown width is not a type that can be declared.
fn opref_spread_labels(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r] = expect_args::<1>("OpRef.spreadLabels", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");
    match r {
        Value::OpRef { spread_labels, .. } => match spread_labels {
            Some(labels) => {
                let elems: Vec<Value> = labels.iter().copied().map(symbol_value).collect();
                let list = build_value_list(interp, elems)?;
                Ok(option_some(some_sym, value_key, list))
            }
            None => Ok(option_none(none_sym)),
        },
        other => Err(type_mismatch("OpRef", &other, None)),
    }
}

/// `OpRef.opRequirements(r) -> Option[List[Option[Dictionary]]]` — the OPERATION's own
/// `requires` slots captured at the eta site, in chain order; none() for an op that
/// writes no `requires` of its own, and a none() ELEMENT for a slot the eta site could
/// not project.
///
/// WI-1091 declared it for the reason WI-1019 declared `named` and WI-1088
/// `spreadLabels`: it is part of the value's identity ([`crate::kb::term_view`]'s
/// `opref_shape`), and the accessor set claims to expose everything the value holds. It
/// is the sharpest case of the three — for an eta of an operation whose SORT requires
/// nothing, `dict` is none() on every reference, so this is the only field that can tell
/// two of them apart.
///
/// Two renderings of one field, as with `spreadLabels`: the structural view spells it as
/// a positional TUPLE (order is which requirement each slot answers, and a `cons` chain
/// per child read would be an allocation on the equality / `goal_fingerprint` / discrim
/// path), this accessor as a `List` (the anthill surface, where a tuple of
/// statically-unknown width is not a declarable type).
fn opref_op_requirements(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [r] = expect_args::<1>("OpRef.opRequirements", args)?;
    let some_sym = require_symbol(interp, "anthill.prelude.Option.some", "some")?;
    let none_sym = require_symbol(interp, "anthill.prelude.Option.none", "none")?;
    let value_key = interp.kb.intern("value");
    match r {
        Value::OpRef { op_reqs, .. } => match op_reqs {
            Some(slots) => {
                let elems: Vec<Value> = slots
                    .iter()
                    .map(|slot| match slot {
                        Some(d) => option_some(some_sym, value_key, d.as_value().clone()),
                        None => option_none(none_sym),
                    })
                    .collect();
                let list = build_value_list(interp, elems)?;
                Ok(option_some(some_sym, value_key, list))
            }
            None => Ok(option_none(none_sym)),
        },
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
fn option_some(
    some_sym: crate::intern::Symbol,
    value_key: crate::intern::Symbol,
    v: Value,
) -> Value {
    Value::Entity {
        functor: some_sym,
        pos: Vec::new().into(),
        named: vec![(value_key, v)].into(),
    }
}
fn option_none(none_sym: crate::intern::Symbol) -> Value {
    Value::Entity {
        functor: none_sym,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    }
}

/// The `MapKey` a builtin's key argument addresses, or the loud type error.
///
/// One owner for the four `Map` builtins, which all ask the same question and
/// used to spell it two different ways (one `ok_or_else`, three four-line
/// `match`es). WI-1016 had to thread a `&KnowledgeBase` through every one of
/// them — the reader canonicalizes the two carriers of a symbol — which is
/// the second time this sequence was edited in lockstep.
///
/// WI-20260827-3ZNBC took the `&mut`, so a structural OCCURRENCE key can be interned
/// to the term it denotes and address the SAME slot its `Value::Term` twin does. See
/// [`MapKey::of_value_interning`](super::map_arena::MapKey::of_value_interning) for
/// why that is not a store write on any path that used to work.
fn map_key(
    kb: &mut crate::kb::KnowledgeBase,
    v: &Value,
) -> Result<super::map_arena::MapKey, EvalError> {
    super::map_arena::MapKey::of_value_interning(kb, v).ok_or_else(|| EvalError::TypeMismatch {
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
    let key = map_key(&mut interp.kb, &k_arg)?;
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
    let key = map_key(&mut interp.kb, &k_arg)?;
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
    let key = map_key(&mut interp.kb, &k_arg)?;
    let present = interp.maps.with_body(&handle, |b| b.contains_key(&key));
    Ok(Value::Bool(present))
}

fn map_remove(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg, k_arg] = expect_args::<2>("Map.remove", args)?;
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let key = map_key(&mut interp.kb, &k_arg)?;
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
    let elements: Vec<Value> = interp
        .maps
        .with_body(&handle, |b| b.keys().map(|k| k.to_value()).collect());
    interp.build_list_value(elements, &[])
}

fn map_values(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [m_arg] = expect_args::<1>("Map.values", args)?;
    let handle = match m_arg {
        Value::Map(h) => h,
        other => return Err(type_mismatch("Map", &other, None)),
    };
    let elements: Vec<Value> = interp
        .maps
        .with_body(&handle, |b| b.values().cloned().collect());
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
        b.iter()
            .map(|(k, v)| Value::Entity {
                functor: pair_sym,
                pos: Vec::new().into(),
                named: vec![(fst_key, k.to_value()), (snd_key, v.clone())].into(),
            })
            .collect()
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

/// WI-913 — THE HOST-NAME READ for an eval builtin: what functor a name that
/// arrives as a runtime `String` denotes. Same question WI-908 gave one answer
/// ([`KnowledgeBase::resolve_name_in_global`](crate::kb::KnowledgeBase::resolve_name_in_global)),
/// so the same ladder — not `try_resolve_symbol`, whose absolute `by_qualified_name`
/// lookup consults no scope and could not see the implicit tier a program writes
/// bare (`cons`, `nil`, `some`, `SortInfo`, …).
///
/// An UNMARKED dotted path is the RELATIVE reading (WI-1075) — head segment resolved
/// in scope, tail appended — so `..a.b.c` is how a host says it means the ROOT, exactly
/// as source does. That is what re-spells the names whose only reading was the absolute
/// one: the loader's `define_qualified_only` kernel names (`Sort`, `Fact`, `Member`,
/// `meta`, …) answer to `..Member`, not to `Member`. Not a casualty — they are
/// delocalized precisely so that user name resolution cannot surface them (WI-422 /
/// WI-423), and a name a PROGRAM hands to `make_fn` IS user name resolution, while
/// `..` is the spelling that says it is not. Driven by `wi913_host_name_ladder_test::
/// a_qualified_only_kernel_name_is_reachable_only_by_the_root_spelling`.
///
/// An AMBIGUITY is its own answer, never folded into "unknown" (kernel-language.md
/// §8.6, WI-907): the name denotes several symbols here, and reporting it as
/// unknown sends the author looking for a declaration that already exists.
///
/// Not to be confused with [`require_symbol`] below, which resolves a BUILTIN'S OWN
/// registration target — a Rust-side constant, always absolute, never host text.
pub fn resolve_host_name(
    interp: &mut Interpreter,
    ctx: &str,
    name: &str,
) -> Result<crate::intern::Symbol, EvalError> {
    match interp.kb.resolve_name_in_global(name) {
        crate::intern::ResolveResult::Found(sym) => Ok(sym),
        crate::intern::ResolveResult::Ambiguous(cands) => {
            let names: Vec<&str> = cands
                .iter()
                .map(|&s| interp.kb.qualified_name_of(s))
                .collect();
            Err(EvalError::Internal(format!(
                "{ctx}: `{name}` is ambiguous at <global> — {}",
                names.join(", ")
            )))
        }
        crate::intern::ResolveResult::NotFound => Err(EvalError::Internal(format!(
            "{ctx}: unknown symbol `{name}` — a bare name must be in the implicit \
             tier or in scope at <global>, a qualified one spelled in full"
        ))),
    }
}

/// Resolve a builtin's target symbol. Tries the fully-qualified name first,
/// then falls back to the short name. Exposed so downstream crates that
/// register their own builtins (e.g. `anthill-stl`) error consistently.
pub fn require_symbol(
    interp: &Interpreter,
    qualified: &str,
    short: &str,
) -> Result<crate::intern::Symbol, EvalError> {
    interp
        .kb
        .try_resolve_symbol(qualified)
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

effect_dispatcher!(
    console_print,
    "anthill.prelude.Console.print",
    "print",
    "anthill.prelude.Console.ConsoleOutput"
);
effect_dispatcher!(
    console_println,
    "anthill.prelude.Console.println",
    "println",
    "anthill.prelude.Console.ConsoleOutput"
);
effect_dispatcher!(
    console_eprint,
    "anthill.prelude.Console.eprint",
    "eprint",
    "anthill.prelude.Console.ConsoleError"
);
effect_dispatcher!(
    console_eprintln,
    "anthill.prelude.Console.eprintln",
    "eprintln",
    "anthill.prelude.Console.ConsoleError"
);
effect_dispatcher!(
    console_read_line,
    "anthill.prelude.Console.read_line",
    "read_line",
    "anthill.prelude.Console.ConsoleInput"
);
effect_dispatcher!(
    modify_get,
    "anthill.prelude.ModifyRuntime.get",
    "get",
    "anthill.prelude.Modify"
);
effect_dispatcher!(
    modify_set,
    "anthill.prelude.ModifyRuntime.set",
    "set",
    "anthill.prelude.Modify"
);

// `Error.raise` deliberately does NOT use the generic dispatcher. An unhandled
// Console/Modify effect is a missing-capability `Internal` fault, but an
// unhandled `Error` DEFAULTS to Throw — [`Interpreter::raise_error`]'s
// no-handler arm is `Raised { payload }` (WI-467: the payload is never lost),
// the same channel a native builtin's declared `effects Error` takes. The
// generic dispatcher's no-handler `Internal` became reachable from surface
// code the moment `Stream.head`'s default body raised (WI-818).
fn error_raise(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [payload] = args else {
        return Err(EvalError::ArityMismatch {
            op: "Error.raise",
            expected: 1,
            got: args.len(),
        });
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
    let resolve =
        |kb: &crate::kb::KnowledgeBase, name: &str| -> Result<crate::intern::Symbol, EvalError> {
            kb.try_resolve_symbol(name).ok_or_else(|| {
                EvalError::Internal(format!(
                    "fact_monotonicity guard: `{name}` unresolved — the anthill.reflect \
             substrate (proposal 053) must be loaded"
                ))
            })
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
    let (result, _changes) = kb.apply_eq_rules(
        &Value::term(call),
        100,
        &crate::kb::subst::Substitution::new(),
    );

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
        Ok(self
            .kb
            .mirror_monotonicity(functor)
            .unwrap_or(Monotonicity::Monotone))
    }
}

// ── Persistence builtins (proposal 007 §4) ─────────────────────

/// `anthill.persistence.Store.persist(store, fact, meta) -> StoredRef[Term]`.
/// `meta` is accepted but not yet consumed — pass `none()`.
fn persistence_persist(interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    let [store_val, fact_val, _meta_val] = expect_args::<3>("persist", args)?;
    let key = interp.store_canonical_key(&store_val)?;

    let fact_term = interp
        .kb
        .alloc_from_value(&fact_val)
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
             (proposal 053)"
                .into(),
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
    let row = interp
        .kb
        .persist_mirrored(&key, Value::term(fact_term), None)
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

    let head_sym = crate::kb::term_view::TermView::head(&functor_val, &interp.kb).functor_sym();
    let functor = match head_sym {
        Some(sym) => sym,
        // A functor passed as its raw name string — HOST text, so the WI-908
        // ladder (WI-913), not the absolute `by_qualified_name` lookup this used.
        //
        // An unresolvable name is now a NAME error and no longer falls through to
        // the carrier error below: `TypeMismatch { expected: "Symbol (functor)",
        // got: "String" }` was the single exit for both, so a misspelled functor
        // was reported as a wrong-KIND value when the value was exactly right.
        // On ANY carrier (WI-20260827-3ZNBC): a name is a string whether it rides
        // native, hash-consed, or as an occurrence, and `head().functor_sym()` above
        // already answered carrier-neutrally for the non-string spelling.
        None => match str_operand(interp.kb(), &functor_val) {
            Ok(name) => {
                let name = name.into_owned();
                resolve_host_name(interp, "monotonicity", &name)?
            }
            Err(_) => {
                return Err(EvalError::TypeMismatch {
                    expected: "Symbol (functor)",
                    got: functor_val.type_name().to_string(),
                })
            }
        },
    };

    let mono = interp.resolve_fact_monotonicity(functor)?;
    // `variant` is a Rust-side constant qualified name, not host text — the
    // absolute lookup is the right question here and stays (WI-913).
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
        other => {
            return Err(EvalError::TypeMismatch {
                expected: "FactRef",
                got: other.type_name().to_string(),
            })
        }
    };

    // An external owner receives its native key through the KB seam. For a
    // mirrored resident row, the reference also carries the mirror it came
    // from; accepting a different `store` argument would silently route a
    // mutation to the wrong durable extent.
    let Some(rule_id) = reference.resident_rule() else {
        let outcome = interp
            .kb
            .retract_persistent(&reference)
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
             (proposal 053)"
                .into(),
        ));
    };
    if interp.resolve_fact_monotonicity(functor)? != Monotonicity::NonMonotone {
        let name = interp.kb.qualified_name_of(functor).to_string();
        return Err(interp.raise_error(Value::Str(format!(
            "retract refused: functor `{name}` is not non_monotone (proposal 053)"
        ))));
    }

    let outcome = interp
        .kb
        .retract_persistent(&reference)
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
        other => {
            return Err(EvalError::TypeMismatch {
                expected: "FactRef",
                got: other.type_name().to_string(),
            })
        }
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
        let Some(functor) = crate::kb::term_view::TermView::head(&old, &interp.kb).functor_sym()
        else {
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
        Some(row) => option_some(
            some_sym,
            interp.fields.value,
            stored_ref_value(interp, row)?,
        ),
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

    let pattern_term = interp
        .kb
        .alloc_from_value(&pattern_val)
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
    let source = StreamSource::Native(Box::new(move || iter.next().map(Value::term)));
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
        let kb = crate::kb::KnowledgeBase::new();
        for (key, _, _) in HOST_FNS {
            let host = host_fn_by_key(&kb, key).unwrap_or_else(|| panic!("{key} is registered"));
            let args = vec![Value::Float(1.0); host.arity];
            if let Err(EvalError::ArityMismatch { expected, got, .. }) =
                host.call(&mut dummy(), &args)
            {
                panic!(
                    "host_fn_by_key says {key} takes {}, but the function wants {expected} \
                     (it was given {got})",
                    host.arity
                );
            }
        }
        assert!(
            host_fn_by_key(&kb, "no_such_host_function").is_none(),
            "the control: the registry is CLOSED, so an unknown key has no entry",
        );
    }

    /// WI-1122 — THE `Dynamic` HALF, which the audit above cannot reach. That test
    /// iterates `HOST_FNS`, and `host_fn_by_key`'s HOST_FNS leg only ever mints
    /// `HostFnImpl::Static`, so the `Dynamic` arm an EMBEDDER entry takes is never
    /// exercised by it. Nor is it exercised end-to-end anywhere else: production does
    /// not go through `HostFn::call` at all — it goes through `register_on` into the
    /// interpreter's builtin map — and `wi1122_embedder_host_fn_test` is an INTEGRATION
    /// test, linking the lib compiled without `cfg(test)`.
    ///
    /// So the two paths must agree, and nothing checked that they did. This drives
    /// BOTH with one `Dynamic` entry that records what it received.
    ///
    /// CONTROL: `register_on`'s Dynamic wrapper (kb/host_fns.rs) is the only thing
    /// between the two halves. Drop, duplicate or reorder `a` in that wrapper and the
    /// `register_on` half fails while the `call` half still passes — which is the
    /// asymmetry that makes this test worth having rather than a restatement.
    #[test]
    fn a_dynamic_host_fn_forwards_operands_identically_through_both_paths() {
        use std::cell::RefCell;
        use std::rc::Rc;

        let seen: Rc<RefCell<Vec<Vec<Value>>>> = Rc::new(RefCell::new(Vec::new()));
        let recorder = Rc::clone(&seen);
        let hf = HostFn {
            arity: 2,
            f: HostFnImpl::Dynamic(std::sync::Arc::new(
                move |_i: &mut Interpreter, a: &[Value]| {
                    recorder.borrow_mut().push(a.to_vec());
                    Ok(Value::Int(a.len() as i64))
                },
            )),
        };

        let args = vec![Value::Int(7), Value::Int(9)];

        let mut kb = crate::kb::KnowledgeBase::new();
        let sym = kb.intern("probe.dynamic.forwarding");
        let mut interp = Interpreter::new(kb);

        // Path 1 — what the arity audit uses.
        let direct = hf
            .call(&mut interp, &args)
            .expect("a Dynamic entry must be invocable through `call`");

        // Path 2 — what production uses.
        hf.register_on(&mut interp, sym);
        let registered = interp
            .builtins
            .get(&sym)
            .cloned()
            .expect("register_on must bind the entry under its symbol");
        let through_map =
            registered(&mut interp, &args).expect("the registered closure must be invocable");

        assert_eq!(
            direct.as_int(),
            through_map.as_int(),
            "both paths must return the same value"
        );
        let calls = seen.borrow();
        assert_eq!(calls.len(), 2, "the closure must have run once per path");
        // Compared through `as_int` rather than `==`: WI-486 removed the carrier-blind
        // `Value` comparator deliberately, so `Value` has no `PartialEq` to lean on.
        let ints = |vs: &[Value]| vs.iter().map(|v| v.as_int()).collect::<Vec<_>>();
        assert_eq!(
            ints(&calls[0]),
            ints(&args),
            "`call` must forward the operands unchanged and in order"
        );
        assert_eq!(
            ints(&calls[0]),
            ints(&calls[1]),
            "`register_on`'s wrapper must forward exactly what `call` does"
        );
    }

    #[test]
    fn numeric_add_int() {
        let r = numeric_add("Int64.add", &Value::Int(2), &Value::Int(3)).unwrap();
        assert_eq!(r.as_int(), Some(5));
    }

    #[test]
    fn numeric_add_float() {
        let r = numeric_add("Float.add", &Value::Float(1.5), &Value::Float(2.25)).unwrap();
        assert!(matches!(r, Value::Float(v) if (v - 3.75).abs() < 1e-9));
    }

    /// WI-880 — AND THE OVERFLOW NAMES THE CARRIER'S OPERATION, driven through the
    /// wrapper rather than through the shared function, because the wrapper is what
    /// supplies the label and the label is the subject.
    ///
    /// Found by /code-review: the wrappers delegated with no label, so an `Int64`
    /// overflow reported `op: "Numeric.add"` — a spec operation this ticket stopped
    /// implementing — in exactly the diagnostic the per-carrier split exists to sharpen.
    /// The integration arm is
    /// `wi880_arithmetic_mapping_test::the_three_carriers_disagree_at_the_boundary`,
    /// which asserts the same name from the language side; this one is the unit-level
    /// twin and is what fails first if the label is dropped again.
    #[test]
    fn numeric_add_overflow_is_error_and_names_the_carriers_operation() {
        let err = int_add(&mut dummy(), &[Value::Int(i64::MAX), Value::Int(1)]).unwrap_err();
        assert!(
            matches!(err, EvalError::Overflow { op: "Int64.add" }),
            "an Int64 overflow names Int64's own operation; got {err:?}"
        );
    }

    #[test]
    fn numeric_add_mixed_type_shows_both_in_message() {
        let err = numeric_add("Int64.add", &Value::Int(1), &Value::Float(2.0)).unwrap_err();
        match err {
            EvalError::TypeMismatch { got, .. } => {
                assert!(
                    got.contains("Int64") && got.contains("Float"),
                    "got = {got}"
                );
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
        let a = Value::Tuple {
            pos: vec![Value::Int(1)].into(),
            named: Vec::new().into(),
        };
        let b = Value::Tuple {
            pos: vec![Value::Int(1)].into(),
            named: Vec::new().into(),
        };
        let r = builtin_eq(&mut dummy(), &[a, b]).unwrap();
        assert_eq!(r.as_bool(), Some(true));
    }

    #[test]
    fn eq_on_different_tuples_is_false() {
        let a = Value::Tuple {
            pos: vec![Value::Int(1)].into(),
            named: Vec::new().into(),
        };
        let b = Value::Tuple {
            pos: vec![Value::Int(2)].into(),
            named: Vec::new().into(),
        };
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
        let r = string_concat(
            &mut dummy(),
            &[Value::Str("hi ".into()), Value::Str("there".into())],
        )
        .unwrap();
        assert_eq!(r.as_str(), Some("hi there"));
    }

    /// WI-880 moved the subject from `numeric_add` to `int_add`: the shared arithmetic
    /// takes its operands directly now (the label has to come from the caller), so the
    /// per-carrier WRAPPER is the thing that counts arguments.
    #[test]
    fn arity_mismatch_carries_counts() {
        let err = int_add(&mut dummy(), &[Value::Int(1)]).unwrap_err();
        assert!(matches!(
            err,
            EvalError::ArityMismatch {
                expected: 2,
                got: 1,
                ..
            }
        ));
    }

    // ── WI-1121: slug / digestBase32 ────────────────────────────

    #[test]
    fn slug_keeps_only_lowercase_alnum_and_single_separators() {
        assert_eq!(slug("Item-per-file store", 30), "item-per-file-store");
        assert_eq!(slug("  leading & trailing  ", 30), "leading-trailing");
        assert_eq!(slug("A//B__C", 30), "a-b-c");
        assert_eq!(slug("WI-437: the backend!", 30), "wi-437-the-backend");
    }

    /// The empty answer is the property a caller must not build an identity on:
    /// a description in a non-Latin script keeps nothing, and the mint has to
    /// stay total over it (§6.5).
    #[test]
    fn slug_of_non_latin_or_punctuation_is_empty() {
        assert_eq!(slug("Перевірка типів", 30), "");
        assert_eq!(slug("!!! ??? ...", 30), "");
        assert_eq!(slug("anything", 0), "");
    }

    #[test]
    fn slug_cuts_at_a_word_boundary_but_never_to_nothing() {
        // 30 lands inside "store"; the cut retreats to the preceding `-`.
        assert_eq!(
            slug("anthill todo backend increment two", 30),
            "anthill-todo-backend-increment"
        );
        // No `-` at or before the cap: truncate the single word rather than
        // returning "", which would make the slug absent for a long word.
        assert_eq!(slug("supercalifragilisticexpialidocious", 10), "supercalif");
    }

    #[test]
    fn digest_is_deterministic_and_uses_the_crockford_alphabet() {
        let a = digest_base32("alice\n2026-08-17T10:22:03Z\nfix the thing\n0", 5);
        let b = digest_base32("alice\n2026-08-17T10:22:03Z\nfix the thing\n0", 5);
        assert_eq!(a, b, "the same input must re-derive the same id");
        assert_eq!(a.chars().count(), 5);
        assert!(
            a.chars()
                .all(|c| "0123456789ABCDEFGHJKMNPQRSTVWXYZ".contains(c)),
            "{a} left the Crockford alphabet"
        );
    }

    /// The property that lets §6.5 widen the hash later without renumbering:
    /// five characters are the first five of six.
    #[test]
    fn a_narrow_digest_is_a_prefix_of_a_wider_one() {
        assert_eq!(
            digest_base32("some input", 5),
            digest_base32("some input", 8)[..5]
        );
    }

    #[test]
    fn digest_spreads_over_the_partition_it_claims() {
        // 1000 distinct inputs into 25 bits: the birthday bound predicts ~0.015
        // collisions, so any collision at all here means the avalanche is not
        // avalanching. The control is the FNV word without the finisher, which
        // varies only in its low bits and collides here in the thousands.
        let mut seen = std::collections::HashSet::new();
        for i in 0..1000 {
            assert!(
                seen.insert(digest_base32(
                    &format!("claude\n2026-08-17\nitem {i}\n0"),
                    5
                )),
                "collision at {i}"
            );
        }
    }

    #[test]
    fn digest_refuses_a_width_it_cannot_supply() {
        let err = string_digest_base32(&mut dummy(), &[Value::Str("x".into()), Value::Int(16)])
            .unwrap_err();
        assert!(matches!(err, EvalError::TypeMismatch { .. }));
    }
}
