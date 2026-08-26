//! WI-876 — a spec-op builtin must not serve carriers it cannot handle.
//!
//! THE PRE-FIX MEASUREMENT, reproduced before the change and both halves confirmed.
//! `WeakOrd.compare` and `PartialOrd.gt`/`gte`/`lt`/`lte` were registered on the SPEC
//! op and compared host SCALARS only, so a STRUCTURAL carrier providing `Ord` was
//! intercepted by an implementation that could not run on its values:
//!
//!   * the LOAD refused [`CARRIER`] outright for `max`/`min` — *"provides
//!     'anthill.prelude.Ord' but backs no operation … max"* — because those two
//!     are NOT resolver builtins, so `op_backed` found no backing and demanded a
//!     member;
//!   * with `max`/`min` hand-written, the load went clean and `gt(pt(2,1), pt(1,9))`
//!     died *"expected Ord scalars of matching type, got Entity and Entity"* —
//!     because `gt`/`gte`/`lt`/`lte` ARE resolver builtins, so `op_backed` demanded
//!     nothing and they broke at eval instead.
//!
//! Two halves of one surface treated oppositely, and seven-or-nothing for the carrier.
//! `wi858_pair_orderings_test`'s header records why `anthill.prelude.Pair` shipped with
//! NO ordering rather than six workaround members; WI-877 adds it now that one suffices.
//!
//! WHAT THE FIX IS. The host implementation had nowhere to be KEYED: a `provides X
//! language rust` block admitted an artifact, a carrier, a namespace map, facts and
//! rules — and nothing mapping an OPERATION to a host function. So `Int64`'s host
//! `compare` went on the spec op, where one implementation served every carrier. This
//! adds the missing clause (`operation_map`), keys the scalar implementations per
//! carrier, deletes the spec-op registrations, and lets `PartialOrd`/`Ord` carry
//! the DEFAULT BODIES that `ordered.anthill` previously stated only as laws — a rule is
//! not backing (WI-818), and until the spec-op builtin was gone they were shadowed
//! anyway.
//!
//! Reference: `stdlib/anthill/realization/realization.anthill` (`OperationMapping`),
//! `stdlib/anthill/prelude/ordered.anthill`, `rustland/anthill-stl/anthill/*.anthill`.

use anthill_core::eval::Value;

/// A structural `Ord` carrier that supplies exactly ONE operation — `compare`.
/// Everything else (`gt`/`gte`/`lt`/`lte`, `max`/`min`) must come from the spec.
const CARRIER: &str = r#"
namespace wi876.lex
  import anthill.prelude.{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}

  sort Point
    import anthill.prelude.{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}
    entity pt(x: Int64, y: Int64)

    provides PartialEq[Point]
    provides Eq[Point]
    provides PartialOrd[Point]
    provides Ord[Point]

    operation eq(a: Point, b: Point) -> Bool =
      match a
        case pt(ax, ay) ->
          match b
            case pt(bx, by) ->
              if PartialEq.eq(ax, bx) then PartialEq.eq(ay, by) else false

    -- Lexicographic x-then-y. The ONLY comparison operation this carrier writes.
    operation compare(a: Point, b: Point) -> Int64 =
      match a
        case pt(ax, ay) ->
          match b
            case pt(bx, by) ->
              let c = WeakOrd.compare(ax, bx)
              if PartialEq.eq(c, 0) then WeakOrd.compare(ay, by) else c
  end

  sort Driver
    import anthill.prelude.{Int64, Bool, Ord, WeakOrd, PartialOrd}
    import wi876.lex.Point.{pt}
    operation cmpGt(n: Int64) -> Int64 = WeakOrd.compare(pt(2, 1), pt(1, 9))
    operation cmpLt(n: Int64) -> Int64 = WeakOrd.compare(pt(1, 9), pt(2, 1))
    operation cmpEq(n: Int64) -> Int64 = WeakOrd.compare(pt(2, 1), pt(2, 1))
    operation isGt(n: Int64) -> Bool = PartialOrd.gt(pt(2, 1), pt(1, 9))
    operation isGte(n: Int64) -> Bool = PartialOrd.gte(pt(2, 1), pt(2, 1))
    operation isLt(n: Int64) -> Bool = PartialOrd.lt(pt(2, 1), pt(1, 9))
    operation isLte(n: Int64) -> Bool = PartialOrd.lte(pt(1, 9), pt(2, 1))
    operation maxX(n: Int64) -> Int64 =
      match WeakOrd.max(pt(2, 1), pt(1, 9))
        case pt(x, y) -> x
    operation minX(n: Int64) -> Int64 =
      match WeakOrd.min(pt(2, 1), pt(1, 9))
        case pt(x, y) -> x
  end
end
"#;

fn eval_fresh(src: &str, entry: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

/// Call several entries on ONE interpreter, returning `(entry, value)` pairs.
///
/// The fresh-per-call rule (`interp_for` per assertion) exists because a TRAPPED call
/// poisons every later call on the same interpreter — but every call here is expected
/// to SUCCEED, so one load serves the lot. It is not a micro-optimisation: each
/// `interp_for` parses and loads the whole stdlib, and this file had ~25 of them.
fn eval_all(src: &str, entries: &[&str]) -> Vec<Value> {
    let mut interp = crate::common::interp_for(src);
    entries
        .iter()
        .map(|e| {
            interp
                .call(e, &[Value::Int(0)])
                .unwrap_or_else(|err| panic!("call {e}: {err:?}"))
        })
        .collect()
}

fn as_int(v: &Value, why: &str) -> i64 {
    match v {
        Value::Int(n) => *n,
        other => panic!("{why}; got {other:?}"),
    }
}

fn as_bool(v: &Value, why: &str) -> bool {
    match v {
        Value::Bool(b) => *b,
        other => panic!("{why}; got {other:?}"),
    }
}

fn eval_bool(src: &str, entry: &str, why: &str) -> bool {
    match eval_fresh(src, entry) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{why}; got {other:?}"),
    }
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

fn loads_clean(src: &str, why: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{why}; got load errors: {errs:?}");
    }
}

/// The harness reports breakage: an unknown sort must still fail to load, so every
/// value assertion below — each of which loads through `interp_for`, which panics on
/// a dirty load — is a real clean-load assertion and not a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    load_errs(
        "\nnamespace wi876.control\n  \
         sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end\nend\n",
    );
}

/// THE ACCEPTANCE: the whole `Ord`/`PartialOrd` surface works on a structural
/// carrier that declared only `compare` — no `max`/`min`, no `gt`/`gte`/`lt`/`lte`.
///
/// Every arm is asserted in BOTH directions, and `cmpEq`/`isGte` on a tie: a body that
/// answered a constant, or one that read only the sign of the first component, would
/// pass a one-sided test. `maxX`/`minX` read the WINNER's first component rather than a
/// Bool, so a `max` that returned the wrong operand is visible.
#[test]
fn the_whole_comparison_surface_works_from_one_operation() {
    let v = eval_all(
        CARRIER,
        &[
            "wi876.lex.Driver.cmpGt",
            "wi876.lex.Driver.cmpLt",
            "wi876.lex.Driver.cmpEq",
            "wi876.lex.Driver.isGt",
            "wi876.lex.Driver.isGte",
            "wi876.lex.Driver.isLt",
            "wi876.lex.Driver.isLte",
            "wi876.lex.Driver.maxX",
            "wi876.lex.Driver.minX",
        ],
    );
    assert_eq!(as_int(&v[0], "compare, greater"), 1);
    assert_eq!(as_int(&v[1], "compare, less"), -1);
    assert_eq!(as_int(&v[2], "compare, equal"), 0);
    assert!(as_bool(&v[3], "gt"));
    assert!(as_bool(&v[4], "gte on a tie"));
    assert!(!as_bool(&v[5], "lt"));
    assert!(as_bool(&v[6], "lte"));
    assert_eq!(as_int(&v[7], "max"), 2);
    assert_eq!(as_int(&v[8], "min"), 1);
}

// ── The mechanism: mappings are FACTS, and they are keyed per carrier ─

/// The `operation_map` clause reaches the KB as
/// `anthill.realization.OperationMapping` facts — the thing the runtime's builtin
/// registry reads INSTEAD of a hardcoded spec-op list. Asserted on the facts rather
/// than on "the comparisons work", because the comparisons would also work if the
/// registrations had quietly stayed on the spec op, which is the defect.
///
/// `Float` is the discriminating carrier: it maps the four IEEE comparisons and NOT
/// `compare` (it provides `PartialOrd`, not `Ord`), so a mapping table that had
/// collapsed to one per-language entry would show `compare` here. WI-881 filled the
/// rest of `Float`'s surface in through this same clause, so the assertion is on the
/// ABSENCE of `compare` and on `Float`'s own IEEE host functions rather than on an
/// exact list — the ordering-only list was this ticket's shape, not a rule.
///
/// WI-884 — the same is now true of `Int64` and `String`, which gained their bounds
/// and their search/edit surface through this clause: every carrier is asserted by
/// CONTAINMENT of the family under test. An exact-list assertion here reads as "these
/// are the mappings" and is really "these are the mappings I happened to write", so
/// each later ticket that legitimately adds one has to edit it — and the edit is
/// indistinguishable from one that papers over a mapping that went missing.
#[test]
fn a_binding_blocks_operation_map_lands_as_facts() {
    let kb = crate::common::load_kb_with("\nnamespace wi876.facts\n  sort S\n  end\nend\n");
    let mappings = kb.host_op_mappings();
    // Sorted only so a failure message reads in a fixed order — every assertion below
    // is by containment, so the order carries no meaning.
    let mapped = |carrier: &str| -> Vec<String> {
        let prefix = format!("anthill.prelude.{carrier}.");
        let mut v: Vec<String> = mappings
            .iter()
            .filter(|m| m.lang == "rust" && m.op_qn.starts_with(&prefix))
            .map(|m| m.op_qn[prefix.len()..].to_string())
            .collect();
        v.sort();
        v
    };
    let maps_all = |carrier: &str, ops: &[&str]| {
        let have = mapped(carrier);
        for op in ops {
            assert!(
                have.iter().any(|m| m == op),
                "{carrier} maps {op}; has {have:?}"
            );
        }
    };
    let total = ["compare", "gt", "gte", "lt", "lte", "max", "min"];
    maps_all("Int64", &total);
    maps_all("String", &total);
    maps_all("BigInt", &total);
    maps_all("Float", &["gt", "gte", "lt", "lte"]);
    let float_mapped = mapped("Float");
    assert!(
        !float_mapped.iter().any(|m| m == "compare"),
        "`Float` maps no `compare` — it provides `PartialOrd` and not the total \
         `Ord`, so there is no total comparison for the derivation to bottom out \
         in; got {float_mapped:?}",
    );

    // And each mapping names a DIFFERENT host function for `Float` than for the total
    // carriers — "Float's order is IEEE" as a fact in Float's binding rather than a
    // branch inside one shared spec-op implementation.
    let host_fn = |op_qn: &str| -> String {
        mappings
            .iter()
            .find(|m| m.op_qn == op_qn && m.lang == "rust")
            .unwrap_or_else(|| panic!("no mapping for {op_qn}"))
            .host_fn
            .clone()
    };
    assert_eq!(host_fn("anthill.prelude.Int64.gt"), "ordered_gt");
    assert_eq!(host_fn("anthill.prelude.Float.gt"), "float_gt");
}

/// A mapped operation is EXECUTABLE for the load check — and only for the carrier that
/// mapped it. Before, `kb.is_builtin` answered `true` for the SPEC op, so
/// `check_provider_operations` certified `gt` as backed for EVERY carrier, which is
/// defect A: a load-time claim that did not imply the operation runs.
#[test]
fn a_host_mapping_backs_only_the_carrier_that_wrote_it() {
    let kb = crate::common::load_kb_with("\nnamespace wi876.mapped\n  sort S\n  end\nend\n");
    let sym = |qn: &str| {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("no symbol {qn}"))
    };
    assert!(
        kb.is_host_mapped_op(sym("anthill.prelude.Int64.compare")),
        "Int64.compare"
    );
    assert!(
        kb.is_host_mapped_op(sym("anthill.prelude.Float.gt")),
        "Float.gt"
    );
    assert!(
        !kb.is_host_mapped_op(sym("anthill.prelude.WeakOrd.compare")),
        "the SPEC op carries no host implementation any more — that keying IS the defect",
    );
    assert!(
        !kb.is_host_mapped_op(sym("anthill.prelude.Int64.abs")),
        "the control: an unmapped operation of a mapped carrier is not host-mapped",
    );
}

// ── Controls: the carriers that already worked still work ────────────

/// The SCALAR path is unchanged — asserted on all three total carriers and on both
/// `compare` and the derived surface, because the migration moved every one of them
/// from a spec-op registration to a per-carrier one and a carrier left behind would
/// fall into `PartialOrd`'s default body (correct answer, wrong route) or die.
#[test]
fn the_scalar_orderings_are_unchanged() {
    let src = "
namespace wi876.scalars
  import anthill.prelude.{Int64, String, BigInt, Bool, Ord, WeakOrd, PartialOrd}
  import anthill.prelude.BigInt.{to_bigint}
  sort Driver
    operation ints(n: Int64) -> Int64 = WeakOrd.compare(7, 3)
    operation strings(n: Int64) -> Int64 = WeakOrd.compare(\"b\", \"a\")
    operation bigs(n: Int64) -> Int64 = WeakOrd.compare(to_bigint(7), to_bigint(3))
    operation intGt(n: Int64) -> Bool = PartialOrd.gt(7, 3)
    operation intLt(n: Int64) -> Bool = PartialOrd.lt(7, 3)
    operation strLte(n: Int64) -> Bool = PartialOrd.lte(\"a\", \"b\")
    operation intMax(n: Int64) -> Int64 = WeakOrd.max(7, 3)
    operation intMin(n: Int64) -> Int64 = WeakOrd.min(7, 3)
    operation strMax(n: Int64) -> String = WeakOrd.max(\"a\", \"b\")
  end
end
";
    let v = eval_all(
        src,
        &[
            "wi876.scalars.Driver.ints",
            "wi876.scalars.Driver.strings",
            "wi876.scalars.Driver.bigs",
            "wi876.scalars.Driver.intGt",
            "wi876.scalars.Driver.intLt",
            "wi876.scalars.Driver.strLte",
            "wi876.scalars.Driver.intMax",
            "wi876.scalars.Driver.intMin",
            "wi876.scalars.Driver.strMax",
        ],
    );
    assert_eq!(as_int(&v[0], "Int64 compare"), 1);
    assert_eq!(as_int(&v[1], "String compare"), 1);
    assert_eq!(as_int(&v[2], "BigInt compare"), 1);
    assert!(as_bool(&v[3], "Int64 gt"));
    assert!(!as_bool(&v[4], "Int64 lt"));
    assert!(as_bool(&v[5], "String lte"));
    assert_eq!(as_int(&v[6], "Int64 max"), 7);
    assert_eq!(as_int(&v[7], "Int64 min"), 3);
    match &v[8] {
        Value::Str(s) => assert_eq!(s, "b", "String max"),
        other => panic!("String max; got {other:?}"),
    }
}

/// `Float`'s IEEE comparisons are unchanged, including the NaN arm that is the whole
/// reason they are separate host functions. The `1.5 < 2.5` arms are the control: a
/// `float_gt` that always answered false would pass the NaN assertion alone.
#[test]
fn floats_stay_ieee() {
    let src = "
namespace wi876.floats
  import anthill.prelude.{Int64, Bool, Float, PartialOrd}
  import anthill.prelude.Float.{nan}
  sort Driver
    operation gtPlain(n: Int64) -> Bool = PartialOrd.gt(2.5, 1.5)
    operation ltPlain(n: Int64) -> Bool = PartialOrd.lt(2.5, 1.5)
    operation gteEq(n: Int64) -> Bool = PartialOrd.gte(1.5, 1.5)
    operation gtNan(n: Int64) -> Bool = PartialOrd.gt(nan, 1.5)
    operation ltNan(n: Int64) -> Bool = PartialOrd.lt(nan, 1.5)
    operation gteNan(n: Int64) -> Bool = PartialOrd.gte(nan, nan)
    operation lteNan(n: Int64) -> Bool = PartialOrd.lte(nan, 1.5)
  end
end
";
    let v = eval_all(
        src,
        &[
            "wi876.floats.Driver.gtPlain",
            "wi876.floats.Driver.ltPlain",
            "wi876.floats.Driver.gteEq",
            "wi876.floats.Driver.gtNan",
            "wi876.floats.Driver.ltNan",
            "wi876.floats.Driver.gteNan",
            "wi876.floats.Driver.lteNan",
        ],
    );
    assert!(as_bool(&v[0], "2.5 > 1.5"));
    assert!(!as_bool(&v[1], "2.5 < 1.5"));
    assert!(as_bool(&v[2], "1.5 >= 1.5"));
    for (i, op) in ["gtNan", "ltNan", "gteNan", "lteNan"].iter().enumerate() {
        assert!(
            !as_bool(&v[3 + i], op),
            "IEEE: a NaN operand is UNORDERED, so {op} must be false",
        );
    }
}

// ── A broken mapping is LOUD, not silently unregistered ──────────────

/// Register the standard eval builtins over `src`, returning the error instead of
/// panicking — `common::interp_for` `.expect()`s this step, which is exactly the
/// failure the runtime-owned arm below is about.
fn registration_err(src: &str) -> String {
    let kb = crate::common::load_kb_with(src);
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    match anthill_core::eval::builtins::register_standard_builtins(&mut interp) {
        Ok(()) => panic!("expected a registration error, but registration succeeded"),
        Err(e) => format!("{e:?}"),
    }
}

/// A binding block carrying one `operation_map` entry, over a carrier declaring a
/// TWO-argument `squish` — so a mapping to `"ordered_compare"` agrees on arity and the
/// control below is genuinely well-formed. (It did not, in this file's first draft:
/// the control mapped a ONE-argument operation to a two-argument host function and
/// asserted the program loaded clean, enshrining exactly the "backed at load, dies at
/// the call" defect this ticket exists to close. Caught in review, pinned as
/// `a_host_function_of_the_wrong_arity_is_loud` below.)
fn mapping_program(ns: &str, entry: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         sort Widget\n    import anthill.prelude.{{Int64}}\n  import anthill.prelude.PartialOrd.{{gt}}\n    \
         entity widget(v: Int64)\n    \
         operation squish(a: Widget, b: Widget) -> Int64\n  end\n  \
         provides Widget language rust\n    artifact \"nowhere.rs\"\n    \
         operation_map {{ {entry} }}\n  end\nend\n"
    )
}

/// THE CONTROL for the refusals below: a well-formed entry — a declared OPERATION, of
/// matching arity, quoted, unique, in a HOST-language block — loads and registers.
#[test]
fn a_well_formed_mapping_over_a_declared_operation_loads() {
    let src = mapping_program("wi876.okmap", "squish: \"ordered_compare\"");
    loads_clean(&src, "a well-formed operation_map must load");
    let kb = crate::common::load_kb_with(&src);
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("a well-formed mapping must register");
}

/// A host function name written UNQUOTED is refused at the PRODUCER. Not a
/// hypothetical spelling: `bindings` accepts any term, and `carrier {{ T: i64 }}` in
/// the grammar's own doc comment teaches the unquoted form. MEASURED before this
/// guard: the entry produced a fact whose `host_fn` was not a string, the shape
/// reader dropped it, and the mapping VANISHED — the program loaded clean, ran
/// clean, registered nothing, and no layer ever mentioned it.
#[test]
fn an_unquoted_host_function_is_refused_at_load() {
    let errs = load_errs(&mapping_program(
        "wi876.unquoted",
        "squish: no_such_host_function",
    ));
    let joined = errs.join("\n");
    assert!(joined.contains("squish"), "names the entry: {joined}");
    assert!(
        joined.contains("STRING"),
        "says what is wrong with it: {joined}"
    );
}

/// A mapping for an operation the carrier never DECLARED is refused at LOAD — by the
/// loader, which can see it, so `anthill load` and `anthill check` say so rather than
/// leaving it to whoever first runs the operation. The clause says what BACKS an
/// operation; it does not bring one into existence.
#[test]
fn a_mapping_for_an_undeclared_operation_is_refused_at_load() {
    let errs = load_errs(&mapping_program(
        "wi876.badop",
        "compare: \"ordered_compare\"",
    ));
    let joined = errs.join("\n");
    assert!(
        joined.contains("wi876.badop.Widget.compare"),
        "names the operation: {joined}"
    );
    assert!(
        joined.contains("declares no operation"),
        "says what is wrong: {joined}"
    );
}

/// RESOLVING IS NOT ENOUGH — the target must be an OPERATION. An entity constructor is
/// a qualified `<ns>.<Sort>.<entity>` name, so it resolves; MEASURED before this guard,
/// `operation_map {{ widget: "ordered_compare" }}` registered a builtin against the
/// CONSTRUCTOR, and since every builtin lookup consults the builtin map FIRST, calling
/// `widget(1)` would have run a comparison. A `const` (`Float.nan`) resolves the same
/// way.
#[test]
fn a_mapping_over_a_non_operation_is_refused_at_load() {
    let errs = load_errs(&mapping_program(
        "wi876.ctor",
        "widget: \"ordered_compare\"",
    ));
    let joined = errs.join("\n");
    assert!(
        joined.contains("not an OPERATION"),
        "says what is wrong: {joined}"
    );
}

/// The declared operation and the host function must AGREE ON ARITY. Checked at
/// REGISTRATION rather than load, which is the earliest point that knows both: the
/// loader knows the operation's arity but not another language's function set, and the
/// closed host registry is the only thing that knows the host's. MEASURED before this
/// guard: a 1-argument operation mapped to a 2-argument host function loaded clean,
/// passed `anthill check`, and died `ArityMismatch` on the first call.
#[test]
fn a_host_function_of_the_wrong_arity_is_loud() {
    let src = "\nnamespace wi876.arity\n  \
        sort Widget\n    import anthill.prelude.{Int64}\n    \
        entity widget(v: Int64)\n    operation squish(a: Widget) -> Int64\n  end\n  \
        provides Widget language rust\n    artifact \"nowhere.rs\"\n    \
        operation_map { squish: \"ordered_compare\" }\n  end\nend\n";
    let err = registration_err(src);
    assert!(
        err.contains("wi876.arity.Widget.squish"),
        "names the operation: {err}"
    );
    assert!(
        err.contains("1 argument"),
        "names the declared arity: {err}"
    );
    assert!(err.contains("takes 2"), "names the host arity: {err}");
}

/// A REPEATED KEY is refused as SYNTAX — repetition within one list needs no type
/// information, the same reason the named-argument and tuple/entity label rules are
/// checked at that layer (WI-805/808/809). MEASURED before this guard: BOTH facts were
/// emitted and the runtime's `HashMap` insert let the second overwrite the first, so
/// `gt` quietly acquired IEEE semantics with no diagnostic from any layer.
#[test]
fn a_repeated_operation_map_key_is_refused() {
    let msgs = crate::common::parse_errs(&mapping_program(
        "wi876.dup",
        "squish: \"ordered_compare\", squish: \"ordered_max\"",
    ));
    let joined = msgs.join("\n");
    assert!(joined.contains("duplicate"), "{joined}");
    assert!(joined.contains("squish"), "names the key: {joined}");
}

/// `operation_map` under `language anthill` is refused rather than IGNORED. The
/// grammar admits the clause in every binding block, and an anthill implementation is
/// an operation BODY — there is no host function for the clause to name. MEASURED
/// before this guard it loaded clean and produced no mapping: precisely the
/// loads-clean/runs-clean/registers-nothing shape this ticket removes.
#[test]
fn an_operation_map_under_language_anthill_is_refused() {
    let errs = load_errs(
        "\nnamespace wi876.anthlang\n  \
         sort Widget\n    import anthill.prelude.{Int64}\n    \
         entity widget(v: Int64)\n    operation squish(a: Widget) -> Int64\n  end\n  \
         provides Widget language anthill\n    \
         operation_map { squish: \"ordered_compare\" }\n  end\nend\n",
    );
    assert!(
        errs.join("\n").contains("not meaningful"),
        "should refuse the clause: {errs:?}",
    );
}

/// A mapping naming a host function the RUNTIME does not have stays the runtime's to
/// answer — the loader cannot know another language's function set, and a cpp-only
/// mapping must not be judged by whether the Rust interpreter can run it. Loud there,
/// naming the key, rather than a silently unregistered operation that would later
/// misreport as a missing implementation.
#[test]
fn an_unknown_host_function_is_loud_at_registration() {
    let src = mapping_program("wi876.badfn", "squish: \"no_such_host_function\"");
    loads_clean(&src, "the loader must not judge a host function name");
    let err = registration_err(&src);
    assert!(
        err.contains("no_such_host_function"),
        "names the key: {err}"
    );
    assert!(
        err.contains("wi876.badfn.Widget.squish"),
        "names the operation: {err}"
    );
}

/// A carrier's OWN host-mapped member must WIN over the spec's default body. This is
/// the gate WI-876 widened (`carrier_override_op` filtered on a runnable BODY, so a
/// member whose body is the HOST's read as absent) and it is not ceremony: MEASURED
/// with the narrow gate, `gt(nan, 1.5)` fell through to `PartialOrd`'s `compare`-based
/// default and died `OperationBodyMissing {WeakOrd.compare}` — `Float` has no
/// `compare` — while a `String` comparison inside a program's witness ordering fell
/// through into an `AmbiguousSpecOpDispatch` between `String.compare` and the
/// program's own witnesses (six `wi844_sorted_set_driver_test` arms).
///
/// Asserted through a program that declares a RIVAL `Ord[String]`, which is what
/// makes it discriminating: if the default body ran, the value-directed resolution
/// underneath it would see two suppliers for `String` and go loud.
#[test]
fn a_carriers_own_host_member_beats_the_spec_default() {
    let src = "
namespace wi876.rival
  import anthill.prelude.{Int64, String, Bool, Ord, WeakOrd, PartialOrd}
  sort ByLength
    import anthill.prelude.{Int64, String}
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end
  sort Driver
    import anthill.prelude.{Int64, Bool, PartialOrd}
    operation hostOrder(n: Int64) -> Bool = PartialOrd.lt(\"zz\", \"aaa\")
  end
end
";
    assert!(
        !eval_bool(
            src,
            "wi876.rival.Driver.hostOrder",
            "String lt beside a rival ordering"
        ),
        "`String`'s OWN host `lt` must answer — alphabetically \"zz\" is NOT before \
         \"aaa\". Falling through to the spec default would resolve `compare` by value \
         and find both `String` and `ByLength`.",
    );
}
