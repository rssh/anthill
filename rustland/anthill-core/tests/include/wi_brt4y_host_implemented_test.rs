//! WI-20260922-BRT4Y — `@[host_implemented]`: an operation says in its DECLARATION that
//! it is body-less by design, and the load holds that claim against the binding layer.
//!
//! The attribute is the CLAIM, an `operation_map` entry (in any language) is the
//! EVIDENCE, and `load::check_host_implemented_claims` is the one place the two meet:
//!   * claimed and unsupplied — a load error naming the operation and the missing
//!     `provides <owner> language …` block (`HostImplementedUnsupplied`);
//!   * supplied and unclaimed — the drift check (`HostMappingUnclaimed`);
//!   * claimed and bodied — a contradiction (`HostImplementedWithBody`).
//!
//! And the migration: the 46 host functions `register_standard_builtins` registered by
//! hardcoded qualified name are `HOST_FNS` rows named by binding blocks, so every
//! operation the interpreter registers is one `is_interpreter_mapped_op` can see.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ─────────────────────────────
//!
//! Removing `check_host_implemented_claims` from the load pipeline fails the three
//! refusal rows (`a_claimed_operation_no_binding_supplies_is_a_load_error`,
//! `a_mapping_whose_operation_does_not_claim_it_is_a_load_error`,
//! `a_claimed_operation_with_a_body_is_a_load_error`) and
//! `the_stdlib_without_its_binding_layer_does_not_load`. Restoring the hardcoded
//! `register_if_present` registrations (and deleting the new binding blocks) fails
//! `every_operation_the_interpreter_registers_is_interpreter_mapped`. The controls
//! (`the_same_program_with_its_binding_layer_runs`, `the_same_mapping_over_the_claim_loads`,
//! `the_same_body_without_the_attribute_loads`, `the_full_closure_loads`) pass either way
//! BY DESIGN: they are what the refusals must disagree with.

use anthill_core::eval::{self, Interpreter, Value};
use anthill_core::kb::load::{meta_has_flag, INTERPRETER_LANG};
use anthill_core::kb::op_info;
use anthill_core::kb::KnowledgeBase;

/// A user carrier with one host-backed operation. The DECLARATION alone.
const CLAIM: &str = r#"
namespace brt4y.claim
  import anthill.prelude.{Int64}
  sort Gauge
    entity gauge(v: Int64)
    operation reading(v: Int64) -> Int64 @[host_implemented]
  end
end
"#;

/// The same declaration WITHOUT the attribute — the drift check's subject.
const UNCLAIMED: &str = r#"
namespace brt4y.claim
  import anthill.prelude.{Int64}
  sort Gauge
    entity gauge(v: Int64)
    operation reading(v: Int64) -> Int64
  end
end
"#;

/// The claim beside a body.
const CLAIM_WITH_BODY: &str = r#"
namespace brt4y.claim
  import anthill.prelude.{Int64}
  sort Gauge
    entity gauge(v: Int64)
    operation reading(v: Int64) -> Int64 = v @[host_implemented]
  end
end
"#;

/// The binding layer for `Gauge`, a separate FILE — the shape of every rustland
/// binding (`rustland/anthill-stl/anthill/`): the declaration stays host-agnostic.
const BINDING: &str = r#"
namespace brt4y.claim
  provides Gauge language rust
    artifact "brt4y-test"
    operation_map { reading: "brt4y_reading" }
  end
end
"#;

const READING: &str = "brt4y.claim.Gauge.reading";

/// The embedder half of the binding: the host function its `operation_map` names,
/// registered before load (WI-1122). Answers `v + 41`, so a call that reaches it is
/// distinguishable from any default.
fn register_reading(kb: &mut KnowledgeBase) {
    kb.register_host_fn("brt4y_reading", 1, |_i: &mut Interpreter, a: &[Value]| match a {
        [Value::Int(v)] => Ok(Value::Int(v + 41)),
        other => panic!("brt4y_reading: unexpected operands {other:?}"),
    })
    .expect("register brt4y_reading");
}

fn load(sources: &[&str]) -> Result<KnowledgeBase, Vec<String>> {
    crate::common::try_load_kb_prepared_files(sources, register_reading)
}

/// THE MARKER IS AN ORDINARY OPERATION ATTRIBUTE: it parses as the trailing `@[…]`
/// block and reaches `OperationInfo.meta`, where `meta_has_flag` reads it — on a user
/// operation, on a stdlib operation, and on an `operation { … }` BLOCK ENTRY (`BigInt`'s
/// comparisons are written that way). The check reads the flag through that same field.
#[test]
fn the_marker_reaches_operation_info_meta() {
    let kb = crate::common::expect_loaded(load(&[CLAIM, BINDING]));
    for qn in [
        READING,
        "anthill.prelude.Map.get",
        "anthill.prelude.BigInt.compare",
    ] {
        let sym = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("{qn} resolves"));
        let info = op_info::lookup_operation_info(&kb, sym)
            .unwrap_or_else(|| panic!("{qn} has an OperationInfo record"));
        assert!(
            meta_has_flag(&kb, info.meta, "host_implemented"),
            "{qn} is declared `@[host_implemented]`; its OperationInfo.meta must say so"
        );
    }
    // CONTROL: an operation with a body carries no such flag.
    let sym = kb
        .try_resolve_symbol("anthill.prelude.List.length")
        .expect("List.length resolves");
    let info = op_info::lookup_operation_info(&kb, sym).expect("List.length record");
    assert!(
        !meta_has_flag(&kb, info.meta, "host_implemented"),
        "control: a bodied operation does not claim host backing"
    );
}

/// THE POINT OF THE MARKER. Declared host-implemented, and no binding in the loaded
/// program supplies it: a LOAD error naming the operation and the missing layer — not a
/// program that loads clean and dies `OperationBodyMissing` at the first call.
#[test]
fn a_claimed_operation_no_binding_supplies_is_a_load_error() {
    crate::common::expect_load_errors(
        load(&[CLAIM]),
        &["operation `brt4y.claim.Gauge.reading` is declared `@[host_implemented]`, but no \
           binding block in the loaded program realizes it: no `provides brt4y.claim.Gauge \
           language …` block maps `reading`"],
    );
}

/// CONTROL for the row above: the SAME program with its binding layer loaded loads, and
/// the operation RUNS — its implementation is the host function the binding names.
#[test]
fn the_same_program_with_its_binding_layer_runs() {
    let kb = crate::common::expect_loaded(load(&[CLAIM, BINDING]));
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("register builtins");
    match interp.call(READING, &[Value::Int(1)]) {
        Ok(Value::Int(42)) => {}
        other => panic!("{READING}(1) must run the host function and answer 42, got {other:?}"),
    }
}

/// THE DRIFT CHECK: a binding realizes an operation whose declaration does not claim
/// host backing. Reading the declaration must keep answering "is this body-less on
/// purpose?", so the mismatch is refused rather than inferred.
#[test]
fn a_mapping_whose_operation_does_not_claim_it_is_a_load_error() {
    crate::common::expect_load_errors(
        load(&[UNCLAIMED, BINDING]),
        &["`operation_map` (language rust) realizes `brt4y.claim.Gauge.reading` with host \
           function \"brt4y_reading\", but the declaration of `brt4y.claim.Gauge.reading` \
           does not claim host backing"],
    );
}

/// CONTROL: the same mapping over the CLAIMED declaration loads.
#[test]
fn the_same_mapping_over_the_claim_loads() {
    crate::common::expect_loaded(load(&[CLAIM, BINDING]));
}

/// "Body-less by design" beside a body is a contradiction, refused rather than resolved
/// by whichever the builtin map happens to prefer.
#[test]
fn a_claimed_operation_with_a_body_is_a_load_error() {
    crate::common::expect_load_errors(
        load(&[CLAIM_WITH_BODY]),
        &["operation `brt4y.claim.Gauge.reading` is declared `@[host_implemented]` and \
           also has a body"],
    );
}

/// CONTROL: the bodied operation without the attribute loads.
#[test]
fn the_same_body_without_the_attribute_loads() {
    crate::common::expect_loaded(load(&[
        "namespace brt4y.claim\n  import anthill.prelude.{Int64}\n  sort Gauge\n    \
         entity gauge(v: Int64)\n    operation reading(v: Int64) -> Int64 = v\n  end\nend\n",
    ]));
}

/// THE DEFECT THE TICKET NAMED: `stdlib/` alone used to LOAD CLEAN and die
/// `OperationBodyMissing` at eval. Its host-backed operations are claimed now, so the
/// load itself refuses — once per operation, each naming its owner's binding block.
#[test]
fn the_stdlib_without_its_binding_layer_does_not_load() {
    let files = crate::common::collect_anthill_files(&crate::common::stdlib_dir());
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            anthill_core::parse::parse(&src)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    let errs: Vec<String> = match anthill_core::kb::load::load_all(
        &mut kb,
        &refs,
        &anthill_core::kb::load::NullResolver,
    ) {
        Ok(_) => panic!("the stdlib without its binding layer must not load"),
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    };
    for (op, owner) in [
        ("anthill.prelude.Map.get", "anthill.prelude.Map"),
        ("anthill.prelude.Int64.compare", "anthill.prelude.Int64"),
        ("anthill.prelude.PartialEq.eq", "anthill.prelude.PartialEq"),
        ("anthill.reflect.term_field", "anthill.reflect"),
    ] {
        assert!(
            errs.iter()
                .any(|e| e.contains(&format!("operation `{op}` is declared"))
                    && e.contains(&format!("no `provides {owner} language …` block"))),
            "the refusal must name `{op}` and its owner's missing binding block; got {} \
             error(s), e.g. {:?}",
            errs.len(),
            errs.first()
        );
    }
    assert!(
        errs.iter()
            .all(|e| e.contains("is declared `@[host_implemented]`, but no binding block")),
        "every refusal of a binding-less stdlib is an unsupplied claim, nothing else: {errs:#?}"
    );
}

/// CONTROL for the row above: the full closure — what every front end loads — is clean.
#[test]
fn the_full_closure_loads() {
    crate::common::load_kb_with("namespace brt4y.closure\nend\n");
}

/// THE MIGRATION, MEASURED. Before this ticket 46 operations were registered by
/// hardcoded qualified name and INVISIBLE to `is_interpreter_mapped_op` (measured on the
/// full closure: 137 rust-mapped operations, 46 registered-but-unmapped); after it, every
/// operation the interpreter registers is one the mapping index can see (183 mapped, 0
/// invisible). The invariant is asserted over everything `register_standard_builtins`
/// registers, not over a hand-kept list, so a hardcoded registration added THERE later
/// fails here. The 46 are pinned by name as well, because "0 invisible" alone would also
/// hold if they were registered nowhere.
///
/// NOT COVERED, and said here rather than implied: `anthill-stl`'s reflect set
/// (`register_reflect_builtins`) still registers by qualified name — its functions close
/// over resolved reflect symbols and live outside anthill-core — so its operations are
/// neither mapped nor claimed, and a registration added there is invisible to this test.
#[test]
fn every_operation_the_interpreter_registers_is_interpreter_mapped() {
    let kb = crate::common::load_kb_with("namespace brt4y.registry\nend\n");
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("register builtins");
    let registered = interp.registered_builtin_symbols();
    let kb = interp.kb();
    let mut invisible: Vec<&str> = registered
        .iter()
        .filter(|s| kb.kind_of(**s) == Some(anthill_core::intern::SymbolKind::Operation))
        .filter(|s| !kb.is_interpreter_mapped_op(**s))
        .map(|s| kb.qualified_name_of(*s))
        .collect();
    invisible.sort_unstable();
    invisible.dedup();
    assert!(
        invisible.is_empty(),
        "an operation the interpreter registers must be visible to \
         `is_interpreter_mapped_op` — registered without a mapping: {invisible:?}"
    );

    let mapped_rust: std::collections::HashSet<_> = kb
        .host_op_mappings()
        .iter()
        .filter(|m| m.lang == INTERPRETER_LANG)
        .filter_map(|m| m.op)
        .collect();
    for qn in MIGRATED {
        let sym = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("{qn} resolves"));
        assert!(
            mapped_rust.contains(&sym) && kb.is_interpreter_mapped_op(sym),
            "{qn} was a hardcoded registration; it must now be a rust `operation_map` entry"
        );
        assert!(
            registered.contains(&sym),
            "{qn} must still be REGISTERED — mapped and not registered would be worse"
        );
    }
}

/// The 46 registrations `register_standard_builtins` made by hardcoded qualified name
/// before this ticket (`register_if_present`), each now an `operation_map` entry.
const MIGRATED: [&str; 46] = [
    "anthill.prelude.PartialEq.eq",
    "anthill.prelude.PartialEq.neq",
    "anthill.kernel.struct_eq",
    "anthill.prelude.Map.empty",
    "anthill.prelude.Map.put",
    "anthill.prelude.Map.get",
    "anthill.prelude.Map.contains",
    "anthill.prelude.Map.remove",
    "anthill.prelude.Map.keys",
    "anthill.prelude.Map.values",
    "anthill.prelude.Map.entries",
    "anthill.prelude.Map.size",
    "anthill.prelude.LogicalStream.splitFirst",
    "anthill.prelude.Relation.splitFirst",
    "anthill.prelude.Relation.negate",
    "anthill.prelude.Relation.union",
    "anthill.prelude.Relation.where_run",
    "anthill.prelude.Relation.guarded_of",
    "anthill.prelude.Relation.join_run",
    "anthill.prelude.Relation.conjoin_of",
    "anthill.prelude.Relation.project_run",
    "anthill.prelude.Relation.fix",
    "anthill.prelude.Relation.rename",
    "anthill.prelude.Time.now",
    "anthill.prelude.Console.print",
    "anthill.prelude.Console.println",
    "anthill.prelude.Console.eprint",
    "anthill.prelude.Console.eprintln",
    "anthill.prelude.Console.read_line",
    "anthill.prelude.ModifyRuntime.get",
    "anthill.prelude.ModifyRuntime.set",
    "anthill.prelude.Error.raise",
    "anthill.prelude.Cell.new",
    "anthill.prelude.Cell.get",
    "anthill.prelude.Cell.set",
    "anthill.reflect.TypeValue.type_value",
    "anthill.realization.runtime.Dictionary.impl",
    "anthill.realization.runtime.Dictionary.arity",
    "anthill.realization.runtime.Dictionary.sub",
    "anthill.realization.runtime.Dictionary.resolveOp",
    "anthill.realization.runtime.Dictionary.ops",
    "anthill.realization.runtime.OpRef.op",
    "anthill.realization.runtime.OpRef.dict",
    "anthill.realization.runtime.OpRef.named",
    "anthill.realization.runtime.OpRef.spreadLabels",
    "anthill.realization.runtime.OpRef.opRequirements",
];

/// WHAT THE MIGRATION CHANGES AT A RULE BODY — visibility has consequences, and this pins
/// the representative one. The rule-body operand gate (`host_op_reducible_at_a_value`)
/// reads `is_interpreter_mapped_op`, so an effect-free migrated operation REDUCES there
/// now, each call in its own scratch bridge interpreter.
///
/// BOTH POLARITIES, so the row measures the computation and not merely that something
/// reduced: `size = 1` answers DEFINITE, `size = 2` and `not(size = 1)` answer nothing.
///
/// CONTROL, MEASURED by emptying `rustland/anthill-stl/anthill/map.anthill` and dropping
/// `Map`'s `@[host_implemented]` claims — which is what the gate saw while the operations
/// were registered by hardcoded name: all four goal rows SUSPEND (0 definite, 1
/// floundered) instead of deciding.
///
/// AND THE ARENA ROW. The first `size` goal PANICKED (`map_arena.rs`: index out of
/// bounds) before `MapHandle::with_body` read the handle's OWN arena: the inner
/// `Map.put(…)` ran in one bridge interpreter and the outer `Map.size` read its handle
/// against another's slot table. A wrong-arena read that lands on a populated slot
/// answers from SOME OTHER MAP, silently, so the fix is a structural one — the read is a
/// method on the handle — rather than a bounds check.
#[test]
fn a_migrated_pure_operation_reduces_in_a_rule_body() {
    use anthill_core::kb::resolve::ResolveConfig;
    let mut kb = crate::common::load_kb_with(
        "namespace brt4y.rulebody\n  import anthill.prelude.{Map, String, Int64, Bool}\n  \
         rule sz(1)  :- Map.size(Map.put(Map.empty(), \"a\", 1)) = 1\n  \
         rule sz2(1) :- Map.size(Map.put(Map.empty(), \"a\", 1)) = 2\n  \
         rule nsz(1) :- not(Map.size(Map.put(Map.empty(), \"a\", 1)) = 1)\n  \
         rule has(1) :- Map.contains(Map.put(Map.empty(), \"a\", 1), \"a\") = true\nend\n",
    );
    for (goal, definite, total) in [
        ("brt4y.rulebody.sz(1)", 1, 1),
        ("brt4y.rulebody.sz2(1)", 0, 0),
        ("brt4y.rulebody.nsz(1)", 0, 0),
        ("brt4y.rulebody.has(1)", 1, 1),
    ] {
        let g = crate::common::query_pattern_term(&mut kb, goal);
        let sols = kb.resolve(&[g], &ResolveConfig::default());
        assert_eq!(
            (sols.iter().filter(|s| s.is_definite()).count(), sols.len()),
            (definite, total),
            "{goal}: (definite, total) — a migrated pure `Map` operation must REDUCE at a \
             rule-body operand and decide, not suspend"
        );
    }
}

/// THE ATTRIBUTE IS REFUSED WHERE NOTHING WOULD READ IT. The load checks an operation's
/// claim only, so on any other declaration — or a clause — it would be accepted and read
/// by nothing; and it is a FLAG, since presence is what the check reads, so a valued
/// `@[host_implemented: false]` would be a claim that reads as a retraction. Refused at
/// conversion, like `internal`'s misplacements.
#[test]
fn the_attribute_is_refused_off_an_operation_and_with_a_value() {
    for (what, src) in [
        (
            "a const",
            "namespace brt4y.misplaced\n  import anthill.prelude.{Int64}\n  \
             sort S\n    const k: Int64 @[host_implemented]\n  end\nend\n",
        ),
        (
            "an entity",
            "namespace brt4y.misplaced\n  import anthill.prelude.{Int64}\n  \
             entity e(v: Int64) @[host_implemented]\nend\n",
        ),
        (
            "a sort",
            "namespace brt4y.misplaced\n  sort S @[host_implemented]\n  end\nend\n",
        ),
        (
            "a rule",
            "namespace brt4y.misplaced\n  rule r(1) :- r(1) @[host_implemented]\nend\n",
        ),
    ] {
        let errs = crate::common::parse_errs(src);
        assert!(
            errs.iter()
                .any(|e| e.contains(&format!("`@[host_implemented]` on {what}"))),
            "the attribute on {what} must be refused; got {errs:?}"
        );
    }
    let errs = crate::common::parse_errs(
        "namespace brt4y.valued\n  import anthill.prelude.{Int64}\n  sort S\n    \
         operation f(v: Int64) -> Int64 @[host_implemented: false]\n  end\nend\n",
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("`@[host_implemented]` takes no value")),
        "a valued claim must be refused; got {errs:?}"
    );
    // CONTROL: the bare flag on an operation parses (and `the_marker_reaches_…` above
    // shows it reaching `OperationInfo.meta`).
    crate::common::parses_clean(
        "namespace brt4y.valued\n  import anthill.prelude.{Int64}\n  sort S\n    \
         operation f(v: Int64) -> Int64 @[host_implemented]\n  end\nend\n",
    );
}

/// A MAPPING OVER A BODIED OPERATION is its own refusal, not the drift check's "add the
/// attribute" — that advice would only trade it for `HostImplementedWithBody`.
#[test]
fn a_mapping_over_a_bodied_operation_is_its_own_refusal() {
    crate::common::expect_load_errors(
        load(&[
            "namespace brt4y.claim\n  import anthill.prelude.{Int64}\n  sort Gauge\n    \
             entity gauge(v: Int64)\n    operation reading(v: Int64) -> Int64 = v\n  end\nend\n",
            BINDING,
        ]),
        &["realizes `brt4y.claim.Gauge.reading` with host function \"brt4y_reading\", but \
           `brt4y.claim.Gauge.reading` has an anthill BODY"],
    );
}

/// THE DRIFT CHECK IS PHASE-SCOPED, like the claim checks beside it. A later `load_all`
/// into the same KB judges the mappings THAT phase asserted (or whose operation it
/// declared), so a drift an earlier phase already reported is not re-reported —
/// unlocated — against an unrelated batch.
///
/// CONTROL, MEASURED: with the phase filter removed from the drift loop the third load
/// below fails with the second load's `HostMappingUnclaimed`.
#[test]
fn a_drift_is_reported_by_the_phase_that_loaded_it_and_no_later_one() {
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_prepared(
        "namespace brt4y.phase1\nend\n",
        register_reading,
    ));
    let load_into = |kb: &mut KnowledgeBase, sources: &[&str]| -> Result<(), Vec<String>> {
        let parsed: Vec<_> = sources
            .iter()
            .map(|s| anthill_core::parse::parse(s).expect("fixture parses"))
            .collect();
        let refs: Vec<_> = parsed.iter().collect();
        anthill_core::kb::load::load_all(kb, &refs, &anthill_core::kb::load::NullResolver)
            .map(|_| ())
            .map_err(|errs| errs.iter().map(|e| e.to_string()).collect())
    };
    crate::common::expect_load_errors(
        load_into(&mut kb, &[UNCLAIMED, BINDING]),
        &["does not claim host backing"],
    );
    crate::common::expect_loaded(load_into(&mut kb, &["namespace brt4y.phase3\nend\n"]));
}
