//! WI-366 — a value-in-type binding in a sort-relation fact rides as `Value::Node`.
//!
//! After WI-342 retired `make_denoted` from the typer and the value-in-type
//! PRODUCTION paths (entity fields, op signatures, call type-args), the last
//! live `make_denoted` reaches were the ground (hash-consed) lowering of the
//! sort-relation facts: `SortAlias` (`sort T = …`), and the `SortView` spec of
//! `requires` / fact `provides` (`SortRequiresInfo` / `SortProvidesInfo`).
//!
//! WI-366 migrates those producers to carrier-agnostic value facts: a spec/alias
//! target whose structure carries a `denoted` value-in-type (here the literal
//! `3` in `Foo[Int, 3]`) is asserted via `assert_fact_value` with a `Value::Node`
//! occurrence, NOT re-grounded through `make_denoted` (now `#[cfg(test)]`-only).
//! All readers of these facts were made carrier-agnostic so loading the program
//! (which runs `resolve_requires_bindings`, the dispatch walks, etc. over the
//! value-headed fact) no longer panics on the value head.
//!
//! WI-390 UPDATE: the `requires` / `provides` / `sort-alias` value-in-type facts
//! now ride as faithful hash-consed `Term`s again (not `Value::Node`). WI-390 made
//! the Term world lossless for `denoted`, so the spec/target is term-representable
//! and the gated "not yet resolved" diagnostic no longer fires for these. The three
//! `*_rides_as_term` tests pin that the head is a `Term` whose spec still CARRIES
//! the `denoted` value (not dropped). The B1 written-effect-row tests and the
//! ground-alias guard are unchanged.

use anthill_core::eval::Value;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Stdlib + extra sources → the loaded KB (kept regardless of typecheck outcome,
/// so a value-in-type that may not fully type-check is still inspectable) plus
/// the load-error strings. A panic here is itself a test failure — it would mean
/// a fact reader hit the term-only `rule_head` on a value head.
fn load_kb(extras: &[&str]) -> (KnowledgeBase, Vec<String>) {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let errs = match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    };
    (kb, errs)
}

/// Whether a value head transitively carries a `Value::Node` occurrence — the
/// denoted value-in-type. Walks `Entity` / `Tuple` children (the value-fact head
/// shapes). A plain `Value::Term` head (the ground case) carries none.
fn value_carries_node(v: &Value) -> bool {
    match v {
        Value::Node(_) => true,
        Value::Entity { pos, named, .. } | Value::Tuple { pos, named } => {
            pos.iter().any(value_carries_node)
                || named.iter().any(|(_, x)| value_carries_node(x))
        }
        _ => false,
    }
}

/// Does any fact whose functor is `functor_qn` have a `Value::Node`-carrying
/// head? `functor_qn` may be a short or qualified name (resolved as the loader
/// resolves it).
fn any_node_carrying_fact(kb: &KnowledgeBase, functor_qn: &str) -> bool {
    let Some(sym) = kb.try_resolve_symbol(functor_qn) else {
        return false;
    };
    kb.rules_by_functor(sym)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .any(|rid| value_carries_node(kb.rule_head_value(rid)))
}

/// WI-390: whether a hash-consed term transitively contains a `denoted(...)` — the
/// faithful value-in-type form (e.g. the `3` in `Foo[Int, 3]`), proving the
/// round-trip kept it rather than dropping it.
fn term_carries_denoted(kb: &KnowledgeBase, t: anthill_core::kb::term::TermId) -> bool {
    use anthill_core::kb::term::{Term, TermId};
    let (is_denoted, children): (bool, Vec<TermId>) = match kb.get_term(t) {
        Term::Fn { functor, pos_args, named_args } => (
            kb.qualified_name_of(*functor) == "anthill.prelude.TypeExtractor.Denoted",
            pos_args.iter().copied().chain(named_args.iter().map(|(_, c)| *c)).collect(),
        ),
        _ => (false, Vec::new()),
    };
    is_denoted || children.into_iter().any(|c| term_carries_denoted(kb, c))
}

/// WI-390: the hash-consed `Term` head of the first *term*-headed fact whose
/// functor is `functor_qn` and whose spec/target transitively carries a `denoted`.
/// `None` if there is no such term-headed fact (e.g. still a `Value::Node`).
fn denoted_term_fact_head(
    kb: &KnowledgeBase,
    functor_qn: &str,
) -> Option<anthill_core::kb::term::TermId> {
    let sym = kb.try_resolve_symbol(functor_qn)?;
    kb.rules_by_functor(sym)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .find_map(|rid| match kb.rule_head_value(rid) {
            Value::Term(t) if term_carries_denoted(kb, *t) => Some(*t),
            _ => None,
        })
}

/// A two-parameter sort whose second parameter is bound to a literal (`3`),
/// the simplest parseable value-in-type. Shared by the three position tests.
const FOO: &str = r#"
  sort Foo
    sort T = ?
    sort N = ?
  end
"#;

/// `sort Bar = Foo[Int, 3]` — the alias target carries the denoted `3`, so the
/// `SortAlias` fact must ride as a `Value::Node`-carrying value fact (and the
/// SortAlias readers, run on every type-param resolution during load, must not
/// panic iterating it).
#[test]
fn sort_alias_value_in_type_rides_as_term() {
    let src = format!(
        r#"
namespace test.wi366.alias
  import anthill.prelude.{{Int}}
{FOO}
  sort Bar = Foo[Int, 3]
end
"#
    );
    let (kb, errs) = load_kb(&[&src]);
    // WI-390: `Foo[Int, 3]` is faithfully term-representable, so the SortAlias
    // target rides as a hash-consed `Term` (the `3` as a `denoted` term), not a
    // `Value::Node` value fact.
    assert!(
        !any_node_carrying_fact(&kb, "SortAlias"),
        "WI-390: `sort Bar = Foo[Int, 3]` must ride as a hash-consed Term SortAlias, not a Value::Node",
    );
    assert!(
        denoted_term_fact_head(&kb, "SortAlias").is_some(),
        "the SortAlias target must faithfully carry the denoted `3` (not dropped)",
    );
    assert!(
        !errs.iter().any(|e| e.contains("not yet resolved")),
        "WI-390: a representable value-in-type alias must NOT emit the gated diagnostic; got: {errs:?}",
    );
}

/// `requires Foo[Int, 3]` — the SortView spec carries the denoted `3`, so the
/// `SortRequiresInfo` fact rides as a value fact. Loading runs
/// `resolve_requires_bindings` (and `direct_requires` during typing) over the
/// value head, which must not panic.
#[test]
fn requires_value_in_type_rides_as_term() {
    let src = format!(
        r#"
namespace test.wi366.req
  import anthill.prelude.{{Int}}
{FOO}
  sort Carrier
    entity c(x: Int)
    requires Foo[Int, 3]
  end
end
"#
    );
    let (kb, errs) = load_kb(&[&src]);
    // WI-390 ACCEPTANCE: `Foo[Int, 3]` is faithfully term-representable (the `3`
    // rides as a `denoted` term), so the SortRequiresInfo head is a hash-consed
    // `Term` — `direct_requires` reads it (no silent skip) and `resolve_cache` keys
    // on it. (WI-390 reverses the WI-366 `Value::Node` direction here.)
    assert!(
        !any_node_carrying_fact(&kb, "anthill.reflect.SortRequiresInfo"),
        "WI-390: `requires Foo[Int, 3]` must ride as a hash-consed Term fact, not a Value::Node",
    );
    assert!(
        denoted_term_fact_head(&kb, "anthill.reflect.SortRequiresInfo").is_some(),
        "the SortRequiresInfo spec must faithfully carry the denoted `3` (not dropped)",
    );
    assert!(
        !errs.iter().any(|e| e.contains("not yet resolved")),
        "WI-390: a representable value-in-type requires must NOT emit the gated diagnostic; got: {errs:?}",
    );
}

/// `provides Foo[Int, 3]` — symmetric to `requires`: the `SortProvidesInfo` fact
/// rides as a value fact, and the provides/dispatch readers tolerate it.
#[test]
fn provides_value_in_type_rides_as_term() {
    let src = format!(
        r#"
namespace test.wi366.prov
  import anthill.prelude.{{Int}}
{FOO}
  sort Carrier
    entity c(x: Int)
    provides Foo[Int, 3]
  end
end
"#
    );
    let (kb, errs) = load_kb(&[&src]);
    // WI-390: symmetric to `requires` — the SortProvidesInfo head is a hash-consed
    // `Term` (keeping requires/provides symmetric for `check_provider_requires`),
    // its spec faithfully carrying the denoted `3`.
    assert!(
        !any_node_carrying_fact(&kb, "anthill.reflect.SortProvidesInfo"),
        "WI-390: `provides Foo[Int, 3]` must ride as a hash-consed Term fact, not a Value::Node",
    );
    assert!(
        denoted_term_fact_head(&kb, "anthill.reflect.SortProvidesInfo").is_some(),
        "the SortProvidesInfo spec must faithfully carry the denoted `3` (not dropped)",
    );
    assert!(
        !errs.iter().any(|e| e.contains("not yet resolved")),
        "WI-390: a representable value-in-type provides must NOT emit the gated diagnostic; got: {errs:?}",
    );
}

/// Regression: a standalone `provides Spec language X … end` block (proposal 038)
/// whose spec is a value-in-type must not PANIC the loader. The block spec is a
/// ground scope identity, so a denoted-bearing spec projects to its base sort.
/// Before the WI-366 fix, `load_provides_block` called `sort_inst_to_term`, whose
/// `as_term().expect(...)` panicked on the `Value::Entity` spec — reachable from
/// this valid syntax.
#[test]
fn provides_block_value_in_type_spec_loads_without_panic() {
    let src = format!(
        r#"
namespace test.wi366.provblock
  import anthill.prelude.{{Int}}
{FOO}
  provides Foo[Int, 3] language rust
    artifact "foo.rs"
  end
end
"#
    );
    // Must not panic (the spec projects to its base sort for the scope identity);
    // and per WI-366 it emits the gated 'not yet resolved' diagnostic rather than
    // silently accepting an unresolved provides-block.
    let (_kb, errs) = load_kb(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("not yet resolved")),
        "a value-in-type provides-block spec must emit the gated diagnostic \
         (and must not panic); got: {errs:?}",
    );
}

// ── WI-366 B1: a WRITTEN effect-row rides on a fact head, byte-identical to
//    the `provides` clause ───────────────────────────────────────────────────

/// The `spec` field's `E` binding of the (sort-body) `SortProvidesInfo` whose
/// `sort_ref` is `<ns>.MyList`. Term carrier only (a `{}` row is ground).
fn provides_e_binding(
    kb: &KnowledgeBase,
    ns: &str,
) -> Option<anthill_core::kb::term::TermId> {
    use anthill_core::kb::term::Term;
    let sym = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo")?;
    let myl = kb.try_resolve_symbol(&format!("{ns}.MyList"))?;
    for rid in kb.rules_by_functor(sym).into_iter().filter(|r| kb.is_fact(*r)) {
        let Value::Term(t) = kb.rule_head_value(rid) else { continue };
        let Term::Fn { named_args, .. } = kb.get_term(*t) else { continue };
        let matches_ns = named_args
            .iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "sort_ref")
            .is_some_and(|(_, v)| matches!(kb.get_term(*v),
                Term::Fn { functor, .. } if *functor == myl));
        if !matches_ns { continue; }
        let spec = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "spec")?.1;
        if let Term::Fn { named_args: sv, .. } = kb.get_term(spec) {
            return sv.iter().find(|(s, _)| kb.resolve_sym(*s) == "E").map(|(_, t)| *t);
        }
    }
    None
}

/// `fact Spec[E = {}]` and `provides Spec[E = {}]` must emit a BYTE-IDENTICAL
/// effect-row `E` binding in their `SortProvidesInfo`. Before WI-366 B1 the
/// `fact`-head term path stringified `{}` → `Term::Ref("{}")` →
/// `remap_symbol_strict` → an `unresolved name '{}'` load error (the written
/// row was DROPPED — "term loses fact"); only the type-aware `provides` path
/// kept it. Now both lower the row through the same `lower_effect_row`, so the
/// fact-head and `provides` capabilities are the same `effects_rows(empty_row)`.
#[test]
fn fact_head_written_empty_effect_row_matches_provides() {
    // One kb so hash-consing makes equal TermId == structural identity.
    let fact_ns = r#"
namespace test.wi366.factrow.f
  import anthill.prelude.{Int, Stream}
  sort MyList
    entity nil
    fact Stream[T = Int, E = {}]
  end
end
"#;
    let prov_ns = r#"
namespace test.wi366.factrow.p
  import anthill.prelude.{Int, Stream}
  sort MyList
    entity nil
    provides Stream[T = Int, E = {}]
  end
end
"#;
    let (kb, errs) = load_kb(&[fact_ns, prov_ns]);
    // The written `{}` row must NOT produce an unresolved-name load error.
    assert!(
        !errs.iter().any(|e| e.contains("unresolved name '{}'")),
        "`fact Stream[E = {{}}]` must not drop the written row to an unresolved \
         name; got: {errs:?}",
    );
    let fe = provides_e_binding(&kb, "test.wi366.factrow.f");
    let pe = provides_e_binding(&kb, "test.wi366.factrow.p");
    assert!(
        fe.is_some() && fe == pe,
        "the `fact`-head and `provides`-clause SortProvidesInfo must carry a \
         byte-identical effect-row `E` binding; got fact={fe:?} provides={pe:?}",
    );
}

/// Regression (WI-366 B1): a written effect-row in a RULE-BODY atom
/// (`:- Stream[T = Int, E = {}]`) must be CARRIED, not silently dropped. Rule
/// bodies load via `build_body_atom_occurrence` (the occurrence path), which used
/// to filter out ALL `ParseAux` children — so when `{}` started riding as an
/// effect-row ParseAux, the `E` binding vanished (the loud `unresolved name '{}'`
/// became a silent drop). The fix lowers the effect-row ParseAux there too, via
/// the same `lower_effect_row`. We assert the loaded body atom still carries `E`.
#[test]
fn rule_body_written_empty_effect_row_is_carried() {
    use anthill_core::persistence::print::TermPrinter;
    let src = r#"
namespace test.wi366.rulerow
  import anthill.prelude.{Int, Stream}
  sort Carrier
    entity c(x: Int)
  end
  rule wants_stream(?c)
    :- Stream[T = Int, E = {}]
end
"#;
    let (kb, errs) = load_kb(&[src]);
    assert!(
        !errs.iter().any(|e| e.contains("unresolved name '{}'")),
        "the written `{{}}` row in a rule body must not stringify to an unresolved \
         name; got: {errs:?}",
    );
    let sym = kb
        .try_resolve_symbol("test.wi366.rulerow.wants_stream")
        .expect("rule functor resolves");
    let rid = kb.rules_by_functor(sym)[0];
    let printer = TermPrinter::new(&kb);
    let body: String = kb
        .rule_body_nodes(rid)
        .iter()
        .map(|atom| printer.print_occurrence(atom))
        .collect::<Vec<_>>()
        .join(" || ");
    // The element binding (`Int`) AND the effect-row binding (`E`) must both be
    // present — if `E` were dropped, only `Int` would survive.
    assert!(
        body.contains("Int") && body.contains("E"),
        "rule-body atom must carry BOTH the `T = Int` and the `E = {{}}` bindings \
         (the written row must not be dropped); got body: {body}",
    );
}

/// Regression (WI-366 B1): a POSITIONAL written effect-row nested inside a
/// rule-body atom (`:- List[T = Stream[{}]]`) must be CARRIED, not panic.
/// `build_body_atom_occurrence`'s POSITIONAL child loop (distinct from its named
/// loop) also has to lower the effect-row aux — otherwise the positional `{}`
/// recurses into the outer `Term::ParseAux => unreachable!` and panics.
#[test]
fn rule_body_positional_nested_empty_effect_row_is_carried() {
    use anthill_core::persistence::print::TermPrinter;
    let src = r#"
namespace test.wi366.rulerowpos
  import anthill.prelude.{Int, Stream, List}
  sort Carrier
    entity c(x: Int)
  end
  rule wants(?c)
    :- List[T = Stream[{}]]
end
"#;
    // Must NOT panic; the nested positional row must be carried.
    let (kb, errs) = load_kb(&[src]);
    assert!(
        !errs.iter().any(|e| e.contains("unresolved name '{}'")),
        "nested positional `{{}}` must not stringify to an unresolved name; got: {errs:?}",
    );
    let sym = kb
        .try_resolve_symbol("test.wi366.rulerowpos.wants")
        .expect("rule functor resolves");
    let rid = kb.rules_by_functor(sym)[0];
    let body: String = kb
        .rule_body_nodes(rid)
        .iter()
        .map(|atom| TermPrinter::new(&kb).print_occurrence(atom))
        .collect::<Vec<_>>()
        .join(" || ");
    assert!(
        body.contains("Stream") && body.contains("EffectsRows"),
        "the nested `Stream[{{}}]` and its lowered effect-row must both survive in the \
         rule body (no panic/drop); got: {body}",
    );
}

/// Regression (WI-366 B1): a written effect-row in an OP-BODY type-expression
/// (`operation give() -> Type = Stream[T = Int, E = {}]`) must be CARRIED, not
/// dropped. Op bodies load via the `convert_expr_term` work-stack (`visit_load`),
/// a THIRD term-position consumer that also filtered out ParseAux children — so
/// `{}`-as-aux would have been silently dropped (and a naive keep would have
/// panicked in `build_expr_leaf`). The fix lowers it via the same path and
/// materializes the occurrence.
#[test]
fn op_body_written_empty_effect_row_is_carried() {
    use anthill_core::persistence::print::TermPrinter;
    let src = r#"
namespace test.wi366.opbodyrow
  import anthill.prelude.{Int, Stream, Type}
  sort Carrier
    entity c(x: Int)
    operation give(self: Carrier) -> Type = Stream[T = Int, E = {}]
  end
end
"#;
    let (kb, errs) = load_kb(&[src]);
    assert!(
        !errs.iter().any(|e| e.contains("unresolved name '{}'")),
        "the written `{{}}` row in an op body must not stringify to an unresolved \
         name; got: {errs:?}",
    );
    let op = kb
        .try_resolve_symbol("test.wi366.opbodyrow.Carrier.give")
        .expect("op functor resolves");
    let body = kb.op_body_node(op).expect("give has a body");
    let printed = TermPrinter::new(&kb).print_occurrence(body);
    assert!(
        printed.contains("Int") && printed.contains("E"),
        "op-body type-expression must carry BOTH `T = Int` and the `E = {{}}` \
         effect-row binding (the written row must not be dropped); got: {printed}",
    );
}

/// Regression (WI-366 B1): a written effect-row in a QUERY pattern
/// (`anthill query --pattern 'Stream[T = Int, E = {}]'`) must lower, not PANIC.
/// Queries are converted by `convert_query_term` — a FOURTH term-position
/// consumer (a free fn, not the `Loader`) — whose `ParseAux` arm used to be
/// `unreachable!`. The parse change made `{}` ride as an effect-row aux, which
/// would hit that panic (worse than the pre-change loud `unresolved name '{}'`).
/// The fix lowers the empty row to `effects_rows(empty_row)` so the pattern
/// matches `provides`/fact rows.
#[test]
fn query_pattern_written_empty_effect_row_lowers() {
    use anthill_core::kb::load;
    use anthill_core::kb::term::Term;
    use anthill_core::parse;
    use std::collections::HashMap;

    // Load stdlib so Stream / Int / EffectExpression.empty_row are registered.
    let (mut kb, _errs) = load_kb(&[]);

    // Replicate the CLI `query --pattern` path (`fact {pattern}`); stdlib names
    // are already registered in `kb` above, so no import line is needed.
    let src = "fact Stream[T = Int, E = {}]";
    let parsed = parse::parse(src).expect("parse query pattern");
    let _ = load::scan_definitions(&mut kb, &[&parsed]);
    let global_raw = kb.make_name_term("_global").raw();
    let mut var_map = HashMap::new();
    let mut term = None;
    for item in &parsed.items {
        if let anthill_core::parse::ir::Item::Fact(f) = item {
            // Must NOT panic (was `unreachable!` on the effect-row ParseAux).
            term = Some(load::convert_query_term(
                &mut kb,
                &parsed.terms,
                &parsed.symbols,
                f.term,
                global_raw,
                &mut var_map,
            ));
        }
    }
    let term = term.expect("query pattern has a fact term");
    let Term::Fn { named_args, .. } = kb.get_term(term) else {
        panic!("query pattern term must be a Fn");
    };
    let e = named_args
        .iter()
        .find(|(s, _)| kb.resolve_sym(*s) == "E")
        .map(|(_, t)| *t)
        .expect("E binding present (not dropped) in query pattern term");
    assert!(
        matches!(kb.get_term(e), Term::Fn { functor, .. }
            if kb.qualified_name_of(*functor) == "anthill.prelude.TypeExtractor.EffectsRows"),
        "query `Stream[E = {{}}]` must lower E to an `effects_rows` Type (not drop it \
         or panic); got: {:?}",
        kb.get_term(e),
    );
}

/// Guard: the ground case is unchanged. `sort Bar = Int` (no value-in-type)
/// stays a hash-consed `Value::Term` SortAlias — no value fact is minted, so the
/// migration is byte-identical for the universal ground case.
#[test]
fn ground_alias_stays_a_term_fact() {
    let src = r#"
namespace test.wi366.ground
  import anthill.prelude.{Int}
  sort Bar = Int
end
"#;
    let (kb, _errs) = load_kb(&[src]);
    let alias_sym = kb.try_resolve_symbol("SortAlias").expect("SortAlias resolves");
    let bar = kb
        .try_resolve_symbol("test.wi366.ground.Bar")
        .expect("Bar resolves");
    // The Bar alias must be present and a ground Term head (no Node carried).
    let bar_alias = kb
        .rules_by_functor(alias_sym)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .find(|rid| {
            // pos[0] is the sort term whose functor is Bar.
            matches!(kb.rule_head_value(*rid), Value::Term(t)
                if matches!(kb.get_term(*t),
                    anthill_core::kb::term::Term::Fn { pos_args, .. }
                        if pos_args.first().is_some_and(|p|
                            matches!(kb.get_term(*p),
                                anthill_core::kb::term::Term::Fn { functor, .. } if *functor == bar))))
        });
    assert!(
        bar_alias.is_some(),
        "`sort Bar = Int` must stay a ground hash-consed Value::Term SortAlias fact",
    );
}

// ── WI-390: faithful `Value → Term` bridge (deeper coverage) ─────────────────

/// The `spec` named-arg term of the SortRequiresInfo fact whose `sort_ref` is the
/// sort `carrier_qn` — i.e. the lowered `requires` spec, as a hash-consed `TermId`.
fn carrier_requires_spec(
    kb: &KnowledgeBase,
    carrier_qn: &str,
) -> Option<anthill_core::kb::term::TermId> {
    use anthill_core::kb::term::Term;
    let carrier = kb.try_resolve_symbol(carrier_qn)?;
    let req = kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo")?;
    kb.rules_by_functor(req)
        .into_iter()
        .filter(|r| kb.is_fact(*r))
        .find_map(|rid| {
            let Value::Term(t) = kb.rule_head_value(rid) else { return None };
            let Term::Fn { named_args, .. } = kb.get_term(*t) else { return None };
            let sr = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "sort_ref")?.1;
            let sr_functor = match kb.get_term(sr) {
                Term::Fn { functor, .. } => *functor,
                Term::Ref(s) => *s,
                _ => return None,
            };
            if sr_functor != carrier {
                return None;
            }
            named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "spec").map(|(_, t)| *t)
        })
}

/// WI-390 (R1): `value_to_term` of a `Foo[Int, denoted(3)]` occurrence hash-cons-
/// equals the ground twin built directly via the term builders — proving the
/// lowering is byte-faithful (and routes arrows through the non-canonicalizing
/// builder, so a re-canonicalized arrow can't diverge).
#[test]
fn value_to_term_denoted_round_trips_to_ground_twin() {
    use anthill_core::kb::node_occurrence::{self, Expr, NodeOccurrence, TypeChild};
    use anthill_core::kb::term::{Literal, Term};
    use anthill_core::span::{SourceId, SourceSpan};
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    let sp = SourceSpan::new(SourceId::from_raw(0), 0, 0);
    let (t_sym, n_sym) = (kb.intern("T"), kb.intern("N"));
    let foo = kb.make_sort_ref_by_name("Foo");
    let int_ref = kb.make_sort_ref_by_name("Int");

    // Occurrence: Foo[T = Int, N = denoted(3)].
    let three_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(3)), sp, None);
    let denoted_occ = kb.make_denoted_occ(three_occ, sp, None);
    let param_occ = kb.make_parameterized_occ(
        TypeChild::Ground(foo),
        vec![(t_sym, TypeChild::Ground(int_ref)), (n_sym, TypeChild::Node(denoted_occ))],
        sp,
        None,
    );
    let from_occ = node_occurrence::value_to_term(&mut kb, &Value::Node(param_occ))
        .expect("a denoted-bearing type is term-representable");

    // Ground twin built directly via the term builders.
    let three_t = kb.alloc(Term::Const(Literal::Int(3)));
    let denoted_t = kb.make_denoted(three_t);
    let twin = kb.make_parameterized_type(foo, &[(t_sym, int_ref), (n_sym, denoted_t)]);

    assert_eq!(
        from_occ, twin,
        "value_to_term(occurrence) must hash-cons-equal the ground twin (faithful)",
    );
    assert!(
        term_carries_denoted(&kb, from_occ),
        "the lowered term must carry the denoted `3` (not dropped)",
    );
}

/// WI-390 (acceptance): `requires Foo[Int, 3]` vs `Foo[Int, 4]` lower to DISTINCT
/// spec `TermId`s (so the `TermId`-keyed `resolve_cache` distinguishes them), while
/// two `Foo[Int, 3]` dedup to one `TermId`.
#[test]
fn requires_specs_distinguish_by_denoted_literal() {
    let src = format!(
        r#"
namespace test.wi390.cache
  import anthill.prelude.{{Int}}
{FOO}
  sort CarrierA
    entity a(x: Int)
    requires Foo[Int, 3]
  end
  sort CarrierB
    entity b(x: Int)
    requires Foo[Int, 4]
  end
  sort CarrierC
    entity cc(x: Int)
    requires Foo[Int, 3]
  end
end
"#
    );
    let (kb, _errs) = load_kb(&[&src]);
    let s3 = carrier_requires_spec(&kb, "test.wi390.cache.CarrierA").expect("A requires spec");
    let s4 = carrier_requires_spec(&kb, "test.wi390.cache.CarrierB").expect("B requires spec");
    let s3c = carrier_requires_spec(&kb, "test.wi390.cache.CarrierC").expect("C requires spec");
    assert_ne!(
        s3, s4,
        "`Foo[Int, 3]` and `Foo[Int, 4]` must lower to distinct spec TermIds (distinct cache keys)",
    );
    assert_eq!(
        s3, s3c,
        "two `Foo[Int, 3]` must dedup to one spec TermId (hash-consing)",
    );
    // WI-390 R3: the scope-axiom signature (`requires.<flatten_spec>`) must ALSO
    // distinguish the literals — `flatten_spec` must not collapse the denoted to a
    // non-distinguishing token, else two requires differing only in the literal
    // collide on one scope-axiom QN and one is dropped.
    let f3 = anthill_core::kb::load::flatten_spec(&kb, s3);
    let f4 = anthill_core::kb::load::flatten_spec(&kb, s4);
    assert_ne!(
        f3, f4,
        "flatten_spec must distinguish Foo[Int,3] from Foo[Int,4] in the scope-axiom name; got {f3:?} vs {f4:?}",
    );
}

/// WI-390 (d): `Positioned(pos, internal)` is an ordinary hash-consed term — same
/// `(pos, internal)` dedup, a different absolute `pos` is a distinct term (so two
/// local binders with the same surface name don't collide); the children read back.
#[test]
fn positioned_is_a_structural_term() {
    use anthill_core::kb::term::Term;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    let site_a = kb.make_sort_ref_by_name("bindSiteA");
    let site_b = kb.make_sort_ref_by_name("bindSiteB");
    let x = kb.make_sort_ref_by_name("x");
    let pa1 = kb.make_positioned(site_a, x);
    let pa2 = kb.make_positioned(site_a, x);
    let pb = kb.make_positioned(site_b, x);
    assert_eq!(pa1, pa2, "same (pos, internal) → one hash-consed TermId");
    assert_ne!(pa1, pb, "different pos (binding site) → distinct term (no collision)");
    let Term::Fn { functor, named_args, .. } = kb.get_term(pa1) else {
        panic!("Positioned must be a Term::Fn");
    };
    assert_eq!(kb.qualified_name_of(*functor), "anthill.reflect.Positioned");
    let got_pos = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "pos").map(|(_, t)| *t);
    let got_int = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "internal").map(|(_, t)| *t);
    assert_eq!(got_pos, Some(site_a), "pos child reads back");
    assert_eq!(got_int, Some(x), "internal child reads back");
}

/// WI-390 (f): `value_to_term` returns `Err` for a term-less residue (the honest
/// signal) rather than panicking or lowering to a lossy term. `Unit` / an anonymous
/// `Tuple` (no functor) take the same `Err` arm as the opaque runtime handles
/// (`Cell`/`Closure`/…) — none of which appear in a spec/cache position.
#[test]
fn value_to_term_errors_on_term_less_residue() {
    use anthill_core::kb::node_occurrence::value_to_term;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    assert!(
        value_to_term(&mut kb, &Value::Unit).is_err(),
        "`Unit` has no term form → Err residue",
    );
    let tup = Value::Tuple {
        pos: vec![Value::Int(1)].into(),
        named: Vec::new().into(),
    };
    assert!(
        value_to_term(&mut kb, &tup).is_err(),
        "an anonymous Tuple (no functor) has no term form → Err residue",
    );
}
