//! WI-20260914-Z73FX: reflect can say what a scope may name.
//!
//! `internal entity mk(…)` and `entity mk(…) @[internal]` are ONE statement in two
//! spellings, decided at parse (`convert_declaration_attributes`): both hide the name
//! from another scope, and both publish `internal` in the declaration's meta. Reflect
//! gains the kernel's own readers — `visible_from`, `meta_has_flag`, `meta_value` —
//! each driven here from an anthill body. The guardians constructors the
//! ticket names are driven in `guardians_test.rs`, beside the checker they protect.
//!
//! WHY THE READERS ARE DRIVEN FROM A BODY AND NOT FROM A RULE BODY. Measured, and it is
//! not this ticket's: a host operation called in a rule body with a STRING-LITERAL
//! argument does not reduce. `term_functor_name(?m) = some("meta")` over a
//! `DeclarationMeta` join answers 923 definite, and `Bool.and(true, false) = false`
//! answers 1 — but `term_field(7, "x") = none()`, the SHIPPED two-argument reflect
//! accessor, flounders exactly as `meta_has_flag(?m, "internal") = true` does. So the
//! gap is the argument, it predates these bindings, and `describe` — the consumer this
//! ticket exists for — is an operation body, which is where the rows below drive.
//!
//! BACKED OUT (the flag no longer sets `visibility`): `a_flag_hides_a_name_as_the_modifier_does`
//! loads the flagged consumer clean, and `both_spellings_publish_the_flag` loses the
//! modifier rows (no `internal` entry). The spelling-refusal tests fail with a clean
//! parse. The `visible_from` / `meta_*` rows fail with `OperationBodyMissing` without
//! the mapping. The unflagged rows are CONTROLS that pass either way by design.

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;

use crate::common::{assert_refused_naming, parse_errs};

/// A sort whose constructor `mk` is declared as `{decl}`, and a public `make` using it
/// from inside — the WI-369 `Box` shape.
fn box_src(decl: &str) -> String {
    format!(
        "sort test.z73fx.box.Box\n  import anthill.prelude.Int64\n  {decl}\n  \
         operation make(x: Int64) -> Box = mk(v: x)\n  sort Inner\n    \
         operation peek(x: Int64) -> Box = mk(v: x)\n  end\nend\n"
    )
}

/// Another namespace constructing `mk` directly — refused iff `mk` is internal.
const SNEAK: &str = r#"
namespace test.z73fx.outside
  import anthill.prelude.Int64
  import test.z73fx.box.Box
  operation sneak(x: Int64) -> Box = Box.mk(v: x)
end
"#;

#[test]
fn a_flag_hides_a_name_as_the_modifier_does() {
    for decl in ["internal entity mk(v: Int64)", "entity mk(v: Int64) @[internal]"] {
        let errs = crate::common::try_load_kb_with_files(&[&box_src(decl), SNEAK])
            .err()
            .unwrap_or_else(|| panic!("`{decl}`: constructing `mk` from outside must be refused"));
        assert_refused_naming(&errs, &["mk", "is internal to"], decl);
        // Inside the sort, and inside a sort nested in it, `mk` still resolves.
        crate::common::load_kb_with(&box_src(decl));
    }
    // CONTROL: unflagged, the same consumer loads — the refusal above is the flag's.
    crate::common::load_kb_with(&format!("{}{SNEAK}", box_src("entity mk(v: Int64)")));
}

#[test]
fn an_operation_and_a_const_flag_hide_them_too() {
    const LIB: &str = r#"
namespace test.z73fx.lib
  import anthill.prelude.Int64
  operation helper() -> Int64 = 1 @[internal]
  const SEED: Int64 = 2 @[internal]
  operation api() -> Int64 = helper() + SEED
end
"#;
    for (use_, name) in [("helper()", "helper"), ("SEED", "SEED")] {
        let consumer = format!(
            "namespace test.z73fx.user\n  import anthill.prelude.Int64\n  \
             import test.z73fx.lib.{{{name}}}\n  operation f() -> Int64 = {use_}\nend\n"
        );
        let errs = crate::common::try_load_kb_with_files(&[LIB, &consumer])
            .err()
            .unwrap_or_else(|| panic!("importing the flagged `{name}` must be refused"));
        assert_refused_naming(&errs, &[name, "is internal to"], name);
    }
    // The flagged names still serve their own namespace: `api` runs.
    let mut interp = crate::common::interp_for(LIB);
    match interp.call("test.z73fx.lib.api", &[]) {
        Ok(Value::Int(3)) => {}
        other => panic!("`api` uses its namespace's internal names; got {other:?}"),
    }
}

/// The eight declarations, and the rows that reach each one's block. `Subject` and the
/// readers live in the SAME namespace as the declarations, because an internal name is
/// not nameable from anywhere else — which is the rule this file is about.
const SPELLINGS: &str = r#"
namespace test.z73fx.spell
  import anthill.prelude.Int64
  import anthill.reflect.{DeclarationMeta, Term}
  internal entity a(n: Int64)
  entity b(n: Int64) @[internal]
  entity c(n: Int64)
  public entity d(n: Int64)
  entity e(n: Int64) @[public]
  entity h(n: Int64) @[Marker, Key: 7]
  internal operation f() -> Int64 = 1
  operation g() -> Int64 = 1 @[internal, Marker]
  sort Hidden = Int64 @[internal]
  internal sort Shy = Int64

  entity Subject(key: Int64, name: Term)
  fact Subject(key: 0, name: a)
  fact Subject(key: 1, name: b)
  fact Subject(key: 2, name: c)
  fact Subject(key: 3, name: d)
  fact Subject(key: 4, name: e)
  fact Subject(key: 5, name: h)
  fact Subject(key: 6, name: f)
  fact Subject(key: 7, name: g)
  fact Subject(key: 8, name: Hidden)
  fact Subject(key: 9, name: Shy)
  rule block0(?m) :- Subject(key: 0, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)
  rule block1(?m) :- Subject(key: 1, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)
  rule block2(?m) :- Subject(key: 2, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)
  rule block3(?m) :- Subject(key: 3, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)
  rule block4(?m) :- Subject(key: 4, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)
  rule block5(?m) :- Subject(key: 5, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)
  rule block6(?m) :- Subject(key: 6, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)
  rule block7(?m) :- Subject(key: 7, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)
  rule block8(?m) :- Subject(key: 8, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)
  rule block9(?m) :- Subject(key: 9, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)
end
"#;

/// Each declaration's block, read through the join a consumer uses (`DeclarationMeta`
/// by name), keyed by the `Subject` row that names it — a name no rule body may spell.
fn spelling_blocks(kb: &mut KnowledgeBase) -> Vec<Value> {
    (0..10)
        .map(|i| {
            let rows = crate::common::query_unary(kb, &format!("test.z73fx.spell.block{i}"));
            assert_eq!(rows.len(), 1, "declaration {i} has exactly one row: {rows:?}");
            let (meta, definite) = rows.into_iter().next().unwrap();
            assert!(definite, "declaration {i}'s row decides");
            meta
        })
        .collect()
}
#[test]
fn both_spellings_publish_the_flag() {
    let mut kb = crate::common::load_kb_with(&format!("{SPELLINGS}{PROBE}"));
    let blocks = spelling_blocks(&mut kb);
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp).unwrap();
    // DRIVEN THROUGH THE DECLARED OPERATION, not the kernel helper behind it: `has` is
    // an anthill body calling `anthill.reflect.meta_has_flag`, which is how a renderer
    // of a candidate's view reads a block.
    let mut has = |meta: &Value, key: &str| -> bool {
        match interp.call("test.z73fx.probe.has", &[meta.clone(), Value::Str(key.into())]) {
            Ok(Value::Bool(b)) => b,
            other => panic!("meta_has_flag from a body: {other:?}"),
        }
    };
    for (i, name, internal) in [
        (0, "internal entity a", true),
        (1, "entity b @[internal]", true),
        (2, "entity c (unflagged CONTROL)", false),
        (3, "public entity d", false),
        (4, "entity e @[public]", false),
        (5, "entity h @[Marker, Key: 7] (CONTROL: a block with no visibility flag)", false),
        (6, "internal operation f", true),
        (7, "operation g @[internal, Marker]", true),
        (8, "sort Hidden = Int64 @[internal]", true),
        (9, "internal sort Shy = Int64", true),
    ] {
        assert_eq!(
            has(&blocks[i], "internal"),
            internal,
            "{name}: the modifier and the flag are one statement"
        );
        assert!(
            !has(&blocks[i], "public"),
            "{name}: `public` is the default — neither spelling records a flag"
        );
    }
    assert!(
        has(&blocks[5], "Marker") && has(&blocks[7], "Marker"),
        "CONTROL for the rows above: the same reader over another key answers, and `g`'s \
         own entry survives the visibility flag being decided out of its block"
    );
    // The operation's own reflect record says it too — §5.8's `OperationInfo.meta`.
    for op in ["f", "g"] {
        let sym = interp
            .kb()
            .try_resolve_symbol(&format!("test.z73fx.spell.{op}"))
            .unwrap();
        let rec = anthill_core::kb::op_info::lookup_operation_info(interp.kb(), sym)
            .expect("an operation");
        assert!(
            anthill_core::kb::load::meta_has_flag(interp.kb(), rec.meta, "internal"),
            "`{op}`'s OperationInfo.meta carries `internal`"
        );
    }
}

#[test]
fn a_contradiction_is_refused_naming_both_spellings() {
    for (src, first, second) in [
        ("internal entity x @[public]", "`internal`", "`@[public]`"),
        ("public entity x @[internal]", "`public`", "`@[internal]`"),
        ("entity x @[internal, public]", "`@[internal]`", "`@[public]`"),
        ("internal operation f() -> Int64 = 1 @[public]", "`internal`", "`@[public]`"),
        ("sort T = ? @[public, internal]", "`@[public]`", "`@[internal]`"),
    ] {
        let errs = parse_errs(&format!("namespace test.z73fx.c\n  {src}\nend\n"));
        assert_refused_naming(&errs, &[first, second, "contradict"], src);
    }
    // CONTROL: agreeing spellings are one statement said twice, not a contradiction.
    for src in ["internal entity x @[internal]", "public entity x @[public]", "entity x @[public]"] {
        anthill_core::parse::parse(&format!("namespace test.z73fx.c\n  {src}\nend\n"))
            .unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"));
    }
}

#[test]
fn a_visibility_flag_with_a_value_is_refused() {
    // `meta_has_flag` reads any value as present, so `@[internal: false]` would HIDE.
    for (src, flag) in [
        ("entity x @[internal: false]", "`@[internal]`"),
        ("entity x @[public: true]", "`@[public]`"),
    ] {
        let errs = parse_errs(&format!("namespace test.z73fx.v\n  {src}\nend\n"));
        assert_refused_naming(&errs, &[flag, "takes no value"], src);
    }
}

#[test]
fn a_clause_flag_is_refused_naming_where_the_modifier_is_legal() {
    for (src, what) in [
        ("fact p(1) @[internal]", "`@[internal]` on a fact"),
        ("rule q(?x) :- p(?x) @[internal]", "`@[internal]` on a rule"),
        ("rule q(?x) :- p(?x) @[public]", "`@[public]` on a rule"),
        ("constraint small: p(?x) :- ?x > 9 @[internal]", "`@[internal]` on a constraint"),
        ("rule {\n    q(?x) :- p(?x) @[internal]\n  }", "`@[internal]` on a rule entry"),
        (
            "rule t(1)\n  proof t\n    rule s1: t(1) @[internal] by derivation\n  end",
            "`@[internal]` on a proof step",
        ),
    ] {
        let errs = parse_errs(&format!("namespace test.z73fx.k\n  {src}\nend\n"));
        assert_refused_naming(&errs, &[what, "entity, operation or const"], src);
    }
    // CONTROL: the same clauses with another key parse — the refusal is the flag's.
    anthill_core::parse::parse(
        "namespace test.z73fx.k\n  fact p(1) @[Marker]\n  rule q(?x) :- p(?x) @[Marker]\nend\n",
    )
    .expect("a clause block without a visibility flag parses");
}

const PROBE: &str = r#"
namespace test.z73fx.probe
  import anthill.prelude.{Bool, String, Option}
  import anthill.reflect.{Symbol, Term, visible_from, meta_has_flag, meta_value, as_term}
  operation vis(s: Symbol, scope: Symbol) -> Bool = visible_from(s, scope)
  operation has(m: Term, k: String) -> Bool = meta_has_flag(m, k)
  operation value(m: Term, k: String) -> Option[T = Term] = meta_value(m, k)
  operation not_meta() -> Bool = meta_has_flag(as_term(Option.some(3)), "value")
end
"#;

#[test]
fn visible_from_answers_where_it_is_asked() {
    for decl in ["internal entity mk(v: Int64)", "entity mk(v: Int64) @[internal]"] {
        let outside = "namespace test.z73fx.elsewhere\n  import anthill.prelude.Int64\n  \
                       operation open() -> Int64 = 1\nend\n";
        let kb = crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[
            &box_src(decl),
            outside,
            PROBE,
        ]));
        let mut interp = anthill_core::eval::Interpreter::new(kb);
        anthill_core::eval::builtins::register_standard_builtins(&mut interp).unwrap();
        for (s, scope, want, why) in [
            ("test.z73fx.box.Box.mk", "test.z73fx.box.Box", true, "its own sort"),
            ("test.z73fx.box.Box.mk", "test.z73fx.box.Box.Inner", true, "a sort nested in it"),
            ("test.z73fx.box.Box.mk", "test.z73fx.elsewhere", false, "another namespace"),
            (
                "test.z73fx.box.Box.make",
                "test.z73fx.elsewhere",
                true,
                "CONTROL: the public sibling — a query answering false for everything fails here",
            ),
            (
                "test.z73fx.elsewhere.open",
                "test.z73fx.box.Box",
                true,
                "CONTROL: a non-internal name in ANOTHER namespace — a query that only \
                 reports `same scope` fails here",
            ),
        ] {
            let args = [crate::common::symbol_term(&mut interp, s), crate::common::symbol_term(&mut interp, scope)];
            match interp.call("test.z73fx.probe.vis", &args) {
                Ok(Value::Bool(b)) => assert_eq!(b, want, "`{decl}`: {s} from {scope} ({why})"),
                other => panic!("`{decl}`: {s} from {scope}: {other:?}"),
            }
        }
    }
}

/// One `test.z73fx.probe.<op>(meta, key)` call.
fn probe_call(
    interp: &mut anthill_core::eval::Interpreter,
    op: &str,
    meta: &Value,
    key: &str,
) -> Value {
    interp
        .call(
            &format!("test.z73fx.probe.{op}"),
            &[meta.clone(), Value::Str(key.into())],
        )
        .unwrap_or_else(|e| panic!("{op}({key}): {e:?}"))
}

#[test]
fn meta_readers_answer_from_a_body() {
    let mut kb = crate::common::load_kb_with(&format!("{SPELLINGS}{PROBE}"));
    // `h`'s block is the valued one (`@[Marker, Key: 7]`).
    let meta = spelling_blocks(&mut kb).remove(5);
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp).unwrap();

    let some7 = probe_call(&mut interp, "value", &meta, "Key");
    let Value::Entity { named, .. } = &some7 else {
        panic!("`Key` has a written value, so `some(…)`: {some7:?}")
    };
    let inner = named
        .iter()
        .find_map(|(k, v)| (interp.kb().local_name_of(*k) == "value").then(|| v.clone()))
        .unwrap_or_else(|| panic!("`some(value: …)`: {some7:?}"));
    assert_eq!(
        interp.kb().get_term(inner.expect_term()),
        &Term::Const(anthill_core::kb::term::Literal::Int(7)),
        "`Key: 7` reads its value back through the declared operation"
    );
    for (key, why) in [
        ("Marker", "a flag has no written value, so `none()` — presence is `meta_has_flag`'s"),
        ("Absent", "CONTROL: an absent key answers the same way, and neither faults"),
    ] {
        let v = probe_call(&mut interp, "value", &meta, key);
        assert!(
            matches!(&v, Value::Entity { named, .. } if named.is_empty()),
            "`{key}`: {why}; got {v:?}"
        );
    }
    // THE REFUSAL, asserted on its MESSAGE and not merely on `Err`: `Err(_)` is also what
    // an unregistered `as_term`, or an unmapped `meta_has_flag`, would produce, so the row
    // would stay green with the refusal backed out (/code-review).
    match interp.call("test.z73fx.probe.not_meta", &[]) {
        Err(e) => {
            let msg = format!("{e:?}");
            assert!(
                msg.contains("meta(…)"),
                "a term that is not `meta(…)` is refused BY NAME — the kernel readers match \
                 a KEY, so `some(value: 3)` would otherwise answer about `value`; got {msg}"
            );
        }
        Ok(v) => panic!("a term that is not `meta(…)` is refused, not searched; got {v:?}"),
    }
}
