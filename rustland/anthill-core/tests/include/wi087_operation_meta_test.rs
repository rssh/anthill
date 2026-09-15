//! WI-087 — operation attributes / metadata, the kernel mechanism.
//!
//! The surface is the operation's trailing block, `@[Marker, Key: value]`
//! (WI-20260915-G9EA9). WI-087 introduced a keyword clause, `meta [...]`, because a
//! bare `[...]` right after the return type was grabbed as return-type application
//! args (`-> Vec3[...]`); the `@[` token cannot continue a type, so the clause is
//! retired and refused. The loader lowers the block into a `meta(key: value, ...)`
//! term — the same shape and reader idiom rule/fact meta already use — and rides it
//! as the `OperationInfo.meta` field (the chosen representation: one record per op).
//!
//! Three driving use cases, all on the one mechanism:
//!   1. a named marker flag for a lowering pattern (`Vec3FromConstDoublePtr3`),
//!   2. a profile/dispatch hint (`Profile: "cpp20-stl"`),
//!   3. a verbatim host-language body escape hatch (`CppBody: "..."`).
//!
//! Claims:
//!   - the attributes survive load and read back through `lookup_operation_info`;
//!   - a flag attribute is detected by `meta_has_flag`, a valued attribute is
//!     extracted by `meta_value` (the readers downstream codegen uses);
//!   - an operation with no `meta_block` reports `meta == None` (empty `meta()`);
//!   - the `meta`-bearing `OperationInfo` fact stays SLD-queryable.

use anthill_core::intern::Symbol;
use anthill_core::kb::load::{meta_has_flag, meta_value};
use anthill_core::kb::op_info;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

use crate::common::load_kb_with;

/// One sort with two operations: `get_values` carries all three attribute
/// forms (flag marker, string-valued Profile, string-valued CppBody);
/// `plain` carries none. Bodyless ops — only the signature + meta matter.
const SRC: &str = r#"
namespace test.wi087_meta
  import anthill.prelude.{Int64, Float}

  sort Vec3
    entity vec3(x: Float, y: Float, z: Float)
  end

  sort GPS
    operation get_values(self: GPS) -> Vec3
      @[Vec3FromConstDoublePtr3, Profile: "cpp20-stl", CppBody: "return readVec3(self->getValues());"]
    operation plain(self: GPS) -> Int64
  end
end
"#;

const GET_VALUES_QN: &str = "test.wi087_meta.GPS.get_values";
const PLAIN_QN: &str = "test.wi087_meta.GPS.plain";

fn op_sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
    kb.try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("op symbol `{qn}` after load"))
}

/// A string-literal `meta_value` extracted as a Rust `String`.
fn meta_string(kb: &KnowledgeBase, meta: Option<TermId>, key: &str) -> Option<String> {
    match meta_value(kb, meta, key).map(|t| kb.get_term(t)) {
        Some(Term::Const(Literal::String(s))) => Some(s.clone()),
        _ => None,
    }
}

#[test]
fn operation_meta_block_surfaces_on_operation_info() {
    let kb = load_kb_with(SRC);
    let op = op_sym(&kb, GET_VALUES_QN);

    let rec =
        op_info::lookup_operation_info(&kb, op).expect("lookup_operation_info for get_values");
    let meta = rec.meta;
    assert!(
        meta.is_some(),
        "an operation with a meta_block must carry a non-empty `meta`"
    );

    // (1) Flag marker — presence only, value is `Bottom`.
    assert!(
        meta_has_flag(&kb, meta, "Vec3FromConstDoublePtr3"),
        "the `Vec3FromConstDoublePtr3` marker must be detectable via meta_has_flag",
    );
    // A key never written must not spuriously match.
    assert!(
        !meta_has_flag(&kb, meta, "Vec4FromConstDoublePtr4"),
        "an absent marker must not be reported present",
    );

    // (2) Profile hint — string value extracted.
    assert_eq!(
        meta_string(&kb, meta, "Profile").as_deref(),
        Some("cpp20-stl"),
        "the `Profile` attribute value must read back verbatim",
    );

    // (3) Verbatim host body escape hatch — string value extracted.
    assert_eq!(
        meta_string(&kb, meta, "CppBody").as_deref(),
        Some("return readVec3(self->getValues());"),
        "the `CppBody` attribute value must read back verbatim",
    );
}

#[test]
fn operation_without_meta_block_reports_none() {
    let kb = load_kb_with(SRC);
    let op = op_sym(&kb, PLAIN_QN);

    let rec = op_info::lookup_operation_info(&kb, op).expect("lookup_operation_info for plain");
    assert!(
        rec.meta.is_none(),
        "an operation with no meta_block must report `meta == None` (empty meta()), got {:?}",
        rec.meta,
    );
    // And of course no flag matches on the empty meta.
    assert!(!meta_has_flag(&kb, rec.meta, "Vec3FromConstDoublePtr3"));
}

/// An operation has ONE block. WI-087's clauses merged when repeated, and a clause
/// beside a trailing block silently shadowed it; with one trailing `@[...]` a second
/// block is not a second spelling to reconcile but a syntax error.
#[test]
fn a_second_block_is_refused() {
    let errs = crate::common::parse_errs(
        "namespace test.wi087_two
  import anthill.prelude.{Int64}
  operation merged() -> Int64 @[MarkerA] @[MarkerB]
end
",
    );
    crate::common::assert_refused_naming(&errs, &["syntax error"], "second block");
}

/// WI-20260915-G9EA9 acceptance (4): the retired `meta [...]` clause is refused, and
/// the refusal says what to write. CONTROL: on the pre-G9EA9 grammar this source
/// parsed clean (it was the only operation block spelling), so the test fails there.
#[test]
fn the_retired_meta_clause_is_refused_naming_the_block() {
    let errs = crate::common::parse_errs(
        "namespace test.wi087_clause
  import anthill.prelude.{Int64}
  operation get() -> Int64
    meta [MarkerA]
end
",
    );
    crate::common::assert_refused_naming(
        &errs,
        &["`meta [MarkerA]` clause was removed", "`@[MarkerA]`"],
        "retired meta clause",
    );
}

/// The added field must not break SLD-queryability: a full-arity goal binding
/// `name` to the op and `meta` to a fresh var still resolves the fact (the
/// discrimination tree keys on total arity — the WI-348 contract, now with 8
/// fields).
#[test]
fn meta_bearing_operation_info_is_sld_queryable() {
    let mut kb = load_kb_with(SRC);
    let op = op_sym(&kb, GET_VALUES_QN);

    let op_info_sym = kb
        .try_resolve_symbol("anthill.reflect.OperationInfo")
        .unwrap();
    let name_ref = kb.alloc(Term::Ref(op));

    let fields = [
        "name",
        "params",
        "return_type",
        "effects",
        "requires",
        "ensures",
        "type_params",
        "meta",
    ];
    let named_args: SmallVec<[(Symbol, TermId); 2]> = fields
        .iter()
        .map(|field| {
            let key = kb.intern(field);
            let val = if *field == "name" {
                name_ref
            } else {
                let v = kb.fresh_var(key);
                kb.alloc(Term::Var(Var::Global(v)))
            };
            (key, val)
        })
        .collect();
    let goal = kb.alloc(Term::Fn {
        functor: op_info_sym,
        pos_args: SmallVec::new(),
        named_args,
    });

    let config = ResolveConfig {
        max_solutions: 16,
        ..ResolveConfig::default()
    };
    let solutions = kb.resolve(&[goal], &config);
    assert!(
        !solutions.is_empty(),
        "an OperationInfo fact carrying a `meta` field must remain SLD-queryable",
    );
}
