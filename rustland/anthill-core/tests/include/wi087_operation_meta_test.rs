//! WI-087 — operation attributes / metadata, the kernel mechanism.
//!
//! The surface vehicle is a keyword-introduced `meta [...]` clause (WI shape A)
//! carrying the existing `meta_block` payload (`[Marker, Key: value]`). The
//! `meta` keyword is needed because a bare `[...]` right after the return type
//! is grabbed as return-type application args (`-> Vec3[...]`) — which fails for
//! the clauseless getter bindings that actually carry codegen markers. The
//! loader lowers the block into a `meta(key: value, ...)` term — the same shape
//! and reader idiom rule/fact meta already use — and rides it as the
//! `OperationInfo.meta` field (the chosen representation: one record per op).
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

use anthill_core::kb::load::{meta_has_flag, meta_value};
use anthill_core::kb::op_info;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::intern::Symbol;
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
      meta [Vec3FromConstDoublePtr3, Profile: "cpp20-stl", CppBody: "return readVec3(self->getValues());"]
    operation plain(self: GPS) -> Int64
    operation merged(self: GPS) -> Int64
      meta [MarkerA]
      meta [MarkerB, Profile: "p2"]
  end
end
"#;

const GET_VALUES_QN: &str = "test.wi087_meta.GPS.get_values";
const PLAIN_QN: &str = "test.wi087_meta.GPS.plain";
const MERGED_QN: &str = "test.wi087_meta.GPS.merged";

fn op_sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
    kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("op symbol `{qn}` after load"))
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

    let rec = op_info::lookup_operation_info(&kb, op)
        .expect("lookup_operation_info for get_values");
    let meta = rec.meta;
    assert!(meta.is_some(), "an operation with a meta_block must carry a non-empty `meta`");

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

    let rec = op_info::lookup_operation_info(&kb, op)
        .expect("lookup_operation_info for plain");
    assert!(
        rec.meta.is_none(),
        "an operation with no meta_block must report `meta == None` (empty meta()), got {:?}",
        rec.meta,
    );
    // And of course no flag matches on the empty meta.
    assert!(!meta_has_flag(&kb, rec.meta, "Vec3FromConstDoublePtr3"));
}

/// Repeated `meta [...]` clauses on one operation accumulate (merge) — they are
/// not silently overwritten by the last, matching how effects / requires /
/// ensures accumulate across clauses.
#[test]
fn multiple_meta_clauses_merge() {
    let kb = load_kb_with(SRC);
    let op = op_sym(&kb, MERGED_QN);

    let rec = op_info::lookup_operation_info(&kb, op)
        .expect("lookup_operation_info for merged");
    assert!(
        meta_has_flag(&kb, rec.meta, "MarkerA"),
        "the first `meta` clause's marker must survive a second `meta` clause",
    );
    assert!(
        meta_has_flag(&kb, rec.meta, "MarkerB"),
        "the second `meta` clause's marker must be present",
    );
    assert_eq!(
        meta_string(&kb, rec.meta, "Profile").as_deref(),
        Some("p2"),
        "a valued attribute in a later `meta` clause must be readable",
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

    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo").unwrap();
    let name_ref = kb.alloc(Term::Ref(op));

    let fields = ["name", "params", "return_type", "effects", "requires", "ensures", "type_params", "meta"];
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

    let config = ResolveConfig { max_solutions: 16, ..ResolveConfig::default() };
    let solutions = kb.resolve(&[goal], &config);
    assert!(
        !solutions.is_empty(),
        "an OperationInfo fact carrying a `meta` field must remain SLD-queryable",
    );
}
