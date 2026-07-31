//! WI-886 — cpp-gen's per-carrier host surface is DATA, and an operation with no C++
//! realization is a codegen error rather than a call to a function that does not exist.
//!
//! THE PRE-FIX MEASUREMENT, driven through `anthill codegen cpp` on a program that
//! codegen'd "successfully" (exit 0, header written, nothing reported):
//!
//! ```text
//!     static bool nanny(double a)              { return isNaN(a); }
//!     static int64_t icmp(int64_t a, int64_t b){ return compare(a, b); }
//!     static int64_t imax(int64_t a, int64_t b){ return max(a, b); }
//!     static bool lo(int64_t a)                { return gt(a, minValue()); }
//! ```
//!
//! Four unresolvable C++ names. The cause was three hand-written Rust tables
//! (`render_as_math_call`, `render_as_math_constant`, and the per-carrier half of
//! `render_as_operator`) enumerating the same surface WI-876 had just given a
//! declarative channel — so they drifted from the rust runtime AND from each other:
//! `Float`'s IEEE predicates and every `Int64` operation WI-876/WI-884 declared were
//! absent, while the comparisons were still keyed on the SPEC op `PartialOrd.gt` that
//! WI-876 had moved to `Float.gt`. The fall-through that emitted them —
//! `Ok(format!("{fn_short}(...)"))` — reported nothing.
//!
//! The tables are gone; `HostOpTable` reads `kb.host_op_mappings()` filtered to
//! `lang == "cpp"`, fed by `rustland/anthill-cpp-gen/anthill/{float,int64}.anthill`.
//!
//! Reference: WI-876 (the channel and its `lang` column), WI-881 (which measured the
//! divergence), WI-879/WI-880 (the same argument for the SLD registry and the
//! remaining spec-op-keyed eval registrations).

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_namespace_header, emit_traits_struct, CodegenContext};
use common::{
    collect_anthill_files, cpp_bindings_dir, find_cxx, load_kb_with, load_kb_with_extras,
    rustland_root, scratch_dir,
};

/// Wrap `body` expressions in a namespace with one operation each and emit the traits
/// struct. Each entry is `(op_name, params, return_type, body)`.
fn emit_ops(ns: &str, ops: &[(&str, &str, &str, &str)]) -> Result<String, String> {
    let decls: String = ops
        .iter()
        .map(|(name, params, ret, body)| {
            format!("            operation {name}({params}) -> {ret} = {body}\n")
        })
        .collect();
    let source = format!(
        r#"
        namespace {ns}
          import anthill.prelude.{{Float, Int64, Bool, String}}
          sort Calc
{decls}          end
        end
    "#
    );
    let mut kb = load_kb_with(&source);
    emit_traits_struct(&mut kb, &format!("{ns}.Calc")).map_err(|e| e.message)
}

/// The cpp `host_fn` template of each named operation, from a stdlib+cpp-bindings KB.
/// Panics on a name with no cpp mapping — every caller is asserting about one it
/// expects to exist, and "absent" would otherwise read as "different".
fn cpp_templates(op_qns: &[&str]) -> std::collections::BTreeMap<String, String> {
    let kb = load_kb_with("\nnamespace test.wi886_map\n  sort S\n  end\nend\n");
    op_qns
        .iter()
        .map(|qn| {
            let m = kb
                .host_op_mappings()
                .iter()
                .find(|m| m.lang == "cpp" && m.op_qn == *qn)
                .unwrap_or_else(|| panic!("{qn} must have a cpp mapping"));
            (m.op_qn.clone(), m.host_fn.clone())
        })
        .collect()
}

// ── The gaps the ticket named ────────────────────────────────────────

/// `Float.isNaN` / `isInfinite` / `isFinite` were in NO cpp table — the whole reason
/// the sort declares them is that `eq` cannot detect NaN, and cpp-gen emitted
/// `isNaN(a)`. `<cmath>`'s `std::isnan` family is the realization.
#[test]
fn float_ieee_predicates_lower_from_the_binding() {
    let cpp = emit_ops("test.wi886_pred", &[
        ("nan1", "a: Float", "Bool", "Float.isNaN(a)"),
        ("inf1", "a: Float", "Bool", "Float.isInfinite(a)"),
        ("fin1", "a: Float", "Bool", "Float.isFinite(a)"),
    ])
    .expect("emit");
    assert!(cpp.contains("return std::isnan(a);"), "isNaN:\n{cpp}");
    assert!(cpp.contains("return std::isinf(a);"), "isInfinite:\n{cpp}");
    assert!(cpp.contains("return std::isfinite(a);"), "isFinite:\n{cpp}");
}

/// The `Int64` half: `max`/`min`/`compare` (WI-876) and `minValue`/`maxValue`
/// (WI-884) were declared on the carrier and unknown to every cpp table.
///
/// `compare` and `sign` need a non-capturing lambda rather than an expression, because
/// the C++ reads each argument twice and a template that repeated `$1` would EVALUATE
/// it twice — the arguments arrive as already-lowered expressions, which may be calls.
#[test]
fn int64_carrier_operations_lower_from_the_binding() {
    let cpp = emit_ops("test.wi886_int", &[
        ("mx", "a: Int64, b: Int64", "Int64", "Int64.max(a, b)"),
        ("mn", "a: Int64, b: Int64", "Int64", "Int64.min(a, b)"),
        ("lo", "n: Int64", "Bool", "Int64.gt(n, Int64.minValue())"),
        ("hi", "n: Int64", "Bool", "Int64.lt(n, Int64.maxValue())"),
        ("cmp", "a: Int64, b: Int64", "Int64", "Int64.compare(a, b)"),
    ])
    .expect("emit");
    assert!(cpp.contains("return std::max(a, b);"), "max:\n{cpp}");
    assert!(cpp.contains("return std::min(a, b);"), "min:\n{cpp}");
    assert!(
        cpp.contains("(n > std::numeric_limits<int64_t>::min())"),
        "minValue:\n{cpp}"
    );
    assert!(
        cpp.contains("(n < std::numeric_limits<int64_t>::max())"),
        "maxValue:\n{cpp}"
    );
    // Each argument appears ONCE at the call, in the lambda's argument list.
    assert!(
        cpp.contains("(l > r) - (l < r)); }(a, b);"),
        "compare must bind its operands rather than repeat them:\n{cpp}"
    );
}

/// A nullary mapping is its template verbatim, and it must reach BOTH call forms —
/// `pi` (a `var_ref`) and `pi()` (a zero-argument apply). WI-881 measured that
/// distinction the hard way on `tau`: a `[simp]` head is an APPLICATION, so it
/// rewrote `tau()` and left the bare spelling dead. A backend that lowered only one
/// of them would have the same half-working shape.
#[test]
fn a_nullary_mapping_lowers_bare_and_applied() {
    // The bare form needs the member IMPORTED — a qualified `Float.pi` without
    // parentheses does not resolve ("expected resolved name, got unresolved"), which
    // is the loader's business and not this backend's.
    let source = r#"
        namespace test.wi886_const
          import anthill.prelude.{Float}
          import anthill.prelude.Float.{pi}
          sort Calc
            operation bare(n: Float) -> Float = pi
            operation applied(n: Float) -> Float = Float.tau()
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.wi886_const.Calc").expect("emit");
    assert!(cpp.contains("return 3.141592653589793;"), "bare pi:\n{cpp}");
    assert!(cpp.contains("return 6.283185307179586;"), "applied tau:\n{cpp}");
}

/// `Float.floor` returns `Int64` in anthill and `double` in `<cmath>`, so the template
/// carries the cast. Without it the value still converted — a `return` statement
/// narrows implicitly — but only because the enclosing signature happened to say
/// `int64_t`.
#[test]
fn a_template_may_state_the_conversion_its_signature_needs() {
    let cpp = emit_ops("test.wi886_floor", &[
        ("fl", "a: Float", "Int64", "Float.floor(a)"),
    ])
    .expect("emit");
    assert!(
        cpp.contains("return static_cast<int64_t>(std::floor(a));"),
        "floor:\n{cpp}"
    );
}

// ── The silent fall-through, now loud ────────────────────────────────

/// THE ACCEPTANCE's second clause. `String` has no `provides String language cpp`
/// block, so `String.length` has no body and no C++ realization — and cpp-gen must say
/// so instead of emitting `length(s)`.
///
/// Asserted on `Err`, not on a `// TODO:` comment in the body: `synthesise_body_for`
/// degrades an unlowerable body into a TODO plus `return {};`, which for THIS class
/// would be less loud than the defect it replaced — `length(s)` at least failed the C++
/// build, while `return {};` compiles and answers zero.
#[test]
fn an_operation_with_no_body_and_no_cpp_realization_is_a_codegen_error() {
    let err = emit_ops("test.wi886_gap", &[
        ("n", "s: String", "Int64", "String.length(s)"),
    ])
    .expect_err("an unrealized operation must refuse the whole emit");
    assert!(
        err.contains("anthill.prelude.String.length"),
        "the message must name the operation: {err}"
    );
    assert!(
        err.contains("provides anthill.prelude.String language cpp"),
        "...and the carrier whose binding block would fix it: {err}"
    );
    assert!(
        err.contains("operation_map"),
        "...and the clause to write: {err}"
    );
}

/// The refusal is scoped to BODY-LESS operations. A user's own bodied operation still
/// lowers to a plain call on the emitted sibling member — that fall-through is correct
/// and must not be caught by the check.
#[test]
fn a_bodied_operation_still_lowers_to_a_plain_call() {
    let cpp = emit_ops("test.wi886_own", &[
        ("twice", "n: Int64", "Int64", "add(n, n)"),
        ("quad", "n: Int64", "Int64", "twice(twice(n))"),
    ])
    .expect("a bodied sibling is emitted in the same struct and callable by name");
    assert!(cpp.contains("return twice(twice(n));"), "sibling call:\n{cpp}");
}

/// `Int64.mod` was MAPPED TO `%` in the deleted operator table, and that was a silent
/// WRONG ANSWER, not merely a missing entry: anthill's `mod` is documented "always
/// non-negative" and C++ `%` follows the DIVIDEND's sign, so `-7 mod 3` answered `-1`
/// where the interpreter answers `2`. `%` realizes `rem`, which is now mapped to it.
///
/// Asserted on the MAPPING rather than on emitted C++ because `Int64.mod` carries an
/// `Error[DivisionByZero]` effect row, so a caller must declare it and the emitted
/// method returns `tl::expected` — machinery that says nothing about this correction.
/// The lambda shape it shares with `sign` and `compare` is compiled and RUN by the
/// end-to-end test below.
#[test]
fn int64_mod_is_the_non_negative_one_and_rem_is_the_c_operator() {
    let m = cpp_templates(&["anthill.prelude.Int64.mod", "anthill.prelude.Int64.rem"]);
    assert_eq!(m["anthill.prelude.Int64.rem"], "($1 % $2)");
    let md = &m["anthill.prelude.Int64.mod"];
    assert!(
        md.contains("((l % r) + r) % r"),
        "mod must correct the sign of C++ `%`, got {md:?}"
    );
}

// ── The table's own checks ───────────────────────────────────────────

/// Build a `CodegenContext` over a `provides Widget language cpp` block whose sole
/// mapping is `template`, and return the refusal. The two malformed-binding tests
/// differ only in the operation's parameter list, the template, and what the message
/// must say — the scaffold around them is the same twenty lines.
fn refuse_binding(ns: &str, params: &str, template: &str) -> String {
    let kb = load_kb_with(&format!(
        r#"
        namespace {ns}
          import anthill.prelude.{{Int64}}
          sort Widget
            entity w(v: Int64)
            operation squish({params}) -> Int64
          end
          provides Widget language cpp
            operation_map {{ squish: "{template}" }}
          end
        end
    "#
    ));
    match CodegenContext::new(&kb) {
        Err(e) => e.message,
        Ok(_) => panic!("{ns}: the template {template:?} must be refused"),
    }
}

/// The cpp peer of the rust registry's arity column (WI-876). Checked when the table
/// is BUILT rather than at a call site, so a binding whose template drops or invents an
/// argument is caught even when nothing calls it.
#[test]
fn a_template_whose_slots_disagree_with_the_arity_is_refused() {
    let err = refuse_binding("test.wi886_arity", "a: Widget, b: Widget", "host_squish($1)");
    assert!(
        err.contains("test.wi886_arity.Widget.squish"),
        "must name the operation: {err}"
    );
    assert!(
        err.contains("takes 2 argument(s)") && err.contains("$1"),
        "must say what disagrees: {err}"
    );
}

/// EXACTLY ONCE, not merely "all present". A template that repeats a slot evaluates
/// that argument twice — the arguments arrive as already-lowered expressions, which may
/// be calls — and it is the rule the binding files' lambdas exist to obey, so the check
/// must actually enforce it rather than accept any set-equal spelling.
#[test]
fn a_template_that_repeats_a_slot_is_refused() {
    let err = refuse_binding("test.wi886_twice", "a: Widget", "($1 > 0 ? $1 : 0)");
    assert!(
        err.contains("EXACTLY ONCE"),
        "must say why repeating is refused: {err}"
    );
}

/// A `$` that introduces nothing is refused too — `"std::fabs($)"` would otherwise
/// reach the emitted C++ verbatim.
#[test]
fn a_malformed_placeholder_is_refused() {
    let err = refuse_binding("test.wi886_malformed", "a: Widget", "host_squish($)");
    assert!(
        err.contains("not followed by an argument index"),
        "unexpected message: {err}"
    );
}

// ── Includes ─────────────────────────────────────────────────────────

/// `<cmath>` used to be an unconditional `ctx.requested_includes` insert inside the
/// deleted math table; it now rides the `IncludeMapping` probes in
/// `stdlib/anthill/realization/cpp_std.anthill`, where cpp's other "host spelling ->
/// header" entries already live.
///
/// ONCE, though three probes matched. `Includes::render` deduped nothing before this
/// ticket, which was invisible while no two probes shared a directive.
#[test]
fn the_cmath_include_comes_from_the_probe_table_exactly_once() {
    let source = r#"
        namespace test.wi886_inc
          import anthill.prelude.{Float, Bool}
          sort Calc
            operation r(x: Float) -> Float = Float.sqrt(x)
            operation m(a: Float, b: Float) -> Float = Float.max(a, b)
            operation n(a: Float) -> Bool = Float.isNaN(a)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi886_inc").expect("emit header");
    assert_eq!(
        header.matches("#include <cmath>").count(),
        1,
        "three cmath spellings, one include:\n{header}"
    );
}

// ── Anti-drift ───────────────────────────────────────────────────────

/// THE CHECK THAT KEEPS THIS FIXED. The ticket's defect was not a missing entry, it
/// was TWO ENUMERATIONS OF ONE SURFACE that nothing reconciled. Both are now
/// `operation_map` data, so the reconciliation is mechanical: every operation the RUST
/// binding realizes for a carrier that also has a cpp binding block must be realized
/// there too.
///
/// Not the converse — cpp maps MORE (`Float.div`, `Int64.abs`, the IEEE predicates),
/// because those are rust builtins registered by hardcoded qualified name rather than
/// through a binding block. That asymmetry is WI-880's, and this test is worded so that
/// closing it makes the check stricter without editing.
///
/// IT ALSO EMITS, which no other test here can: the rest of this file runs on the
/// harness's KB (stdlib directory + cpp bindings), while the CLI's cpp codegen builds
/// stdlib + RUST bindings + cpp bindings (`load_kb_for_cpp_codegen`). That is the only
/// assembly where both languages' binding blocks coexist — duplicate `provides` facts,
/// two `Implementation`s per carrier — and it is the one a user gets. Emitting here is
/// what makes the suite cover it at all.
#[test]
fn every_rust_realized_primitive_operation_is_realized_in_cpp() {
    // The rust-side bindings are NOT part of the cpp-gen harness's KB (it loads
    // `anthill-cpp-gen/anthill/` instead), so this test loads both — the only place in
    // the tree that sees the two enumerations at once, which is the point.
    let rust_bindings = collect_anthill_files(&rustland_root().join("rustland/anthill-stl/anthill"));
    assert!(!rust_bindings.is_empty(), "rust bindings must be readable");
    let mut kb = load_kb_with_extras(
        r#"
        namespace test.wi886_drift
          import anthill.prelude.{Float, Int64, Bool}
          sort Calc
            operation nan1(a: Float) -> Bool = Float.isNaN(a)
            operation mx(a: Int64, b: Int64) -> Int64 = Int64.max(a, b)
          end
        end
    "#,
        &rust_bindings,
    );
    let cpp = emit_traits_struct(&mut kb, "test.wi886_drift.Calc")
        .expect("the CLI's assembly — both languages' bindings loaded — must still emit");
    assert!(
        cpp.contains("std::isnan(a)") && cpp.contains("std::max(a, b)"),
        "the cpp mappings must win with the rust bindings also present:\n{cpp}"
    );

    let of_lang = |lang: &str| -> std::collections::BTreeSet<String> {
        kb.host_op_mappings()
            .iter()
            .filter(|m| m.lang == lang)
            .map(|m| m.op_qn.clone())
            .collect()
    };
    let rust = of_lang("rust");
    let cpp = of_lang("cpp");
    assert!(!rust.is_empty() && !cpp.is_empty(), "both binding sets must be loaded");

    // Carriers with a cpp binding block at all — a carrier with none (String, BigInt)
    // is a known gap, not a drift, and its operations refuse loudly at codegen.
    let cpp_carriers: std::collections::BTreeSet<String> = cpp
        .iter()
        .filter_map(|qn| qn.rsplit_once('.').map(|(c, _)| c.to_string()))
        .collect();

    let missing: Vec<&String> = rust
        .iter()
        .filter(|qn| {
            qn.rsplit_once('.')
                .is_some_and(|(carrier, _)| cpp_carriers.contains(carrier))
        })
        .filter(|qn| !cpp.contains(*qn))
        .collect();
    assert!(
        missing.is_empty(),
        "these operations have a rust host implementation and no C++ one, on carriers \
         that DO have a cpp binding block — add each to \
         rustland/anthill-cpp-gen/anthill/, or the two hosts have parted company \
         again: {missing:?}"
    );
}

/// THE OTHER HALF OF THE SPLIT. `operation_map` says how an operation is spelled;
/// `cpp_std.anthill`'s `IncludeMapping` probes say which header a spelling needs. That
/// seam is right — one is per-carrier and one-to-one, the other carrier-independent and
/// many-to-one (23 spellings share `<cmath>`) — but nothing reconciled the two, and the
/// consequence is stated in `cpp_std.anthill` itself: "A mapping whose spelling is not
/// probed there emits a header that does not compile."
///
/// Reconciled here rather than by the end-to-end compile test, which `return`s silently
/// when no C++ compiler is installed — a guard that can be absent is not a guard.
///
/// Matching is by SUBSTRING because that is what `Includes::scan` does, so this test
/// agrees with the mechanism rather than with an idealization of it: `std::log` covers
/// `std::log10` and `std::log2`, and `std::isgreater` covers `std::isgreaterequal`.
#[test]
fn every_std_spelling_a_cpp_mapping_emits_has_an_include_probe() {
    let mut kb = load_kb_with("\nnamespace test.wi886_probes\n  sort S\n  end\nend\n");

    let probes = include_mapping_host_types(&mut kb);
    assert!(!probes.is_empty(), "the cpp IncludeMapping table must be loaded");

    let mut unprobed: Vec<String> = Vec::new();
    for m in kb.host_op_mappings().iter().filter(|m| m.lang == "cpp") {
        for spelling in std_identifiers(&m.host_fn) {
            if !probes.iter().any(|p| spelling.contains(p.as_str())) {
                unprobed.push(format!("{} -> {spelling}", m.op_qn));
            }
        }
    }
    unprobed.sort();
    unprobed.dedup();
    assert!(
        unprobed.is_empty(),
        "these `std::` spellings appear in a cpp operation_map and no `IncludeMapping` \
         probe in stdlib/anthill/realization/cpp_std.anthill matches them, so a header \
         using them is emitted without its `#include`: {unprobed:?}"
    );
}

/// Every `host_type` of a cpp `IncludeMapping` fact, read the same way `Includes`
/// reads them — through the KB, so the test cannot drift from the file.
fn include_mapping_host_types(kb: &mut anthill_core::kb::KnowledgeBase) -> Vec<String> {
    let sym = kb
        .try_resolve_symbol("anthill.realization.IncludeMapping")
        .expect("the realization vocabulary is loaded");
    let lang = kb.intern("lang");
    let host_type = kb.intern("host_type");
    let string_arg = |rid, key| {
        kb.fact_head_named_args(rid).and_then(|named| {
            named.iter().find(|(k, _)| *k == key).and_then(|(_, v)| match kb.get_term(*v) {
                anthill_core::kb::term::Term::Const(
                    anthill_core::kb::term::Literal::String(s),
                ) => Some(s.clone()),
                _ => None,
            })
        })
    };
    kb.rules_by_functor_iter(sym)
        .filter(|rid| kb.is_fact(*rid))
        .filter(|rid| string_arg(*rid, lang).as_deref() == Some("cpp"))
        .filter_map(|rid| string_arg(rid, host_type))
        .collect()
}

/// The `std::`-prefixed identifiers a C++ expression template names — what
/// `Includes::scan` will be looking for in the emitted text.
fn std_identifiers(template: &str) -> Vec<String> {
    let mut out = Vec::new();
    let bytes = template.as_bytes();
    let mut i = 0;
    while let Some(off) = template[i..].find("std::") {
        let start = i + off;
        let mut end = start + "std::".len();
        while end < bytes.len()
            && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_' || bytes[end] == b':')
        {
            end += 1;
        }
        // Trim a trailing `::` so `std::numeric_limits<int64_t>::min` contributes the
        // spelling `std::numeric_limits`, which is what the probe table carries.
        let spelling = template[start..end].trim_end_matches(':');
        out.push(spelling.split('<').next().unwrap_or(spelling).to_string());
        i = end;
    }
    out
}

/// `BINDING_SOURCES` (embedded, what a shipped binary loads) against the directory
/// (what this crate's tests walk). Two readers of one file set; the anthill-stl
/// `stdlib_drift_test` guards the same seam for the rust bindings.
#[test]
fn binding_sources_match_on_disk() {
    // Keyed on the path RELATIVE TO the binding root, not the bare file stem: the
    // directory is flat today, and a bare stem would let `anthill/sub/float.anthill`
    // compare equal to `anthill/float.anthill` on the day it is not.
    let root = cpp_bindings_dir().canonicalize().expect("binding dir");
    let on_disk: std::collections::BTreeSet<String> = collect_anthill_files(&root)
        .iter()
        .map(|p| {
            p.strip_prefix(&root)
                .expect("collected under the binding root")
                .with_extension("")
                .to_string_lossy()
                .replace('\\', "/")
        })
        .collect();
    let embedded: std::collections::BTreeSet<String> = anthill_cpp_gen::BINDING_SOURCES
        .iter()
        .map(|(label, _)| {
            label
                .strip_prefix("rustland/anthill-cpp-gen/")
                .unwrap_or(label)
                .to_string()
        })
        .collect();
    assert_eq!(
        on_disk, embedded,
        "anthill_cpp_gen::BINDING_SOURCES drifted from anthill-cpp-gen/anthill/ — a \
         binding reachable from only one of the two is loaded by only one of the CLI \
         and the tests"
    );
}

// ── End to end ───────────────────────────────────────────────────────

/// THE ACCEPTANCE's third clause: a program using `Float.isNaN` and `Float.max`
/// generates C++ that COMPILES — and, since compiling proves only that the names
/// resolve, that computes the right answers.
#[test]
fn a_header_using_the_mapped_operations_compiles_and_runs() {
    let source = r#"
        namespace test.wi886_e2e
          import anthill.prelude.{Float, Int64, Bool}
          sort Calc
            operation nan1(a: Float) -> Bool = Float.isNaN(a)
            operation peak(a: Float, b: Float) -> Float = Float.max(a, b)
            operation cmp(a: Int64, b: Int64) -> Int64 = Int64.compare(a, b)
            operation sgn(a: Int64) -> Int64 = Int64.sign(a)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.wi886_e2e").expect("emit header");

    let Some(cxx) = find_cxx() else {
        eprintln!("no C++ compiler available — skipping compile check");
        return;
    };
    let dir = scratch_dir("wi886_e2e");
    let header_path = dir.join("wi886_e2e.hpp");
    std::fs::write(&header_path, &header).expect("write header");

    let driver = format!(
        r#"#include "{}"
#include <cstdio>
int main() {{
    using C = test::wi886_e2e::Calc;
    int bad = 0;
    if (!C::nan1(0.0 / 0.0))            {{ printf("nan1(nan)\n");      bad = 1; }}
    if (C::nan1(1.0))                   {{ printf("nan1(1.0)\n");      bad = 1; }}
    if (C::peak(1.5, 2.25) != 2.25)     {{ printf("peak\n");           bad = 1; }}
    if (!C::nan1(C::peak(0.0 / 0.0, 0.0 / 0.0))) {{ printf("peak nan\n"); bad = 1; }}
    if (C::peak(0.0 / 0.0, 1.5) != 1.5) {{ printf("peak absorbs nan\n"); bad = 1; }}
    if (C::cmp(2, 9) != -1)             {{ printf("cmp lt\n");         bad = 1; }}
    if (C::cmp(9, 2) != 1)              {{ printf("cmp gt\n");         bad = 1; }}
    if (C::cmp(2, 2) != 0)              {{ printf("cmp eq\n");         bad = 1; }}
    if (C::sgn(-7) != -1)               {{ printf("sgn\n");            bad = 1; }}
    return bad;
}}
"#,
        header_path.display()
    );
    let driver_path = dir.join("driver.cpp");
    std::fs::write(&driver_path, &driver).expect("write driver");
    let bin_path = dir.join("driver");

    let build = Command::new(cxx)
        .args(["-std=c++17", "-Wall", "-Wextra", "-Werror"])
        .arg(&driver_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .expect("invoke compiler");
    assert!(
        build.status.success(),
        "C++ compile failed (compiler: {cxx})\n\
         ── header ───────────────\n{header}\n\
         ── stderr ───────────────\n{}",
        String::from_utf8_lossy(&build.stderr)
    );

    let run = Command::new(&bin_path).output().expect("run driver");
    assert!(
        run.status.success(),
        "generated C++ compiled but computed the wrong answers:\n{}\n── header ──\n{header}",
        String::from_utf8_lossy(&run.stdout)
    );

    let _ = std::fs::remove_dir_all(&dir);
}
