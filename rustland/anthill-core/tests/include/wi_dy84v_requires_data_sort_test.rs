//! WI-20261113-DY84V — proposal 074 stage 5: A `requires` NAMING A SORT WITH CONSTRUCTORS IS
//! REFUSED (`docs/proposals/074-typeclass-instance-is-a-dictionary.md` §2, "A sort with
//! constructors is closed"; kernel-language §5.1, §8.2).
//!
//! A sort with constructors is closed, written `sort` or `enum` alike: nothing joins it by
//! `provides` (WI-1106) and nothing by `requires`. Before the stage, `sort X1 { requires X
//! entity e2(j: Int64) }` over a data sort `X` made `X1` a subtype of `X` (§8.2's refinement):
//! `take(e2(j: 0))` over `take(x: X) = X.get(x)` answered 1. That clause is refused at load,
//! naming both sorts; a data sort requiring a spec and a spec refining a spec run as before.
//!
//! CONTROLS — the back-out ledger at the end of this file.

use anthill_core::eval::Interpreter;
use anthill_core::kb::load::LoadError;

use crate::common::{interp_for, load_errors_of, show_value, unrendered_load_errors_of};

fn call(interp: &mut Interpreter, op: &str) -> String {
    match interp.call(op, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(v) => show_value(interp.kb(), &v),
        Err(e) => panic!("`{op}`: {e:?}"),
    }
}

/// A program of `body` in namespace `p074s5.{ns}`, over the data sort `X` the rows share.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace p074s5.{ns}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Option}}

  sort X
    entity e1(k: Int64)
    operation get(x: Self) -> Int64 = 1
  end
  operation take(x: X) -> Int64 = X.get(x)
{body}
end
"#
    )
}

/// The `RequiresNamesDataSort` refusals of `body`, as (required, requiring) qualified names.
fn refusals(ns: &str, body: &str) -> Vec<(String, String)> {
    unrendered_load_errors_of(&program(ns, body))
        .iter()
        .filter_map(|e| match e.peel() {
            LoadError::RequiresNamesDataSort { required, requiring, .. } => {
                Some((required.clone(), requiring.clone()))
            }
            _ => None,
        })
        .collect()
}

// ── The refusal ────────────────────────────────────────────────────────────────────────────

/// The proposal's row: `X1 requires X` is refused, naming both sorts, where it ran before and
/// answered 1. The CONTROL beside it is the same program without the clause, which loads and
/// runs: so what is refused is the clause, not the program around it.
#[test]
fn x1_requires_x_is_refused_naming_both_sorts() {
    let x1 = "  sort X1
    requires X
    entity e2(j: Int64)
  end
  operation go() -> Int64 = take(e1(k: 0))";
    assert_eq!(
        refusals("row", x1),
        vec![("p074s5.row.X".to_string(), "p074s5.row.X1".to_string())]
    );
    let rendered = load_errors_of(&program("row", x1));
    assert!(
        rendered.iter().any(|e| e.contains("`requires p074s5.row.X`")
            && e.contains("'p074s5.row.X1'")
            && e.contains("DATA sort")),
        "the message names both sorts: {rendered:?}"
    );

    let control = x1.replace("    requires X\n", "");
    let mut interp = interp_for(&program("control", &control));
    assert_eq!(call(&mut interp, "p074s5.control.go"), "1");
}

/// The rule is the named sort's, at every spelling of it: a parametric data sort of an earlier,
/// sealed load (`Option`), an alias of one, an `enum`, a named requirement — and whatever the
/// requiring sort is, a spec without constructors included.
#[test]
fn every_spelling_of_a_data_sort_is_refused() {
    for (ns, body, required, requiring) in [
        (
            "param",
            "  sort P1\n    requires Option[T = Int64]\n    entity p(j: Int64)\n  end",
            "anthill.prelude.Option",
            "p074s5.param.P1",
        ),
        (
            "alias",
            "  sort XA = X\n  sort A1\n    requires XA\n    entity a(j: Int64)\n  end",
            "p074s5.alias.X",
            "p074s5.alias.A1",
        ),
        (
            "enum",
            "  enum Colour\n    entity red\n    entity blue\n  end\n  sort C1\n    requires Colour\n    entity c(j: Int64)\n  end",
            "p074s5.enum.Colour",
            "p074s5.enum.C1",
        ),
        (
            "named",
            "  sort N1\n    requires d: X\n    entity n(j: Int64)\n  end",
            "p074s5.named.X",
            "p074s5.named.N1",
        ),
        (
            "spec",
            "  sort Sp\n    sort T = ?\n    requires X\n    operation f(x: T) -> Int64\n  end",
            "p074s5.spec.X",
            "p074s5.spec.Sp",
        ),
    ] {
        assert_eq!(
            refusals(ns, body),
            vec![(required.to_string(), requiring.to_string())],
            "{ns}"
        );
    }
}

// ── What is unchanged ──────────────────────────────────────────────────────────────────────

/// A data sort requiring a spec is the ordinary case: its requirement is handed to its
/// operations, and `same` answers through `Eq` at `Int64`.
#[test]
fn a_data_sort_requiring_a_spec_loads_and_runs() {
    let body = "  sort Keyed
    sort K = ?
    requires Eq[T = K]
    entity keyed(k: K)
    operation same(a: Self, x: K) -> Bool = PartialEq.eq(a.k, x)
  end
  operation yes() -> Bool = Keyed.same(keyed(k: 3), 3)
  operation no() -> Bool = Keyed.same(keyed(k: 3), 4)";
    let mut interp = interp_for(&program("dict", body));
    assert_eq!(call(&mut interp, "p074s5.dict.yes"), "true");
    assert_eq!(call(&mut interp, "p074s5.dict.no"), "false");
}

/// A spec refining a spec: a body under `requires Ranked[T = X]` reaches `Named.name` through
/// `Ranked`'s own `requires Named[T = T]`, and answers the provider's 105.
#[test]
fn a_spec_refining_a_spec_loads_and_runs() {
    let body = "  sort Named
    sort T = ?
    operation name(x: T) -> Int64
  end
  sort Ranked
    sort T = ?
    requires Named[T = T]
    operation rank(x: T) -> Int64
  end
  sort IntR
    provides Named[T = Int64]
    provides Ranked[T = Int64]
    operation name(x: Int64) -> Int64 = x + 100
    operation rank(x: Int64) -> Int64 = x + 1
  end
  operation viaChain[Y](x: Y) -> Int64 requires Ranked[T = Y] = Named.name(x)
  operation go() -> Int64 = viaChain(5)";
    let mut interp = interp_for(&program("chain", body));
    assert_eq!(call(&mut interp, "p074s5.chain.go"), "105");
}

/// The standard library's `Classical requires Constructive`, itself `requires Minimal`: the
/// refinement is read by `refines`, transitively, as before.
#[test]
fn classical_refines_constructive_as_before() {
    let body = "  import anthill.reflect.typing.{refines}
  import anthill.logic.Classical.{Classical}
  rule up(?s) :- refines(Classical, ?s)";
    let mut kb = crate::common::load_kb_with(&program("logic", body));
    let mut got: Vec<String> = crate::common::query_unary(&mut kb, "p074s5.logic.up")
        .into_iter()
        .map(|(v, _)| show_value(&kb, &v))
        .collect();
    got.sort();
    assert_eq!(got, vec!["Constructive".to_string(), "Minimal".to_string()]);
}

// ── What the refusal removed ───────────────────────────────────────────────────────────────

/// A DERIVED DOMAIN IS ITS OWN SORT'S CONSTRUCTORS. WI-20261104-J9SSG put a value of a sort that
/// refines a data sort in its domain (`sort Other requires Base` made `other(7)` a `Base` at a
/// typed column), and WI-20261115-YR3N7 moved the case to the call, `apply_domain` filling such
/// a value at its own sort. No sort refines one with constructors now, so the case had nothing
/// left to admit and was removed with the refusal, J9SSG's file and YR3N7's two rows with it.
///
/// These are J9SSG's CONTROLS, which passed under its back-outs and must pass with the case
/// gone: a value another sort's constructor heads is in no derived domain, at a plain sort and
/// at a parametric one; a value of the sort is in it at its own instance only; and an unbound
/// column at `Base` is filled with `Base`'s own constructor alone.
#[test]
fn a_value_of_another_sort_is_in_no_derived_domain() {
    use anthill_core::kb::resolve::ResolveConfig;
    let body = "  sort Base
    entity base
  end
  sort Wide
    sort W = ?
    entity wide(w: W)
  end
  sort Narrow
    entity narrow(k: Int64)
  end
  rule allBase(?x: Base) :- true
  rule wideStr(?x: Wide[W = String]) :- true";
    let mut kb = crate::common::load_kb_with(&program("dom", body));
    let mut holds = |pattern: &str| {
        let goal = crate::common::query_pattern_term(&mut kb, pattern);
        kb.resolve(&[goal], &ResolveConfig::default()).iter().any(|s| s.is_definite())
    };
    assert!(!holds("p074s5.dom.allBase(p074s5.dom.Narrow.narrow(3))"), "another sort at `Base`");
    assert!(!holds("p074s5.dom.wideStr(p074s5.dom.Narrow.narrow(3))"), "another sort at `Wide`");
    assert!(holds("p074s5.dom.wideStr(p074s5.dom.Wide.wide(\"a\"))"), "a `Wide` at its instance");
    assert!(!holds("p074s5.dom.wideStr(p074s5.dom.Wide.wide(1))"), "a `Wide` at another");
    assert!(holds("p074s5.dom.allBase(p074s5.dom.Base.base)"), "`Base`'s own");
    let all = crate::common::definite_unary(&mut kb, "p074s5.dom.allBase");
    assert_eq!(all.len(), 1, "`base` alone: {all:?}");
    assert_eq!(crate::common::constructor_qn(&kb, &all[0]), "p074s5.dom.Base.base");
}

// ── The back-out ledger (measured 2026-11-24, one optimized build, the refusal turned off by a
// temporary switch read at load, over the whole of `anthill-core` — 11607 rows; the control, no
// switch, every row passed) ─────────────────────────────────────────────────────────────────
//
// | part backed out | rows that fail |
// |---|---|
// | the refusal in `load_requires_decl` | 4: `x1_requires_x_is_refused_naming_both_sorts`, `every_spelling_of_a_data_sort_is_refused`, `wi_4dyr6…a_requirement_of_a_data_sort_is_refused_in_either_order`, `m460d…a_variant_bearing_spec_is_no_requires_target` |
//
// PASS EITHER WAY BY DESIGN: `a_data_sort_requiring_a_spec_loads_and_runs`,
// `a_spec_refining_a_spec_loads_and_runs` and `classical_refines_constructive_as_before` (what
// the refusal must not reach), and `a_value_of_another_sort_is_in_no_derived_domain`, the
// control of the removed refining case: it asserts what J9SSG's controls asserted on the tree
// before the stage, where they passed, and passes with the case gone. The 20 rewritten census
// files pass either way too, writing no such clause any more.
