//! WI-040 — the kernel DESUGARING VOCAB (reflect `Expr` / `Pattern` constructors,
//! `field_access`, the literal carriers `ListLiteral` / `SetLiteral` / `TupleLiteral`,
//! reflection primitives) resolves to its qualified home with no `<global>` import.
//!
//! WI-20260825-5W3RJ CHANGED HOW, AND THE POLARITY OF TWO ROWS WITH IT — recorded here
//! rather than quietly edited, because it is the measurement.
//!
//! WI-040's mechanism was a RESERVED SHORT NAME: the converter minted `field_access`,
//! and `KERNEL_VOCAB_QUALIFIED` — 28 stdlib addresses written into the resolver — was
//! consulted as the lowest rung of the name ladder when nothing else answered. That
//! encoded one fact twice (the mint site said which form, the table said where it
//! lived) and nothing kept the two agreeing. The converter now names its target
//! outright (`crate::parse::desugar_target`), so a synthesized node resolves through
//! the ordinary ABSOLUTE rung and the table is gone.
//!
//! THE CONSEQUENCE THIS FILE OWNS: a reserved name written BARE, BY HAND, in a query
//! pattern no longer resolves. It was reachable only through the rung that is gone, and
//! this file's two original rows were its ONLY customers in the whole workspace —
//! censused before the change over `anthill-cli`, `anthill-stl`, every `.anthill` source
//! and every Rust fixture; the two other textual hits are prose inside description
//! blocks in `stdlib/anthill/prelude/sort.anthill`. So the population that pays for the
//! deletion is exactly these rows, and what they pay is one `-i` flag.
//!
//! Backing WI-20260825-5W3RJ out inverts every row below: the first three would fail
//! (a bare name would resolve again), and `a_desugared_field_access_carries_its_address`
//! would fail because the minted node would carry the short spelling.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

use crate::common::query_pattern_functor_qn;

fn load_stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib loads clean");
    kb
}

/// Every `field_access`-shaped functor a source text produces, by its PARSE-level name.
fn field_access_functor_names(src: &str) -> Vec<String> {
    let parsed = parse::parse(src).expect("parses");
    let mut out = Vec::new();
    for (_, term) in parsed.terms.iter() {
        if let Term::Fn { functor, .. } = term {
            let n = parsed.symbols.local_name(*functor);
            if n.ends_with("field_access") {
                out.push(n.to_owned());
            }
        }
    }
    out
}

/// A reflection primitive written BARE by hand in a query no longer resolves — it
/// bare-interns, which is what every other unimported name does. The reserved-name rung
/// that used to rescue it is gone.
///
/// THE ASSERTION IS THE OLD ONE INVERTED. Before WI-20260825-5W3RJ this asserted
/// `anthill.reflect.field_access`.
#[test]
fn query_pattern_bare_field_access_no_longer_resolves() {
    let mut kb = load_stdlib_kb();
    let qn = query_pattern_functor_qn(&mut kb, "field_access(object: ?o, field: ?f)");
    assert_eq!(
        qn, "field_access",
        "a bare reserved name in a query is now an ordinary unimported name; got {qn:?}"
    );
}

/// …and the reach is not LOST, only unspelled: the qualified name resolves through the
/// absolute rung, which is what a query author writes (or reaches with
/// `anthill query -i anthill.reflect.field_access`).
///
/// THIS IS THE ROW THAT MAKES THE ONE ABOVE ACCEPTABLE. Without it the pair would read
/// as a capability removed rather than a spelling required.
#[test]
fn query_pattern_qualified_field_access_resolves() {
    let mut kb = load_stdlib_kb();
    let qn = query_pattern_functor_qn(
        &mut kb,
        "anthill.reflect.field_access(object: ?o, field: ?f)",
    );
    assert_eq!(
        qn, "anthill.reflect.field_access",
        "the qualified spelling resolves by qualified name, with no tier involved; \
         got {qn:?}"
    );
}

/// The literal carrier, both ways, for the same reason as the pair above.
#[test]
fn query_pattern_list_literal_needs_its_address() {
    let mut kb = load_stdlib_kb();
    assert_eq!(
        query_pattern_functor_qn(&mut kb, "ListLiteral(?x)"),
        "ListLiteral",
        "bare: an ordinary unimported name"
    );
    assert_eq!(
        query_pattern_functor_qn(&mut kb, "anthill.reflect.ListLiteral(?x)"),
        "anthill.reflect.ListLiteral",
        "qualified: resolves through the absolute rung"
    );
}

/// THE ROW THAT DRIVES THE NEW MECHANISM, and the reason the rows above can lose their
/// rung without losing coverage: a `p.x` written in an operation body is DESUGARED, and
/// the node the converter builds carries the reflect address itself. Nothing looks the
/// name up in a table, and no scope rung stands between the mint and its target.
///
/// FAILS IF a mint site goes back to a short spelling — `dt::FIELD_ACCESS` → the string
/// `"field_access"` in `convert.rs` — which is precisely the back-out.
#[test]
fn a_desugared_field_access_carries_its_address() {
    let names = field_access_functor_names(
        "namespace test.w5w3rj.desugar\n  \
         import anthill.prelude.{Int64}\n  \
         entity Point(x: Int64, y: Int64)\n  \
         operation getx(p: Point) -> Int64 = p.x\n\
         end\n",
    );
    assert_eq!(
        names,
        vec![anthill_core::parse::desugar_target::FIELD_ACCESS.to_owned()],
        "a desugared member access must name its reflect declaration outright, not \
         mint a bare name for a table to look up"
    );
}

/// EVERY DESUGAR TARGET IS DECLARED AFTER A STANDARD LOAD — the invariant the deleted
/// `implicit_target_orphans` half used to cover, restored as a row over the constants
/// the converter actually mints.
///
/// IT IS NOT REDUNDANT WITH THE ROWS BELOW, and the reason is the split registration:
/// `register_stdlib_scopes` pre-defines the literal carriers and the `Expr` entities in
/// Rust, but NOT `anthill.reflect.field_access`, which exists only because
/// `stdlib/anthill/reflect/reflect.anthill` declares it. So the ten addresses are kept
/// in step by two different mechanisms, and a rename in either now surfaces as an
/// unrelated downstream typing error rather than a named orphan report. This row is
/// what names it.
///
/// FAILS IF a constant is edited without its declaration, in either place. Raised by
/// `/code-review`, which caught the module doc claiming "nothing has to be kept in
/// step" — true of the mint-vs-table duplication that was deleted, false of this.
#[test]
fn every_desugar_target_is_declared_by_the_standard_load() {
    use anthill_core::parse::desugar_target as dt;
    let kb = load_stdlib_kb();
    let targets = [
        dt::FIELD_ACCESS,
        dt::HO_APPLY,
        dt::DOT_APPLY,
        dt::SET_LITERAL,
        dt::LIST_LITERAL,
        dt::TUPLE_LITERAL,
        dt::MATCH_EXPR,
        dt::IF_EXPR,
        dt::LET_EXPR,
        dt::LAMBDA_EXPR,
    ];
    let orphans: Vec<&str> = targets
        .iter()
        .copied()
        .filter(|t| {
            let qualified = anthill_core::intern::absolute_path_target(t).unwrap_or(t);
            kb.try_resolve_symbol(qualified).is_none()
        })
        .collect();
    assert!(
        orphans.is_empty(),
        "these desugar targets resolve to nothing after a standard load, so every \
         program using the surface form they lower would fail at its USE site with a \
         diagnostic that names neither the form nor this list: {orphans:?}"
    );
}

/// THE HEAD SEGMENT IS A SCOPE RUNG, AND THE `..` MARKER IS WHAT TAKES IT OUT OF PLAY.
/// A desugar target is written `..anthill.reflect.…`: an UNMARKED `anthill.reflect.X`
/// takes the relative, head-qualified reading (WI-1075), so `resolve_in_scope("anthill",
/// scope)` runs first and any scope where `anthill` denotes something else captures every
/// desugaring in it.
///
/// MEASURED BOTH WAYS on the unmarked version, which is the back-out: a sibling
/// `namespace myapp.anthill` beside the using namespace turned `(a: 1, b: 2)`, `{1, 2}`
/// and `?P(?x)` into "unknown functor" / "names nothing" (3 errors), while renaming that
/// sibling to `myapp.anthillX` loaded clean — 2675 facts either way once marked. A
/// file-local `sort anthill` does it too, which is this row's second arm. Found by
/// `/code-review`; the first cut of this ticket shipped the unmarked spelling AND a spec
/// paragraph asserting a desugaring could not be captured.
///
/// THE BREAKAGE IS PARTIAL, which is why the row drives tuples / sets / lists / `?P(?x)`
/// rather than `if` or `p.x`: those four go through loader arms that are SHAPE-gated and
/// never resolve the functor at all, so they survive an unmarked spelling and would make
/// this row pass while the defect stood.
#[test]
fn a_scope_named_anthill_does_not_capture_a_desugaring() {
    for shadow in [
        "namespace myapp.cap.sibling\n  import anthill.prelude.{Int64}\n  \
         entity Marker(n: Int64)\nend\n",
        "",
    ] {
        let local = if shadow.is_empty() {
            "  sort anthill\n    entity Thing(n: Int64)\n  end\n"
        } else {
            ""
        };
        let src = format!(
            "{shadow}namespace myapp.cap.user\n  \
             import anthill.prelude.{{Int64, Set}}\n{local}  \
             operation tup() -> (a: Int64, b: Int64) = (a: 1, b: 2)\n  \
             operation st() -> Set[T = Int64] = {{1, 2}}\n  \
             rule call(?P, ?x) :- ?P(?x)\n\
             end\n"
        );
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_default();
        assert!(
            errs.is_empty(),
            "a scope named `anthill` must not reach the desugar targets — they are \
             written with the absolute marker precisely so their head segment is not \
             resolved in scope. errors: {errs:#?}"
        );
    }
}

/// A USER-WRITTEN `field_access(...)` still carries the SHORT spelling, which is why
/// the loader's shape questions ask `desugar_target::is` rather than comparing to the
/// address. The two spellings are the same shape and different provenance.
///
/// PASSES BOTH WITH AND WITHOUT the change, by design — it pins the property that made
/// `dt::is` necessary. FAILS if the converter ever starts rewriting a hand-written call
/// to the address, which would silently give it the converter's provenance.
#[test]
fn a_written_field_access_keeps_the_short_spelling() {
    let names = field_access_functor_names(
        "namespace test.w5w3rj.written\n  \
         import anthill.prelude.{Int64}\n  \
         rule r(?o, ?f) :- field_access(?o, ?f)\n\
         end\n",
    );
    assert_eq!(
        names,
        vec!["field_access".to_owned()],
        "a hand-written call is not a desugar; it keeps the name the author typed"
    );
}
